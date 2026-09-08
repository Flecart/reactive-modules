"""Native syntax regressions independent of any consensus protocol."""
import copy

import pytest

from zrth.native_frontend import Frontend
from zrth.native_runtime import Machine, Object, Pending, Finished, Failed, InterfaceError
from zrth.verified_native import compile_native
from zrth.native_checks import Recorder
from .test_verified import load, needs_lean


def module(tmp_path, source, config=None):
    path = tmp_path / "native.py"
    path.write_text(source)
    return compile_native(path, config), load(path, "native_fixture")


def native_result(bundle, function, *args):
    task = bundle.task(function, *args)
    result = task.run(fuel=100000)
    assert result is not None, "test execution exhausted fuel (not a successful result)"
    if isinstance(result, Failed): raise result.error
    assert isinstance(result, Finished)
    return result.value


def test_dictionaries_sets_counter_aliases_and_numeric_keys(tmp_path):
    b, m = module(tmp_path, '''from collections import Counter
def step(key, value):
    d = {}
    d[key] = set()
    alias = d[key]
    alias.add(value)
    alias.add(value)
    copied = alias.copy()
    alias.discard(value)
    c = Counter()
    c["first"] += 1
    c["second"] += 1
    winner, count = c.most_common(1)[0]
    d[True] = 9
    return (len(copied), len(alias), winner, count, d.get(1), d.get("missing", -1))
''')
    for key in (-2**100, "x", None):
        assert native_result(b, "step", key, 7) == m.step(key, 7)


def test_nested_mutation_unpacking_and_augmented_assignment(tmp_path):
    b, m = module(tmp_path, '''def step():
    d = {"x": {2: [1]}}
    alias = d["x"][2]
    d["x"][2] += [3]
    a, (b, c) = (1, (2, 3))
    d["x"][2][0] += 8
    return (alias, a, b, c)
''')
    assert native_result(b, "step") == m.step()


def test_control_flow_loops_short_circuit_and_early_returns(tmp_path):
    b, m = module(tmp_path, '''def helper(x):
    if x > 2:
        return x + 3
    return x - 7
def step(x):
    total = 0
    for i in range(x):
        if i == 1:
            continue
        if i == 8:
            break
        total += helper(i)
    else:
        total += 100
    while x > 0:
        x -= 1
        if x == 3:
            return total
    return (total, False and {}["missing"], 1 < 2 < 3, True or {}["missing"])
''')
    for x in (-1, 0, 2, 7, 20):
        assert native_result(b, "step", x) == m.step(x)


def test_async_helpers_and_awaits_inside_branches_loops_and_expressions(tmp_path):
    b, m = module(tmp_path, '''async def helper(x):
    if x < 0:
        return 0
    return x + 1
async def step(x):
    d = {}
    for i in range(x):
        if i > 1:
            d[i] = 2 + await helper(i)
        else:
            d[i] = await helper(-i)
    return d
''')
    import asyncio
    for x in (0, 1, 5):
        assert native_result(b, "step", x) == asyncio.run(m.step(x))


@pytest.mark.parametrize("operation,error", [("d[3]", KeyError), ("c.most_common(1)[0]", IndexError), ("d[[3]]", TypeError)])
def test_native_errors_are_not_repaired(tmp_path, operation, error):
    b, m = module(tmp_path, f'''from collections import Counter
def step():
    d = {{}}
    c = Counter()
    return {operation}
''')
    with pytest.raises(error): m.step()
    with pytest.raises(error): native_result(b, "step")


def test_external_suspension_preserves_frames_and_rejects_replay(tmp_path):
    path = tmp_path / "native.py"
    path.write_text('''async def step(port):
    d = {"x": set()}
    d["x"].add(7)
    reply = await port.send(d)
    d["x"].add(reply)
    return len(d["x"])
''')
    b = compile_native(path, {"interfaces": {"Port": {"async_methods": ["send"]}}})
    task = b.task("step", Object("Port"))
    pending = task.run()
    assert isinstance(pending, Pending) and pending.args == ({"x": {7}},)
    assert task.resume(pending, 8) == Finished(2)
    with pytest.raises(RuntimeError): task.resume(pending, 9)


def test_retry_keeps_heap_mutations_and_restarts_local_frame(tmp_path):
    path = tmp_path / "native.py"
    path.write_text('''import backoff
from interface import DeliveryError
class Actor:
    def __init__(self, port):
        self.port = port
        self.count = 0
    @backoff.on_exception(backoff.expo, DeliveryError, max_tries=3)
    async def step(self):
        self.count += 1
        reply = await self.port.send(self.count)
        return reply
''')
    config = {"interfaces": {"Port": {"async_methods": ["send"]}, "interface.DeliveryError": "exception"}}
    b = compile_native(path, config)
    actor = b.construct("Actor", Object("Port"))
    task = b.task("Actor.step", actor)
    pending = task.run()
    for attempt in (1, 2):
        assert pending.args == (attempt,)
        delay = task.resume(pending, error=InterfaceError("interface.DeliveryError", "failed"))
        assert delay.interface == "backoff.sleep" and delay.args == (attempt, 2**(attempt-1))
        pending = task.resume(delay)
    assert pending.args == (3,)
    assert task.resume(pending, 11) == Finished(11)
    assert actor.fields["count"] == 3


@needs_lean
def test_native_translation_certificate_and_tamper_rejection(tmp_path):
    b, _ = module(tmp_path, '''async def helper(x):
    return x + 1
async def step(x):
    d = {}
    for i in range(x):
        d[i] = await helper(i)
    return d
''')
    b.certify(tmp_path / "checked")
    assert "native_execution_correct" in (tmp_path / "checked/Certificate.lean").read_text()
    b.artifact["native_program"]["instructions"][0][1] += 1
    with pytest.raises(ValueError, match="source/control/schema"):
        b.certify(tmp_path / "tampered")


def test_foreign_and_cyclic_inputs_fail_before_execution(tmp_path):
    b, _ = module(tmp_path, "def step(value):\n    return value\n")
    cyclic = []
    cyclic.append(cyclic)
    for value in (object(), 1.5, cyclic, "\ud800"):
        with pytest.raises(TypeError): b.task("step", value)
    shared = []
    assert native_result(b, "step", [shared, shared]) == [[], []]


@pytest.mark.parametrize("source", [
    "def step():\n    return dict(a=1)\n",
    "def step(a, b):\n    return a is b\n",
    "class Value:\n    def __eq__(self, other):\n        return True\n",
    "print('must not execute')\ndef step():\n    return 1\n",
])
def test_unsupported_semantics_fail_closed(tmp_path, source):
    path = tmp_path / "bad.py"
    path.write_text(source)
    with pytest.raises(ValueError): compile_native(path)


@needs_lean
def test_native_primitive_samples_are_kernel_replayed(tmp_path):
    b, original = module(tmp_path, '''from collections import Counter
async def helper(value):
    return value + 1
async def step(text):
    d = {"text": text}
    alias = d
    d[True] = 7
    d[1] += await helper(1)
    for i in range(2):
        d[i + 3] = await helper(i)
    seen = {9, 7}
    seen.add(9)
    seen.discard(7)
    copied = seen.copy()
    seen.clear()
    counts = Counter()
    counts["first"] += 1
    counts["second"] += 1
    winner, count = counts.most_common(1)[0]
    print(f"{d}")
    return (alias[1], len(copied), winner, -7 // -2, -7 % -2)
''')
    recorder = Recorder(per_signature=1)
    task = recorder.attach(b.task("step", "\x00\x1b\u200b😀"))
    assert task.run() == Finished((9, 1, "first", 3, -1))
    import asyncio
    import io
    from contextlib import redirect_stdout
    printed = io.StringIO()
    with redirect_stdout(printed):
        assert asyncio.run(original.step("\x00\x1b\u200b😀")) == task.result.value
    assert printed.getvalue() == "".join(event[1] for event in task.events if event[0] == "print")
    output = tmp_path / "checked"
    b.certify(output)
    recorder.check(b, output)
    assert "decide +kernel" in (output / "RuntimeChecks.lean").read_text()
    # Sample replay must bind the recorded instruction to the source PC.
    recorder.samples[0]["instruction"][1] += 1
    with pytest.raises(ValueError, match="sample failed"):
        recorder.check(b, output)


def test_constructor_rejects_non_none_return(tmp_path):
    b, m = module(tmp_path, "class Bad:\n    def __init__(self):\n        return 1\n")
    with pytest.raises(TypeError): m.Bad()
    with pytest.raises(TypeError): b.construct("Bad")
