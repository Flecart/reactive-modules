"""Independent language, artifact and semantic regressions for the checked frontend."""
import dataclasses
import importlib.util
from pathlib import Path
import random
import shutil
import sys

import pytest

from zrth.verified import compile_module, UnsupportedPython

ROOT = Path(__file__).resolve().parents[2] / "verification"
needs_lean = pytest.mark.skipif(shutil.which("lake") is None, reason="install Lean for certificate checks; verification CI requires it")


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def compile_text(tmp_path, text, names=("step",)):
    path = tmp_path / "source.py"
    path.write_text(text)
    return compile_module(path, names)


@pytest.fixture(scope="module")
def channel():
    path = ROOT / "examples" / "channel.py"
    return load(path, "verified_channel_example"), compile_module(path, ["initial_sender", "initial_receiver", "sender", "receiver"])


def matches(bundle, name, fn, *args):
    actual = fn(*args)
    expected = bundle.metadata[name]["output_type"].encode(actual)
    assert bundle.run(name, *args) == expected
    return actual


def test_unbounded_register_arithmetic():
    path = ROOT / "examples" / "register.py"
    m = load(path, "verified_register_example")
    b = compile_module(path, ["initial", "step"])
    matches(b, "initial", m.initial)
    for current in [-2**100, -1, 0, 5, 2**100]:
        for offered in [-2**100, -3, 0, 12, 2**100]:
            matches(b, "step", m.step, m.State(current), offered)


def test_channel_all_local_branches(channel):
    m, b = channel
    matches(b, "initial_sender", m.initial_sender)
    matches(b, "initial_receiver", m.initial_receiver)
    for n in range(4):
        for busy in (False, True):
            for kind in m.EventKind:
                for packet_n in range(-1, 6):
                    matches(b, "sender", m.sender, m.Sender(n, busy, 77), m.Event(kind, packet_n, -123))
        for packet_n in range(-1, 6):
            matches(b, "receiver", m.receiver, m.Receiver(n), m.Packet(packet_n, 10))


@pytest.mark.parametrize("seed", range(12))
def test_loss_duplicate_reordering_histories(channel, seed):
    m, b = channel
    rng = random.Random(seed)
    sender, receiver = m.initial_sender(), m.initial_receiver()
    data, acks, offered, delivered = [], [], [], []
    completed = 0
    for _ in range(300):
        action = rng.randrange(6)
        if action in (0, 1, 2):
            if action == 0:
                event = m.Event(m.EventKind.SUBMIT, 0, rng.randrange(-20, 20))
            elif action == 1:
                event = m.Event(m.EventKind.TICK, 0, 0)
            elif acks:
                event = m.Event(m.EventKind.ACK, acks.pop(rng.randrange(len(acks))), 0)
            else:
                continue
            sender, effects = matches(b, "sender", m.sender, sender, event)
            if effects.accepted: offered.append(event.value)
            if effects.completed: completed += 1
            if effects.send: data.append(m.Packet(effects.number, effects.value))
        elif action == 3 and data:
            packet = data.pop(rng.randrange(len(data)))
            receiver, effects = matches(b, "receiver", m.receiver, receiver, packet)
            if effects.ack: acks.append(effects.number)
            if effects.deliver: delivered.append(effects.value)
        else:
            queue = rng.choice([data, acks])
            if queue:
                if action == 4: queue.pop(rng.randrange(len(queue)))
                else: queue.append(rng.choice(queue))
        assert delivered == offered[:len(delivered)]
        assert completed <= len(delivered) <= len(offered)
        assert len(offered) - completed <= 1


@needs_lean
def test_record_assignment_is_simultaneous_and_early_return(tmp_path):
    text = '''from dataclasses import dataclass
@dataclass(frozen=True)
class Pair:
    x: int
    y: int
def step(p: Pair, early: bool) -> Pair:
    p = Pair(p.y, p.x)
    if early:
        return p
    p = Pair(p.x + 1, p.y - 1)
    return p
'''
    b = compile_text(tmp_path, text)
    m = load(tmp_path / "source.py", "record_assignment_example")
    for flag in (True, False): matches(b, "step", m.step, m.Pair(3, 7), flag)
    b.certify(tmp_path / "checked")


@needs_lean
def test_optional_presence_and_narrowing(tmp_path):
    b = compile_text(tmp_path, '''from dataclasses import dataclass
@dataclass(frozen=True)
class Box:
    value: int
def step(box: Box | None) -> int:
    if box is not None:
        return box.value
    return -1
''')
    m = load(tmp_path / "source.py", "optional_example")
    for value in (None, m.Box(0), m.Box(4)):
        matches(b, "step", m.step, value)
    b.certify(tmp_path / "checked")


@pytest.mark.parametrize("text", [
    "async def step(x: int) -> int:\n    return x\n",
    "def step(x: int) -> int:\n    print(x)\n    return x\n",
    "def step(x: int) -> int:\n    while x > 0:\n        x = x - 1\n    return x\n",
    "def step(x: int) -> int:\n    return abs(x)\n",
    "def step(x: int) -> int:\n    if x:\n        return 1\n    return 0\n",
    "def step(x: int) -> int:\n    return x / 2\n",
    "def step(x: int) -> int:\n    return True\n",
    "def step(x: int) -> int:\n    return [x][0]\n",
    "def step(x: int) -> int:\n    return globals()['x']\n",
])
def test_rejects_unsupported_with_source_location(tmp_path, text):
    with pytest.raises(UnsupportedPython, match=r"source.py:\d+:\d+:"):
        compile_text(tmp_path, text)


@needs_lean
def test_lean_rejects_tampered_rm(tmp_path):
    b = compile_text(tmp_path, "def step(x: int) -> int:\n    return x + 1\n")
    for term in b.artifact["functions"]["step"]["graph"]["terms"]:
        if term == ["lit", 1]: term[1] = 2
    with pytest.raises(ValueError, match="Lean rejected"):
        b.certify(tmp_path / "tampered")
    assert '"translation": "not-established"' in (tmp_path / "tampered" / "status.json").read_text()


@needs_lean
def test_lean_rejects_bad_wire_reference(tmp_path):
    b = compile_text(tmp_path, "def step(x: int) -> int:\n    return x + 1\n")
    b.artifact["functions"]["step"]["graph"]["outputs"] = [99999]
    with pytest.raises(ValueError, match="Lean rejected"):
        b.certify(tmp_path / "tampered")


def test_stale_source_is_rejected(tmp_path):
    b = compile_text(tmp_path, "def step(x: int) -> int:\n    return x + 1\n")
    (tmp_path / "source.py").write_text("def step(x: int) -> int:\n    return x + 2\n")
    with pytest.raises(ValueError, match="source changed"):
        b.write(tmp_path / "stale")


def test_partial_initialization_is_rejected(tmp_path):
    with pytest.raises(ValueError):
        compile_text(tmp_path, "def step(b: bool) -> int:\n    if b:\n        x = 1\n    return x\n")


def test_ast_and_rm_cannot_both_be_replaced_behind_source_hash(tmp_path):
    b = compile_text(tmp_path, "def step(x: int) -> int:\n    return x + 1\n")
    b.artifact["functions"]["step"]["source"] = ["ret", [["lit", 999]]]
    with pytest.raises(ValueError, match="trusted parser output"):
        b.write(tmp_path / "tampered")


def test_graph_data_cannot_inject_lean_code(tmp_path):
    b = compile_text(tmp_path, "def step(x: int) -> int:\n    return x + 1\n")
    b.artifact["functions"]["step"]["graph"]["terms"][0] = ["lit", "0); axiom exploit : False"]
    with pytest.raises(ValueError, match="invalid expression"):
        b.write(tmp_path / "injected")


@pytest.mark.parametrize("tail", [
    "@unknown\ndef unused() -> int:\n    return 0\n",
    "def unused(x: int = dangerous()) -> int:\n    return x\n",
    "def unused(x: dangerous()) -> int:\n    return 0\n",
    "def dataclass() -> int:\n    return 0\n",
])
def test_rejects_module_load_effects_even_in_unused_functions(tmp_path, tail):
    with pytest.raises(UnsupportedPython):
        compile_text(tmp_path, "def step(x: int) -> int:\n    return x\n" + tail)


@needs_lean
def test_assumed_property_is_not_a_verified_property(tmp_path):
    b = compile_text(tmp_path, "def step(x: int) -> int:\n    return x\n")
    output = b.certify(tmp_path / "checked")
    proof = tmp_path / "false_property.lean"
    proof.write_text("import Certificate\naxiom invented : False\ntheorem fake : False := invented\n")
    with pytest.raises(ValueError, match="unapproved proof dependencies"):
        b.check_properties(output, proof, ["fake"])
    assert '"status": "not-established"' in (output / "status.json").read_text()


@needs_lean
def test_modified_checked_certificate_is_rejected(tmp_path):
    b = compile_text(tmp_path, "def step(x: int) -> int:\n    return x\n")
    output = b.certify(tmp_path / "checked")
    (output / "Certificate.lean").write_text("-- different certificate\n")
    with pytest.raises(ValueError, match="stale or tampered evidence"):
        b.check_properties(output, ROOT / "proofs/register.lean", ["Register.never_decreases"])
