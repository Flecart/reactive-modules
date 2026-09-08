import ReactiveModules.Compiler
import ReactiveModules.Objects

namespace ReactiveModules.Native
open Objects

structure Instruction where
  opcode : Nat
  a : Int := 0
  b : Int := 0
  deriving Repr, DecidableEq

def halt : Instruction := ⟨15,0,0⟩
def Instruction.encode (i : Instruction) : List Int := [i.opcode, i.a, i.b]
def decode (values : List Int) : Instruction :=
  ⟨(values[0]?.getD 15).toNat, values[1]?.getD 0, values[2]?.getD 0⟩

def select (pc : Nat) : Nat → List Instruction → Instruction
  | _, [] => halt
  | base, i :: rest => if pc = base then i else select pc (base+1) rest

theorem select_append (front back : List Instruction) (base pc : Nat) (lower : base ≤ pc) :
    select pc base (front ++ back) =
      if pc < base + front.length then select pc base front else select pc (base+front.length) back := by
  induction front generalizing base with
  | nil => simp [select]; omega
  | cons i rest ih =>
    by_cases same : pc = base
    · subst pc
      simp [select]
    · have next : base+1 ≤ pc := by omega
      simp only [List.cons_append, select, if_neg same, List.length_cons]
      rw [ih (base+1) next]
      have arith : base+1+rest.length = base+(rest.length+1) := by omega
      simp only [arith]

def lookupSource : Nat → List Instruction → Source
  | _, [] => .ret (halt.encode.map Expr.lit)
  | base, i :: rest => .branch (.bin .eq (.var 0) (.lit base))
      (.ret (i.encode.map Expr.lit)) (lookupSource (base+1) rest)

theorem lookup_correct (code : List Instruction) (base pc : Nat) :
    (lookupSource base code).run (fun _ => (pc : Int)) 3 = (select pc base code).encode := by
  induction code generalizing base with
  | nil => rfl
  | cons i rest ih =>
    simp only [lookupSource, Source.run, Source.exec, Expr.eval, Bin.eval, flag, select]
    by_cases h : pc = base
    · subst pc
      simp [Instruction.encode, List.range_succ, Expr.eval]
    · have ne : (pc : Int) ≠ (base : Int) := by exact_mod_cast h
      simpa [h, ne] using ih (base+1)

theorem decode_encode (i : Instruction) : decode i.encode = i := by
  cases i
  simp [decode, Instruction.encode]

inductive Constant where
  | value (v : Value)
  | names (names : List String)
  deriving Repr, BEq

structure Function where
  name : String
  entry : Nat
  parameters : List String
  locals : Nat
  asynchronous : Bool
  retryError : String := ""
  tries : Nat := 1
  deriving Repr, BEq

structure Interface where
  name : String
  kind : String
  methods : List String := []
  deriving Repr, BEq

structure Program where
  code : List Instruction
  pool : List Constant
  functions : List Function
  classes : List (String × List (String × String))
  interfaces : List Interface

def Program.value (p : Program) (i : Int) : Value :=
  match p.pool[i.toNat]? with | some (.value v) => v | _ => .nil
def Program.text (p : Program) (i : Int) : String :=
  match p.value i with | .str s => s | _ => ""
def Program.names (p : Program) (i : Int) : List String :=
  match p.pool[i.toNat]? with | some (.names s) => s | _ => []
def Program.function (p : Program) (name : String) : Option Function :=
  p.functions.find? (fun f => f.name == name)
def Program.interface (p : Program) (name : String) : Option Interface :=
  p.interfaces.find? (fun f => f.name == name)

structure Frame where
  name : String
  pc : Nat
  locals : List Value
  arguments : List Value
  stack : List Value := []
  attempt : Nat := 1
  constructor : Option Value := none
  deriving Repr, BEq

structure Request where
  interface : String
  receiver : Value
  args : List Value
  keywords : List (String × Value) := []
  deriving Repr, BEq

inductive Phase where
  | running | waiting (request : Request) | done (value : Value) | failed (error : Error)
  deriving Repr, BEq

structure State where
  heap : Store
  frames : List Frame
  owner : Nat := 0
  epoch : Nat := 0
  phase : Phase := .running
  output : List String := []
  deriving Repr, BEq

def setTop (s : State) (f : Frame) : State := {s with frames := f :: s.frames.drop 1}
def push (s : State) (v : Value) : State :=
  match s.frames with | [] => {s with phase := .done v} | f :: _ => setTop s {f with stack := v :: f.stack}

def fault (p : Program) (s : State) (error : Error) : List Frame → State
  | [] => {s with frames := [], phase := .failed error}
  | f :: rest =>
    match p.function f.name with
    | some fn =>
      if fn.retryError == error.1 && f.attempt < fn.tries then
        {s with frames := f :: rest, phase := .waiting ⟨"backoff.sleep", .nil,
          [.int f.attempt, .int (2 ^ (f.attempt-1))], []⟩}
      else fault p s error rest
    | none => fault p s error rest

def fail (p : Program) (s : State) (error : Error) := fault p s error s.frames
def lift (p : Program) (s : State) (result : Result) (keep : Bool := true) : State :=
  match result with
  | .error e => fail p s e
  | .ok (heap,value) => if keep then push {s with heap := heap} value else {s with heap := heap}

def bindArguments (fn : Function) (args : List Value) (keywords : List (String × Value)) : Except Error (List Value) := do
  if args.length > fn.parameters.length || keywords.any (fun (name,_) => name ∉ fn.parameters) ||
      keywords.any (fun (name,_) => name ∈ fn.parameters.take args.length) then .error ("TypeError", [])
  else
    let remaining ← (fn.parameters.drop args.length).mapM (fun name =>
      ((keywords.find? (fun pair => pair.1 == name)).map Prod.snd).toExcept ("TypeError", []))
    pure (args ++ remaining)

def enter (p : Program) (s : State) (name : String) (args : List Value)
    (keywords : List (String × Value)) (constructor : Option Value := none) : State :=
  match p.function name with
  | none => fail p s ("NameError", [.str name])
  | some fn => match bindArguments fn args keywords with
    | .error error => fail p s error
    | .ok values => {s with frames := ⟨name, fn.entry,
        values ++ List.replicate (fn.locals-values.length) .unbound, values, [], 1, constructor⟩ :: s.frames}

def resolve (p : Program) (heap : Store) (target : Value) (args : List Value) : Value × List Value :=
  match target with
  | .bound (.ref n) method => match heap[n]? with
    | some obj => match p.classes.find? (fun c => c.1 == obj.kind) with
      | some (_, methods) => match methods.find? (fun m => m.1 == method) with
        | some (_,name) => (.global name, .ref n :: args)
        | none => (target,args)
      | none => (target,args)
    | none => (target,args)
  | _ => (target,args)

def invoke (p : Program) (s : State) (target : Value) (args : List Value)
    (keywords : List (String × Value)) (awaiting : Bool := false) : State := Id.run do
  let (target,args) := resolve p s.heap target args
  match target with
  | .global name =>
    if let some fn := p.function name then
      if fn.asynchronous && !awaiting then return push s (.deferred target args keywords)
      else return enter p s name args keywords
    if let some (_,methods) := p.classes.find? (fun c => c.1 == name) then
      let (heap,ref) := allocate s.heap {kind := name}
      if let some (_,init) := methods.find? (fun m => m.1 == "__init__") then
        return enter p {s with heap := heap} init (ref :: args) keywords (some ref)
      else return push {s with heap := heap} ref
    if let some interface := p.interface name then
      if interface.kind == "exception" then return push s (.exception name args)
      if interface.kind == "record" && args.isEmpty then
        let (heap,ref) := allocate s.heap {kind := name, entries := keywords.map (fun (k,v) => (.str k,v))}
        return push {s with heap := heap} ref
    if name == "print" && keywords.isEmpty then
      return push {s with output := s.output ++ [String.intercalate " " (args.map (display s.heap false)) ++ "\n"]} .nil
    if !keywords.isEmpty then return fail p s ("TypeError", [])
    return lift p s (builtin s.heap name args)
  | .bound receiver method =>
    match object s.heap receiver with
    | .error error => return fail p s error
    | .ok obj =>
      if let some interface := p.interface obj.kind then
        if method ∈ interface.methods then
          if !awaiting then return push s (.deferred target args keywords)
          else return {s with phase := .waiting ⟨obj.kind ++ "." ++ method, receiver, args, keywords⟩}
      if !keywords.isEmpty then return fail p s ("TypeError", [])
      return lift p s (Objects.method s.heap receiver method args)
  | _ => return fail p s ("TypeError", [])

def hasMethod (p : Program) (obj : Object) (name : String) : Bool :=
  let user := ((p.classes.find? (fun c => c.1 == obj.kind)).map Prod.snd).getD []
  let external := ((p.interface obj.kind).map Interface.methods).getD []
  user.any (fun pair => pair.1 == name) || name ∈ external ||
    (if obj.kind == "dict" then name ∈ ["get","copy","clear"]
     else if obj.kind == "Counter" then name ∈ ["get","copy","clear","most_common"]
     else if obj.kind == "set" then name ∈ ["add","discard","remove","copy","clear"]
     else if obj.kind == "list" then name ∈ ["append","copy","clear"] else false)

def execute (p : Program) (s : State) (i : Instruction) : State := Id.run do
  let some frame := s.frames.head? | return {s with phase := .done .nil}
  let f := {frame with pc := frame.pc + 1}
  let stack := f.stack
  let s := setTop s f
  let pop (n : Nat) := setTop s {f with stack := stack.drop n}
  let arg (n : Nat) := stack[n]?.getD .unbound
  let a := i.a.toNat
  match i.opcode with
  | 0 => return push s (p.value i.a)
  | 1 =>
    let value := f.locals[a]?.getD .unbound
    if value == .unbound then return fail p s ("UnboundLocalError", [])
    return push s value
  | 2 => return setTop s {f with locals := f.locals.set a (arg 0), stack := stack.drop 1}
  | 3 => return pop 1
  | 4 => return push s (arg 0)
  | 5 => return push (push s (arg 1)) (arg 0)
  | 6 =>
    match object s.heap (arg 0) with
    | .error _ => return fail p (pop 1) ("AttributeError", [.str (p.text i.a)])
    | .ok obj =>
      let name := p.text i.a
      if obj.kind ∉ ["dict","Counter","set","list","tuple","range","iterator"] then
        if let some value := lookup s.heap (.str name) obj.entries then return push (pop 1) value
      if hasMethod p obj name then return push (pop 1) (.bound (arg 0) name)
      return fail p (pop 1) ("AttributeError", [.str name])
  | 7 =>
    match object s.heap (arg 0) with
    | .error _ => return fail p (pop 2) ("AttributeError", [.str (p.text i.a)])
    | .ok obj =>
      let heap := replace s.heap (arg 0) {obj with entries := put s.heap (.str (p.text i.a)) (arg 1) obj.entries}
      return {pop 2 with heap := heap}
  | 8 => return lift p (pop 2) ((getitem s.heap (arg 1) (arg 0)).map (fun v => (s.heap,v)))
  | 9 => return lift p (pop 3) (setitem s.heap (arg 1) (arg 0) (arg 2)) false
  | 10 => return lift p (pop 2) (binary s.heap (p.text i.a) (arg 1) (arg 0))
  | 11 => return lift p (pop 1) ((unary s.heap (p.text i.a) (arg 0)).map (fun v => (s.heap,v)))
  | 12 =>
    let count := i.b.toNat * (if p.text i.a == "dict" then 2 else 1)
    return lift p (pop count) (build s.heap (p.text i.a) (stack.take count).reverse)
  | 13 =>
    let names := p.names i.b
    let count := a + names.length
    let values := (stack.take count).reverse
    return invoke p (pop (count+1)) (arg count) (values.take a) (names.zip (values.drop a))
  | 14 => match arg 0 with
    | .deferred target args keywords => return invoke p (pop 1) target args keywords true
    | _ => return fail p (pop 1) ("TypeError", [])
  | 15 =>
    let value := arg 0
    let s := {s with frames := s.frames.drop 1}
    if let some constructed := f.constructor then
      if value != .nil then return fail p s ("TypeError", [])
      return push s constructed
    return push s value
  | 16 => return setTop s {f with pc := a}
  | 17 => return setTop s {f with pc := if truth s.heap (arg 0) then f.pc else a, stack := stack.drop 1}
  | 18 => match iterable s.heap (arg 0) with
    | .error error => return fail p (pop 1) error
    | .ok values =>
      if values.length != a then return fail p (pop 1) ("ValueError", [])
      return setTop s {f with stack := values ++ stack.drop 1}
  | 19 => return push (pop 1) (.str (display s.heap (i.a == 114 || i.a == 97) (arg 0)))
  | 20 =>
    let texts := (stack.take a).reverse.map (fun v => match v with | .str t => t | _ => "")
    return push (pop a) (.str (String.join texts))
  | 21 => match arg 0 with
    | .exception name args => return fail p (pop 1) (name,args)
    | _ => return fail p (pop 1) ("TypeError", [])
  | 22 => return push s (.global (p.text i.a))
  | 23 => match iterable s.heap (arg 0) with
    | .error error => return fail p (pop 1) error
    | .ok values => return lift p (pop 1) (.ok (allocate s.heap
        {kind := "iterator", source := arg 0, expected := values.length}))
  | 24 =>
    match object s.heap (arg 0) with
    | .error error => return fail p (pop 1) error
    | .ok it => match iterable s.heap it.source, object s.heap it.source with
      | .ok values, .ok base =>
        if (base.kind == "dict" || base.kind == "Counter") && values.length != it.expected then
          return fail p (pop 1) ("RuntimeError", [])
        if let some value := values[it.cursor]? then
          return push {pop 1 with heap := replace s.heap (arg 0) {it with cursor := it.cursor+1}} value
        else return setTop s {f with pc := a, stack := stack.drop 1}
      | .error error, _ => return fail p (pop 1) error
      | _, .error error => return fail p (pop 1) error
  | 25 => return lift p (pop 2) (delitem s.heap (arg 1) (arg 0)) false
  | 26 => return setTop s {f with stack := arg 1 :: arg 0 :: stack.drop 2}
  | _ => return fail p s ("InvalidInstruction", [])

def step (p : Program) (fetch : Nat → Instruction) (s : State) : State :=
  match s.phase, s.frames with
  | .running, f :: _ => execute p s (fetch f.pc)
  | _, _ => s

def resume (p : Program) (s : State) (owner epoch : Nat) (response : Except Error Value) : State :=
  if owner != s.owner || epoch != s.epoch then s else
  match s.phase with
  | .waiting request =>
    let next := {s with epoch := s.epoch+1, phase := .running}
    match response with
    | .error error =>
      let next := if request.interface == "backoff.sleep" then {next with frames := next.frames.drop 1} else next
      fail p next error
    | .ok value =>
      if request.interface == "backoff.sleep" then
        match next.frames with
        | f :: _ => match p.function f.name with
          | some fn =>
            let fresh := f.arguments ++ List.replicate (fn.locals-f.arguments.length) .unbound
            setTop next {f with pc := fn.entry, stack := [], attempt := f.attempt+1, locals := fresh}
          | none => fail p next ("NameError", [])
        | [] => next
      else push next value
  | _ => s

inductive Action where
  | tick
  | reply (owner epoch : Nat) (response : Except Error Value)

def run (p : Program) (fetch : Nat → Instruction) : State → List Action → State
  | s, [] => s
  | s, .tick :: rest => run p fetch (step p fetch s) rest
  | s, .reply owner epoch response :: rest => run p fetch (resume p s owner epoch response) rest

theorem step_correct (p : Program) (compiled : Nat → Instruction)
    (correct : ∀ pc, compiled pc = select pc 0 p.code) (s : State) :
    step p compiled s = step p (fun pc => select pc 0 p.code) s := by
  rw [show compiled = (fun pc => select pc 0 p.code) from funext correct]

/-- All finite executions, arbitrary unbounded stores, nested call stacks,
    error paths and external replies. The generated certificate discharges
    instruction-selection equality using the actual exported RM graph. -/
theorem execution_correct (p : Program) (compiled : Nat → Instruction)
    (correct : ∀ pc, compiled pc = select pc 0 p.code) (s : State) (actions : List Action) :
    run p compiled s actions = run p (fun pc => select pc 0 p.code) s actions := by
  rw [show compiled = (fun pc => select pc 0 p.code) from funext correct]

theorem stale_resume (p : Program) (s : State) (owner epoch : Nat) (response : Except Error Value)
    (stale : owner ≠ s.owner ∨ epoch ≠ s.epoch) : resume p s owner epoch response = s := by
  rcases stale with h | h <;> simp [resume, h]

/-- Set storage order is not an observable part of this profile. Other heap
    fields, dictionary order, aliases, frames, requests, and errors are compared. -/
def objectAgrees (a b : Object) : Bool :=
  if a.kind == "set" && b.kind == "set" then
    a.entries.length == b.entries.length && a.entries.all (fun x => b.entries.any (fun y => x == y))
  else a == b

def agrees (a b : State) : Bool :=
  a.heap.length == b.heap.length && (a.heap.zip b.heap).all (fun (x,y) => objectAgrees x y) &&
  a.frames == b.frames && a.owner == b.owner && a.epoch == b.epoch && a.phase == b.phase && a.output == b.output

end ReactiveModules.Native
