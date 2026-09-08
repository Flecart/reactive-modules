import Std
import ReactiveModules.Unicode

def Option.toExcept (value : Option α) (error : ε) : Except ε α :=
  match value with | some a => .ok a | none => .error error

namespace ReactiveModules.Objects

/-- Unbounded tagged values. References preserve object identity and aliasing;
    bool and int stay distinct tags but compare as Python numeric keys. -/
inductive Value where
  | nil | unbound
  | int (n : Int)
  | bool (b : Bool)
  | str (s : String)
  | ref (n : Nat)
  | global (name : String)
  | bound (receiver : Value) (name : String)
  | deferred (target : Value) (args : List Value) (keywords : List (String × Value))
  | exception (name : String) (args : List Value)
  deriving Repr, Inhabited

/-- Total, kernel-reducible structural comparison. The default nested-inductive
    BEq derivation uses a partial implementation and cannot replay certificates. -/
def Value.structural : Nat → Value → Value → Bool
  | 0, _, _ => false
  | fuel+1, a, b => match a,b with
    | .nil, .nil | .unbound, .unbound => true
    | .int x, .int y => x == y
    | .bool x, .bool y => x == y
    | .str x, .str y | .global x, .global y => x == y
    | .ref x, .ref y => x == y
    | .bound x n, .bound y m => n == m && structural fuel x y
    | .exception n xs, .exception m ys => n == m && xs.length == ys.length &&
        (xs.zip ys).all (fun (x,y) => structural fuel x y)
    | .deferred f xs kws, .deferred g ys keys =>
        structural fuel f g && xs.length == ys.length &&
        (xs.zip ys).all (fun (x,y) => structural fuel x y) && kws.length == keys.length &&
        (kws.zip keys).all (fun ((n,x),(m,y)) => n == m && structural fuel x y)
    | _, _ => false

def Value.depth : Value → Nat
  | .bound receiver _ => receiver.depth + 1
  | .exception _ args => (args.map Value.depth).sum + 1
  | .deferred target args keywords => target.depth + (args.map Value.depth).sum +
      (keywords.map (fun (pair : String × Value) =>
        have smaller : sizeOf pair.2 < sizeOf pair := by cases pair; simp; omega
        pair.2.depth)).sum + 1
  | _ => 1
termination_by value => sizeOf value
decreasing_by
  all_goals simp_wf
  all_goals first
    | decreasing_tactic
    | (have bound := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)

instance : BEq Value := ⟨fun a b => Value.structural (a.depth + b.depth + 1) a b⟩

structure Object where
  kind : String
  entries : List (Value × Value) := []
  items : List Value := []
  source : Value := .nil
  cursor : Nat := 0
  expected : Nat := 0
  deriving Repr, BEq

abbrev Store := List Object
abbrev Error := String × List Value
abbrev Result := Except Error (Store × Value)

def number : Value → Option Int
  | .int n => some n
  | .bool b => some (if b then 1 else 0)
  | _ => none

def object (heap : Store) : Value → Except Error Object
  | .ref n => (heap[n]?).toExcept ("ReferenceError", [])
  | _ => .error ("TypeError", [])

def allocate (heap : Store) (obj : Object) : Store × Value := (heap ++ [obj], .ref heap.length)

def replace (heap : Store) (reference : Value) (obj : Object) : Store :=
  match reference with | .ref n => heap.set n obj | _ => heap

def truth (heap : Store) : Value → Bool
  | .nil | .unbound => false
  | .int n => n != 0
  | .bool b => b
  | .str s => !s.isEmpty
  | .ref n => match heap[n]? with
    | some obj => if obj.kind == "dict" || obj.kind == "Counter" || obj.kind == "set" then !obj.entries.isEmpty
      else if obj.kind == "tuple" || obj.kind == "list" || obj.kind == "range" then !obj.items.isEmpty else true
    | none => false
  | _ => true

/-- Fuel is a structural recursion bound derived from the object graph, not a
    heap capacity or execution bound. Cyclic equality requires explicit policy. -/
def equal (heap : Store) : Nat → Value → Value → Bool
  | 0, a, b => a == b
  | fuel + 1, a, b =>
    if a == b then true else
    match number a, number b with
    | some x, some y => x == y
    | _, _ => match a, b with
      | .ref x, .ref y => match heap[x]?, heap[y]? with
        | some p, some q =>
          if p.kind == "Counter" && q.kind == "Counter" then
            (p.entries ++ q.entries).all (fun (key,_) =>
              equal heap fuel
                (((p.entries.find? (fun pair => equal heap fuel key pair.1)).map Prod.snd).getD (.int 0))
                (((q.entries.find? (fun pair => equal heap fuel key pair.1)).map Prod.snd).getD (.int 0)))
          else if (p.kind == "dict" || p.kind == "Counter") && (q.kind == "dict" || q.kind == "Counter") then
            p.entries.length == q.entries.length && p.entries.all (fun (k,v) =>
              q.entries.any (fun (l,w) => equal heap fuel k l && equal heap fuel v w))
          else if p.kind == q.kind && (p.kind == "tuple" || p.kind == "list" || p.kind == "range") then
            p.items.length == q.items.length && (p.items.zip q.items).all (fun (v,w) => equal heap fuel v w)
          else if p.kind == "set" && q.kind == "set" then
            p.entries.length == q.entries.length && p.entries.all (fun (k,_) => q.entries.any (fun (l,_) => equal heap fuel k l))
          else false
        | _, _ => false
      | _, _ => false

def eq (heap : Store) := equal heap (heap.length + 1)

def hashable (heap : Store) : Nat → Value → Bool
  | 0, .ref _ => false
  | fuel + 1, .ref n => match heap[n]? with
    | some obj => obj.kind == "tuple" && obj.items.all (hashable heap fuel)
    | none => false
  | _, .nil | _, .int _ | _, .bool _ | _, .str _ => true
  | _, _ => false

def lookup (heap : Store) (key : Value) (entries : List (Value × Value)) : Option Value :=
  (entries.find? (fun pair => eq heap key pair.1)).map Prod.snd

def put (heap : Store) (key value : Value) : List (Value × Value) → List (Value × Value)
  | [] => [(key, value)]
  | (k,v) :: rest => if eq heap key k then (k,value) :: rest else (k,v) :: put heap key value rest

def index (items : List Value) (key : Value) : Except Error Value := do
  let n ← (number key).toExcept ("TypeError", [])
  let position := if n < 0 then (items.length : Int) + n else n
  if position < 0 then .error ("IndexError", [])
  else (items[position.toNat]?).toExcept ("IndexError", [])

def getitem (heap : Store) (container key : Value) : Except Error Value := do
  let obj ← object heap container
  if obj.kind == "dict" || obj.kind == "Counter" then
    if !hashable heap (heap.length + 1) key then .error ("TypeError", [])
    else match lookup heap key obj.entries with
      | some value => pure value
      | none => if obj.kind == "Counter" then pure (.int 0) else .error ("KeyError", [key])
  else if obj.kind == "list" || obj.kind == "tuple" || obj.kind == "range" then index obj.items key
  else .error ("TypeError", [])

def setitem (heap : Store) (container key value : Value) : Result := do
  let obj ← object heap container
  if obj.kind == "dict" || obj.kind == "Counter" then
    if !hashable heap (heap.length + 1) key then .error ("TypeError", [])
    else pure (replace heap container {obj with entries := put heap key value obj.entries}, .nil)
  else if obj.kind == "list" then
    let _ ← index obj.items key
    let n := (number key).getD 0
    let position := if n < 0 then (obj.items.length : Int) + n else n
    pure (replace heap container {obj with items := obj.items.set position.toNat value}, .nil)
  else .error ("TypeError", [])

def delitem (heap : Store) (container key : Value) : Result := do
  let obj ← object heap container
  if obj.kind == "dict" || obj.kind == "Counter" then
    if !hashable heap (heap.length + 1) key then .error ("TypeError", [])
    else if (lookup heap key obj.entries).isNone && obj.kind != "Counter" then .error ("KeyError", [key])
    else pure (replace heap container {obj with entries := obj.entries.filter (fun pair => !eq heap pair.1 key)}, .nil)
  else .error ("TypeError", [])

def contains (heap : Store) (container key : Value) : Except Error Bool := do
  let obj ← object heap container
  if obj.kind == "dict" || obj.kind == "Counter" || obj.kind == "set" then
    if !hashable heap (heap.length + 1) key then .error ("TypeError", [])
    else pure ((lookup heap key obj.entries).isSome)
  else if obj.kind == "list" || obj.kind == "tuple" || obj.kind == "range" then
    pure (obj.items.any (eq heap key))
  else .error ("TypeError", [])

def size (heap : Store) : Value → Except Error Int
  | .str s => pure s.length
  | value => do
    let obj ← object heap value
    if obj.kind == "dict" || obj.kind == "Counter" || obj.kind == "set" then pure obj.entries.length
    else if obj.kind == "list" || obj.kind == "tuple" || obj.kind == "range" then pure obj.items.length
    else .error ("TypeError", [])

def floor (a b : Int) : Int := if b < 0 then (-a) / (-b) else a / b

def binary (heap : Store) (op : String) (a b : Value) : Result := do
  if op == "eq" then return (heap, .bool (eq heap a b))
  if op == "ne" then return (heap, .bool (!eq heap a b))
  if op == "is" then return (heap, .bool (a == b))
  if op == "isnot" then return (heap, .bool (a != b))
  if op == "in" || op == "notin" then
    let found ← contains heap b a
    return (heap, .bool (if op == "in" then found else !found))
  if op == "add" || op == "iadd" then
    match a, b with
    | .str x, .str y => return (heap, .str (x ++ y))
    | .ref x, .ref y =>
      let p ← (heap[x]?).toExcept ("ReferenceError", [])
      let q ← (heap[y]?).toExcept ("ReferenceError", [])
      if p.kind == q.kind && (p.kind == "list" || p.kind == "tuple") then
        if op == "iadd" && p.kind == "list" then return (heap.set x {p with items := p.items ++ q.items}, a)
        else return allocate heap {p with items := p.items ++ q.items}
    | _, _ => pure ()
  let x ← (number a).toExcept ("TypeError", [])
  let y ← (number b).toExcept ("TypeError", [])
  let value ← match op with
    | "add" | "iadd" => pure (.int (x+y))
    | "sub" | "isub" => pure (.int (x-y))
    | "mul" | "imul" => pure (.int (x*y))
    | "floordiv" | "ifloordiv" => if y == 0 then .error ("ZeroDivisionError", []) else pure (.int (floor x y))
    | "mod" | "imod" => if y == 0 then .error ("ZeroDivisionError", []) else pure (.int (x-y*floor x y))
    | "lt" => pure (.bool (x < y))
    | "le" => pure (.bool (x ≤ y))
    | "gt" => pure (.bool (x > y))
    | "ge" => pure (.bool (x ≥ y))
    | _ => .error ("TypeError", [])
  pure (heap, value)

def unary (heap : Store) (op : String) (v : Value) : Except Error Value := do
  if op == "not" then return .bool (!truth heap v)
  let n ← (number v).toExcept ("TypeError", [])
  return .int (if op == "neg" then -n else n)

def buildPairs (heap : Store) : List Value → List (Value × Value) → Except Error (List (Value × Value))
  | [], entries => pure entries
  | key :: value :: rest, entries =>
    if hashable heap (heap.length + 1) key then buildPairs heap rest (put heap key value entries)
    else .error ("TypeError", [])
  | _, _ => .error ("TypeError", [])

def build (heap : Store) (kind : String) (values : List Value) : Result := do
  if kind == "dict" || kind == "Counter" then
    let entries ← buildPairs heap values []
    return allocate heap {kind := kind, entries := entries}
  if kind == "set" then
    let entries ← buildPairs heap (values.flatMap (fun v => [v, .nil])) []
    return allocate heap {kind := kind, entries := entries}
  return allocate heap {kind := kind, items := values}

def rankedInsert (entry : Value × Value) : List (Value × Value) → List (Value × Value)
  | [] => [entry]
  | x :: xs => if (number entry.2).getD 0 ≥ (number x.2).getD 0 then entry :: x :: xs
    else x :: rankedInsert entry xs

def ranked : List (Value × Value) → List (Value × Value)
  | [] => []
  | x :: xs => rankedInsert x (ranked xs)

def pairsToTuples : Store → List (Value × Value) → Store × List Value
  | heap, [] => (heap, [])
  | heap, (key,value) :: rest =>
    let (after, ref) := allocate heap {kind := "tuple", items := [key,value]}
    let (last, refs) := pairsToTuples after rest
    (last, ref :: refs)

/-- Counter tie-breaking is stable insertion order, not a sorted-key policy. -/
def mostCommon (heap : Store) (obj : Object) (count : Int) : Result :=
  if obj.entries.any (fun pair => (number pair.2).isNone) then .error ("TypeError", [])
  else
    let selected := (ranked obj.entries).take count.toNat
    let (withList, ref) := allocate heap {kind := "list"}
    let (after, refs) := pairsToTuples withList selected
    .ok (replace after ref {kind := "list", items := refs}, ref)

def method (heap : Store) (receiver : Value) (name : String) (args : List Value) : Result := do
  let obj ← object heap receiver
  match name, args with
  | "get", key :: rest =>
    if !(obj.kind == "dict" || obj.kind == "Counter") || rest.length > 1 || !hashable heap (heap.length+1) key then
      .error ("TypeError", [])
    else pure (heap, (lookup heap key obj.entries).getD (rest.headD .nil))
  | "copy", [] => pure (allocate heap obj)
  | "clear", [] => pure (replace heap receiver {obj with entries := [], items := []}, .nil)
  | "add", [key] =>
    if obj.kind != "set" || !hashable heap (heap.length+1) key then .error ("TypeError", [])
    else pure (replace heap receiver {obj with entries := put heap key .nil obj.entries}, .nil)
  | "discard", [key] | "remove", [key] =>
    if obj.kind != "set" || !hashable heap (heap.length+1) key then .error ("TypeError", [])
    else if name == "remove" && (lookup heap key obj.entries).isNone then .error ("KeyError", [key])
    else pure (replace heap receiver {obj with entries := obj.entries.filter (fun p => !eq heap p.1 key)}, .nil)
  | "append", [value] =>
    if obj.kind != "list" then .error ("TypeError", [])
    else pure (replace heap receiver {obj with items := obj.items ++ [value]}, .nil)
  | "most_common", [count] =>
    if obj.kind != "Counter" then .error ("AttributeError", [.str name])
    else mostCommon heap obj (← (number count).toExcept ("TypeError", []))
  | _, _ => .error ("TypeError", [])

def hexDigits : Nat → Nat → List Char
  | 0, _ => []
  | count+1, n => hexDigits count (n/16) ++ ["0123456789abcdef".toList[n%16]!]

def quote (s : String) : String :=
  -- Avoid String.contains' opaque iterator on embedded NUL in kernel replay.
  let chars := s.toList
  let mark := if chars.any (· == '\'') && !chars.any (· == '"') then '"' else '\''
  String.singleton mark ++ String.ofList (chars.flatMap (fun c =>
    if c == mark || c == '\\' then ['\\', c]
    else if c == '\n' then ['\\','n'] else if c == '\r' then ['\\','r']
    else if c == '\t' then ['\\','t']
    else if printable c then [c]
    else if Nat.blt c.toNat 256 then ['\\','x'] ++ hexDigits 2 c.toNat
    else if Nat.blt c.toNat 65536 then ['\\','u'] ++ hexDigits 4 c.toNat
    else ['\\','U'] ++ hexDigits 8 c.toNat)) ++ String.singleton mark

def render (heap : Store) : Nat → Bool → Value → String
  | 0, _, _ => "..."
  | fuel + 1, repr, value => match value with
    | .nil => "None"
    | .bool b => if b then "True" else "False"
    | .int n => toString n
    | .str s => if repr then quote s else s
    | .ref n => match heap[n]? with
      | none => "<invalid reference>"
      | some obj =>
        if obj.kind == "dict" || obj.kind == "Counter" then
          let entries := if obj.kind == "Counter" then ranked obj.entries else obj.entries
          let body := "{" ++ String.intercalate ", " (entries.map (fun (k,v) =>
            render heap fuel true k ++ ": " ++ render heap fuel true v)) ++ "}"
          if obj.kind == "Counter" then (if obj.entries.isEmpty then "Counter()" else "Counter(" ++ body ++ ")") else body
        else if obj.kind == "set" then
          if obj.entries.isEmpty then "set()" else "{" ++ String.intercalate ", "
            (obj.entries.map (fun p => render heap fuel true p.1)) ++ "}"
        else if obj.kind == "tuple" then
          "(" ++ String.intercalate ", " (obj.items.map (render heap fuel true)) ++
            (if obj.items.length == 1 then "," else "") ++ ")"
        else if obj.kind == "list" then
          "[" ++ String.intercalate ", " (obj.items.map (render heap fuel true)) ++ "]"
        else "<" ++ obj.kind ++ ">"
    | .exception name args =>
      if repr then (name.splitOn ".").getLast! ++ "(" ++ String.intercalate ", " (args.map (render heap fuel true)) ++ ")"
      else String.intercalate ", " (args.map (render heap fuel false))
    | _ => "<internal>"

def display (heap : Store) (repr : Bool) (v : Value) := render heap (heap.length + 2) repr v

def iterable (heap : Store) (v : Value) : Except Error (List Value) := do
  let obj ← object heap v
  if obj.kind == "dict" || obj.kind == "Counter" then return obj.entries.map Prod.fst
  if obj.kind == "tuple" || obj.kind == "list" || obj.kind == "range" then return obj.items
  .error ("TypeError", [])

def extremum (heap : Store) (greatest : Bool) : List Value → Except Error Value
  | [] => .error ("ValueError", [])
  | x :: xs => xs.foldlM (fun best candidate => do
      let (_, result) ← binary heap (if greatest then "gt" else "lt") candidate best
      return if truth heap result then candidate else best) x

def builtin (heap : Store) (name : String) (args : List Value) : Result := do
  match name, args with
  | "dict", [] => pure (allocate heap {kind := "dict"})
  | "collections.Counter", [] => pure (allocate heap {kind := "Counter"})
  | "set", [] => pure (allocate heap {kind := "set"})
  | "tuple", [] => pure (allocate heap {kind := "tuple"})
  | "list", [] => pure (allocate heap {kind := "list"})
  | "dict", [source] =>
    let obj ← object heap source
    if obj.kind != "dict" && obj.kind != "Counter" then .error ("TypeError", [])
    else pure (allocate heap {kind := "dict", entries := obj.entries})
  | "set", [source] => build heap "set" (← iterable heap source)
  | "list", [source] => build heap "list" (← iterable heap source)
  | "tuple", [source] => build heap "tuple" (← iterable heap source)
  | "len", [v] => return (heap, .int (← size heap v))
  | "bool", [v] => pure (heap, .bool (truth heap v))
  | "int", [v] => return (heap, .int (← (number v).toExcept ("TypeError", [])))
  | "str", [v] => pure (heap, .str (display heap false v))
  | "repr", [v] => pure (heap, .str (display heap true v))
  | "max", [v] => return (heap, ← extremum heap true (← iterable heap v))
  | "min", [v] => return (heap, ← extremum heap false (← iterable heap v))
  | "max", values => return (heap, ← extremum heap true values)
  | "min", values => return (heap, ← extremum heap false values)
  | "range", values =>
    let numbers ← values.mapM (fun v => (number v).toExcept ("TypeError", []))
    let (start, stop, step) ← match numbers with
      | [n] => pure (0,n,1) | [a,b] => pure (a,b,1) | [a,b,c] => pure (a,b,c)
      | _ => .error ("TypeError", [])
    if step == 0 then .error ("ValueError", [])
    else
      let count := if step > 0 then ((stop-start+step-1)/step).toNat
        else ((start-stop-step-1)/(-step)).toNat
      pure (allocate heap {kind := "range", items := (List.range count).map (fun (i : Nat) => .int (start + (i : Int)*step))})
  | name, values =>
    if name ∈ ["KeyError", "IndexError", "TypeError", "ValueError", "RuntimeError", "ZeroDivisionError"] then
      pure (heap, .exception name values)
    else .error ("TypeError", [])

theorem new_reference_fresh (heap : Store) (obj : Object) :
    (allocate heap obj).2 = .ref heap.length := rfl

theorem bool_int_key_alias (heap : Store) : eq heap (.bool true) (.int 1) = true := by
  simp [eq, equal, number]

theorem counter_absent_reads_zero :
    getitem [{kind := "Counter"}] (.ref 0) (.str "missing") = .ok (.int 0) := rfl

theorem dictionary_absent_is_error :
    getitem [{kind := "dict"}] (.ref 0) (.str "missing") = .error ("KeyError", [.str "missing"]) := rfl

theorem failed_operation_keeps_heap (heap : Store) (error : Error) :
    ((Except.error error : Result).toOption.getD (heap, .nil)).1 = heap := rfl

end ReactiveModules.Objects
