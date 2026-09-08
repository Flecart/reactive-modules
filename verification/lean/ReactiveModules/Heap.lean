import Std

namespace ReactiveModules.Heap

/-- Exact integer keys/values. Dictionary order is observable; set order is not. -/
abbrev Dictionary := List (Int × Int)

def lookup (key : Int) : Dictionary → Option Int
  | [] => none
  | (k, v) :: rest => if key = k then some v else lookup key rest

def put (key value : Int) : Dictionary → Dictionary
  | [] => [(key, value)]
  | (k, v) :: rest => if key = k then (k, value) :: rest else (k, v) :: put key value rest

def erase (key : Int) (entries : Dictionary) : Dictionary :=
  entries.filter (fun entry => entry.1 != key)

theorem lookup_put_same (entries : Dictionary) (key value : Int) :
    lookup key (put key value entries) = some value := by
  induction entries with
  | nil => simp [put, lookup]
  | cons entry rest ih =>
    rcases entry with ⟨k, v⟩
    by_cases h : key = k <;> simp [put, lookup, h, ih]

theorem lookup_put_other (entries : Dictionary) (key other value : Int) (h : other ≠ key) :
    lookup other (put key value entries) = lookup other entries := by
  induction entries with
  | nil => simp [put, lookup, h]
  | cons entry rest ih =>
    rcases entry with ⟨k, v⟩
    by_cases hk : key = k <;> by_cases ho : other = k <;> simp_all [put, lookup]

theorem lookup_erase_same (entries : Dictionary) (key : Int) :
    lookup key (erase key entries) = none := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨k, v⟩
    by_cases h : key = k <;> simp_all [erase, lookup, Ne.symm]

theorem overwrite_keeps_order (entries : Dictionary) (key value : Int)
    (present : (lookup key entries).isSome) :
    (put key value entries).map Prod.fst = entries.map Prod.fst := by
  induction entries with
  | nil => simp [lookup] at present
  | cons entry rest ih =>
    rcases entry with ⟨k, v⟩
    by_cases h : key = k
    · simp [put, h]
    · simp only [lookup, if_neg h] at present
      simp [put, h, ih present]

theorem keys_put (entries : Dictionary) (key value other : Int) :
    other ∈ (put key value entries).map Prod.fst ↔ other = key ∨ other ∈ entries.map Prod.fst := by
  induction entries with
  | nil => simp [put]
  | cons entry rest ih =>
    rcases entry with ⟨k, v⟩
    by_cases h : key = k <;> simp_all [put, or_left_comm]

theorem put_preserves_unique_keys (entries : Dictionary) (key value : Int)
    (valid : (entries.map Prod.fst).Nodup) : ((put key value entries).map Prod.fst).Nodup := by
  induction entries with
  | nil => simp [put]
  | cons entry rest ih =>
    rcases entry with ⟨k, v⟩
    by_cases h : key = k
    · simpa [put, h] using valid
    · simp only [List.map_cons, List.nodup_cons] at valid
      simp [put, h, List.nodup_cons, keys_put, Ne.symm h, valid, ih valid.2]

def setAdd (key : Int) (entries : List Int) : List Int :=
  if key ∈ entries then entries else entries ++ [key]

def setErase (key : Int) (entries : List Int) : List Int :=
  entries.filter (· != key)

theorem mem_setAdd (key other : Int) (entries : List Int) :
    other ∈ setAdd key entries ↔ other = key ∨ other ∈ entries := by
  by_cases h : key ∈ entries <;> simp_all [setAdd, or_comm]

theorem setAdd_idempotent (key : Int) (entries : List Int) :
    setAdd key (setAdd key entries) = setAdd key entries := by
  have h : key ∈ setAdd key entries := (mem_setAdd key key entries).2 (Or.inl rfl)
  exact if_pos h

theorem mem_setErase (key other : Int) (entries : List Int) :
    other ∈ setErase key entries ↔ other ∈ entries ∧ other ≠ key := by
  simp [setErase]

theorem setAdd_preserves_unique (key : Int) (entries : List Int) (valid : entries.Nodup) :
    (setAdd key entries).Nodup := by
  by_cases h : key ∈ entries
  · simpa [setAdd, h] using valid
  · simp only [setAdd, if_neg h, List.nodup_append]
    refine ⟨valid, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst b
    intro equal
    exact h (equal ▸ ha)

inductive Object where
  | dictionary (entries : Dictionary)
  | set (entries : List Int)
  deriving Repr, DecidableEq

abbrev Store := List Object

inductive Operation where
  | newDict | newSet | dictSet | dictGet | dictContains | dictLen | dictDelete
  | dictCopy | dictKeyAt | setAdd | setDiscard | setContains | setLen | setRemove
  | setCopy | dictItem | dictClear | setClear
  deriving Repr, DecidableEq

structure Request where
  operation : Operation
  reference : Int := 0
  key : Int := 0
  value : Int := 0
  deriving Repr, DecidableEq

inductive Error where
  | invalidReference (reference : Int)
  | wrongKind (reference : Int)
  | keyError (key : Int)
  | indexError (index : Int)
  deriving Repr, DecidableEq

inductive Response where
  | ok (value : Int)
  | error (reason : Error)
  deriving Repr, DecidableEq

def allocate (heap : Store) (object : Object) : Store × Int :=
  (heap ++ [object], heap.length)

def access (heap : Store) (reference : Int) : Except Error Object :=
  if reference < 0 then .error (.invalidReference reference) else
    match heap[reference.toNat]? with
    | none => .error (.invalidReference reference)
    | some object => .ok object

def replace (heap : Store) (reference : Int) (object : Object) : Store × Int :=
  (heap.set reference.toNat object, 0)

/-- Negative indices have Python tuple-index semantics. -/
def keyAt (entries : Dictionary) (index : Int) : Except Error Int :=
  let position := if index < 0 then (entries.length : Int) + index else index
  if position < 0 then .error (.indexError index) else
    match entries[position.toNat]? with
    | some (key, _) => .ok key
    | none => .error (.indexError index)

def execute (heap : Store) (request : Request) : Except Error (Store × Int) := do
  let ref := request.reference
  let key := request.key
  let value := request.value
  match request.operation with
  | .newDict => return allocate heap (.dictionary [])
  | .newSet => return allocate heap (.set [])
  | op =>
    let object ← access heap ref
    match op, object with
    | .dictSet, .dictionary entries => return replace heap ref (.dictionary (put key value entries))
    | .dictGet, .dictionary entries => return (heap, (lookup key entries).getD value)
    | .dictItem, .dictionary entries =>
      match lookup key entries with
      | some found => return (heap, found)
      | none => throw (.keyError key)
    | .dictContains, .dictionary entries => return (heap, if (lookup key entries).isSome then 1 else 0)
    | .dictLen, .dictionary entries => return (heap, entries.length)
    | .dictDelete, .dictionary entries =>
      if (lookup key entries).isSome then return replace heap ref (.dictionary (erase key entries))
      else throw (.keyError key)
    | .dictCopy, .dictionary entries => return allocate heap (.dictionary entries)
    | .dictKeyAt, .dictionary entries => return (heap, ← keyAt entries key)
    | .dictClear, .dictionary _ => return replace heap ref (.dictionary [])
    | .setAdd, .set entries => return replace heap ref (.set (setAdd key entries))
    | .setDiscard, .set entries => return replace heap ref (.set (setErase key entries))
    | .setContains, .set entries => return (heap, if key ∈ entries then 1 else 0)
    | .setLen, .set entries => return (heap, entries.length)
    | .setRemove, .set entries =>
      if key ∈ entries then return replace heap ref (.set (setErase key entries))
      else throw (.keyError key)
    | .setCopy, .set entries => return allocate heap (.set entries)
    | .setClear, .set _ => return replace heap ref (.set [])
    | _, _ => throw (.wrongKind ref)

def apply (heap : Store) (request : Request) : Store × Response :=
  match execute heap request with
  | .ok (after, result) => (after, .ok result)
  | .error reason => (heap, .error reason)

theorem error_preserves_heap (heap : Store) (request : Request) (reason : Error)
    (h : (apply heap request).2 = .error reason) : (apply heap request).1 = heap := by
  unfold apply at *
  split at * <;> simp_all

theorem allocate_fresh (heap : Store) (object : Object) :
    (allocate heap object).1[heap.length]? = some object := by
  simp [allocate]

theorem allocate_preserves (heap : Store) (object : Object) (i : Nat) (h : i < heap.length) :
    (allocate heap object).1[i]? = heap[i]? := by
  simp [allocate, List.getElem?_append_left h]

theorem replace_preserves_other (heap : Store) (reference : Int) (object : Object)
    (i : Nat) (different : i ≠ reference.toNat) :
    (replace heap reference object).1[i]? = heap[i]? := by
  simp [replace, Ne.symm different]

end ReactiveModules.Heap
