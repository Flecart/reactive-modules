import ReactiveModules.Compiler

namespace ReactiveModules

inductive ScalarSort where
  | int | bool
  deriving Repr, DecidableEq, BEq

def Expr.sort (types : List ScalarSort) (initialized : List Nat) : Expr → Option ScalarSort
  | .lit _ => some .int
  | .boolean _ => some .bool
  | .var n => if initialized.contains n then types[n]? else none
  | .not a => if a.sort types initialized == some .bool then some .bool else none
  | .bin op a b => do
    let sa ← a.sort types initialized
    let sb ← b.sort types initialized
    match op with
    | .add | .sub => if sa == .int && sb == .int then some .int else none
    | .eq | .ne => if sa == sb then some .bool else none
    | .lt | .le | .gt | .ge => if sa == .int && sb == .int then some .bool else none
    | .and | .or | .xor => if sa == .bool && sb == .bool then some .bool else none
  | .ite c a b => do
    if c.sort types initialized != some .bool then none else do
      let sa ← a.sort types initialized
      let sb ← b.sort types initialized
      if sa == sb then some sa else none

/-- none = ill formed; some none = all paths returned; some (some slots) = fallthrough. -/
def checkSource (types outputs : List ScalarSort) (initialized : List Nat) :
    Source → Option (Option (List Nat))
  | .skip => some (some initialized)
  | .assign n e => do
    let expected ← types[n]?
    let actual ← e.sort types initialized
    if actual == expected then some (some (n :: initialized)) else none
  | .assignMany ns es => do
    let expected ← ns.mapM (fun n => types[n]?)
    let actual ← es.mapM (Expr.sort types initialized)
    if actual == expected then some (some (ns ++ initialized)) else none
  | .ret values => do
    let actual ← values.mapM (Expr.sort types initialized)
    if actual == outputs then some none else none
  | .branch c a b => do
    if c.sort types initialized != some .bool then none else do
      let a' ← checkSource types outputs initialized a
      let b' ← checkSource types outputs initialized b
      match a', b' with
      | none, rest | rest, none => some rest
      | some x, some y => some (some (x.filter y.contains))
  | .seq a b => do
    let result ← checkSource types outputs initialized a
    match result with
    | none => some none
    | some slots => checkSource types outputs slots b
  | .call targets body => do
    let results ← targets.mapM (fun n => types[n]?)
    let state ← checkSource types results initialized body
    if state == none then some (some (targets ++ initialized)) else none
  | .forEach slots rows body => do
    let expected ← slots.mapM (fun n => types[n]?)
    let actual ← rows.mapM (fun row => row.mapM (Expr.sort types initialized))
    if actual.any (fun sorts => sorts != expected) then none else do
      let state ← checkSource types outputs (slots ++ initialized) body
      if rows.isEmpty then some (some initialized) else some state

def validSource (s : Source) (types outputs : List ScalarSort) (inputs : Nat) : Bool :=
  inputs ≤ types.length && checkSource types outputs (List.range inputs) s == some none

def graphTypes (types : List ScalarSort) : List Expr → Option (List ScalarSort)
  | [] => some types
  | term :: rest => do
    let sort ← term.sort types (List.range types.length)
    graphTypes (types ++ [sort]) rest

def validGraph (g : Graph) (inputs outputs : List ScalarSort) : Bool :=
  if g.inputs != inputs.length then false else
    match graphTypes inputs g.terms with
    | none => false
    | some types => g.outputs.mapM (fun n => types[n]?) == some outputs

end ReactiveModules
