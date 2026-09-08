import Certificate

open ReactiveModules Objects Native Verified

namespace NativeAsync

/-- The entry state is built using the function's compiled parameter schema. -/
def initial (value : Int) : Native.State :=
  Native.enter native_program {heap := [], frames := []} "increment" [.int value] []

/-- A property of the compiled async helper for every mathematical integer.
    This is a separate authored contract, not inferred algorithm correctness. -/
theorem increment_result (value : Int) :
    (Native.run native_program native_fetch (initial value)
      (List.replicate 4 Native.Action.tick)).phase = .done (.int (value + 1)) := by
  rw [native_execution_correct]
  rfl

end NativeAsync
