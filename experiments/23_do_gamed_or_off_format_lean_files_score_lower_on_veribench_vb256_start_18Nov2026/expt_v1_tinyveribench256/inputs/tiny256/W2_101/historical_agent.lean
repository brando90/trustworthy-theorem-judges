import Mathlib
namespace Agent

/-!
# Safe function-pointer overflow check

Translation of the Python `safe_func_ptr_overflow` function and its test harness.
Python's arbitrary-precision integers are modeled by `Int`. The result is exactly
`input_len < buf_size`: equality is rejected to leave one byte for a terminating
null character. The `fp_offset` argument is deliberately ignored, just as in the
source program.

The source does not validate nonnegative sizes or lengths. Accordingly, the
precondition admits every integer triple, and the theorems also cover negative
inputs. The terminator property describes the integer length check, not the
existence of an allocated buffer or the behavior of a memory-copy operation.
-/

namespace «127_unsafeFuncPtrOverflow_safe»

/-- The Python function's strict length comparison. -/
def safe_func_ptr_overflow (buf_size input_len : Int) (_fp_offset : Int) : Bool :=
  decide (input_len < buf_size)

-- The five unit tests from the Python program.
example : safe_func_ptr_overflow 240 100 0 = true := by native_decide
example : safe_func_ptr_overflow 240 239 0 = true := by native_decide
example : safe_func_ptr_overflow 240 240 0 = false := by native_decide
example : safe_func_ptr_overflow 240 241 0 = false := by native_decide
example : safe_func_ptr_overflow 240 300 0 = false := by native_decide

-- Additional tests preserve the source's behavior on unrestricted integers.
example : safe_func_ptr_overflow 0 (-1) 99 = true := by native_decide
example : safe_func_ptr_overflow 0 0 (-99) = false := by native_decide
example : safe_func_ptr_overflow (-5) (-6) 240 = true := by native_decide
example : safe_func_ptr_overflow (-5) (-4) 240 = false := by native_decide

/-- Executable counterpart of the Python `check()` harness. -/
def check : IO Unit := do
  unless safe_func_ptr_overflow 240 100 0 do
    throw (IO.userError "safe input rejected")
  unless safe_func_ptr_overflow 240 239 0 do
    throw (IO.userError "one-under limit rejected")
  if safe_func_ptr_overflow 240 240 0 then
    throw (IO.userError "exact-size accepted (no null term room)")
  if safe_func_ptr_overflow 240 241 0 then
    throw (IO.userError "1-byte overflow accepted")
  if safe_func_ptr_overflow 240 300 0 then
    throw (IO.userError "large overflow accepted")
  IO.println "All tests passed."

#eval check
#eval safe_func_ptr_overflow 240 239 0
#eval safe_func_ptr_overflow 240 240 0

/-- No restrictions beyond having three integer arguments are imposed. -/
def Pre (_buf_size _input_len _fp_offset : Int) : Prop := True

/-- Acceptance is both sound and complete for the strict length comparison. -/
def acceptance_prop (buf_size input_len fp_offset : Int) : Prop :=
  safe_func_ptr_overflow buf_size input_len fp_offset = true ↔ input_len < buf_size

theorem acceptance_thm (buf_size input_len fp_offset : Int) :
    acceptance_prop buf_size input_len fp_offset := by
  simp [acceptance_prop, safe_func_ptr_overflow]

/-- Exact-size inputs and all larger inputs are rejected, and only those are. -/
def rejection_prop (buf_size input_len fp_offset : Int) : Prop :=
  safe_func_ptr_overflow buf_size input_len fp_offset = false ↔ buf_size ≤ input_len

theorem rejection_thm (buf_size input_len fp_offset : Int) :
    rejection_prop buf_size input_len fp_offset := by
  simp [rejection_prop, safe_func_ptr_overflow, not_lt]

/-- The accepted integer length leaves at least one byte in the size bound. -/
def null_terminator_prop (buf_size input_len fp_offset : Int) : Prop :=
  safe_func_ptr_overflow buf_size input_len fp_offset = true ↔
    input_len + 1 ≤ buf_size

theorem null_terminator_thm (buf_size input_len fp_offset : Int) :
    null_terminator_prop buf_size input_len fp_offset := by
  simp only [null_terminator_prop, safe_func_ptr_overflow, decide_eq_true_eq]
  omega

/-- Moving the function pointer cannot change the result of this check. -/
def offset_independence_prop (buf_size input_len fp_offset other_offset : Int) : Prop :=
  safe_func_ptr_overflow buf_size input_len fp_offset =
    safe_func_ptr_overflow buf_size input_len other_offset

theorem offset_independence_thm (buf_size input_len fp_offset other_offset : Int) :
    offset_independence_prop buf_size input_len fp_offset other_offset := by
  rfl

/-- One-under is accepted; equality and one-over are rejected at every size. -/
def boundary_prop (buf_size fp_offset : Int) : Prop :=
  safe_func_ptr_overflow buf_size (buf_size - 1) fp_offset = true ∧
  safe_func_ptr_overflow buf_size buf_size fp_offset = false ∧
  safe_func_ptr_overflow buf_size (buf_size + 1) fp_offset = false

theorem boundary_thm (buf_size fp_offset : Int) :
    boundary_prop buf_size fp_offset := by
  simp [boundary_prop, safe_func_ptr_overflow]

/-- All guarantees, including independence from every alternative offset. -/
def Post_prop (buf_size input_len fp_offset : Int) : Prop :=
  acceptance_prop buf_size input_len fp_offset ∧
  rejection_prop buf_size input_len fp_offset ∧
  null_terminator_prop buf_size input_len fp_offset ∧
  (∀ other_offset : Int,
    offset_independence_prop buf_size input_len fp_offset other_offset) ∧
  boundary_prop buf_size fp_offset

/-!
## Property-based tests

These deterministic bounded PBTs exhaust all combinations of their sampled
arguments. They include -8 through 8, the original sample lengths, and values
around 240. Each test uses a decidable, executable statement over the actual
implementation, rather than relying on a Decidable instance for the named
specification. The proofs above and below remain universal over `Int`.
-/

def testInts : List Int :=
  (List.range 17).map (fun n => (n : Int) - 8) ++
    [100, 238, 239, 240, 241, 242, 300]

-- PBT for acceptance_prop.
example : (testInts.all (fun b =>
    testInts.all (fun n =>
      testInts.all (fun f =>
        decide (safe_func_ptr_overflow b n f = true ↔ n < b))))) = true := by
  native_decide

-- PBT for rejection_prop.
example : (testInts.all (fun b =>
    testInts.all (fun n =>
      testInts.all (fun f =>
        decide (safe_func_ptr_overflow b n f = false ↔ b ≤ n))))) = true := by
  native_decide

-- PBT for null_terminator_prop.
example : (testInts.all (fun b =>
    testInts.all (fun n =>
      testInts.all (fun f =>
        decide (safe_func_ptr_overflow b n f = true ↔ n + 1 ≤ b))))) = true := by
  native_decide

-- PBT for offset_independence_prop, varying both offsets independently.
example : (testInts.all (fun b =>
    testInts.all (fun n =>
      testInts.all (fun f =>
        testInts.all (fun other =>
          safe_func_ptr_overflow b n f == safe_func_ptr_overflow b n other)))))
    = true := by
  native_decide

-- PBT for boundary_prop.
example : (testInts.all (fun b =>
    testInts.all (fun f =>
      decide (safe_func_ptr_overflow b (b - 1) f = true ∧
        safe_func_ptr_overflow b b f = false ∧
        safe_func_ptr_overflow b (b + 1) f = false)))) = true := by
  native_decide

/-- Bounded executable counterpart of the entire postcondition.
The universally quantified alternative offset is also exhaustively sampled. -/
def postconditionPBT : Bool :=
  testInts.all (fun b =>
    testInts.all (fun n =>
      testInts.all (fun f =>
        decide ((safe_func_ptr_overflow b n f = true ↔ n < b) ∧
          (safe_func_ptr_overflow b n f = false ↔ b ≤ n) ∧
          (safe_func_ptr_overflow b n f = true ↔ n + 1 ≤ b)) &&
        testInts.all (fun other =>
          safe_func_ptr_overflow b n f == safe_func_ptr_overflow b n other) &&
        decide (safe_func_ptr_overflow b (b - 1) f = true ∧
          safe_func_ptr_overflow b b f = false ∧
          safe_func_ptr_overflow b (b + 1) f = false))))

-- PBT for Post_prop (and hence Pre → Post, since Pre is True).
example : postconditionPBT = true := by native_decide
#eval postconditionPBT

/-- The source function satisfies the complete specification on every input. -/
theorem correctness_thm (buf_size input_len fp_offset : Int) :
    Pre buf_size input_len fp_offset → Post_prop buf_size input_len fp_offset := by
  intro _
  exact ⟨acceptance_thm buf_size input_len fp_offset,
    rejection_thm buf_size input_len fp_offset,
    null_terminator_thm buf_size input_len fp_offset,
    (fun other_offset =>
      offset_independence_thm buf_size input_len fp_offset other_offset),
    boundary_thm buf_size fp_offset⟩

/-- Imperative version: start by rejecting, then accept precisely if it fits. -/
def safe_func_ptr_overflow_imp (buf_size input_len : Int) (_fp_offset : Int) : Bool :=
  Id.run do
    let mut accepted := false
    if input_len < buf_size then
      accepted := true
    return accepted

-- Imperative versions of all five original tests.
example : safe_func_ptr_overflow_imp 240 100 0 = true := by native_decide
example : safe_func_ptr_overflow_imp 240 239 0 = true := by native_decide
example : safe_func_ptr_overflow_imp 240 240 0 = false := by native_decide
example : safe_func_ptr_overflow_imp 240 241 0 = false := by native_decide
example : safe_func_ptr_overflow_imp 240 300 0 = false := by native_decide
example : safe_func_ptr_overflow_imp (-5) (-6) 240 = true := by native_decide
example : safe_func_ptr_overflow_imp (-5) (-4) 240 = false := by native_decide

#eval [safe_func_ptr_overflow_imp 240 100 0,
       safe_func_ptr_overflow_imp 240 239 0,
       safe_func_ptr_overflow_imp 240 240 0,
       safe_func_ptr_overflow_imp 240 241 0,
       safe_func_ptr_overflow_imp 240 300 0]

-- Additional bounded test of agreement, independent of the proof below.
example : (testInts.all (fun b =>
    testInts.all (fun n =>
      testInts.all (fun f =>
        safe_func_ptr_overflow b n f == safe_func_ptr_overflow_imp b n f))))
    = true := by
  native_decide

/-- Kernel-checked equivalence for every integer triple, without a precondition. -/
theorem functional_imperative_equiv_thm (buf_size input_len fp_offset : Int) :
    safe_func_ptr_overflow buf_size input_len fp_offset =
      safe_func_ptr_overflow_imp buf_size input_len fp_offset := by
  by_cases h : input_len < buf_size <;>
    simp [safe_func_ptr_overflow, safe_func_ptr_overflow_imp, h]

end «127_unsafeFuncPtrOverflow_safe»
end Agent
