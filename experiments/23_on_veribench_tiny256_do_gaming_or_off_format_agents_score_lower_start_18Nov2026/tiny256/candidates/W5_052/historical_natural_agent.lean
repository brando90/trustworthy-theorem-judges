import Mathlib
namespace Agent

/-!
# Unsafe function-pointer overflow check

Translation of the Python `unsafe_func_ptr_overflow` and its four checks.
The function always returns `True`: neither the buffer size, the input length,
nor the function-pointer offset influences the answer. In particular, an input
longer than the buffer is accepted, not detected or rejected.

`Int` models Python's unbounded integers, including negative arguments. The
precondition imposes no additional restrictions. This is a model of the given
check, not of `strcpy`, memory layout, or actual control-flow redirection; no
memory-safety guarantee is asserted. The imperative version deliberately has
the same vulnerable behavior.
-/

namespace UnsafeFuncPtrOverflow

/-! ## Functional implementation -/

/-- The deliberately unsafe check ignores all three arguments. -/
def unsafe_func_ptr_overflow (_buf_size _input_len _fp_offset : Int) : Bool :=
  true

/-! ## Unit tests and the source program's check routine -/

example : unsafe_func_ptr_overflow 240 100 0 = true := by native_decide
example : unsafe_func_ptr_overflow 240 241 0 = true := by native_decide
example : unsafe_func_ptr_overflow 240 300 0 = true := by native_decide
example : unsafe_func_ptr_overflow 240 240 0 = true := by native_decide

-- These additional cases emphasize that the integer domain is unrestricted.
example : unsafe_func_ptr_overflow (-1) (-2) (-3) = true := by native_decide
example : unsafe_func_ptr_overflow 0 1 17 = true := by native_decide

/-- Execute the four Python assertions, retaining their failure messages. -/
def check : IO Unit := do
  unless unsafe_func_ptr_overflow 240 100 0 do
    throw (IO.userError "safe input rejected")
  unless unsafe_func_ptr_overflow 240 241 0 do
    throw (IO.userError "vuln: 1-byte overflow accepted")
  unless unsafe_func_ptr_overflow 240 300 0 do
    throw (IO.userError "vuln: large overflow accepted")
  unless unsafe_func_ptr_overflow 240 240 0 do
    throw (IO.userError "exact-size input rejected")
  IO.println "All tests passed."

#eval check
#eval unsafe_func_ptr_overflow 240 300 0

/-! ## Precondition -/

/-- Python performs no validation: every integer triple is admissible. -/
def Pre (_buf_size _input_len _fp_offset : Int) : Prop := True

/-! ## Properties and kernel-checked proofs -/

/-- The exact return-value specification, without any restrictions. -/
def always_accepts_prop (buf_size input_len fp_offset : Int) : Prop :=
  unsafe_func_ptr_overflow buf_size input_len fp_offset = true

theorem always_accepts_thm (buf_size input_len fp_offset : Int) :
    always_accepts_prop buf_size input_len fp_offset := by
  rfl

/-- Lengths at or below the buffer size are accepted. -/
def within_bounds_prop (buf_size input_len fp_offset : Int) : Prop :=
  input_len ≤ buf_size →
    unsafe_func_ptr_overflow buf_size input_len fp_offset = true

theorem within_bounds_thm (buf_size input_len fp_offset : Int) :
    within_bounds_prop buf_size input_len fp_offset := by
  intro _
  rfl

/-- Equality of the two sizes does not cause rejection. -/
def exact_size_prop (buf_size input_len fp_offset : Int) : Prop :=
  input_len = buf_size →
    unsafe_func_ptr_overflow buf_size input_len fp_offset = true

theorem exact_size_thm (buf_size input_len fp_offset : Int) :
    exact_size_prop buf_size input_len fp_offset := by
  intro _
  rfl

/-- Even an input longer than the buffer is accepted, for every offset. -/
def overflow_accepted_prop (buf_size input_len fp_offset : Int) : Prop :=
  buf_size < input_len →
    unsafe_func_ptr_overflow buf_size input_len fp_offset = true

theorem overflow_accepted_thm (buf_size input_len fp_offset : Int) :
    overflow_accepted_prop buf_size input_len fp_offset := by
  intro _
  rfl

/-- Changing any or all arguments leaves the result unchanged. -/
def arguments_ignored_prop (buf_size input_len fp_offset : Int) : Prop :=
  ∀ other_buf_size other_input_len other_fp_offset : Int,
    unsafe_func_ptr_overflow buf_size input_len fp_offset =
      unsafe_func_ptr_overflow other_buf_size other_input_len other_fp_offset

theorem arguments_ignored_thm (buf_size input_len fp_offset : Int) :
    arguments_ignored_prop buf_size input_len fp_offset := by
  intro other_buf_size other_input_len other_fp_offset
  rfl

/-! ## Postcondition -/

/-- Behavioral correctness here describes the bug; it does not mean safety. -/
def Post_prop (buf_size input_len fp_offset : Int) : Prop :=
  always_accepts_prop buf_size input_len fp_offset ∧
  within_bounds_prop buf_size input_len fp_offset ∧
  exact_size_prop buf_size input_len fp_offset ∧
  overflow_accepted_prop buf_size input_len fp_offset ∧
  arguments_ignored_prop buf_size input_len fp_offset

/-! ## Property-based tests

These checks use executable expressions over the implementation, separately
from the proofs above. None of the named theorems relies on these tests.
-/

-- PBT for always_accepts_prop.
#eval Plausible.Testable.check
  (∀ buf_size input_len fp_offset : Int,
    unsafe_func_ptr_overflow buf_size input_len fp_offset = true)

-- PBT for within_bounds_prop. Boolean implication evaluates every sample.
#eval Plausible.Testable.check
  (∀ buf_size input_len fp_offset : Int,
    ((!decide (input_len ≤ buf_size)) ||
      unsafe_func_ptr_overflow buf_size input_len fp_offset) = true)

-- PBT for exact_size_prop. Construct equal sizes rather than discarding
-- almost every random sample; this covers every triple satisfying equality.
#eval Plausible.Testable.check
  (∀ buf_size fp_offset : Int,
    unsafe_func_ptr_overflow buf_size buf_size fp_offset = true)

-- PBT for overflow_accepted_prop. Boolean implication avoids discards.
#eval Plausible.Testable.check
  (∀ buf_size input_len fp_offset : Int,
    ((!decide (buf_size < input_len)) ||
      unsafe_func_ptr_overflow buf_size input_len fp_offset) = true)

-- PBT for arguments_ignored_prop: vary all six integer arguments.
#eval Plausible.Testable.check
  (∀ buf_size input_len fp_offset other_buf_size other_input_len other_fp_offset : Int,
    unsafe_func_ptr_overflow buf_size input_len fp_offset =
      unsafe_func_ptr_overflow other_buf_size other_input_len other_fp_offset)

-- PBT for the complete Post_prop. Quantifying the comparison triple outside
-- the conjunction makes its executable form explicit. Boolean implications
-- evaluate all cases, rather than requiring mutually exclusive antecedents.
#eval Plausible.Testable.check
  (∀ buf_size input_len fp_offset other_buf_size other_input_len other_fp_offset : Int,
    ((unsafe_func_ptr_overflow buf_size input_len fp_offset == true) &&
      ((!decide (input_len ≤ buf_size)) ||
        unsafe_func_ptr_overflow buf_size input_len fp_offset) &&
      ((!decide (input_len = buf_size)) ||
        unsafe_func_ptr_overflow buf_size input_len fp_offset) &&
      ((!decide (buf_size < input_len)) ||
        unsafe_func_ptr_overflow buf_size input_len fp_offset) &&
      (unsafe_func_ptr_overflow buf_size input_len fp_offset ==
        unsafe_func_ptr_overflow other_buf_size other_input_len other_fp_offset)) = true)

/-- Boundary-rich finite inputs, including negatives and the original sizes. -/
def pbtInts : List Int := [-3, -1, 0, 1, 2, 100, 239, 240, 241, 300]

/-- Exhaustive Boolean form of the entire postcondition on the finite grid.
Every component property, including argument independence, is tested. -/
def boundedPostTest : Bool :=
  pbtInts.all fun buf_size =>
    pbtInts.all fun input_len =>
      pbtInts.all fun fp_offset =>
        let accepted := unsafe_func_ptr_overflow buf_size input_len fp_offset
        (accepted == true) &&
        ((!decide (input_len ≤ buf_size)) || accepted) &&
        ((!decide (input_len = buf_size)) || accepted) &&
        ((!decide (buf_size < input_len)) || accepted) &&
        (pbtInts.all fun other_buf_size =>
          pbtInts.all fun other_input_len =>
            pbtInts.all fun other_fp_offset =>
              accepted == unsafe_func_ptr_overflow
                other_buf_size other_input_len other_fp_offset)

example : boundedPostTest = true := by native_decide
#eval boundedPostTest

/-! ## Correctness: unrestricted precondition implies the behavioral postcondition -/

theorem correctness_thm (buf_size input_len fp_offset : Int) :
    Pre buf_size input_len fp_offset → Post_prop buf_size input_len fp_offset := by
  intro _
  exact ⟨always_accepts_thm buf_size input_len fp_offset,
    within_bounds_thm buf_size input_len fp_offset,
    exact_size_thm buf_size input_len fp_offset,
    overflow_accepted_thm buf_size input_len fp_offset,
    arguments_ignored_thm buf_size input_len fp_offset⟩

/-! ## Imperative implementation -/

/-- Assign the answer unconditionally, without inspecting the inputs. -/
def unsafe_func_ptr_overflow_imp (_buf_size _input_len _fp_offset : Int) : Bool :=
  Id.run do
    let mut accepted := false
    accepted := true
    return accepted

/-! ## Imperative tests -/

example : unsafe_func_ptr_overflow_imp 240 100 0 = true := by native_decide
example : unsafe_func_ptr_overflow_imp 240 241 0 = true := by native_decide
example : unsafe_func_ptr_overflow_imp 240 300 0 = true := by native_decide
example : unsafe_func_ptr_overflow_imp 240 240 0 = true := by native_decide
example : unsafe_func_ptr_overflow_imp (-1) (-2) (-3) = true := by native_decide

#eval [unsafe_func_ptr_overflow_imp 240 100 0,
  unsafe_func_ptr_overflow_imp 240 241 0,
  unsafe_func_ptr_overflow_imp 240 300 0,
  unsafe_func_ptr_overflow_imp 240 240 0]

-- Additional randomized equivalence test, independent of the proof below.
#eval Plausible.Testable.check
  (∀ buf_size input_len fp_offset : Int,
    unsafe_func_ptr_overflow buf_size input_len fp_offset =
      unsafe_func_ptr_overflow_imp buf_size input_len fp_offset)

/-! ## Functional–imperative equivalence -/

theorem equivalence_thm (buf_size input_len fp_offset : Int) :
    unsafe_func_ptr_overflow buf_size input_len fp_offset =
      unsafe_func_ptr_overflow_imp buf_size input_len fp_offset := by
  rfl

end UnsafeFuncPtrOverflow
end Agent
