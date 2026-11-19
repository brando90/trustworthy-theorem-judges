import Mathlib
namespace Agent

/-!
# Unsafe tainted length

Translation of the RLBox tainted-length example: a sandboxed library's `skip`
value is accepted without checking it against `buf_size`. Python integers are
modelled by `Int`, including negative values and arbitrarily large values.
The result is always `true`; in particular, this is NOT a safe bounds checker.
The program only returns permission to proceed: it does not itself perform or
model a memory access. The properties below describe that unchecked permission.
-/

namespace UnsafeTaintedLen

/-- Proceed regardless of either argument, exactly as in the Python function. -/
def unsafe_tainted_len (_skip _buf_size : Int) : Bool :=
  true

/-- Boolean form of the Python assertion harness: true iff all assertions pass. -/
def check (candidate : Int → Int → Bool) : Bool :=
  candidate 5 100 &&
  candidate 200 100 &&
  candidate 100 100 &&
  candidate 0 0 &&
  candidate 999999 1

-- Unit tests: the five assertions from the Python source.
example : unsafe_tainted_len 5 100 = true := by native_decide
example : unsafe_tainted_len 200 100 = true := by native_decide
example : unsafe_tainted_len 100 100 = true := by native_decide
example : unsafe_tainted_len 0 0 = true := by native_decide
example : unsafe_tainted_len 999999 1 = true := by native_decide
example : check unsafe_tainted_len = true := by native_decide

-- Python's annotations do not rule out negative integer arguments.
example : unsafe_tainted_len (-5) 100 = true := by native_decide
example : unsafe_tainted_len 0 (-1) = true := by native_decide

#eval unsafe_tainted_len 200 100
#eval check unsafe_tainted_len
#eval if check unsafe_tainted_len then "All tests passed." else "Candidate failed tests"

/-- No bounds or sign assumption is imposed by the source program. -/
def Pre (_skip _buf_size : Int) : Prop := True

/-- Exact return-value specification on the entire integer domain. -/
def always_true_prop (skip buf_size : Int) : Prop :=
  unsafe_tainted_len skip buf_size = true

theorem always_true_thm (skip buf_size : Int) :
    always_true_prop skip buf_size := by
  rfl

/-- The vulnerability: even a skip exceeding the buffer is accepted. -/
def out_of_bounds_prop (skip buf_size : Int) : Prop :=
  skip > buf_size → unsafe_tainted_len skip buf_size = true

theorem out_of_bounds_thm (skip buf_size : Int) :
    out_of_bounds_prop skip buf_size := by
  intro _
  rfl

/-- There is no lower-bound validation either. -/
def negative_skip_prop (skip buf_size : Int) : Prop :=
  skip < 0 → unsafe_tainted_len skip buf_size = true

theorem negative_skip_thm (skip buf_size : Int) :
    negative_skip_prop skip buf_size := by
  intro _
  rfl

/-- Changing either or both integer inputs never changes the result. -/
def input_independent_prop (skip buf_size : Int) : Prop :=
  ∀ other_skip other_buf_size : Int,
    unsafe_tainted_len skip buf_size =
      unsafe_tainted_len other_skip other_buf_size

theorem input_independent_thm (skip buf_size : Int) :
    input_independent_prop skip buf_size := by
  intro other_skip other_buf_size
  rfl

/-- All behavioral properties, without assuming that the inputs are safe. -/
def Post_prop (skip buf_size : Int) : Prop :=
  always_true_prop skip buf_size ∧
  out_of_bounds_prop skip buf_size ∧
  negative_skip_prop skip buf_size ∧
  input_independent_prop skip buf_size

/-! ## Property-based tests

Exhaustive bounded tests use the Cartesian products of a signed range and
additional large values. The implications are tested in their executable form,
including both true and false antecedents. For universal input independence,
the comparison inputs are independently sampled from the same finite set.
These tests are evidence only; none is used to prove a named theorem.
-/

def testInputs : List Int :=
  ((List.range 31).map (fun n => (n : Int) - 15)) ++
    [-1000000, -100, 100, 200, 999999, 1000000]

-- PBT for always_true_prop.
example : testInputs.all (fun skip =>
    testInputs.all (fun buf_size =>
      unsafe_tainted_len skip buf_size == true)) = true := by
  native_decide

-- PBT for out_of_bounds_prop, including many oversized skips.
example : testInputs.all (fun skip =>
    testInputs.all (fun buf_size =>
      decide (skip > buf_size → unsafe_tainted_len skip buf_size = true))) =
    true := by
  native_decide

-- PBT for negative_skip_prop, including many negative skips.
example : testInputs.all (fun skip =>
    testInputs.all (fun buf_size =>
      decide (skip < 0 → unsafe_tainted_len skip buf_size = true))) = true := by
  native_decide

-- PBT for input_independent_prop: all four inputs vary independently.
example : testInputs.all (fun skip =>
    testInputs.all (fun buf_size =>
      testInputs.all (fun other_skip =>
        testInputs.all (fun other_buf_size =>
          unsafe_tainted_len skip buf_size ==
            unsafe_tainted_len other_skip other_buf_size)))) = true := by
  native_decide

-- PBT for Post_prop: its full executable conjunction, with the universal
-- comparison inputs exhaustively checked over testInputs as above.
example : testInputs.all (fun skip =>
    testInputs.all (fun buf_size =>
      (unsafe_tainted_len skip buf_size == true) &&
      decide (skip > buf_size → unsafe_tainted_len skip buf_size = true) &&
      decide (skip < 0 → unsafe_tainted_len skip buf_size = true) &&
      testInputs.all (fun other_skip =>
        testInputs.all (fun other_buf_size =>
          unsafe_tainted_len skip buf_size ==
            unsafe_tainted_len other_skip other_buf_size)))) = true := by
  native_decide

/-- Correctness means faithfully preserving the unsafe behavior, not safety. -/
theorem correctness (skip buf_size : Int) :
    Pre skip buf_size → Post_prop skip buf_size := by
  intro _
  exact ⟨always_true_thm skip buf_size,
    out_of_bounds_thm skip buf_size,
    negative_skip_thm skip buf_size,
    input_independent_thm skip buf_size⟩

/-- Imperative version: update the decision without inspecting either input. -/
def unsafe_tainted_len_imperative (_skip _buf_size : Int) : Bool := Id.run do
  let mut proceed : Bool := false
  proceed := true
  return proceed

-- Imperative tests repeat all five source assertions.
example : unsafe_tainted_len_imperative 5 100 = true := by native_decide
example : unsafe_tainted_len_imperative 200 100 = true := by native_decide
example : unsafe_tainted_len_imperative 100 100 = true := by native_decide
example : unsafe_tainted_len_imperative 0 0 = true := by native_decide
example : unsafe_tainted_len_imperative 999999 1 = true := by native_decide
example : check unsafe_tainted_len_imperative = true := by native_decide

#eval unsafe_tainted_len_imperative 999999 1
#eval check unsafe_tainted_len_imperative

/-- Functional and imperative results agree for every pair of Python integers. -/
theorem functional_eq_imperative (skip buf_size : Int) :
    unsafe_tainted_len skip buf_size =
      unsafe_tainted_len_imperative skip buf_size := by
  rfl

end UnsafeTaintedLen
end Agent
