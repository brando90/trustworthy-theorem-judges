import Mathlib
namespace Agent

/-!
# Unsafe integer division

Translation of the Python `unsafe_divide` example from MIT 6.858's symbolic
execution discussion. Python integers are modelled by unbounded `Int`, and
Python `//` by `Int.fdiv` (floor division, not truncation or Euclidean division
when the divisor is negative). The zero-divisor branch deliberately returns
an ordinary integer zero: this file specifies the bug rather than repairing it.

The precondition admits all integer pairs, including zero and negative divisors.
Tests are executable evidence; the named theorems use kernel-checked proofs.
-/

namespace UnsafeDivide

/-- Return Python's floor quotient, but silently return zero on division by zero. -/
def unsafe_divide (n d : Int) : Int :=
  if d = 0 then 0 else n.fdiv d

/-! ## Unit tests: all assertions from the Python `check` -/
example : unsafe_divide 10 2 = 5 := by native_decide
example : unsafe_divide 9 3 = 3 := by native_decide
example : unsafe_divide 5 0 = 0 := by native_decide
example : unsafe_divide 100 0 = 0 := by native_decide
example : unsafe_divide 0 1 = 0 := by native_decide
example : unsafe_divide 0 0 = 0 := by native_decide

-- These distinguish Python floor division from other signed division conventions.
example : unsafe_divide (-7) 3 = -3 := by native_decide
example : unsafe_divide 7 (-3) = -3 := by native_decide
example : unsafe_divide (-7) (-3) = 2 := by native_decide
example : unsafe_divide 1 (-2) = -1 := by native_decide
example : unsafe_divide 0 (-2) = 0 := by native_decide

/-- Executable version of the supplied Python test harness. -/
def check (candidate : Int → Int → Int) : Bool :=
  candidate 10 2 == 5 && candidate 9 3 == 3 &&
  candidate 5 0 == 0 && candidate 100 0 == 0 &&
  candidate 0 1 == 0 && candidate 0 0 == 0

#eval check unsafe_divide
#eval if check unsafe_divide then "All tests passed." else "Candidate failed tests"
#eval [unsafe_divide (-7) 3, unsafe_divide 7 (-3), unsafe_divide (-7) (-3)]

/-- The Python function accepts every pair of integers; division by zero is included. -/
def Pre (_n _d : Int) : Prop := True

/-- On a nonzero divisor the output is exactly Python's floor quotient. -/
def normal_division_prop (n d : Int) : Prop :=
  d ≠ 0 → unsafe_divide n d = n.fdiv d

theorem normal_division_thm (n d : Int) : normal_division_prop n d := by
  intro hd
  simp [unsafe_divide, hd]

/-- Every zero-divisor call silently returns zero, regardless of the numerator. -/
def zero_divisor_prop (n : Int) : Prop := unsafe_divide n 0 = 0

theorem zero_divisor_thm (n : Int) : zero_divisor_prop n := by
  simp [zero_divisor_prop, unsafe_divide]

/-- A zero numerator produces the same zero result, even when the divisor is zero. -/
def zero_numerator_prop (d : Int) : Prop := unsafe_divide 0 d = 0

theorem zero_numerator_thm (d : Int) : zero_numerator_prop d := by
  simp [zero_numerator_prop, unsafe_divide]

/-- The returned value alone does not distinguish an error from legitimate zero. -/
def ambiguity_prop (n d : Int) : Prop :=
  d ≠ 0 → unsafe_divide n 0 = unsafe_divide 0 d

theorem ambiguity_thm (n d : Int) : ambiguity_prop n d := by
  intro _
  simp [unsafe_divide]

/-- Arithmetic characterization of floor rounding, for both signs of the divisor.
For `d < 0`, multiplication reverses the inequalities; no negative inputs are excluded.
The zero-divisor case is specified separately by `zero_divisor_prop`. -/
def floor_bounds_prop (n d : Int) : Prop :=
  (0 < d → unsafe_divide n d * d ≤ n ∧ n < (unsafe_divide n d + 1) * d) ∧
  (d < 0 → (unsafe_divide n d + 1) * d < n ∧ n ≤ unsafe_divide n d * d)

theorem floor_bounds_thm (n d : Int) : floor_bounds_prop n d := by
  constructor
  · intro hd
    rw [normal_division_thm n d (ne_of_gt hd)]
    have hlo := Int.mul_fdiv_self_le (x := n) hd
    have hhi := Int.lt_mul_fdiv_self_add (x := n) hd
    constructor <;> nlinarith
  · intro hd
    rw [normal_division_thm n d (ne_of_lt hd)]
    have h := (Int.fdiv_fmod_unique' (a := n) (b := d)
      (r := n.fmod d) (q := n.fdiv d) hd).mp ⟨rfl, rfl⟩
    constructor <;> nlinarith [h.1, h.2.1, h.2.2]

/-- Full observable contract, including the intentionally vulnerable behavior. -/
def Post_prop (n d : Int) : Prop :=
  normal_division_prop n d ∧ zero_divisor_prop n ∧
  zero_numerator_prop d ∧ ambiguity_prop n d ∧ floor_bounds_prop n d

/-! ## Property-based tests

Each test below exhaustively checks its executable Boolean property on the
signed grid [-30, 30], not just the fixed unit-test arguments. The implication
forms are executable and test both zero and nonzero divisor branches.
-/

def testInts : List Int := (List.range 61).map (fun k => (k : Int) - 30)

-- PBT for normal_division_prop.
example : testInts.all (fun n => testInts.all (fun d =>
    decide (d ≠ 0 → unsafe_divide n d = n.fdiv d))) = true := by native_decide

-- PBT for zero_divisor_prop.
example : testInts.all (fun n => unsafe_divide n 0 == 0) = true := by native_decide

-- PBT for zero_numerator_prop.
example : testInts.all (fun d => unsafe_divide 0 d == 0) = true := by native_decide

-- PBT for ambiguity_prop.
example : testInts.all (fun n => testInts.all (fun d =>
    decide (d ≠ 0 → unsafe_divide n 0 = unsafe_divide 0 d))) = true := by native_decide

-- PBT for floor_bounds_prop, including the reversed negative-divisor bounds.
example : testInts.all (fun n => testInts.all (fun d =>
    decide ((0 < d → unsafe_divide n d * d ≤ n ∧ n < (unsafe_divide n d + 1) * d) ∧
      (d < 0 → (unsafe_divide n d + 1) * d < n ∧ n ≤ unsafe_divide n d * d))))
    = true := by native_decide

-- PBT for the entire Post_prop, unfolding it into an executable proposition.
example : testInts.all (fun n => testInts.all (fun d =>
    decide ((d ≠ 0 → unsafe_divide n d = n.fdiv d) ∧
      unsafe_divide n 0 = 0 ∧ unsafe_divide 0 d = 0 ∧
      (d ≠ 0 → unsafe_divide n 0 = unsafe_divide 0 d) ∧
      (0 < d → unsafe_divide n d * d ≤ n ∧ n < (unsafe_divide n d + 1) * d) ∧
      (d < 0 → (unsafe_divide n d + 1) * d < n ∧ n ≤ unsafe_divide n d * d))))
    = true := by native_decide

/-- Correctness does not exclude the bug: it proves the specified unsafe contract. -/
theorem correctness_thm (n d : Int) : Pre n d → Post_prop n d := by
  intro _
  exact ⟨normal_division_thm n d, zero_divisor_thm n,
    zero_numerator_thm d, ambiguity_thm n d, floor_bounds_thm n d⟩

/-! ## Imperative implementation -/

def unsafe_divide_imp (n d : Int) : Int := Id.run do
  let mut result : Int := 0
  if d = 0 then
    result := 0
  else
    result := n.fdiv d
  return result

example : unsafe_divide_imp 10 2 = 5 := by native_decide
example : unsafe_divide_imp 9 3 = 3 := by native_decide
example : unsafe_divide_imp 5 0 = 0 := by native_decide
example : unsafe_divide_imp 100 0 = 0 := by native_decide
example : unsafe_divide_imp 0 1 = 0 := by native_decide
example : unsafe_divide_imp 0 0 = 0 := by native_decide
example : unsafe_divide_imp 7 (-3) = -3 := by native_decide
example : unsafe_divide_imp (-7) 3 = -3 := by native_decide
example : unsafe_divide_imp (-7) (-3) = 2 := by native_decide
#eval check unsafe_divide_imp
#eval unsafe_divide_imp 100 0

example : testInts.all (fun n => testInts.all (fun d =>
    unsafe_divide n d == unsafe_divide_imp n d)) = true := by native_decide

/-- The mutable implementation has identical behavior on every integer pair. -/
theorem equivalence_thm (n d : Int) : unsafe_divide n d = unsafe_divide_imp n d := by
  by_cases hd : d = 0 <;> simp [unsafe_divide, unsafe_divide_imp, hd]

end UnsafeDivide
end Agent
