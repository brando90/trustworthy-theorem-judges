import Mathlib
namespace Agent

/-!
# OddSumParity (`9_MyOddSumParity`)

Lean 4 translation of a Python program returning the parity (`0` or `1`) of the sum of
all elements of a non-empty list of odd integers.

Python source:
```python
def pre(xs: List[int]) -> bool:
    return (isinstance(xs, list) and len(xs) > 0 and
            all(isinstance(x, int) and x % 2 == 1 for x in xs))

def prog(xs: List[int]) -> int:
    if not pre(xs):
        raise ValueError(f"Require non-empty list of odd integers (got xs={xs})")
    return sum(xs) % 2
```

Modelling choices:
* Python `int` is modelled by `Int`; the `isinstance` side conditions are enforced by the
  Lean type `List Int`.
* Python's `%` with the positive divisor `2` always yields `0` or `1`; Lean's `Int` `%`
  (`Int.emod`) has the same behaviour, so `sum(xs) % 2` is `xs.sum % 2`.
* The `ValueError` raised on a pre-violation is modelled by `oddSumParityChecked`, which
  returns `Except.error` exactly when the precondition `Pre` fails.

Contents: functional implementation, unit tests, `Pre`, named properties with proofs,
`Post_prop`, property-based tests, the correctness theorem `Pre → Post`, an imperative
implementation (`Id.run do` with mutable state) and the equivalence theorem.
-/

namespace «9_MyOddSumParity»

/-! ## Functional implementation -/

/-- Parity of the sum of a list of integers (`sum(xs) % 2` in Python).
`Int` `%` is Euclidean modulo, so the result is `0` or `1` even for negative sums,
matching Python's `%` for the positive divisor `2`. -/
def oddSumParity (xs : List Int) : Int :=
  xs.sum % 2

/-- Executable precondition (`pre` in Python): non-empty list, all elements odd. -/
def preB (xs : List Int) : Bool :=
  decide (0 < xs.length) && xs.all (fun x => x % 2 == 1)

/-- Checked entry point mirroring Python's `prog`: a pre-violation yields `Except.error`
(Python raises `ValueError`), otherwise the parity is returned in `Except.ok`. -/
def oddSumParityChecked (xs : List Int) : Except String Int :=
  if preB xs then
    .ok (oddSumParity xs)
  else
    .error s!"Require non-empty list of odd integers (got xs={xs})"

/-! ## Unit tests -/

example : oddSumParity [1, 3, 5] = 1 := by native_decide
example : oddSumParity [1] = 1 := by native_decide
example : oddSumParity [1, 3] = 0 := by native_decide
example : oddSumParity [-1, 3, 5] = 1 := by native_decide
example : oddSumParity [-1, -3] = 0 := by native_decide
example : oddSumParity [7, -7, 9, 11] = 0 := by native_decide

example : preB [1, 3, 5] = true := by native_decide
example : preB [1] = true := by native_decide
example : preB [] = false := by native_decide
example : preB [2, 4, 6] = false := by native_decide
example : preB [1, 2, 3] = false := by native_decide

example : (oddSumParityChecked [1, 3, 5]).toOption = some 1 := by native_decide
example : (oddSumParityChecked [1]).toOption = some 1 := by native_decide
example : (oddSumParityChecked []).toOption = none := by native_decide
example : (oddSumParityChecked [2, 4, 6]).toOption = none := by native_decide

#eval oddSumParity [1, 3, 5]        -- 1
#eval oddSumParity [1]              -- 1
#eval oddSumParity [1, 3]           -- 0
#eval oddSumParityChecked [1, 3, 5] -- Except.ok 1
#eval oddSumParityChecked []        -- Except.error ...
#eval oddSumParityChecked [2, 4, 6] -- Except.error ...

/-! ## Pre-condition -/

/-- Precondition (`pre` in Python): `xs` is a non-empty list of odd integers. -/
def Pre (xs : List Int) : Prop :=
  0 < xs.length ∧ ∀ x ∈ xs, x % 2 = 1

/-- The executable precondition `preB` decides `Pre`. -/
theorem preB_iff_Pre (xs : List Int) : preB xs = true ↔ Pre xs := by
  simp [preB, Pre]

/-- The Python negative tests: the empty list violates the precondition. -/
theorem not_Pre_nil : ¬ Pre [] := by
  simp [Pre]

/-- The Python negative tests: a list of even numbers violates the precondition. -/
theorem not_Pre_evens : ¬ Pre [2, 4, 6] := by
  simp [Pre]

/-- Key arithmetic fact: the sum of a list of odd integers has the parity of its length. -/
theorem sum_emod_two_eq_length_emod_two (xs : List Int) (h : ∀ x ∈ xs, x % 2 = 1) :
    xs.sum % 2 = (xs.length : Int) % 2 := by
  induction xs with
  | nil => simp
  | cons a t ih =>
    rw [List.forall_mem_cons] at h
    obtain ⟨ha, ht⟩ := h
    have ih' := ih ht
    simp only [List.sum_cons, List.length_cons]
    push_cast
    omega

/-! ## Properties -/

/-- The result is a parity bit: `0` or `1`. -/
def parity_in_range_prop (_xs : List Int) (r : Int) : Prop :=
  r = 0 ∨ r = 1

theorem parity_in_range_thm (xs : List Int) :
    parity_in_range_prop xs (oddSumParity xs) := by
  unfold parity_in_range_prop oddSumParity
  omega

/-- The result is the remainder of the sum modulo 2 (Python `sum(xs) % 2`). -/
def parity_eq_sum_mod_prop (xs : List Int) (r : Int) : Prop :=
  r = xs.sum % 2

theorem parity_eq_sum_mod_thm (xs : List Int) :
    parity_eq_sum_mod_prop xs (oddSumParity xs) := rfl

/-- For a list of odd integers the parity of the sum is the parity of the length. -/
def parity_eq_length_prop (xs : List Int) (r : Int) : Prop :=
  r = (xs.length : Int) % 2

theorem parity_eq_length_thm (xs : List Int) (h : Pre xs) :
    parity_eq_length_prop xs (oddSumParity xs) :=
  sum_emod_two_eq_length_emod_two xs h.2

/-- A single odd number has parity `1`. -/
def singleton_prop (xs : List Int) (r : Int) : Prop :=
  xs.length = 1 → r = 1

theorem singleton_thm (xs : List Int) (h : Pre xs) :
    singleton_prop xs (oddSumParity xs) := by
  intro hlen
  have hl := parity_eq_length_thm xs h
  unfold parity_eq_length_prop at hl
  rw [hl, hlen]
  rfl

/-- An even count of odd integers sums to an even number: parity `0`. -/
def even_count_prop (xs : List Int) (r : Int) : Prop :=
  xs.length % 2 = 0 → r = 0

theorem even_count_thm (xs : List Int) (h : Pre xs) :
    even_count_prop xs (oddSumParity xs) := by
  intro hlen
  have hl := parity_eq_length_thm xs h
  unfold parity_eq_length_prop at hl
  omega

/-- An odd count of odd integers sums to an odd number: parity `1`. -/
def odd_count_prop (xs : List Int) (r : Int) : Prop :=
  xs.length % 2 = 1 → r = 1

theorem odd_count_thm (xs : List Int) (h : Pre xs) :
    odd_count_prop xs (oddSumParity xs) := by
  intro hlen
  have hl := parity_eq_length_thm xs h
  unfold parity_eq_length_prop at hl
  omega

/-- The result is `1` exactly when the sum is odd (and `0` exactly when it is even). -/
def odd_sum_iff_prop (xs : List Int) (r : Int) : Prop :=
  (r = 1 ↔ Odd xs.sum) ∧ (r = 0 ↔ Even xs.sum)

theorem odd_sum_iff_thm (xs : List Int) :
    odd_sum_iff_prop xs (oddSumParity xs) := by
  unfold odd_sum_iff_prop oddSumParity
  rw [Int.odd_iff, Int.even_iff]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- The checked entry point succeeds on admissible inputs, returning the parity. -/
theorem checked_ok_of_pre (xs : List Int) (h : Pre xs) :
    oddSumParityChecked xs = .ok (oddSumParity xs) := by
  unfold oddSumParityChecked
  rw [if_pos ((preB_iff_Pre xs).2 h)]

/-- The checked entry point fails (Python `ValueError`) on every pre-violation. -/
theorem checked_error_of_not_pre (xs : List Int) (h : ¬ Pre xs) :
    ∃ msg, oddSumParityChecked xs = .error msg := by
  unfold oddSumParityChecked
  rw [if_neg (fun hb => h ((preB_iff_Pre xs).1 hb))]
  exact ⟨_, rfl⟩

/-- `Pre` holds iff the checked entry point returns an `ok` value. -/
theorem checked_isOk_iff_Pre (xs : List Int) :
    (∃ r, oddSumParityChecked xs = .ok r) ↔ Pre xs := by
  constructor
  · rintro ⟨r, hr⟩
    by_contra hnp
    obtain ⟨msg, hmsg⟩ := checked_error_of_not_pre xs hnp
    rw [hmsg] at hr
    exact Except.noConfusion hr
  · intro h
    exact ⟨_, checked_ok_of_pre xs h⟩

/-! ## Post-condition -/

/-- Post-condition: conjunction of all the properties above. -/
def Post_prop (xs : List Int) (r : Int) : Prop :=
  parity_in_range_prop xs r ∧
  parity_eq_sum_mod_prop xs r ∧
  parity_eq_length_prop xs r ∧
  singleton_prop xs r ∧
  even_count_prop xs r ∧
  odd_count_prop xs r ∧
  odd_sum_iff_prop xs r

/-- Executable Boolean form of `Post_prop` (used by the property-based tests). -/
def postB (xs : List Int) (r : Int) : Bool :=
  decide ((r = 0 ∨ r = 1) ∧
    r = xs.sum % 2 ∧
    r = (xs.length : Int) % 2 ∧
    (xs.length = 1 → r = 1) ∧
    (xs.length % 2 = 0 → r = 0) ∧
    (xs.length % 2 = 1 → r = 1) ∧
    ((r = 1 ↔ xs.sum % 2 = 1) ∧ (r = 0 ↔ xs.sum % 2 = 0)))

/-- `postB` is a faithful executable form of `Post_prop`. -/
theorem postB_iff_Post_prop (xs : List Int) (r : Int) : postB xs r = true ↔ Post_prop xs r := by
  unfold postB Post_prop parity_in_range_prop parity_eq_sum_mod_prop parity_eq_length_prop
    singleton_prop even_count_prop odd_count_prop odd_sum_iff_prop
  rw [Int.odd_iff, Int.even_iff, decide_eq_true_eq]

/-! ## Property-based tests

Admissible inputs are generated by construction: `toOdd ys = ys.map (fun y => 2 * y + 1)`
is a list of odd integers for every `ys : List Int`, and `toOdd (y :: ys)` is non-empty.
Pre-violations are generated as `ys ++ 2 * y :: zs` (contains an even element) or `[]`. -/

/-- Helper: turn an arbitrary integer list into a list of odd integers. -/
def toOdd (ys : List Int) : List Int := ys.map (fun y => 2 * y + 1)

/-- Bounded test data: `[1, 3, 5, ..., 2n-1]`. -/
def oddList (n : Nat) : List Int := (List.range n).map (fun i => 2 * (i : Int) + 1)

/-- Bounded test data with mixed signs: all entries are odd. -/
def oddListMixed (n : Nat) : List Int :=
  (List.range n).map (fun i => if i % 3 = 0 then -(2 * (i : Int) + 1) else 2 * (i : Int) - 7)

-- parity_in_range_prop (holds for every list)
#eval Plausible.Testable.check (∀ xs : List Int, oddSumParity xs = 0 ∨ oddSumParity xs = 1)

-- parity_eq_sum_mod_prop (holds for every list)
#eval Plausible.Testable.check (∀ xs : List Int, oddSumParity xs = xs.sum % 2)

-- parity_eq_length_prop on admissible inputs
#eval Plausible.Testable.check (∀ (y : Int) (ys : List Int),
  oddSumParity (toOdd (y :: ys)) = ((toOdd (y :: ys)).length : Int) % 2)

-- singleton_prop on admissible inputs
#eval Plausible.Testable.check (∀ y : Int, oddSumParity (toOdd [y]) = 1)

-- even_count_prop: `toOdd (y :: ys ++ y :: ys)` is admissible with even length
#eval Plausible.Testable.check (∀ (y : Int) (ys : List Int),
  oddSumParity (toOdd (y :: ys ++ y :: ys)) = 0)

-- odd_count_prop: `toOdd (y :: (ys ++ ys))` is admissible with odd length
#eval Plausible.Testable.check (∀ (y : Int) (ys : List Int),
  oddSumParity (toOdd (y :: (ys ++ ys))) = 1)

-- odd_sum_iff_prop (holds for every list; `Odd`/`Even` on `Int` are decidable)
#eval Plausible.Testable.check (∀ xs : List Int,
  (oddSumParity xs = 1 ↔ Odd xs.sum) ∧ (oddSumParity xs = 0 ↔ Even xs.sum))

-- preB accepts the constructed admissible inputs and rejects lists containing an even number
#eval Plausible.Testable.check (∀ (y : Int) (ys : List Int), preB (toOdd (y :: ys)) = true)
#eval Plausible.Testable.check (∀ (y : Int) (ys zs : List Int), preB (ys ++ 2 * y :: zs) = false)

-- Post_prop on admissible inputs (randomized)
#eval Plausible.Testable.check (∀ (y : Int) (ys : List Int),
  postB (toOdd (y :: ys)) (oddSumParity (toOdd (y :: ys))) = true)

-- checked entry point: `ok` exactly on admissible inputs (returning the parity), `error` otherwise
#eval Plausible.Testable.check (∀ xs : List Int,
  (oddSumParityChecked xs).toOption = (if preB xs then some (oddSumParity xs) else none))
#eval Plausible.Testable.check (∀ (y : Int) (ys : List Int),
  (oddSumParityChecked (toOdd (y :: ys))).toOption = some (oddSumParity (toOdd (y :: ys))))
#eval Plausible.Testable.check (∀ (y : Int) (ys zs : List Int),
  (oddSumParityChecked (ys ++ 2 * y :: zs)).toOption = none)

-- Bounded, exhaustive-style tests on admissible inputs of lengths 1..60
example : (List.range 60).all (fun n =>
    preB (oddList (n + 1)) && postB (oddList (n + 1)) (oddSumParity (oddList (n + 1)))) = true := by
  native_decide
example : (List.range 60).all (fun n =>
    preB (oddListMixed (n + 1)) &&
      postB (oddListMixed (n + 1)) (oddSumParity (oddListMixed (n + 1)))) = true := by
  native_decide
example : (List.range 60).all (fun n =>
    oddSumParity (oddList (n + 1)) == ((n + 1 : Nat) : Int) % 2) = true := by
  native_decide
example : (List.range 60).all (fun n =>
    oddSumParity (oddListMixed (n + 1)) == ((n + 1 : Nat) : Int) % 2) = true := by
  native_decide
-- Pre-violations: lists of even numbers of every length (including the empty list) are rejected
example : (List.range 30).all (fun n =>
    (oddSumParityChecked ((List.range n).map (fun i => 2 * (i : Int)))).toOption == none) = true := by
  native_decide

/-! ## Correctness theorem -/

/-- Correctness: on admissible inputs the functional implementation satisfies the
post-condition. -/
theorem correctness (xs : List Int) (h : Pre xs) : Post_prop xs (oddSumParity xs) :=
  ⟨parity_in_range_thm xs, parity_eq_sum_mod_thm xs, parity_eq_length_thm xs h,
   singleton_thm xs h, even_count_thm xs h, odd_count_thm xs h, odd_sum_iff_thm xs⟩

/-- Correctness of the checked entry point: on admissible inputs it returns `ok r` with `r`
satisfying the post-condition. -/
theorem checked_correctness (xs : List Int) (h : Pre xs) :
    ∃ r, oddSumParityChecked xs = .ok r ∧ Post_prop xs r :=
  ⟨oddSumParity xs, checked_ok_of_pre xs h, correctness xs h⟩

/-! ## Imperative implementation -/

/-- Imperative implementation: accumulate the sum in a mutable variable, then take `% 2`. -/
def oddSumParityImp (xs : List Int) : Int := Id.run do
  let mut s : Int := 0
  for x in xs do
    s := s + x
  return s % 2

/-- Imperative checked entry point mirroring Python's `prog`: validates the input while
summing (mutable `allOdd` flag) and reports a pre-violation as `Except.error`. -/
def oddSumParityImpChecked (xs : List Int) : Except String Int := Id.run do
  let mut s : Int := 0
  let mut allOdd : Bool := true
  for x in xs do
    allOdd := allOdd && (x % 2 == 1)
    s := s + x
  if 0 < xs.length && allOdd then
    return .ok (s % 2)
  else
    return .error s!"Require non-empty list of odd integers (got xs={xs})"

/-! ## Imperative tests -/

example : oddSumParityImp [1, 3, 5] = 1 := by native_decide
example : oddSumParityImp [1] = 1 := by native_decide
example : oddSumParityImp [1, 3] = 0 := by native_decide
example : oddSumParityImp [-1, 3, 5] = 1 := by native_decide
example : oddSumParityImp [-1, -3] = 0 := by native_decide
example : (oddSumParityImpChecked [1, 3, 5]).toOption = some 1 := by native_decide
example : (oddSumParityImpChecked [1]).toOption = some 1 := by native_decide
example : (oddSumParityImpChecked []).toOption = none := by native_decide
example : (oddSumParityImpChecked [2, 4, 6]).toOption = none := by native_decide

#eval oddSumParityImp [1, 3, 5]          -- 1
#eval oddSumParityImp [1]                -- 1
#eval oddSumParityImpChecked [1, 3, 5]   -- Except.ok 1
#eval oddSumParityImpChecked []          -- Except.error ...
#eval oddSumParityImpChecked [2, 4, 6]   -- Except.error ...

#eval Plausible.Testable.check (∀ xs : List Int, oddSumParityImp xs = oddSumParity xs)
#eval Plausible.Testable.check (∀ xs : List Int,
  (oddSumParityImpChecked xs).toOption = (oddSumParityChecked xs).toOption)
example : (List.range 60).all (fun n =>
    oddSumParityImp (oddListMixed (n + 1)) == oddSumParity (oddListMixed (n + 1))) = true := by
  native_decide

/-! ## Equivalence theorems -/

/-- Loop invariant for the summation loop. -/
theorem foldl_add_eq_sum (xs : List Int) (s : Int) :
    xs.foldl (fun acc x => acc + x) s = s + xs.sum := by
  induction xs generalizing s with
  | nil => simp
  | cons a t ih => simp [List.foldl_cons, List.sum_cons, ih, add_assoc]

/-- The imperative implementation agrees with the functional one on every input. -/
theorem imp_eq_functional (xs : List Int) : oddSumParityImp xs = oddSumParity xs := by
  unfold oddSumParityImp oddSumParity
  simp [foldl_add_eq_sum]

/-- Loop invariant for the validating summation loop (state `⟨allOdd, s⟩`). -/
theorem foldl_check_eq (xs : List Int) (b : Bool) (s : Int) :
    xs.foldl (fun (r : MProd Bool Int) x => ⟨r.fst && (x % 2 == 1), r.snd + x⟩) ⟨b, s⟩ =
      ⟨b && xs.all (fun x => x % 2 == 1), s + xs.sum⟩ := by
  induction xs generalizing b s with
  | nil => simp
  | cons a t ih => simp [List.foldl_cons, List.sum_cons, ih, add_assoc, Bool.and_assoc]

/-- The imperative checked entry point agrees with the functional checked one on every input
(including pre-violations, where both report the error). -/
theorem impChecked_eq_checked (xs : List Int) :
    oddSumParityImpChecked xs = oddSumParityChecked xs := by
  unfold oddSumParityImpChecked oddSumParityChecked preB oddSumParity
  simp [foldl_check_eq]
  split <;> rfl

end «9_MyOddSumParity»
end Agent
