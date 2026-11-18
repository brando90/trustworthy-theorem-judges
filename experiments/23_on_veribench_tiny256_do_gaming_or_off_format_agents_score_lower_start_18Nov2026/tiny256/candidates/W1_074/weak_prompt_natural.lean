/-!
# Parity of the sum of a list of odd integers

This is a Lean 4 translation of a Python program. The program returns `sum(xs) % 2` for a
nonempty list of odd integers and raises `ValueError` otherwise.

Translation notes:
* Python's `ValueError` becomes `Except.error`, and a normal return becomes `Except.ok`.
* Python's `%` and Lean's `Int` `%` (`Int.emod`) give the same result when the divisor
  is `2`. Both return `0` or `1`, including for negative inputs: `-3 % 2 = 1` in both
  languages.
* The type `List Int` already guarantees what Python checks at runtime with
  `isinstance(xs, list)` and `isinstance(x, int)`.
* Python's `True` is the integer `1`, which is odd and accepted. `False` is `0`, which is
  even and rejected. Here they behave exactly like `1` and `0`.

The docstring's edge cases are proved below:
* A single odd number has parity 1: `prog_singleton`.
* An even count of odd numbers has parity 0: `prog_even_count`.
* `prog` fails exactly when the precondition fails: `prog_error_iff`.
-/

namespace OddSumParity

/-- Sum of a list of integers (Python's built-in `sum`). -/
def listSum : List Int → Int
  | [] => 0
  | x :: xs => x + listSum xs

/-- Precondition: `xs` is nonempty and every element has remainder one modulo two. -/
def pre (xs : List Int) : Prop :=
  xs ≠ [] ∧ ∀ x ∈ xs, x % 2 = 1

instance (xs : List Int) : Decidable (pre xs) :=
  inferInstanceAs (Decidable (xs ≠ [] ∧ ∀ x ∈ xs, x % 2 = 1))

/-- For a nonempty list of odd integers, return `sum xs % 2`, which is either `0` or `1`.
If the precondition fails, return an error, as Python raises `ValueError`. -/
def prog (xs : List Int) : Except String Int :=
  if pre xs then
    .ok (listSum xs % 2)
  else
    .error s!"Require non-empty list of odd integers (got xs={xs})"

/-! ## Tests (translation of `check`) -/

/-- The call returned normally with value `v`. -/
def returns (r : Except String Int) (v : Int) : Bool :=
  match r with
  | .ok w => w == v
  | .error _ => false

/-- The call failed (in Python, it raised `ValueError`). -/
def raises (r : Except String Int) : Bool :=
  match r with
  | .ok _ => false
  | .error _ => true

/-- Run the fixed examples. Returns `true` if and only if every check passes. -/
def check (candidate : List Int → Except String Int) : Bool :=
  returns (candidate [1, 3, 5]) 1 &&
  returns (candidate [1]) 1 &&
  raises (candidate []) &&
  returns (candidate [5]) 1 &&
  returns (candidate [1, 3]) 0

theorem check_prog : check prog = true := by decide

/-! ## Basic facts about the precondition -/

theorem pre_iff {xs : List Int} : pre xs ↔ xs ≠ [] ∧ ∀ x ∈ xs, x % 2 = 1 := Iff.rfl

theorem not_pre_nil : ¬ pre [] := fun h => (pre_iff.mp h).1 rfl

theorem pre_singleton {x : Int} (hx : x % 2 = 1) : pre [x] :=
  pre_iff.mpr ⟨fun h => nomatch h, fun y hy => by
    rw [List.mem_singleton.mp hy]
    exact hx⟩

theorem pre_cons {x : Int} {xs : List Int} (hx : x % 2 = 1)
    (hxs : ∀ y ∈ xs, y % 2 = 1) : pre (x :: xs) :=
  pre_iff.mpr ⟨fun h => nomatch h, fun y hy => by
    cases List.mem_cons.mp hy with
    | inl h => rw [h]; exact hx
    | inr h => exact hxs y h⟩

/-! ## Key arithmetic lemma -/

/-- A sum of odd integers has the same parity as the number of terms. -/
theorem listSum_emod_two_of_all_odd :
    ∀ xs : List Int, (∀ x ∈ xs, x % 2 = 1) → listSum xs % 2 = (xs.length : Int) % 2 := by
  intro xs
  induction xs with
  | nil => intro _; first | rfl | decide | simp [listSum]
  | cons x xs ih =>
    intro h
    have hx : x % 2 = 1 := h x (by simp)
    have ih' := ih (fun y hy => h y (by simp [hy]))
    simp only [listSum, List.length_cons]
    omega

/-! ## Behaviour of `prog` -/

theorem prog_eq_ok_of_pre {xs : List Int} (h : pre xs) :
    prog xs = .ok (listSum xs % 2) := by
  unfold prog
  rw [if_pos h]

theorem prog_eq_error_of_not_pre {xs : List Int} (h : ¬ pre xs) :
    ∃ msg, prog xs = .error msg := by
  unfold prog
  rw [if_neg h]
  exact ⟨_, rfl⟩

/-- `prog` returns `r` exactly when the precondition holds and `r = sum xs % 2`. -/
theorem prog_ok_iff {xs : List Int} {r : Int} :
    prog xs = .ok r ↔ pre xs ∧ r = listSum xs % 2 := by
  by_cases h : pre xs
  · rw [prog_eq_ok_of_pre h]
    constructor
    · intro hr
      cases hr
      exact ⟨h, rfl⟩
    · intro ⟨_, hr⟩
      rw [hr]
  · obtain ⟨msg, hm⟩ := prog_eq_error_of_not_pre h
    rw [hm]
    constructor
    · intro hr
      cases hr
    · intro ⟨hp, _⟩
      exact absurd hp h

/-- `prog` fails (Python: raises `ValueError`) exactly when the precondition fails. -/
theorem prog_error_iff {xs : List Int} :
    (∃ msg, prog xs = .error msg) ↔ ¬ pre xs := by
  constructor
  · intro ⟨msg, hm⟩ hp
    rw [prog_eq_ok_of_pre hp] at hm
    cases hm
  · exact prog_eq_error_of_not_pre

/-- Every successful result is either `0` or `1`. -/
theorem prog_ok_zero_or_one {xs : List Int} {r : Int} (h : prog xs = .ok r) :
    r = 0 ∨ r = 1 := by
  have ⟨_, hr⟩ := prog_ok_iff.mp h
  rw [hr]
  omega

/-- Main correctness theorem: on valid input, the result is the parity of the length. -/
theorem prog_eq_length_parity {xs : List Int} (h : pre xs) :
    prog xs = .ok ((xs.length : Int) % 2) := by
  rw [prog_eq_ok_of_pre h, listSum_emod_two_of_all_odd xs (pre_iff.mp h).2]

/-- Full specification, combining the success and failure cases. -/
theorem prog_spec (xs : List Int) :
    (pre xs → prog xs = .ok (listSum xs % 2) ∧ listSum xs % 2 = (xs.length : Int) % 2) ∧
    (¬ pre xs → ∃ msg, prog xs = .error msg) :=
  ⟨fun h => ⟨prog_eq_ok_of_pre h, listSum_emod_two_of_all_odd xs (pre_iff.mp h).2⟩,
   prog_eq_error_of_not_pre⟩

/-- Edge case: a single odd number has parity 1. -/
theorem prog_singleton {x : Int} (hx : x % 2 = 1) : prog [x] = .ok 1 :=
  (prog_eq_length_parity (pre_singleton hx)).trans rfl

/-- Edge case: the sum of an even count of odd numbers has parity 0. -/
theorem prog_even_count {xs : List Int} (h : pre xs) (he : xs.length % 2 = 0) :
    prog xs = .ok 0 := by
  rw [prog_eq_length_parity h]
  have : (xs.length : Int) % 2 = 0 := by omega
  rw [this]

/-- The result is `1` exactly for valid input with an odd number of elements. -/
theorem prog_eq_ok_one_iff {xs : List Int} :
    prog xs = .ok 1 ↔ pre xs ∧ xs.length % 2 = 1 := by
  constructor
  · intro h
    have ⟨hp, hr⟩ := prog_ok_iff.mp h
    rw [listSum_emod_two_of_all_odd xs (pre_iff.mp hp).2] at hr
    exact ⟨hp, by omega⟩
  · intro ⟨hp, hl⟩
    rw [prog_eq_length_parity hp]
    have : (xs.length : Int) % 2 = 1 := by omega
    rw [this]

/-- On valid inputs, the result depends only on the number of elements. -/
theorem prog_eq_of_length_eq {xs ys : List Int} (hx : pre xs) (hy : pre ys)
    (hl : xs.length = ys.length) : prog xs = prog ys := by
  rw [prog_eq_length_parity hx, prog_eq_length_parity hy, hl]

/-- Adding one more odd number flips the parity. -/
theorem prog_cons_flip {x : Int} {xs : List Int} (hx : x % 2 = 1) (hxs : pre xs) :
    ∃ r, prog xs = .ok r ∧ prog (x :: xs) = .ok (1 - r) := by
  refine ⟨(xs.length : Int) % 2, prog_eq_length_parity hxs, ?_⟩
  rw [prog_eq_length_parity (pre_cons hx (pre_iff.mp hxs).2)]
  have : ((x :: xs).length : Int) % 2 = 1 - (xs.length : Int) % 2 := by
    simp only [List.length_cons]
    omega
  rw [this]

/-! ## Concrete examples -/

example : pre [1, 3, 5] := by decide
example : pre [-3, 7] := by decide        -- negative odd integers are accepted
example : ¬ pre [] := by decide
example : ¬ pre [0] := by decide          -- Python's `False` (= 0) is rejected
example : ¬ pre [1, 2] := by decide

example : prog [1, 3, 5] = .ok 1 := rfl
example : prog [1] = .ok 1 := rfl
example : ∃ msg, prog [] = .error msg := prog_eq_error_of_not_pre not_pre_nil
example : prog [5] = .ok 1 := rfl
example : prog [1, 3] = .ok 0 := rfl
example : prog [-3, 7] = .ok 0 := rfl
example : ∃ msg, prog [1, 2] = .error msg := prog_eq_error_of_not_pre (by decide)

end OddSumParity
