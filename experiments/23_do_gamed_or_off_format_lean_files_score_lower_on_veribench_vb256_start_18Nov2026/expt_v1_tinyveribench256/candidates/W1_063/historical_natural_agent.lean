import Mathlib
namespace Agent

/-!
# Maximum of a nonempty list of natural-valued integers

This translation keeps `List Int` as the input type, so negative integers can
be rejected as in Python. Lean's static types account for the Python list and
integer type checks. `Except ValueError Int` models either the returned integer
or a raised `ValueError`; the particular diagnostic string is not observable in
the specification. Empty lists and lists containing negative integers fail.
The recursive implementation and the mutable-loop implementation are proved
equivalent on all inputs, including failures.
-/

namespace MyMaxList

inductive ValueError where
  | invalidInput
  deriving DecidableEq, Repr

-- Executable equality for return values and exceptions in the tests.
deriving instance DecidableEq for Except

/-- A total auxiliary fold; its zero seed is appropriate for natural values. -/
def maxList : List Int → Int
  | [] => 0
  | x :: xs => max x (maxList xs)

/-- The guarded functional translation of `prog`. -/
def prog (xs : List Int) : Except ValueError Int :=
  if xs ≠ [] ∧ ∀ x ∈ xs, 0 ≤ x then
    .ok (maxList xs)
  else
    .error .invalidInput

-- Fixed unit tests, including both of Python's precondition violations.
example : prog [7, 3, 9, 2] = .ok 9 := by native_decide
example : prog [5] = .ok 5 := by native_decide
example : prog [0] = .ok 0 := by native_decide
example : prog [4, 4, 0] = .ok 4 := by native_decide
example : prog [] = .error .invalidInput := by native_decide
example : prog [-1, 2, 3] = .error .invalidInput := by native_decide
#eval prog [7, 3, 9, 2]
#eval prog [5]
#eval prog ([] : List Int)
#eval prog [-1, 2, 3]

/-- Exactly the Python precondition within the statically typed input domain. -/
def Pre (xs : List Int) : Prop := xs ≠ [] ∧ ∀ x ∈ xs, 0 ≤ x

/-- Successful execution returns a member which bounds every input element. -/
def maximum_prop (xs : List Int) : Prop :=
  ∃ m, prog xs = .ok m ∧ m ∈ xs ∧ ∀ x ∈ xs, x ≤ m

/-- A successful, admissible call returns a natural-valued integer. -/
def nonnegative_prop (xs : List Int) : Prop :=
  ∃ m, prog xs = .ok m ∧ 0 ≤ m

/-- A singleton is returned unchanged if natural, and otherwise rejected. -/
def singleton_prop (xs : List Int) : Prop :=
  ∀ x, xs = [x] → prog xs = if 0 ≤ x then .ok x else .error .invalidInput

/-- Failure happens exactly on a precondition violation. -/
def rejection_prop (xs : List Int) : Prop :=
  prog xs = .error .invalidInput ↔ ¬ Pre xs

theorem maxList_nonnegative (xs : List Int) : 0 ≤ maxList xs := by
  induction xs with
  | nil => simp [maxList]
  | cons x xs ih => exact le_trans ih (le_max_right x (maxList xs))

theorem le_maxList (xs : List Int) (x : Int) (hx : x ∈ xs) :
    x ≤ maxList xs := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with h | h
    · subst x
      exact le_max_left y (maxList ys)
    · exact le_trans (ih h) (le_max_right y (maxList ys))

theorem maxList_mem (xs : List Int) (h : Pre xs) : maxList xs ∈ xs := by
  induction xs with
  | nil => exact (h.1 rfl).elim
  | cons x xs ih =>
    by_cases ht : xs = []
    · subst xs
      have hx : 0 ≤ x := h.2 x (by simp)
      simp [maxList, max_eq_left hx]
    · have hm : maxList xs ∈ xs := ih ⟨ht, fun y hy => h.2 y (by simp [hy])⟩
      rcases le_total x (maxList xs) with hle | hle
      · simpa [maxList, max_eq_right hle] using List.mem_cons_of_mem x hm
      · simp [maxList, max_eq_left hle]

theorem prog_of_pre (xs : List Int) (h : Pre xs) :
    prog xs = .ok (maxList xs) := by
  exact if_pos h

theorem maximum_thm (xs : List Int) (h : Pre xs) : maximum_prop xs := by
  exact ⟨maxList xs, prog_of_pre xs h, maxList_mem xs h, fun x hx => le_maxList xs x hx⟩

theorem nonnegative_thm (xs : List Int) (h : Pre xs) : nonnegative_prop xs := by
  exact ⟨maxList xs, prog_of_pre xs h, maxList_nonnegative xs⟩

theorem singleton_thm (xs : List Int) : singleton_prop xs := by
  intro x h
  subst xs
  by_cases hx : 0 ≤ x
  · simp [prog, maxList, hx]
  · simp [prog, hx]

theorem rejection_thm (xs : List Int) : rejection_prop xs := by
  unfold rejection_prop prog Pre
  split <;> simp_all

/-- Full successful-call contract; failure is specified separately and exactly. -/
def Post_prop (xs : List Int) : Prop :=
  maximum_prop xs ∧ nonnegative_prop xs ∧ singleton_prop xs ∧ rejection_prop xs

/-! Bounded exhaustive property-based tests.
The sample set contains every list of length at most four over an alphabet
with negative values, zero, positive values, repetitions, and different orders.
The tests use Boolean counterparts rather than unbounded existential decisions.
-/
def sampleAlphabet : List Int := [-2, -1, 0, 1, 2, 3, 9]

def sampleLists : Nat → List (List Int)
  | 0 => [[]]
  | n + 1 => [] :: sampleAlphabet.flatMap (fun x => (sampleLists n).map (x :: ·))

def preCheck (xs : List Int) : Bool :=
  decide (xs ≠ [] ∧ ∀ x ∈ xs, 0 ≤ x)

def maximumCheck (xs : List Int) : Bool :=
  match prog xs with
  | .ok m => xs.contains m && xs.all (fun x => decide (x ≤ m))
  | .error _ => false

def nonnegativeCheck (xs : List Int) : Bool :=
  match prog xs with
  | .ok m => decide (0 ≤ m)
  | .error _ => false

def singletonCheck (xs : List Int) : Bool :=
  match xs with
  | [x] => decide (prog xs = if 0 ≤ x then .ok x else .error .invalidInput)
  | _ => true

def rejectionCheck (xs : List Int) : Bool :=
  decide (prog xs = .error .invalidInput) == !preCheck xs

def postCheck (xs : List Int) : Bool :=
  maximumCheck xs && nonnegativeCheck xs && singletonCheck xs && rejectionCheck xs

-- PBT for maximum_prop, restricted to the original precondition.
example : (sampleLists 4).all (fun xs => !preCheck xs || maximumCheck xs) = true := by
  native_decide
-- PBT for nonnegative_prop.
example : (sampleLists 4).all (fun xs => !preCheck xs || nonnegativeCheck xs) = true := by
  native_decide
-- PBT for singleton_prop, including negative singletons.
example : (sampleLists 4).all singletonCheck = true := by native_decide
-- PBT for rejection_prop, without restricting to admissible inputs.
example : (sampleLists 4).all rejectionCheck = true := by native_decide
-- PBT for the entire postcondition.
example : (sampleLists 4).all (fun xs => !preCheck xs || postCheck xs) = true := by
  native_decide
#eval (sampleLists 4).length
#eval (sampleLists 4).all (fun xs => !preCheck xs || postCheck xs)
#eval (sampleLists 4).all rejectionCheck

/-- Kernel-checked correctness for every admissible input, not just samples. -/
theorem correctness (xs : List Int) : Pre xs → Post_prop xs := by
  intro h
  exact ⟨maximum_thm xs h, nonnegative_thm xs h, singleton_thm xs, rejection_thm xs⟩

/-- Imperative implementation: validate, then scan with a mutable maximum. -/
def progImperative (xs : List Int) : Except ValueError Int := Id.run do
  if xs ≠ [] ∧ ∀ x ∈ xs, 0 ≤ x then
    let mut current : Int := 0
    for x in xs do
      current := max current x
    return .ok current
  else
    return .error .invalidInput

example : progImperative [7, 3, 9, 2] = .ok 9 := by native_decide
example : progImperative [5] = .ok 5 := by native_decide
example : progImperative [0] = .ok 0 := by native_decide
example : progImperative [] = .error .invalidInput := by native_decide
example : progImperative [-1, 2, 3] = .error .invalidInput := by native_decide
example : (sampleLists 4).all (fun xs => decide (prog xs = progImperative xs)) = true := by
  native_decide
#eval progImperative [7, 3, 9, 2]
#eval progImperative [-1, 2, 3]

/-- Loop invariant: scanning from a nonnegative seed computes its maximum
with the recursively computed list maximum. -/
theorem foldl_max_eq (xs : List Int) (a : Int) (ha : 0 ≤ a) :
    xs.foldl max a = max a (maxList xs) := by
  induction xs generalizing a with
  | nil => simp [maxList, max_eq_left ha]
  | cons x xs ih =>
    rw [List.foldl_cons, ih (max a x) (le_trans ha (le_max_left a x))]
    exact max_assoc a x (maxList xs)

/-- Equality on all inputs, including empty and negative-containing lists. -/
theorem functional_eq_imperative (xs : List Int) : prog xs = progImperative xs := by
  have hf : xs.foldl max 0 = maxList xs := by
    rw [foldl_max_eq xs 0 (le_refl 0), max_eq_right (maxList_nonnegative xs)]
  unfold prog progImperative
  split <;> simp_all [Id.run] <;> rfl

end MyMaxList
end Agent
