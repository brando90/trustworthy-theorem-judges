import Mathlib
namespace Agent

/-!
# HumanEval 9: rolling maximum

A translation of the Python program on arbitrary-precision signed integers.
The optional accumulator distinguishes the first element from subsequent ones,
so in particular all-negative inputs are handled without an artificial zero.
The specification identifies each output as the maximum of its input prefix.
-/

namespace humaneval_9_rolling_max

/-- Update Python's optional `running_max`. -/
def nextMax (current : Option Int) (n : Int) : Int :=
  match current with
  | none => n
  | some m => max m n

/-- Functional version of the loop, with its initial accumulator exposed. -/
def rollingAux (current : Option Int) : List Int → List Int
  | [] => []
  | n :: ns =>
    let m := nextMax current n
    m :: rollingAux (some m) ns

/-- The function in the Python source. -/
def rolling_max (numbers : List Int) : List Int :=
  rollingAux none numbers

example : rolling_max [] = [] := by native_decide
example : rolling_max [1, 2, 3, 4] = [1, 2, 3, 4] := by native_decide
example : rolling_max [4, 3, 2, 1] = [4, 4, 4, 4] := by native_decide
example : rolling_max [3, 2, 3, 100, 3] = [3, 3, 3, 100, 100] := by native_decide
example : rolling_max [1, 2, 3, 2, 3, 4, 2] = [1, 2, 3, 3, 3, 4, 4] := by native_decide
example : rolling_max [-5, -9, -2, -8] = [-5, -5, -2, -2] := by native_decide
#eval rolling_max [1, 2, 3, 2, 3, 4, 2]
#eval rolling_max ([] : List Int)

/-- Every list of integers is admissible. -/
def Pre (_numbers : List Int) : Prop := True

/-- A maximum is attained in the list and bounds every member. -/
def IsMaximum (xs : List Int) (m : Int) : Prop :=
  m ∈ xs ∧ ∀ x ∈ xs, x ≤ m

/-- The optional accumulator correctly summarizes the already processed prefix. -/
def CurrentMax (seen : List Int) (current : Option Int) : Prop :=
  match current with
  | none => seen = []
  | some m => IsMaximum seen m

/-- Extending a nonempty prefix updates its maximum with `max`. -/
theorem maximum_append_singleton {xs : List Int} {m : Int}
    (h : IsMaximum xs m) (n : Int) : IsMaximum (xs ++ [n]) (max m n) := by
  constructor
  · rcases le_total m n with hmn | hnm
    · simp [max_eq_right hmn]
    · simp only [max_eq_left hnm, List.mem_append, List.mem_singleton]
      exact Or.inl h.1
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact le_trans (h.2 x hx) (le_max_left m n)
    · have hx' : x = n := by simpa using hx
      subst x
      exact le_max_right m n

theorem nextMax_spec {seen : List Int} {current : Option Int}
    (h : CurrentMax seen current) (n : Int) :
    IsMaximum (seen ++ [n]) (nextMax current n) := by
  cases current with
  | none =>
    change seen = [] at h
    subst seen
    simp [nextMax, IsMaximum]
  | some m => exact maximum_append_singleton h n

theorem rollingAux_length (current : Option Int) (xs : List Int) :
    (rollingAux current xs).length = xs.length := by
  induction xs generalizing current with
  | nil => rfl
  | cons n ns ih => simp [rollingAux, ih]

/-- Every output is the attained maximum of the prefix processed up to it. -/
theorem rollingAux_prefix (xs : List Int) :
    ∀ (current : Option Int) (seen : List Int), CurrentMax seen current →
      ∀ (i : Nat) (m : Int), (rollingAux current xs)[i]? = some m →
        IsMaximum (seen ++ xs.take (i + 1)) m := by
  induction xs with
  | nil =>
    intro current seen hc i m hm
    simp [rollingAux] at hm
  | cons n ns ih =>
    intro current seen hc i m hm
    cases i with
    | zero =>
      simp only [rollingAux, List.getElem?_cons_zero, Option.some.injEq] at hm
      subst m
      simpa using nextMax_spec hc n
    | succ i =>
      simp only [rollingAux, List.getElem?_cons_succ] at hm
      have hc' : CurrentMax (seen ++ [n]) (some (nextMax current n)) :=
        nextMax_spec hc n
      have h := ih (some (nextMax current n)) (seen ++ [n]) hc' i m hm
      simpa [List.take_succ_cons, List.append_assoc] using h

def length_prop (numbers result : List Int) : Prop :=
  result.length = numbers.length

theorem length_thm (numbers : List Int) : length_prop numbers (rolling_max numbers) :=
  rollingAux_length none numbers

/-- At every output position, the value occurs in, and bounds, its input prefix. -/
def prefix_max_prop (numbers result : List Int) : Prop :=
  ∀ (i : Nat) (m : Int), result[i]? = some m →
    IsMaximum (numbers.take (i + 1)) m

theorem prefix_max_thm (numbers : List Int) :
    prefix_max_prop numbers (rolling_max numbers) := by
  intro i m hm
  have h := rollingAux_prefix numbers none [] rfl i m hm
  simpa using h

def monotone_prop (_numbers result : List Int) : Prop :=
  result.Pairwise (· ≤ ·)

theorem rollingAux_lower_bound (xs : List Int) (m y : Int)
    (hy : y ∈ rollingAux (some m) xs) : m ≤ y := by
  induction xs generalizing m with
  | nil => simp [rollingAux] at hy
  | cons n ns ih =>
    simp only [rollingAux, nextMax, List.mem_cons] at hy
    rcases hy with hy | hy
    · subst y
      exact le_max_left m n
    · exact le_trans (le_max_left m n) (ih (max m n) hy)

theorem rollingAux_pairwise (xs : List Int) (current : Option Int) :
    (rollingAux current xs).Pairwise (· ≤ ·) := by
  induction xs generalizing current with
  | nil => simp [rollingAux]
  | cons n ns ih =>
    rw [rollingAux, List.pairwise_cons]
    exact ⟨fun y hy => rollingAux_lower_bound ns (nextMax current n) y hy,
      ih (some (nextMax current n))⟩

theorem monotone_thm (numbers : List Int) : monotone_prop numbers (rolling_max numbers) :=
  rollingAux_pairwise numbers none

/-- The output at each position is at least the corresponding input. -/
def dominates_prop (numbers result : List Int) : Prop :=
  List.Forall₂ (· ≤ ·) numbers result

theorem rollingAux_dominates (xs : List Int) (current : Option Int) :
    List.Forall₂ (· ≤ ·) xs (rollingAux current xs) := by
  induction xs generalizing current with
  | nil => exact .nil
  | cons n ns ih =>
    apply List.Forall₂.cons
    · cases current with
      | none => exact le_refl n
      | some m => exact le_max_right m n
    · exact ih _

theorem dominates_thm (numbers : List Int) :
    dominates_prop numbers (rolling_max numbers) :=
  rollingAux_dominates numbers none

/-- The first input is copied; both heads are absent on empty input. -/
def first_prop (numbers result : List Int) : Prop :=
  result.head? = numbers.head?

theorem first_thm (numbers : List Int) : first_prop numbers (rolling_max numbers) := by
  cases numbers <;> rfl

/-- Complete behavioral contract; there is no restriction on signed inputs. -/
def Post_prop (numbers result : List Int) : Prop :=
  length_prop numbers result ∧
  prefix_max_prop numbers result ∧
  monotone_prop numbers result ∧
  dominates_prop numbers result ∧
  first_prop numbers result

/-! ## Property-based tests

The prefix checker enumerates the output indices, checking both attainment and
upper-boundedness. The other checks are the decidable forms of their predicates.
The bounded suite enumerates all lists of length at most four over five signed
integers, including negative-only, repeated, increasing and decreasing inputs.
-/

def prefixMaxCheck (numbers result : List Int) : Bool :=
  (List.range result.length).all fun i =>
    match result[i]? with
    | none => false
    | some m => (numbers.take (i + 1)).contains m &&
        (numbers.take (i + 1)).all (fun n => n ≤ m)

def postCheck (numbers result : List Int) : Bool :=
  decide (result.length = numbers.length) &&
  prefixMaxCheck numbers result &&
  decide (result.Pairwise (· ≤ ·)) &&
  decide (List.Forall₂ (· ≤ ·) numbers result) &&
  decide (result.head? = numbers.head?)

-- Randomized PBT for length_prop.
#eval Plausible.Testable.check (∀ xs : List Int, (rolling_max xs).length = xs.length)
-- Randomized PBT for prefix_max_prop (its finite Boolean form).
#eval Plausible.Testable.check (∀ xs : List Int, prefixMaxCheck xs (rolling_max xs) = true)
-- Randomized PBT for monotone_prop.
#eval Plausible.Testable.check (∀ xs : List Int, (rolling_max xs).Pairwise (· ≤ ·))
-- Randomized PBT for dominates_prop.
#eval Plausible.Testable.check (∀ xs : List Int, List.Forall₂ (· ≤ ·) xs (rolling_max xs))
-- Randomized PBT for first_prop.
#eval Plausible.Testable.check (∀ xs : List Int, (rolling_max xs).head? = xs.head?)
-- Randomized PBT for Post_prop, checking all conjuncts.
#eval Plausible.Testable.check (∀ xs : List Int, postCheck xs (rolling_max xs) = true)

def smallLists : Nat → List (List Int)
  | 0 => [[]]
  | k + 1 => [] :: [-2, -1, 0, 1, 2].flatMap (fun n =>
      (smallLists k).map (fun xs => n :: xs))

example : (smallLists 4).all (fun xs => decide ((rolling_max xs).length = xs.length)) = true := by
  native_decide
example : (smallLists 4).all (fun xs => prefixMaxCheck xs (rolling_max xs)) = true := by
  native_decide
example : (smallLists 4).all (fun xs => decide ((rolling_max xs).Pairwise (· ≤ ·))) = true := by
  native_decide
example : (smallLists 4).all (fun xs => decide (List.Forall₂ (· ≤ ·) xs (rolling_max xs))) = true := by
  native_decide
example : (smallLists 4).all (fun xs => decide ((rolling_max xs).head? = xs.head?)) = true := by
  native_decide
example : (smallLists 4).all (fun xs => postCheck xs (rolling_max xs)) = true := by
  native_decide
#eval (smallLists 4).length
#eval (smallLists 4).all (fun xs => postCheck xs (rolling_max xs))

/-- Correctness on all admissible inputs. -/
theorem correctness (numbers : List Int) :
    Pre numbers → Post_prop numbers (rolling_max numbers) := by
  intro _
  exact ⟨length_thm numbers, prefix_max_thm numbers, monotone_thm numbers,
    dominates_thm numbers, first_thm numbers⟩

/-! ## Imperative translation -/

/-- The Python loop with mutable running maximum and append-only result. -/
def rollingImperativeFrom (current : Option Int) (out numbers : List Int) : List Int :=
  Id.run do
    let mut running_max := current
    let mut result := out
    for n in numbers do
      let m := nextMax running_max n
      running_max := some m
      result := result ++ [m]
    return result

def rolling_max_imp (numbers : List Int) : List Int :=
  rollingImperativeFrom none [] numbers

example : rolling_max_imp [] = [] := by native_decide
example : rolling_max_imp [1, 2, 3, 4] = [1, 2, 3, 4] := by native_decide
example : rolling_max_imp [4, 3, 2, 1] = [4, 4, 4, 4] := by native_decide
example : rolling_max_imp [3, 2, 3, 100, 3] = [3, 3, 3, 100, 100] := by native_decide
example : rolling_max_imp [-5, -9, -2, -8] = [-5, -5, -2, -2] := by native_decide
#eval rolling_max_imp [1, 2, 3, 2, 3, 4, 2]
#eval Plausible.Testable.check (∀ xs : List Int, rolling_max xs = rolling_max_imp xs)

/-- Unrolling one iteration of the actual imperative loop. -/
theorem rollingImperativeFrom_cons (current : Option Int) (out : List Int)
    (n : Int) (ns : List Int) :
    rollingImperativeFrom current out (n :: ns) =
      rollingImperativeFrom (some (nextMax current n)) (out ++ [nextMax current n]) ns := by
  simp [rollingImperativeFrom]

/-- The loop appends exactly the functional continuation to the existing output. -/
theorem rollingImperativeFrom_eq (xs : List Int) (current : Option Int) (out : List Int) :
    rollingImperativeFrom current out xs = out ++ rollingAux current xs := by
  induction xs generalizing current out with
  | nil => simp [rollingImperativeFrom, rollingAux]
  | cons n ns ih =>
    rw [rollingImperativeFrom_cons, ih]
    simp [rollingAux, List.append_assoc]

/-- Functional and mutable-state translations agree for every integer list. -/
theorem functional_eq_imperative (numbers : List Int) :
    rolling_max numbers = rolling_max_imp numbers := by
  simpa [rolling_max_imp, rolling_max] using
    (rollingImperativeFrom_eq numbers none []).symm

end humaneval_9_rolling_max
end Agent
