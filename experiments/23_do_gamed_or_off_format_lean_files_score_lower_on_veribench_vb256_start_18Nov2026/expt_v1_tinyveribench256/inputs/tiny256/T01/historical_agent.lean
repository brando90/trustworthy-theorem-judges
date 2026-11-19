import Mathlib
namespace Agent

/-!
# HumanEval 20 — `find_closest_elements`

Given a list of numbers of length at least two, select the two entries (taken at two
*distinct positions*) whose difference has the smallest absolute value, and return them
ordered as `(smaller, larger)`.

The Python reference scans every ordered pair of distinct indices `(idx, idx2)` and keeps
the first pair achieving a strictly smaller distance than the current best, returning the
sorted version of that pair.

This file contains

* a functional implementation (`find_closest_elements`) that mirrors the Python fold,
* unit tests taken from the Python `check` function,
* the pre-condition (`Pre`), the individual specification properties with proofs, the
  post-condition (`Post_prop`) and the correctness theorem `Pre → Post`,
* an imperative implementation (`find_closest_elementsImp`) written with `Id.run do` and
  mutable state, mirroring the Python loops literally, together with a proof that it agrees
  with the functional one.

Real numbers are modelled by `ℚ`, which is a computable ordered field (so the unit tests can
be discharged by `native_decide` while the theorems remain provable).
-/

namespace humaneval_20_find_closest_elements

/-! ## Functional implementation -/

/-- The distance between the two components of a pair. -/
def pdist (p : ℚ × ℚ) : ℚ := |p.1 - p.2|

/-- One iteration of the Python loop body: keep `p` iff it is *strictly* closer than the
current best pair (and take it whenever there is no current best). -/
def closer (acc : Option (ℚ × ℚ)) (p : ℚ × ℚ) : Option (ℚ × ℚ) :=
  match acc with
  | none => some p
  | some q => if pdist p < pdist q then some p else some q

/-- All ordered pairs of entries sitting at two distinct indices, listed in the order in
which Python's nested `enumerate` loops visit them. -/
def pairs (numbers : List ℚ) : List (ℚ × ℚ) :=
  (List.range numbers.length).flatMap fun i =>
    (List.range numbers.length).flatMap fun j =>
      if i = j then [] else [(numbers[i]!, numbers[j]!)]

/-- The pair selected by the scan (`none` for lists of length `< 2`). -/
def best (numbers : List ℚ) : Option (ℚ × ℚ) := (pairs numbers).foldl closer none

/-- `find_closest_elements numbers` returns the two closest entries of `numbers`, ordered.
(The `(0, 0)` branch is unreachable under the pre-condition.) -/
def find_closest_elements (numbers : List ℚ) : ℚ × ℚ :=
  match best numbers with
  | none => (0, 0)
  | some p => (min p.1 p.2, max p.1 p.2)

/-! ## Unit tests (from the Python `check`) -/

#eval find_closest_elements [1.0, 2.0, 3.9, 4.0, 5.0, 2.2]
#eval find_closest_elements [1.1, 2.2, 3.1, 4.1, 5.1]

example : find_closest_elements [1.0, 2.0, 3.9, 4.0, 5.0, 2.2] = (3.9, 4.0) := by native_decide
example : find_closest_elements [1.0, 2.0, 5.9, 4.0, 5.0] = (5.0, 5.9) := by native_decide
example : find_closest_elements [1.0, 2.0, 3.0, 4.0, 5.0, 2.2] = (2.0, 2.2) := by native_decide
example : find_closest_elements [1.0, 2.0, 3.0, 4.0, 5.0, 2.0] = (2.0, 2.0) := by native_decide
example : find_closest_elements [1.1, 2.2, 3.1, 4.1, 5.1] = (2.2, 3.1) := by native_decide

/-! ## Pre-condition -/

/-- The Python docstring requires a list "of length at least two". -/
def Pre (numbers : List ℚ) : Prop := 2 ≤ numbers.length

/-! ## Auxiliary lemmas -/

theorem mem_pairs {numbers : List ℚ} {p : ℚ × ℚ} :
    p ∈ pairs numbers ↔ ∃ i j, i < numbers.length ∧ j < numbers.length ∧ i ≠ j ∧
      p = (numbers[i]!, numbers[j]!) := by
  constructor
  · intro h
    simp only [pairs, List.mem_flatMap, List.mem_range] at h
    obtain ⟨i, hi, j, hj, hmem⟩ := h
    by_cases hij : i = j
    · simp [hij] at hmem
    · simp only [hij, if_false] at hmem
      exact ⟨i, j, hi, hj, hij, by simpa using hmem⟩
  · rintro ⟨i, j, hi, hj, hij, rfl⟩
    simp only [pairs, List.mem_flatMap, List.mem_range]
    exact ⟨i, hi, j, hj, by simp [hij]⟩

theorem closer_spec (acc : Option (ℚ × ℚ)) (p : ℚ × ℚ) :
    ∃ s, closer acc p = some s ∧ pdist s ≤ pdist p ∧ (∀ q, acc = some q → pdist s ≤ pdist q) ∧
      (s = p ∨ acc = some s) := by
  cases acc with
  | none => exact ⟨p, rfl, le_refl _, by simp, Or.inl rfl⟩
  | some q =>
      by_cases h : pdist p < pdist q
      · refine ⟨p, by simp [closer, h], le_refl _, ?_, Or.inl rfl⟩
        intro q' hq'
        rw [Option.some_inj] at hq'
        subst hq'
        exact h.le
      · refine ⟨q, by simp [closer, h], not_lt.1 h, ?_, Or.inr rfl⟩
        intro q' hq'
        rw [Option.some_inj] at hq'
        subst hq'
        exact le_refl _

theorem foldl_closer_spec : ∀ (l : List (ℚ × ℚ)) (acc : Option (ℚ × ℚ)) (r : ℚ × ℚ),
    l.foldl closer acc = some r →
      (acc = some r ∨ r ∈ l) ∧ (∀ p ∈ l, pdist r ≤ pdist p) ∧
        (∀ q, acc = some q → pdist r ≤ pdist q) := by
  intro l
  induction l with
  | nil =>
      intro acc r h
      simp only [List.foldl_nil] at h
      refine ⟨Or.inl h, by simp, ?_⟩
      intro q hq
      rw [h, Option.some_inj] at hq
      subst hq
      exact le_refl _
  | cons a t ih =>
      intro acc r h
      rw [List.foldl_cons] at h
      obtain ⟨s, hs, hsa, hsq, hor⟩ := closer_spec acc a
      rw [hs] at h
      obtain ⟨h1, h2, h3⟩ := ih (some s) r h
      refine ⟨?_, ?_, ?_⟩
      · rcases h1 with h1 | h1
        · rw [Option.some_inj] at h1
          subst h1
          rcases hor with hr | hacc
          · exact Or.inr (by simp [hr])
          · exact Or.inl hacc
        · exact Or.inr (List.mem_cons_of_mem _ h1)
      · intro p hp
        rcases List.mem_cons.1 hp with hp | hp
        · subst hp
          exact le_trans (h3 s rfl) hsa
        · exact h2 p hp
      · intro q hq
        exact le_trans (h3 s rfl) (hsq q hq)

theorem foldl_closer_isSome : ∀ (l : List (ℚ × ℚ)) (q : ℚ × ℚ),
    ∃ r, l.foldl closer (some q) = some r := by
  intro l
  induction l with
  | nil => intro q; exact ⟨q, rfl⟩
  | cons a t ih =>
      intro q
      rw [List.foldl_cons]
      obtain ⟨s, hs, -, -, -⟩ := closer_spec (some q) a
      rw [hs]
      exact ih s

theorem best_isSome (numbers : List ℚ) (h : Pre numbers) : ∃ r, best numbers = some r := by
  have h2 : 2 ≤ numbers.length := h
  have hne : pairs numbers ≠ [] := by
    intro hnil
    have hmem : ((numbers[0]!, numbers[1]!) : ℚ × ℚ) ∈ pairs numbers :=
      mem_pairs.2 ⟨0, 1, by omega, by omega, by omega, rfl⟩
    rw [hnil] at hmem
    simp at hmem
  obtain ⟨a, t, hat⟩ := List.exists_cons_of_ne_nil hne
  show ∃ r, (pairs numbers).foldl closer none = some r
  rw [hat, List.foldl_cons]
  exact foldl_closer_isSome t a

/-- Everything the scan guarantees: it returns a pair sitting at two distinct positions of
the list, and no other such pair is closer. -/
theorem best_spec (numbers : List ℚ) (h : Pre numbers) :
    ∃ i j, i < numbers.length ∧ j < numbers.length ∧ i ≠ j ∧
      best numbers = some (numbers[i]!, numbers[j]!) ∧
      ∀ k l, k < numbers.length → l < numbers.length → k ≠ l →
        |numbers[i]! - numbers[j]!| ≤ |numbers[k]! - numbers[l]!| := by
  obtain ⟨r, hr⟩ := best_isSome numbers h
  obtain ⟨h1, h2, -⟩ := foldl_closer_spec (pairs numbers) none r hr
  have hmem : r ∈ pairs numbers := by
    rcases h1 with h1 | h1
    · exact absurd h1.symm (by simp)
    · exact h1
  obtain ⟨i, j, hi, hj, hij, hrij⟩ := mem_pairs.1 hmem
  refine ⟨i, j, hi, hj, hij, by rw [hr, hrij], ?_⟩
  intro k l hk hl hkl
  have hp : ((numbers[k]!, numbers[l]!) : ℚ × ℚ) ∈ pairs numbers :=
    mem_pairs.2 ⟨k, l, hk, hl, hkl, rfl⟩
  have := h2 _ hp
  simpa [pdist, hrij] using this

/-! ## Specification properties -/

/-- The two returned numbers are returned in order: `(smaller, larger)`. -/
def ordered_prop (numbers : List ℚ) : Prop :=
  (find_closest_elements numbers).1 ≤ (find_closest_elements numbers).2

theorem ordered_thm (numbers : List ℚ) : ordered_prop numbers := by
  unfold ordered_prop find_closest_elements
  cases best numbers with
  | none => exact le_refl _
  | some p => exact min_le_max

/-- Both returned numbers are elements of the input list. -/
def mem_prop (numbers : List ℚ) : Prop :=
  (find_closest_elements numbers).1 ∈ numbers ∧ (find_closest_elements numbers).2 ∈ numbers

theorem mem_thm (numbers : List ℚ) (h : Pre numbers) : mem_prop numbers := by
  obtain ⟨i, j, hi, hj, -, hbest, -⟩ := best_spec numbers h
  have hai : numbers[i]! ∈ numbers := by
    rw [getElem!_pos numbers i hi]; exact List.getElem_mem hi
  have haj : numbers[j]! ∈ numbers := by
    rw [getElem!_pos numbers j hj]; exact List.getElem_mem hj
  unfold mem_prop find_closest_elements
  rw [hbest]
  constructor
  · show min numbers[i]! numbers[j]! ∈ numbers
    rcases min_choice numbers[i]! numbers[j]! with hm | hm <;> rw [hm] <;> assumption
  · show max numbers[i]! numbers[j]! ∈ numbers
    rcases max_choice numbers[i]! numbers[j]! with hm | hm <;> rw [hm] <;> assumption

/-- The returned pair really comes from two *distinct positions* of the list (so that, e.g.,
`[2.0, 2.0]` may legitimately return `(2.0, 2.0)`). -/
def witness_prop (numbers : List ℚ) : Prop :=
  ∃ i j, i < numbers.length ∧ j < numbers.length ∧ i ≠ j ∧
    (find_closest_elements numbers).1 = numbers[i]! ∧ (find_closest_elements numbers).2 = numbers[j]!

theorem witness_thm (numbers : List ℚ) (h : Pre numbers) : witness_prop numbers := by
  obtain ⟨i, j, hi, hj, hij, hbest, -⟩ := best_spec numbers h
  unfold witness_prop find_closest_elements
  rw [hbest]
  rcases le_total numbers[i]! numbers[j]! with hle | hle
  · refine ⟨i, j, hi, hj, hij, ?_, ?_⟩
    · show min numbers[i]! numbers[j]! = numbers[i]!
      exact min_eq_left hle
    · show max numbers[i]! numbers[j]! = numbers[j]!
      exact max_eq_right hle
  · refine ⟨j, i, hj, hi, hij.symm, ?_, ?_⟩
    · show min numbers[i]! numbers[j]! = numbers[j]!
      exact min_eq_right hle
    · show max numbers[i]! numbers[j]! = numbers[i]!
      exact max_eq_left hle

/-- No pair of entries at distinct positions is closer than the returned one. -/
def minimal_prop (numbers : List ℚ) : Prop :=
  ∀ i j, i < numbers.length → j < numbers.length → i ≠ j →
    (find_closest_elements numbers).2 - (find_closest_elements numbers).1 ≤
      |numbers[i]! - numbers[j]!|

theorem minimal_thm (numbers : List ℚ) (h : Pre numbers) : minimal_prop numbers := by
  obtain ⟨i, j, hi, hj, -, hbest, hmin⟩ := best_spec numbers h
  intro k l hk hl hkl
  have hgoal : (find_closest_elements numbers).2 - (find_closest_elements numbers).1
      = |numbers[i]! - numbers[j]!| := by
    unfold find_closest_elements
    rw [hbest]
    exact max_sub_min_eq_abs' numbers[i]! numbers[j]!
  rw [hgoal]
  exact hmin k l hk hl hkl

/-! ## Post-condition and correctness -/

/-- The full post-condition: the answer is an ordered pair of entries of the list taken at
two distinct positions, and it minimises the distance among all such pairs. -/
def Post_prop (numbers : List ℚ) : Prop :=
  ordered_prop numbers ∧ mem_prop numbers ∧ witness_prop numbers ∧ minimal_prop numbers

theorem correctness (numbers : List ℚ) (h : Pre numbers) : Post_prop numbers :=
  ⟨ordered_thm numbers, mem_thm numbers h, witness_thm numbers h, minimal_thm numbers h⟩

/-! ## Imperative implementation -/

/-- The imperative loop body, acting on the pair of mutable variables
`(closest_pair, distance)`. -/
def closerI (acc : MProd (Option (ℚ × ℚ)) (Option ℚ)) (p : ℚ × ℚ) :
    MProd (Option (ℚ × ℚ)) (Option ℚ) :=
  match acc.2 with
  | none => ⟨some p, some (pdist p)⟩
  | some d0 => if pdist p < d0 then ⟨some p, some (pdist p)⟩ else acc

/-- A literal transcription of the Python function: two nested loops over the indices, two
mutable variables `closest_pair` and `distance`. -/
def find_closest_elementsImp (numbers : List ℚ) : ℚ × ℚ := Id.run do
  let n := numbers.length
  let mut closest_pair : Option (ℚ × ℚ) := none
  let mut distance : Option ℚ := none
  for i in List.range n do
    for j in List.range n do
      if i ≠ j then
        let d := |numbers[i]! - numbers[j]!|
        match distance with
        | none =>
            distance := some d
            closest_pair := some (numbers[i]!, numbers[j]!)
        | some d0 =>
            if d < d0 then
              distance := some d
              closest_pair := some (numbers[i]!, numbers[j]!)
  match closest_pair with
  | none => return (0, 0)
  | some p => return (min p.1 p.2, max p.1 p.2)

#eval find_closest_elementsImp [1.0, 2.0, 3.9, 4.0, 5.0, 2.2]
#eval find_closest_elementsImp [1.1, 2.2, 3.1, 4.1, 5.1]

example : find_closest_elementsImp [1.0, 2.0, 3.9, 4.0, 5.0, 2.2] = (3.9, 4.0) := by native_decide
example : find_closest_elementsImp [1.0, 2.0, 5.9, 4.0, 5.0] = (5.0, 5.9) := by native_decide
example : find_closest_elementsImp [1.0, 2.0, 3.0, 4.0, 5.0, 2.2] = (2.0, 2.2) := by native_decide
example : find_closest_elementsImp [1.0, 2.0, 3.0, 4.0, 5.0, 2.0] = (2.0, 2.0) := by native_decide
example : find_closest_elementsImp [1.1, 2.2, 3.1, 4.1, 5.1] = (2.2, 3.1) := by native_decide

/-! ## Equivalence of the two implementations -/

theorem Id_pure {α : Type} (a : α) : (pure a : Id α) = a := rfl

theorem Id_bind {α β : Type} (x : Id α) (f : α → Id β) : (x >>= f) = f x := rfl

/-- A `for` loop in `Id` whose body always `yield`s is a `foldl`. -/
theorem Id_forIn_of {α β : Type} (l : List α) (init : β) (body : α → β → ForInStep β)
    (g : α → β → β) (h : ∀ a b, body a b = ForInStep.yield (g a b)) :
    (forIn (m := Id) l init body) = l.foldl (fun r a => g a r) init := by
  induction l generalizing init with
  | nil => rfl
  | cons a t ih => rw [List.forIn_cons, h a init]; exact ih _

theorem foldl_flatMap {α β γ : Type} (l : List α) (f : α → List β) (g : γ → β → γ) (init : γ) :
    (l.flatMap f).foldl g init = l.foldl (fun acc a => (f a).foldl g acc) init := by
  induction l generalizing init with
  | nil => rfl
  | cons a t ih => simp [List.flatMap_cons, List.foldl_append, ih]

/-- The imperative state keeps `distance` in sync with the distance of `closest_pair`, so its
first component follows the functional fold. -/
theorem foldl_closerI : ∀ (l : List (ℚ × ℚ)) (acc : MProd (Option (ℚ × ℚ)) (Option ℚ)),
    acc.2 = acc.1.map pdist →
      (l.foldl closerI acc).1 = l.foldl closer acc.1 ∧
        (l.foldl closerI acc).2 = ((l.foldl closerI acc).1).map pdist := by
  intro l
  induction l with
  | nil => intro acc h; exact ⟨rfl, h⟩
  | cons a t ih =>
      intro acc h
      rw [List.foldl_cons, List.foldl_cons]
      have hstep : (closerI acc a).1 = closer acc.1 a ∧ (closerI acc a).2 = (closer acc.1 a).map pdist := by
        obtain ⟨cp, d⟩ := acc
        cases cp with
        | none =>
            simp only [Option.map_none] at h
            subst h
            exact ⟨rfl, rfl⟩
        | some q =>
            simp only [Option.map_some] at h
            subst h
            by_cases hd : pdist a < pdist q <;> simp [closerI, closer, hd]
      obtain ⟨hs1, hs2⟩ := hstep
      have := ih (closerI acc a) (by rw [hs1, hs2])
      rw [hs1] at this
      exact this

theorem loop_eq (numbers : List ℚ) :
    ((List.range numbers.length).foldl
        (fun r i => (List.range numbers.length).foldl
          (fun r j => if i = j then r else closerI r (numbers[i]!, numbers[j]!)) r)
        (⟨none, none⟩ : MProd (Option (ℚ × ℚ)) (Option ℚ))).1 = best numbers := by
  have key : (pairs numbers).foldl closerI (⟨none, none⟩ : MProd (Option (ℚ × ℚ)) (Option ℚ))
      = (List.range numbers.length).foldl
          (fun r i => (List.range numbers.length).foldl
            (fun r j => if i = j then r else closerI r (numbers[i]!, numbers[j]!)) r)
          (⟨none, none⟩ : MProd (Option (ℚ × ℚ)) (Option ℚ)) := by
    unfold pairs
    rw [foldl_flatMap]
    congr 1
    funext acc i
    rw [foldl_flatMap]
    congr 1
    funext acc' j
    by_cases hij : i = j <;> simp [hij]
  rw [← key]
  exact (foldl_closerI (pairs numbers) ⟨none, none⟩ rfl).1

theorem find_closest_elementsImp_eq (numbers : List ℚ) :
    find_closest_elementsImp numbers = find_closest_elements numbers := by
  unfold find_closest_elementsImp
  simp only [Id.run, Id_pure, Id_bind]
  rw [Id_forIn_of (g := fun i r => (List.range numbers.length).foldl (fun r j =>
        if i = j then r else closerI r (numbers[i]!, numbers[j]!)) r)]
  · rw [loop_eq]
    rfl
  · intro i r
    congr 1
    rw [Id_forIn_of (g := fun j r => if i = j then r else closerI r (numbers[i]!, numbers[j]!))]
    intro j r
    obtain ⟨cp, d⟩ := r
    by_cases hij : i = j
    · simp [hij]
    · simp only [ne_eq, if_pos hij, if_neg hij, closerI, pdist]
      cases d with
      | none => rfl
      | some d0 => dsimp only; split <;> rfl

end humaneval_20_find_closest_elements
end Agent
