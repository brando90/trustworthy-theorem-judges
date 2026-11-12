import Mathlib

/-!
# Levenshtein edit distance

A polymorphic exact-natural-number model of the Python function. `Input` represents
strings, lists, and the rejected non-sequence case. The parameter `charValue`
interprets a one-character string in the element type; equality of elements is
provided by `DecidableEq`. This supports heterogeneous element universes as well
as ordinary lists. All non-sequence values have the same observable error and
are represented by `Input.invalid`.

The functional recurrence uses all three edit choices, with a zero-cost matching
choice. Below we prove the common-head optimization used by Python, optimality
among edit scripts, and equivalence with a mutable, bottom-up DP implementation.
-/

namespace edit_distance

deriving instance DecidableEq for Except

variable {α : Type} [DecidableEq α]

/-- The mathematical, functional implementation. -/
def distance : List α → List α → Nat
  | [], ys => ys.length
  | xs, [] => xs.length
  | a :: xs, b :: ys =>
      min (distance xs (b :: ys) + 1)
        (min (distance (a :: xs) ys + 1)
          (distance xs ys + if a = b then 0 else 1))
termination_by xs ys => xs.length + ys.length

inductive Input (α : Type) where
  | string : String → Input α
  | list : List α → Input α
  | invalid : Input α
  deriving DecidableEq, Repr

def Input.sequence (charValue : Char → α) : Input α → Option (List α)
  | .string s => some (s.toList.map charValue)
  | .list xs => some xs
  | .invalid => none

/-- `Except.error` models the Python `ValueError`. -/
def editDistance (charValue : Char → α) (a b : Input α) : Except String Nat :=
  match a.sequence charValue, b.sequence charValue with
  | some xs, some ys => .ok (distance xs ys)
  | _, _ => .error "Inputs must be str or list"

def stringDistance (s t : String) : Nat := distance s.toList t.toList

-- The public string examples (including the longer and repeated-character cases).
example : stringDistance "hello" "hello" = 0 := by native_decide
example : stringDistance "cat" "bat" = 1 := by native_decide
example : stringDistance "cat" "cats" = 1 := by native_decide
example : stringDistance "cats" "cat" = 1 := by native_decide
example : stringDistance "cat" "dog" = 3 := by native_decide
example : stringDistance "kitten" "sitting" = 3 := by native_decide
example : stringDistance "" "" = 0 := by native_decide
example : stringDistance "" "abc" = 3 := by native_decide
example : stringDistance "ab" "" = 2 := by native_decide
example : stringDistance "a" "b" = 1 := by native_decide
example : distance ([1,2,3] : List Int) [1,2,3] = 0 := by native_decide
example : distance ([1,2,3] : List Int) [1,4,3] = 1 := by native_decide
example : distance ([1,2,3,4] : List Int) [1,3,4] = 1 := by native_decide
example : distance ([1,2,3] : List Int) [4,5,6] = 3 := by native_decide
example : distance ([1,2,3,4,5] : List Int) [6,7,8] = 5 := by native_decide
example : distance ['h','e','l','l','o'] ['h','e','l','l','o'] = 0 := by native_decide
example : distance ['c','a','t'] ['b','a','t'] = 1 := by native_decide
example : distance ['c','a','t'] ['c','a','t','s'] = 1 := by native_decide
example : distance ['c','a','t','s'] ['c','a','t'] = 1 := by native_decide
example : stringDistance "intention" "execution" = 5 := by native_decide
example : stringDistance "saturday" "sunday" = 3 := by native_decide
example : stringDistance "abc" "def" = 3 := by native_decide
example : stringDistance "xyz" "abc" = 3 := by native_decide
example : stringDistance "a" "a" = 0 := by native_decide
example : stringDistance "a" "" = 1 := by native_decide
example : stringDistance "" "a" = 1 := by native_decide
example : stringDistance "aaa" "aa" = 1 := by native_decide
example : stringDistance "aa" "aaa" = 1 := by native_decide
example : stringDistance "aaaa" "bbbb" = 4 := by native_decide
example : editDistance id (.string "cat") (.list ['b','a','t']) = .ok 1 := by native_decide
example : editDistance id .invalid (.string "abc") = .error "Inputs must be str or list" := by native_decide
-- A canonical heterogeneous universe keeps characters distinct from integers.
example : editDistance (Sum.inl : Char → Char ⊕ Int)
    (.string "a") (.list [.inr 97]) = .ok 1 := by native_decide
example : editDistance (Sum.inl : Char → Char ⊕ Int)
    (.string "cat") (.list [.inl 'c', .inl 'a', .inl 't']) = .ok 0 := by native_decide
example : editDistance (Sum.inl : Char → Char ⊕ Int)
    (.list [.inr 1, .inr 2, .inr 3]) (.list [.inr 1, .inr 4, .inr 3]) = .ok 1 := by native_decide
#eval stringDistance "kitten" "sitting"
#eval editDistance id (.string "cat") (.string "cats")

/-- Exactly the Python type check; there are no restrictions on sequence contents. -/
def Pre (a b : Input α) : Prop := a ≠ .invalid ∧ b ≠ .invalid

@[simp] theorem distance_nil_left (ys : List α) : distance [] ys = ys.length := by
  rw [distance]

@[simp] theorem distance_nil_right (xs : List α) : distance xs [] = xs.length := by
  cases xs <;> simp [distance]

def empty_prop (xs : List α) : Prop :=
  distance [] xs = xs.length ∧ distance xs [] = xs.length

theorem empty_thm (xs : List α) : empty_prop xs := by
  simp [empty_prop]

def symmetry_prop (xs ys : List α) : Prop := distance xs ys = distance ys xs

theorem symmetry_thm (xs ys : List α) : symmetry_prop xs ys := by
  unfold symmetry_prop
  fun_induction distance xs ys with
  | case1 ys => simp
  | case2 a xs => simp
  | case3 a xs b ys ih1 ih2 ih3 =>
    simp only [distance.eq_3, ih1, ih2, ih3]
    by_cases h : a = b
    · subst b; simp [min_comm, min_left_comm]
    · simp [h, Ne.symm h, min_comm, min_left_comm]

/-- Deleting the first source element is always an available edit. -/
theorem delete_upper (a : α) (xs ys : List α) :
    distance (a :: xs) ys ≤ distance xs ys + 1 := by
  cases ys with
  | nil => simp
  | cons b ys => rw [distance]; exact min_le_left _ _

/-- Inserting the first target element is always an available edit. -/
theorem insert_upper (b : α) (xs ys : List α) :
    distance xs (b :: ys) ≤ distance xs ys + 1 := by
  rw [symmetry_thm xs (b :: ys), symmetry_thm xs ys]
  exact delete_upper b ys xs

/-- Removing a source head can increase distance by at most one. -/
theorem delete_lower (a : α) (xs ys : List α) :
    distance xs ys ≤ distance (a :: xs) ys + 1 := by
  induction ys with
  | nil => simp; omega
  | cons b ys ih =>
    have hi := insert_upper b xs ys
    rw [distance.eq_3]
    split_ifs <;> omega

theorem insert_lower (b : α) (xs ys : List α) :
    distance xs ys ≤ distance xs (b :: ys) + 1 := by
  rw [symmetry_thm xs (b :: ys), symmetry_thm xs ys]
  exact delete_lower b ys xs

@[simp] theorem same_cons (a : α) (xs ys : List α) :
    distance (a :: xs) (a :: ys) = distance xs ys := by
  have h₁ := delete_lower a xs ys
  have h₂ := insert_lower a xs ys
  rw [distance]
  simp only [ite_true, Nat.add_zero]
  omega

def recurrence_prop (a b : α) (xs ys : List α) : Prop :=
  distance (a :: xs) (b :: ys) =
    if a = b then distance xs ys else
      1 + min (distance xs (b :: ys)) (min (distance (a :: xs) ys) (distance xs ys))

theorem recurrence_thm (a b : α) (xs ys : List α) : recurrence_prop a b xs ys := by
  unfold recurrence_prop
  by_cases h : a = b
  · subst b; simp
  · rw [distance]; simp only [h, if_false]; omega


@[simp] theorem distance_self (xs : List α) : distance xs xs = 0 := by
  induction xs with
  | nil => simp
  | cons a xs ih => simpa using ih

def identity_prop (xs ys : List α) : Prop := distance xs ys = 0 ↔ xs = ys

theorem identity_thm (xs ys : List α) : identity_prop xs ys := by
  unfold identity_prop
  fun_induction distance xs ys with
  | case1 ys => simp
  | case2 a xs => simp
  | case3 a xs b ys ih1 ih2 ih3 =>
    by_cases h : a = b
    · subst b; simp [ih3, Nat.min_eq_zero_iff]
    · simp [h, Nat.min_eq_zero_iff]

def bounds_prop (xs ys : List α) : Prop :=
  distance xs ys ≤ max xs.length ys.length ∧
  xs.length ≤ ys.length + distance xs ys ∧
  ys.length ≤ xs.length + distance xs ys

theorem upper_bound (xs ys : List α) : distance xs ys ≤ max xs.length ys.length := by
  fun_induction distance xs ys with
  | case1 ys => simp
  | case2 a xs => simp
  | case3 a xs b ys ih1 ih2 ih3 =>
    simp only [List.length_cons]
    split_ifs <;> omega

theorem length_lower (xs ys : List α) : xs.length ≤ ys.length + distance xs ys := by
  fun_induction distance xs ys with
  | case1 ys => simp
  | case2 a xs => simp
  | case3 a xs b ys ih1 ih2 ih3 =>
    simp only [List.length_cons] at *
    split_ifs <;> omega

theorem bounds_thm (xs ys : List α) : bounds_prop xs ys := by
  refine ⟨upper_bound xs ys, length_lower xs ys, ?_⟩
  rw [symmetry_thm xs ys]
  exact length_lower ys xs

/-- A declarative, left-to-right edit script. `keep` costs zero; deletion,
insertion and substitution each cost one. This definition does not mention DP. -/
inductive Script : List α → List α → Nat → Prop
  | done : Script [] [] 0
  | delete {xs ys n} (a : α) : Script xs ys n → Script (a :: xs) ys (n + 1)
  | insert {xs ys n} (b : α) : Script xs ys n → Script xs (b :: ys) (n + 1)
  | keep {xs ys n} (a : α) : Script xs ys n → Script (a :: xs) (a :: ys) n
  | substitute {xs ys n} (a b : α) : Script xs ys n → Script (a :: xs) (b :: ys) (n + 1)

theorem substitute_upper (a b : α) (xs ys : List α) :
    distance (a :: xs) (b :: ys) ≤ distance xs ys + 1 := by
  rw [distance.eq_3]
  split_ifs <;> omega

/-- No edit script is cheaper than the computed result. -/
theorem script_lower {xs ys : List α} {n : Nat} (h : Script xs ys n) :
    distance xs ys ≤ n := by
  induction h with
  | done => simp
  | delete a h ih => exact le_trans (delete_upper _ _ _) (Nat.add_le_add_right ih 1)
  | insert b h ih => exact le_trans (insert_upper _ _ _) (Nat.add_le_add_right ih 1)
  | keep a h ih => simpa using ih
  | substitute a b h ih => exact le_trans (substitute_upper _ _ _ _) (Nat.add_le_add_right ih 1)

omit [DecidableEq α] in
theorem script_nil_left (ys : List α) : Script [] ys ys.length := by
  induction ys with
  | nil => exact .done
  | cons b ys ih => exact .insert b ih

omit [DecidableEq α] in
theorem script_nil_right (xs : List α) : Script xs [] xs.length := by
  induction xs with
  | nil => exact .done
  | cons a xs ih => exact .delete a ih

/-- The returned minimum is attained by an actual script. -/
theorem script_exists (xs ys : List α) : Script xs ys (distance xs ys) := by
  fun_induction distance xs ys with
  | case1 ys => simpa using script_nil_left ys
  | case2 xs h => simpa using script_nil_right xs
  | case3 a xs b ys ih1 ih2 ih3 =>
    by_cases hd : distance xs (b :: ys) + 1 ≤
        min (distance (a :: xs) ys + 1) (distance xs ys + if a = b then 0 else 1)
    · rw [min_eq_left hd]; exact .delete a ih1
    · rw [min_eq_right (le_of_not_ge hd)]
      by_cases hi : distance (a :: xs) ys + 1 ≤ distance xs ys + if a = b then 0 else 1
      · rw [min_eq_left hi]; exact .insert b ih2
      · rw [min_eq_right (le_of_not_ge hi)]
        by_cases hab : a = b
        · subst b; simpa using Script.keep a ih3
        · simp only [if_neg hab]; exact .substitute a b ih3

/-- A uniform distance bound is preserved by a shared source head. -/
theorem cons_transport (a : α) {xs ys : List α} {n : Nat}
    (h : ∀ zs, distance xs zs ≤ distance ys zs + n) :
    ∀ zs, distance (a :: xs) zs ≤ distance (a :: ys) zs + n := by
  intro zs
  induction zs with
  | nil =>
    have h₀ := h []
    simp only [distance_nil_right, List.length_cons] at *
    omega
  | cons b zs ih =>
    have h₁ := h (b :: zs)
    have h₂ := h zs
    simp only [distance.eq_3]
    split_ifs <;> omega

/-- Changing one source head changes distance to any target by at most one. -/
theorem substitute_transport (a b : α) (xs zs : List α) :
    distance (a :: xs) zs ≤ distance (b :: xs) zs + 1 := by
  induction zs with
  | nil => simp
  | cons c zs ih =>
    simp only [distance.eq_3]
    split_ifs <;> omega

theorem script_transport {xs ys : List α} {n : Nat} (h : Script xs ys n) :
    ∀ zs, distance xs zs ≤ distance ys zs + n := by
  induction h with
  | done => intro zs; simp
  | @delete xs ys n a h ih =>
    intro zs
    have h₁ := ih zs
    have h₂ := delete_upper a xs zs
    omega
  | @insert xs ys n b h ih =>
    intro zs
    have h₁ := ih zs
    have h₂ := delete_lower b ys zs
    omega
  | @keep xs ys n a h ih => exact cons_transport a ih
  | @substitute xs ys n a b h ih =>
    intro zs
    have h₁ := cons_transport a ih zs
    have h₂ := substitute_transport a b ys zs
    omega

def triangle_prop (xs ys zs : List α) : Prop :=
  distance xs zs ≤ distance xs ys + distance ys zs

theorem triangle_thm (xs ys zs : List α) : triangle_prop xs ys zs := by
  have h := script_transport (script_exists xs ys) zs
  unfold triangle_prop
  omega

theorem prefix_cancel (pref xs ys : List α) :
    distance (pref ++ xs) (pref ++ ys) = distance xs ys := by
  induction pref with
  | nil => rfl
  | cons a pref ih => simpa using ih

/-- A single edit at any position, not necessarily at the head. -/
inductive SingleEdit : List α → List α → Prop
  | delete (pref suff : List α) (a : α) :
      SingleEdit (pref ++ a :: suff) (pref ++ suff)
  | insert (pref suff : List α) (a : α) :
      SingleEdit (pref ++ suff) (pref ++ a :: suff)
  | substitute (pref suff : List α) (a b : α) :
      SingleEdit (pref ++ a :: suff) (pref ++ b :: suff)

/-- An unrestricted sequence of exactly `n` single-element edits. -/
inductive EditPath : List α → List α → Nat → Prop
  | refl (xs : List α) : EditPath xs xs 0
  | step {xs ys zs n} : SingleEdit xs ys → EditPath ys zs n → EditPath xs zs (n + 1)

omit [DecidableEq α] in
theorem singleEdit_prefix (pref : List α) {xs ys : List α} (h : SingleEdit xs ys) :
    SingleEdit (pref ++ xs) (pref ++ ys) := by
  cases h with
  | delete p s a => simpa only [List.append_assoc] using SingleEdit.delete (pref ++ p) s a
  | insert p s a => simpa only [List.append_assoc] using SingleEdit.insert (pref ++ p) s a
  | substitute p s a b =>
    simpa only [List.append_assoc] using SingleEdit.substitute (pref ++ p) s a b

omit [DecidableEq α] in
theorem path_prefix (pref : List α) {xs ys : List α} {n : Nat} (h : EditPath xs ys n) :
    EditPath (pref ++ xs) (pref ++ ys) n := by
  induction h with
  | refl xs => exact .refl _
  | step edit path ih => exact .step (singleEdit_prefix pref edit) ih

omit [DecidableEq α] in
theorem script_to_path {xs ys : List α} {n : Nat} (h : Script xs ys n) : EditPath xs ys n := by
  induction h with
  | done => exact .refl []
  | @delete xs ys n a h ih => exact .step (.delete [] xs a) ih
  | @insert xs ys n b h ih => exact .step (.insert [] xs b) (path_prefix [b] ih)
  | keep a h ih => exact path_prefix [a] ih
  | @substitute xs ys n a b h ih =>
    exact .step (.substitute [] xs a b) (path_prefix [b] ih)

theorem singleEdit_bound {xs ys : List α} (h : SingleEdit xs ys) : distance xs ys ≤ 1 := by
  cases h with
  | delete p s a => rw [prefix_cancel]; simpa using delete_upper a s s
  | insert p s a => rw [prefix_cancel]; simpa using insert_upper a s s
  | substitute p s a b => rw [prefix_cancel]; simpa using substitute_upper a b s s

/-- No unrestricted edit path is cheaper than the returned distance. -/
theorem path_lower {xs ys : List α} {n : Nat} (h : EditPath xs ys n) : distance xs ys ≤ n := by
  induction h with
  | refl xs => simp
  | @step xs ys zs n edit path ih =>
    have h₁ := singleEdit_bound edit
    have h₂ : distance xs zs ≤ distance xs ys + distance ys zs := triangle_thm xs ys zs
    omega

def optimal_prop (xs ys : List α) : Prop :=
  EditPath xs ys (distance xs ys) ∧ ∀ n, EditPath xs ys n → distance xs ys ≤ n

theorem optimal_thm (xs ys : List α) : optimal_prop xs ys := by
  exact ⟨script_to_path (script_exists xs ys), fun _ h => path_lower h⟩

def validation_prop (charValue : Char → α) (a b : Input α) : Prop :=
  editDistance charValue a b = .error "Inputs must be str or list" ↔ ¬ Pre a b

theorem validation_thm (charValue : Char → α) (a b : Input α) :
    validation_prop charValue a b := by
  cases a <;> cases b <;> simp [validation_prop, editDistance, Input.sequence, Pre]


/-- On admissible inputs the returned value is the optimal edit count, with the
zero characterization, symmetry, and sharp length bounds. -/
def Post_prop (charValue : Char → α) (a b : Input α) (result : Except String Nat) : Prop :=
  ∃ xs ys, a.sequence charValue = some xs ∧ b.sequence charValue = some ys ∧
    result = .ok (distance xs ys) ∧
    identity_prop xs ys ∧ symmetry_prop xs ys ∧ bounds_prop xs ys ∧ optimal_prop xs ys

/-! ## Exhaustive bounded property-based tests
These tests enumerate all binary lists of length at most three (15 lists, 225
pairs), not merely the examples above. The optimality test uses independent
enumeration of alignment costs. Its minimum is the executable counterpart of
the quantified, proof-valued `EditPath` specification. The proofs above show
that canonical minima are also unrestricted edit-path minima. Tests are not used in proofs.
-/

def smallLists : List (List Nat) :=
  let levels := (List.range 4).map fun n =>
    (List.finRange (2^n)).map fun k => (List.range n).map fun i => (k.val / 2^i) % 2
  levels.flatten

def pairsCheck (p : List Nat → List Nat → Bool) : Bool :=
  smallLists.all fun xs => smallLists.all fun ys => p xs ys

/-- Exhaustively enumerate costs of canonical alignments, independently of min. -/
def alignmentCosts : List α → List α → List Nat
  | [], ys => [ys.length]
  | xs, [] => [xs.length]
  | a :: xs, b :: ys =>
      ((alignmentCosts xs (b :: ys)).map (· + 1)) ++
      ((alignmentCosts (a :: xs) ys).map (· + 1)) ++
      ((alignmentCosts xs ys).map (· + if a = b then 0 else 1))
termination_by xs ys => xs.length + ys.length

def optimalCheck (xs ys : List α) : Bool :=
  let d := distance xs ys
  let costs := alignmentCosts xs ys
  costs.contains d && costs.all (fun n => d ≤ n)

-- PBT: empty_prop
example : smallLists.all (fun xs =>
    distance [] xs == xs.length && distance xs [] == xs.length) = true := by native_decide
-- PBT: symmetry_prop
example : pairsCheck (fun xs ys => distance xs ys == distance ys xs) = true := by native_decide
-- PBT: identity_prop
example : pairsCheck (fun xs ys => (distance xs ys == 0) == (xs == ys)) = true := by native_decide
-- PBT: bounds_prop (all three conjuncts)
example : pairsCheck (fun xs ys =>
    decide (distance xs ys ≤ max xs.length ys.length) &&
    decide (xs.length ≤ ys.length + distance xs ys) &&
    decide (ys.length ≤ xs.length + distance xs ys)) = true := by native_decide
-- PBT: recurrence_prop; both matching and mismatching heads are enumerated.
example : (List.range 3).all (fun a => (List.range 3).all (fun b =>
    pairsCheck (fun xs ys => distance (a :: xs) (b :: ys) ==
      if a = b then distance xs ys else
        1 + min (distance xs (b :: ys)) (min (distance (a :: xs) ys) (distance xs ys))))) = true := by
  native_decide
-- PBT: triangle_prop
example : smallLists.all (fun xs => smallLists.all (fun ys => smallLists.all (fun zs =>
    decide (distance xs zs ≤ distance xs ys + distance ys zs)))) = true := by native_decide
-- PBT: optimal_prop (finite exhaustive alignment search).
example : pairsCheck optimalCheck = true := by native_decide

/-- Include strings, lists, mixed pairs, and invalid inputs in wrapper PBTs. -/
def smallInputs : List (Input Nat) :=
  smallLists.map Input.list ++ [.string "", .string "aba", .string "bb", .invalid]

-- PBT: validation_prop, including both orders of an invalid argument.
example : smallInputs.all (fun a => smallInputs.all (fun b =>
    decide (editDistance Char.toNat a b = .error "Inputs must be str or list") ==
      (decide (a = .invalid) || decide (b = .invalid)))) = true := by native_decide

/-- Executable form of the post-condition, checked under precisely `Pre`. -/
def postCheck (charValue : Char → α) (a b : Input α) : Bool :=
  match a.sequence charValue, b.sequence charValue with
  | some xs, some ys =>
      decide (editDistance charValue a b = .ok (distance xs ys)) &&
      ((distance xs ys == 0) == (xs == ys)) &&
      (distance xs ys == distance ys xs) &&
      decide (distance xs ys ≤ max xs.length ys.length) &&
      decide (xs.length ≤ ys.length + distance xs ys) &&
      decide (ys.length ≤ xs.length + distance xs ys) && optimalCheck xs ys
  | _, _ => true -- the implication Pre → Post has a false premise

-- PBT: Post_prop, covering every executable conjunct and the optimality search.
example : smallInputs.all (fun a => smallInputs.all (postCheck Char.toNat a)) = true := by native_decide
#eval (smallLists.length, pairsCheck optimalCheck)
#eval smallInputs.all (fun a => smallInputs.all (postCheck Char.toNat a))

/-! ## Correctness on precisely the Python precondition -/
theorem correctness_thm (charValue : Char → α) (a b : Input α) :
    Pre a b → Post_prop charValue a b (editDistance charValue a b) := by
  intro h
  have valid : ∀ x : Input α, x ≠ .invalid → ∃ xs, x.sequence charValue = some xs := by
    intro x hx
    cases x with
    | string s => exact ⟨s.toList.map charValue, rfl⟩
    | list xs => exact ⟨xs, rfl⟩
    | invalid => exact (hx rfl).elim
  obtain ⟨xs, hx⟩ := valid a h.1
  obtain ⟨ys, hy⟩ := valid b h.2
  refine ⟨xs, ys, hx, hy, ?_, identity_thm xs ys, symmetry_thm xs ys,
    bounds_thm xs ys, optimal_thm xs ys⟩
  simp [editDistance, hx, hy]


/-! ## Imperative implementation

The DP is evaluated from the ends of the sequences. A row stores distances to
all target suffixes, so its last entry is the empty-target base case. Reversing
the iteration order gives exactly the deletion/insertion/diagonal dependencies
of Python's table. Only the previous and current rows are retained. With unit-cost element
comparisons this takes O((m+1)(n+1)) time and O(m+n) auxiliary storage,
including the reversed source traversal. No call to `distance` occurs in this implementation.
-/

/-- Initial row: the number of insertions for each target suffix. -/
def initialRow (ys : List α) : List Nat :=
  (List.range (ys.length + 1)).reverse

/-- Pair each target symbol with its deletion and diagonal entries. -/
def cells : List α → List Nat → List (α × Nat × Nat)
  | b :: ys, up :: diagonal :: rest =>
      (b, up, diagonal) :: cells ys (diagonal :: rest)
  | _, _ => []

def cellStep (a : α) (cell : α × Nat × Nat) (row : List Nat) : List Nat :=
  (if a = cell.1 then cell.2.2 else
    1 + min cell.2.1 (min (row.headD 0) cell.2.2)) :: row

/-- Mutable inner DP loop. -/
def nextRow (a : α) (base : Nat) (ys : List α) (previous : List Nat) : List Nat := Id.run do
  let mut row := [base]
  for cell in (cells ys previous).reverse do
    row := cellStep a cell row
  return row

def rowStep (ys : List α) (a : α) (state : Nat × List Nat) : Nat × List Nat :=
  (state.1 + 1, nextRow a (state.1 + 1) ys state.2)

/-- Mutable outer DP loop, maintaining the source length and the previous row. -/
def distanceImperative (xs ys : List α) : Nat := Id.run do
  let mut state := (0, initialRow ys)
  for a in xs.reverse do
    state := (state.1 + 1, nextRow a (state.1 + 1) ys state.2)
  return state.2.headD 0

def editDistanceImperative (charValue : Char → α) (a b : Input α) : Except String Nat := Id.run do
  match a.sequence charValue, b.sequence charValue with
  | some xs, some ys =>
      let mut result := 0
      result := distanceImperative xs ys
      return .ok result
  | _, _ => return .error "Inputs must be str or list"

-- Imperative tests: all public string cases, integer cases, and character lists.
def stringCases : List (String × String × Nat) :=
  [("hello","hello",0), ("cat","bat",1), ("cat","cats",1), ("cats","cat",1),
   ("cat","dog",3), ("kitten","sitting",3), ("","",0), ("","abc",3),
   ("ab","",2), ("a","b",1), ("intention","execution",5), ("saturday","sunday",3),
   ("abc","def",3), ("xyz","abc",3), ("a","a",0), ("a","",1), ("","a",1),
   ("aaa","aa",1), ("aa","aaa",1), ("aaaa","bbbb",4)]
example : stringCases.all (fun (s,t,n) => distanceImperative s.toList t.toList == n) = true := by
  native_decide
example : distanceImperative ([1,2,3] : List Int) [1,2,3] = 0 := by native_decide
example : distanceImperative ([1,2,3] : List Int) [1,4,3] = 1 := by native_decide
example : distanceImperative ([1,2,3,4] : List Int) [1,3,4] = 1 := by native_decide
example : distanceImperative ([1,2,3] : List Int) [4,5,6] = 3 := by native_decide
example : distanceImperative ([1,2,3,4,5] : List Int) [6,7,8] = 5 := by native_decide
example : distanceImperative ['h','e','l','l','o'] ['h','e','l','l','o'] = 0 := by native_decide
example : distanceImperative ['c','a','t'] ['b','a','t'] = 1 := by native_decide
example : distanceImperative ['c','a','t'] ['c','a','t','s'] = 1 := by native_decide
example : distanceImperative ['c','a','t','s'] ['c','a','t'] = 1 := by native_decide
example : editDistanceImperative id .invalid (.string "abc") =
    .error "Inputs must be str or list" := by native_decide
example : editDistanceImperative id (.string "abc") .invalid =
    .error "Inputs must be str or list" := by native_decide
example : editDistanceImperative id (.string "cat") (.list ['b','a','t']) = .ok 1 := by native_decide
example : pairsCheck (fun xs ys => distance xs ys == distanceImperative xs ys) = true := by native_decide
example : smallInputs.all (fun a => smallInputs.all (fun b =>
    decide (editDistance Char.toNat a b = editDistanceImperative Char.toNat a b))) = true := by
  native_decide
example : editDistanceImperative (Sum.inl : Char → Char ⊕ Int)
    (.string "a") (.list [.inr 97]) = .ok 1 := by native_decide
#eval distanceImperative "intention".toList "execution".toList
#eval editDistanceImperative id .invalid (.string "abc")

/-! ## Kernel-checked loop invariants and equivalence -/

private def runLoop {β γ : Type} (f : β → γ → β) (init : β) (xs : List γ) : β := Id.run do
  let mut state := init
  for x in xs do
    state := f state x
  return state

private theorem runLoop_eq {β γ : Type} (f : β → γ → β) (init : β) (xs : List γ) :
    runLoop f init xs = xs.foldl f init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih => simp [runLoop]

/-- The mathematical meaning of every entry of a DP row. -/
def specRow (xs : List α) : List α → List Nat
  | [] => [distance xs []]
  | b :: ys => distance xs (b :: ys) :: specRow xs ys

@[simp] theorem specRow_head (xs ys : List α) :
    (specRow xs ys).headD 0 = distance xs ys := by
  cases ys <;> rfl

theorem initialRow_spec (ys : List α) : initialRow ys = specRow ([] : List α) ys := by
  induction ys with
  | nil => simp [initialRow, specRow]
  | cons b ys ih =>
    simp only [initialRow, List.length_cons]
    rw [List.range_succ, List.reverse_append]
    change (ys.length + 1) :: initialRow ys =
      distance [] (b :: ys) :: specRow [] ys
    simp [ih]

theorem cells_spec_cons (xs ys : List α) (b : α) :
    cells (b :: ys) (specRow xs (b :: ys)) =
      (b, distance xs (b :: ys), distance xs ys) :: cells ys (specRow xs ys) := by
  cases ys <;> rfl

theorem nextRow_fold (a : α) (base : Nat) (ys : List α) (previous : List Nat) :
    nextRow a base ys previous = (cells ys previous).foldr (cellStep a) [base] := by
  change runLoop (fun row cell => cellStep a cell row) [base] (cells ys previous).reverse = _
  rw [runLoop_eq, List.foldl_reverse]

/-- Inner-loop invariant: extending the source updates every target-suffix cost. -/
theorem nextRow_spec (a : α) (xs ys : List α) :
    nextRow a (xs.length + 1) ys (specRow xs ys) = specRow (a :: xs) ys := by
  rw [nextRow_fold]
  induction ys with
  | nil => simp [cells, specRow]
  | cons b ys ih =>
    rw [cells_spec_cons, List.foldr_cons, ih]
    simp only [cellStep, specRow_head, specRow]
    exact congrArg (fun n => n :: specRow (a :: xs) ys) (recurrence_thm a b xs ys).symm

/-- Outer-loop invariant: after a suffix is consumed, the row and counter are exact. -/
theorem state_invariant (xs ys : List α) :
    xs.foldr (rowStep ys) (0, initialRow ys) = (xs.length, specRow xs ys) := by
  induction xs with
  | nil => simp [initialRow_spec]
  | cons a xs ih => simp [List.foldr_cons, ih, rowStep, nextRow_spec]

theorem distance_equivalence_thm (xs ys : List α) :
    distance xs ys = distanceImperative xs ys := by
  change distance xs ys =
    (runLoop (fun state a => rowStep ys a state) (0, initialRow ys) xs.reverse).2.headD 0
  rw [runLoop_eq, List.foldl_reverse, state_invariant, specRow_head]

/-- Functional and imperative translations agree on *all* inputs, including errors. -/
theorem equivalence_thm (charValue : Char → α) (a b : Input α) :
    editDistance charValue a b = editDistanceImperative charValue a b := by
  cases hx : a.sequence charValue <;> cases hy : b.sequence charValue <;>
    simp [editDistance, editDistanceImperative, hx, hy, distance_equivalence_thm]

end edit_distance
