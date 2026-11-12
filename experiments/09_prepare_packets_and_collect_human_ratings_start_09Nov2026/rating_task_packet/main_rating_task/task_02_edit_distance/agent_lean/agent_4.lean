import Mathlib

/-!
# Levenshtein edit distance

A translation of the Python string/list algorithm. The polymorphic core works with
any decidable element equality. `Input` retains the distinction between strings,
lists, and non-sequences; `Except.error` represents the Python `ValueError`.
Strings are decoded into Unicode characters, using an explicit character embedding
into the list element type. The concrete Python-facing adapter supports integers
and strings (including heterogeneous lists); the core is not restricted to them.

The functional implementation is Mathlib's dynamic program with unit insertion,
deletion and substitution costs. We prove the Python recurrence, metric laws,
length bounds, and minimum edit-script semantics. The imperative implementation
computes the same suffix table using mutable rows and nested loops. Processing
suffixes instead of prefixes and retaining only one row preserve the result.
-/

namespace EditDistance

deriving instance DecidableEq, BEq for Except

/-- Unit-cost Levenshtein distance on arbitrary sequences. -/
def distance {α : Type*} [DecidableEq α] (xs ys : List α) : Nat :=
  levenshtein Levenshtein.defaultCost xs ys

/-- All non-sequence Python values are represented by `invalid`. -/
inductive Input (α : Type*) where
  | str : String → Input α
  | list : List α → Input α
  | invalid : Input α
  deriving DecidableEq, Repr

/-- The embedding identifies a character with its corresponding list element. -/
def normalize {α : Type*} (ofChar : Char → α) : Input α → Option (List α)
  | .str s => some (s.toList.map ofChar)
  | .list xs => some xs
  | .invalid => none

def run {α : Type*} [DecidableEq α] (ofChar : Char → α)
    (s₁ s₂ : Input α) : Except String Nat :=
  match normalize ofChar s₁, normalize ofChar s₂ with
  | some xs, some ys => .ok (distance xs ys)
  | _, _ => .error "Inputs must be str or list"

inductive Atom where
  | integer : Int → Atom
  | text : String → Atom
  deriving DecidableEq, Repr

def atomChar (c : Char) : Atom := .text (String.singleton c)
def edit_distance : Input Atom → Input Atom → Except String Nat := run atomChar

def ints (xs : List Int) : Input Atom := .list (xs.map Atom.integer)
def chars (s : String) : Input Atom := .list (s.toList.map atomChar)

-- Unit tests: all examples from the Python test suite.
def stringCases : List (String × String × Nat) :=
  [("hello", "hello", 0), ("cat", "bat", 1), ("cat", "cats", 1),
   ("cats", "cat", 1), ("cat", "dog", 3), ("kitten", "sitting", 3),
   ("", "", 0), ("", "abc", 3), ("ab", "", 2), ("a", "b", 1),
   ("intention", "execution", 5), ("saturday", "sunday", 3),
   ("abc", "def", 3), ("xyz", "abc", 3), ("a", "a", 0),
   ("a", "b", 1), ("a", "", 1), ("", "a", 1),
   ("aaa", "aa", 1), ("aa", "aaa", 1), ("aaaa", "bbbb", 4)]

example : stringCases.all (fun (x, y, d) =>
    edit_distance (.str x) (.str y) == .ok d) = true := by native_decide
example : edit_distance (ints [1, 2, 3]) (ints [1, 2, 3]) = .ok 0 := by native_decide
example : edit_distance (ints [1, 2, 3]) (ints [1, 4, 3]) = .ok 1 := by native_decide
example : edit_distance (ints [1, 2, 3, 4]) (ints [1, 3, 4]) = .ok 1 := by native_decide
example : edit_distance (ints [1, 2, 3]) (ints [4, 5, 6]) = .ok 3 := by native_decide
example : edit_distance (ints [1, 2, 3, 4, 5]) (ints [6, 7, 8]) = .ok 5 := by native_decide
example : edit_distance (chars "hello") (chars "hello") = .ok 0 := by native_decide
example : edit_distance (chars "cat") (chars "bat") = .ok 1 := by native_decide
example : edit_distance (chars "cat") (chars "cats") = .ok 1 := by native_decide
example : edit_distance (chars "cats") (chars "cat") = .ok 1 := by native_decide
example : edit_distance .invalid (.str "abc") =
    .error "Inputs must be str or list" := by native_decide
example : edit_distance (.str "abc") .invalid =
    .error "Inputs must be str or list" := by native_decide
example : edit_distance .invalid .invalid =
    .error "Inputs must be str or list" := by native_decide
example : edit_distance (.str "cat") (chars "cat") = .ok 0 := by native_decide
example : edit_distance (.str "é🐈") (chars "é🐈") = .ok 0 := by native_decide
example : edit_distance (.list [.integer 1, .text "x"]) (.list [.text "1", .text "x"]) =
    .ok 1 := by native_decide
#eval edit_distance (.str "kitten") (.str "sitting")
#eval edit_distance .invalid (.str "abc")

/-- Exactly the Python precondition: each argument is a string or a list. -/
def Pre {α : Type*} (s₁ s₂ : Input α) : Prop :=
  (match s₁ with | .invalid => False | _ => True) ∧
  (match s₂ with | .invalid => False | _ => True)

section Properties
variable {α : Type*} [DecidableEq α]

@[simp] theorem distance_nil_left (ys : List α) : distance [] ys = ys.length := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    unfold distance at *
    rw [levenshtein_nil_cons]
    change 1 + levenshtein Levenshtein.defaultCost [] ys = ys.length + 1
    rw [ih]; omega

@[simp] theorem distance_nil_right (xs : List α) : distance xs [] = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change 1 + distance xs [] = xs.length + 1
    rw [ih]; omega

/-- The three edit choices, with zero substitution cost for equal elements. -/
theorem distance_cons (a b : α) (xs ys : List α) :
    distance (a :: xs) (b :: ys) =
      min (1 + distance xs (b :: ys))
        (min (1 + distance (a :: xs) ys)
          ((if a = b then 0 else 1) + distance xs ys)) := by
  exact levenshtein_cons_cons a xs b ys

def empty_prop (xs : List α) : Prop :=
  distance [] xs = xs.length ∧ distance xs [] = xs.length

theorem empty_thm (xs : List α) : empty_prop xs := by simp [empty_prop]

def symmetry_prop (xs ys : List α) : Prop := distance xs ys = distance ys xs

theorem symmetry_thm (xs ys : List α) : symmetry_prop xs ys := by
  unfold symmetry_prop
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    induction ys with
    | nil => simp
    | cons b ys jh =>
      rw [distance_cons, distance_cons, ih (b :: ys), ih ys, jh]
      simp only [eq_comm (a := a) (b := b)]
      omega

theorem distance_symm (xs ys : List α) : distance xs ys = distance ys xs :=
  symmetry_thm xs ys

/-- Inserting one leading element costs at most one. -/
theorem add_left_le (a : α) (xs ys : List α) :
    distance (a :: xs) ys ≤ 1 + distance xs ys := by
  cases ys with
  | nil => simp; omega
  | cons b ys => rw [distance_cons]; exact Nat.min_le_left _ _

theorem add_right_le (a : α) (xs ys : List α) :
    distance xs (a :: ys) ≤ 1 + distance xs ys := by
  rw [distance_symm xs (a :: ys), distance_symm xs ys]
  exact add_left_le a ys xs

/-- Removing one leading element also changes distance by at most one. -/
theorem remove_left_le (a : α) (xs ys : List α) :
    distance xs ys ≤ 1 + distance (a :: xs) ys := by
  induction ys with
  | nil => simp; omega
  | cons b ys ih =>
    have hi := add_right_le b xs ys
    rw [distance_cons]
    split_ifs <;> omega

theorem remove_right_le (a : α) (xs ys : List α) :
    distance xs ys ≤ 1 + distance xs (a :: ys) := by
  rw [distance_symm xs ys, distance_symm xs (a :: ys)]
  exact remove_left_le a ys xs

@[simp] theorem cancel_cons (a : α) (xs ys : List α) :
    distance (a :: xs) (a :: ys) = distance xs ys := by
  have h₁ := remove_right_le a xs ys
  have h₂ := remove_left_le a xs ys
  rw [distance_cons]
  simp only [ite_true, zero_add]
  omega

/-- Exactly the branch used by the Python DP for a nonempty pair. -/
def recurrence_prop (a b : α) (xs ys : List α) : Prop :=
  distance (a :: xs) (b :: ys) =
    if a = b then distance xs ys
    else 1 + min (distance xs (b :: ys))
      (min (distance (a :: xs) ys) (distance xs ys))

theorem recurrence_thm (a b : α) (xs ys : List α) : recurrence_prop a b xs ys := by
  unfold recurrence_prop
  by_cases h : a = b
  · subst b; simp
  · rw [distance_cons]
    simp only [if_neg h]
    omega

@[simp] theorem distance_self (xs : List α) : distance xs xs = 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simpa using ih

def zero_prop (xs ys : List α) : Prop := (distance xs ys = 0 ↔ xs = ys)

theorem zero_thm (xs ys : List α) : zero_prop xs ys := by
  unfold zero_prop
  constructor
  · induction xs generalizing ys with
    | nil => simp
    | cons a xs ih =>
      cases ys with
      | nil => simp
      | cons b ys =>
        rw [distance_cons]
        by_cases h : a = b
        · subst b
          simp only [ite_true, zero_add]
          intro hz
          have he : distance xs ys = 0 := by omega
          simp [ih ys he]
        · simp only [if_neg h]
          omega
  · intro h; subst ys; exact distance_self xs

/-- Both length-difference lower bounds and the sharp maximum-length upper bound. -/
def bounds_prop (xs ys : List α) : Prop :=
  xs.length ≤ ys.length + distance xs ys ∧
  ys.length ≤ xs.length + distance xs ys ∧
  distance xs ys ≤ max xs.length ys.length

theorem bounds_thm (xs ys : List α) : bounds_prop xs ys := by
  unfold bounds_prop
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    induction ys with
    | nil => simp
    | cons b ys jh =>
      have hd := ih (b :: ys)
      have hs := ih ys
      rw [distance_cons]
      simp only [List.length_cons] at *
      split_ifs <;> omega

/-- A monotone alignment, charging exactly one for each actual edit. -/
inductive Alignment : List α → List α → Nat → Prop where
  | nil : Alignment [] [] 0
  | keep (a : α) : Alignment xs ys n → Alignment (a :: xs) (a :: ys) n
  | delete (a : α) : Alignment xs ys n → Alignment (a :: xs) ys (1 + n)
  | insert (b : α) : Alignment xs ys n → Alignment xs (b :: ys) (1 + n)
  | substitute (a b : α) : Alignment xs ys n → Alignment (a :: xs) (b :: ys) (1 + n)

theorem substitute_le (a b : α) (xs ys : List α) :
    distance (a :: xs) (b :: ys) ≤ 1 + distance xs ys := by
  rw [distance_cons]
  split_ifs <;> omega

theorem alignment_lower {xs ys : List α} {n : Nat} (h : Alignment xs ys n) :
    distance xs ys ≤ n := by
  induction h with
  | nil => simp
  | keep a h ih => simpa using ih
  | delete a h ih => exact (add_left_le a _ _).trans (Nat.add_le_add_left ih 1)
  | insert b h ih => exact (add_right_le b _ _).trans (Nat.add_le_add_left ih 1)
  | substitute a b h ih => exact (substitute_le a b _ _).trans (Nat.add_le_add_left ih 1)

theorem alignment_exists (xs ys : List α) : Alignment xs ys (distance xs ys) := by
  induction xs generalizing ys with
  | nil =>
    induction ys with
    | nil => exact .nil
    | cons b ys ih => simpa [Nat.add_comm] using Alignment.insert b ih
  | cons a xs ih =>
    induction ys with
    | nil => simpa [Nat.add_comm] using Alignment.delete a (ih [])
    | cons b ys jh =>
      rw [distance_cons]
      rcases le_total (1 + distance xs (b :: ys))
          (min (1 + distance (a :: xs) ys) ((if a = b then 0 else 1) + distance xs ys)) with h | h
      · rw [min_eq_left h]; exact .delete a (ih (b :: ys))
      · rw [min_eq_right h]
        rcases le_total (1 + distance (a :: xs) ys)
            ((if a = b then 0 else 1) + distance xs ys) with h' | h'
        · rw [min_eq_left h']; exact .insert b jh
        · rw [min_eq_right h']
          by_cases hab : a = b
          · subst b; simpa using Alignment.keep a (ih ys)
          · simpa [hab] using Alignment.substitute a b (ih ys)

/-- A distance comparison is preserved by a common leading element. -/
theorem cons_comparison (a : α) (xs ys : List α) (n : Nat)
    (h : ∀ zs, distance xs zs ≤ n + distance ys zs) :
    ∀ zs, distance (a :: xs) zs ≤ n + distance (a :: ys) zs := by
  intro zs
  induction zs with
  | nil => have hh := h []; simp at *; omega
  | cons b zs ih =>
    have h₁ := h (b :: zs)
    have h₂ := h zs
    rw [distance_cons, distance_cons]
    split_ifs <;> omega

/-- Changing a single leading element changes the distance by at most one. -/
theorem substitute_left_le (a b : α) (xs zs : List α) :
    distance (a :: xs) zs ≤ 1 + distance (b :: xs) zs := by
  induction zs with
  | nil => simp
  | cons c zs ih =>
    rw [distance_cons, distance_cons]
    split_ifs <;> omega

theorem alignment_comparison {xs ys : List α} {n : Nat} (h : Alignment xs ys n) :
    ∀ zs, distance xs zs ≤ n + distance ys zs := by
  induction h with
  | nil => intro zs; simp
  | keep a h ih => exact cons_comparison a _ _ _ ih
  | @delete xs ys n a h ih =>
    intro zs
    have h₁ := add_left_le a xs zs
    have h₂ := ih zs
    omega
  | @insert xs ys n b h ih =>
    intro zs
    have h₁ := remove_left_le b ys zs
    have h₂ := ih zs
    omega
  | @substitute xs ys n a b h ih =>
    intro zs
    have h₁ := cons_comparison a xs ys n ih zs
    have h₂ := substitute_left_le a b ys zs
    omega

def triangle_prop (xs ys zs : List α) : Prop :=
  distance xs zs ≤ distance xs ys + distance ys zs

theorem triangle_thm (xs ys zs : List α) : triangle_prop xs ys zs :=
  alignment_comparison (alignment_exists xs ys) zs

/-- One insertion, deletion, or substitution at any position. -/
inductive Edit : List α → List α → Prop where
  | insert (front suffix : List α) (a : α) :
      Edit (front ++ suffix) (front ++ a :: suffix)
  | delete (front suffix : List α) (a : α) :
      Edit (front ++ a :: suffix) (front ++ suffix)
  | substitute (front suffix : List α) (a b : α) :
      Edit (front ++ a :: suffix) (front ++ b :: suffix)

/-- An arbitrary sequence of `n` single-element edits, including intermediate lists. -/
inductive Script : List α → List α → Nat → Prop where
  | done (xs : List α) : Script xs xs 0
  | step : Edit xs ys → Script ys zs n → Script xs zs (1 + n)

omit [DecidableEq α] in
theorem edit_cons (a : α) {xs ys : List α} (h : Edit xs ys) :
    Edit (a :: xs) (a :: ys) := by
  cases h with
  | insert p s b => exact Edit.insert (a :: p) s b
  | delete p s b => exact Edit.delete (a :: p) s b
  | substitute p s b c => exact Edit.substitute (a :: p) s b c

omit [DecidableEq α] in
theorem script_cons (a : α) {xs ys : List α} {n : Nat} (h : Script xs ys n) :
    Script (a :: xs) (a :: ys) n := by
  induction h with
  | done xs => exact .done _
  | step e h ih => exact .step (edit_cons a e) ih

omit [DecidableEq α] in
theorem script_append {xs ys zs : List α} {m n : Nat}
    (h₁ : Script xs ys m) (h₂ : Script ys zs n) : Script xs zs (m + n) := by
  induction h₁ with
  | done => simpa using h₂
  | step e h ih => simpa [Nat.add_assoc] using Script.step e (ih h₂)

omit [DecidableEq α] in
theorem alignment_script {xs ys : List α} {n : Nat} (h : Alignment xs ys n) :
    Script xs ys n := by
  induction h with
  | nil => exact .done []
  | keep a h ih => exact script_cons a ih
  | delete a h ih => exact .step (.delete [] _ a) ih
  | @insert xs ys n b h ih =>
    exact .step (.insert [] xs b) (script_cons b ih)
  | @substitute xs ys n a b h ih =>
    exact .step (.substitute [] xs a b) (script_cons b ih)

theorem prefix_comparison (front xs ys : List α) (n : Nat)
    (h : ∀ zs, distance xs zs ≤ n + distance ys zs) :
    ∀ zs, distance (front ++ xs) zs ≤ n + distance (front ++ ys) zs := by
  induction front with
  | nil => exact h
  | cons a front ih => exact cons_comparison a _ _ n ih

theorem edit_comparison {xs ys : List α} (h : Edit xs ys) (zs : List α) :
    distance xs zs ≤ 1 + distance ys zs := by
  cases h with
  | insert p s a => exact prefix_comparison p s (a :: s) 1 (remove_left_le a s) zs
  | delete p s a => exact prefix_comparison p (a :: s) s 1 (add_left_le a s) zs
  | substitute p s a b =>
    exact prefix_comparison p (a :: s) (b :: s) 1 (substitute_left_le a b s) zs

theorem script_lower {xs ys : List α} {n : Nat} (h : Script xs ys n) :
    distance xs ys ≤ n := by
  induction h with
  | done => simp
  | step e h ih => exact (edit_comparison e _).trans (Nat.add_le_add_left ih 1)

/-- The result is attained and is no greater than the cost of *any* edit script. -/
def minimum_prop (xs ys : List α) : Prop :=
  Script xs ys (distance xs ys) ∧ ∀ n, Script xs ys n → distance xs ys ≤ n

theorem minimum_thm (xs ys : List α) : minimum_prop xs ys :=
  ⟨alignment_script (alignment_exists xs ys), fun _ h => script_lower h⟩

omit [DecidableEq α] in
/-- Reversing an edit gives an edit at the reflected position. -/
theorem edit_reverse {xs ys : List α} (h : Edit xs ys) : Edit xs.reverse ys.reverse := by
  cases h with
  | insert p s a =>
    simpa [List.reverse_append, List.reverse_cons, List.append_assoc] using
      Edit.insert s.reverse p.reverse a
  | delete p s a =>
    simpa [List.reverse_append, List.reverse_cons, List.append_assoc] using
      Edit.delete s.reverse p.reverse a
  | substitute p s a b =>
    simpa [List.reverse_append, List.reverse_cons, List.append_assoc] using
      Edit.substitute s.reverse p.reverse a b

omit [DecidableEq α] in
theorem script_reverse {xs ys : List α} {n : Nat} (h : Script xs ys n) :
    Script xs.reverse ys.reverse n := by
  induction h with
  | done xs => exact .done _
  | step e h ih => exact .step (edit_reverse e) ih

def reverse_prop (xs ys : List α) : Prop :=
  distance xs.reverse ys.reverse = distance xs ys

theorem reverse_thm (xs ys : List α) : reverse_prop xs ys := by
  have h₁ := script_lower (script_reverse (alignment_script (alignment_exists xs ys)))
  have h₂ := script_lower
    (script_reverse (alignment_script (alignment_exists xs.reverse ys.reverse)))
  simp only [List.reverse_reverse] at h₂
  exact Nat.le_antisymm h₁ h₂

theorem distance_reverse (xs ys : List α) : distance xs.reverse ys.reverse = distance xs ys :=
  reverse_thm xs ys

/-- The recurrence on prefixes, in the orientation of the original Python table. -/
theorem snoc_recurrence (a b : α) (xs ys : List α) :
    distance (xs ++ [a]) (ys ++ [b]) =
      if a = b then distance xs ys else
        1 + min (distance xs (ys ++ [b]))
          (min (distance (xs ++ [a]) ys) (distance xs ys)) := by
  have h := recurrence_thm a b xs.reverse ys.reverse
  unfold recurrence_prop at h
  have hx : (xs ++ [a]).reverse = a :: xs.reverse := by simp
  have hy : (ys ++ [b]).reverse = b :: ys.reverse := by simp
  rw [← hx, ← hy] at h
  simpa only [distance_reverse] using h

/-- Every interior DP cell satisfies the indexed Python update. -/
def table_prop (xs ys : List α) : Prop :=
  ∀ (i j : Nat) (hi : i < xs.length) (hj : j < ys.length),
    distance (xs.take (i + 1)) (ys.take (j + 1)) =
      if xs[i] = ys[j] then distance (xs.take i) (ys.take j) else
        1 + min (distance (xs.take i) (ys.take (j + 1)))
          (min (distance (xs.take (i + 1)) (ys.take j)) (distance (xs.take i) (ys.take j)))

theorem table_thm (xs ys : List α) : table_prop xs ys := by
  intro i j hi hj
  rw [List.take_succ_eq_append_getElem hi, List.take_succ_eq_append_getElem hj]
  exact snoc_recurrence _ _ _ _

/-- Invalid arguments raise exactly the error specified by the source program. -/
def validation_prop (ofChar : Char → α) (s₁ s₂ : Input α) : Prop :=
  (run ofChar s₁ s₂ = .error "Inputs must be str or list" ↔ ¬ Pre s₁ s₂)

theorem validation_thm (ofChar : Char → α) (s₁ s₂ : Input α) :
    validation_prop ofChar s₁ s₂ := by
  cases s₁ <;> cases s₂ <;> simp [validation_prop, Pre, run, normalize]

/-- String-to-list conversion is uniform in either argument, including mixed inputs. -/
def conversion_prop (ofChar : Char → α) (s : String) (other : Input α) : Prop :=
  run ofChar (.str s) other = run ofChar (.list (s.toList.map ofChar)) other ∧
  run ofChar other (.str s) = run ofChar other (.list (s.toList.map ofChar))

theorem conversion_thm (ofChar : Char → α) (s : String) (other : Input α) :
    conversion_prop ofChar s other := ⟨rfl, rfl⟩

/-- A successful result, together with its semantic and quantitative guarantees. -/
def Post_prop (ofChar : Char → α) (s₁ s₂ : Input α) (result : Except String Nat) : Prop :=
  match normalize ofChar s₁, normalize ofChar s₂ with
  | some xs, some ys =>
      result = .ok (distance xs ys) ∧
      minimum_prop xs ys ∧ bounds_prop xs ys ∧ zero_prop xs ys ∧
      symmetry_prop xs ys ∧ empty_prop xs ∧ empty_prop ys ∧
      reverse_prop xs ys ∧ table_prop xs ys ∧
      (∀ zs, triangle_prop xs ys zs)
  | _, _ => False

end Properties

-- Property-based tests. `words alphabet n` exhausts all words of length at most n.
def words {α : Type*} (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => [] :: alphabet.flatMap (fun a => (words alphabet n).map (a :: ·))

def smallWords : List (List Nat) := words [0, 1] 3

-- PBT: empty_prop (all 15 binary words of length at most three).
example : smallWords.all (fun xs =>
    distance [] xs == xs.length && distance xs [] == xs.length) = true := by native_decide

-- PBT: symmetry_prop (all 225 pairs).
example : smallWords.all (fun xs => smallWords.all (fun ys =>
    distance xs ys == distance ys xs)) = true := by native_decide

-- PBT: recurrence_prop (both equal and unequal leading elements).
example : [0, 1].all (fun a => [0, 1].all (fun b =>
    smallWords.all (fun xs => smallWords.all (fun ys =>
      distance (a :: xs) (b :: ys) ==
        if a = b then distance xs ys else
          1 + min (distance xs (b :: ys))
            (min (distance (a :: xs) ys) (distance xs ys)))))) = true := by native_decide

-- PBT: zero_prop.
example : smallWords.all (fun xs => smallWords.all (fun ys =>
    (distance xs ys == 0) == (xs == ys))) = true := by native_decide

-- PBT: bounds_prop, testing both lower bounds and the maximum-length upper bound.
example : smallWords.all (fun xs => smallWords.all (fun ys =>
    decide (xs.length ≤ ys.length + distance xs ys) &&
    decide (ys.length ≤ xs.length + distance xs ys) &&
    decide (distance xs ys ≤ max xs.length ys.length))) = true := by native_decide

-- PBT: triangle_prop (all 3,375 triples).
example : smallWords.all (fun xs => smallWords.all (fun ys => smallWords.all (fun zs =>
    decide (distance xs zs ≤ distance xs ys + distance ys zs)))) = true := by native_decide

/-- An independent, exponential test oracle: enumerate every monotone alignment cost.
No minimum is taken while generating the candidates. -/
def alignmentCosts {α : Type*} [DecidableEq α] : List α → List α → List Nat
  | [], ys => [ys.length]
  | xs, [] => [xs.length]
  | a :: xs, b :: ys =>
      (alignmentCosts xs (b :: ys)).map (1 + ·) ++
      (alignmentCosts (a :: xs) ys).map (1 + ·) ++
      (alignmentCosts xs ys).map (1 + ·) ++
      (if a = b then alignmentCosts xs ys else [])
termination_by xs ys => xs.length + ys.length

/-- Test both existence of an optimal alignment and the lower bound on every candidate. -/
def minimumCheck {α : Type*} [DecidableEq α] (xs ys : List α) : Bool :=
  let costs := alignmentCosts xs ys
  costs.any (· == distance xs ys) && costs.all (fun n => decide (distance xs ys ≤ n))

-- PBT: minimum_prop quantifies over unbounded edit scripts, so it has no direct
-- Decidable instance. Its executable counterpart exhausts the alignment costs.
-- The proofs above relate alignments to arbitrary scripts, without bounding the theorem.
example : smallWords.all (fun xs => smallWords.all (fun ys =>
    minimumCheck xs ys)) = true := by native_decide

-- PBT: reverse_prop.
example : smallWords.all (fun xs => smallWords.all (fun ys =>
    distance xs.reverse ys.reverse == distance xs ys)) = true := by native_decide

/-- Check every interior table cell; `getD` is only used at indices inside `range length`. -/
def tableCheck {α : Type*} [DecidableEq α] [Inhabited α] (xs ys : List α) : Bool :=
  (List.range xs.length).all (fun i => (List.range ys.length).all (fun j =>
    distance (xs.take (i + 1)) (ys.take (j + 1)) ==
      if xs.getD i default = ys.getD j default then distance (xs.take i) (ys.take j) else
        1 + min (distance (xs.take i) (ys.take (j + 1)))
          (min (distance (xs.take (i + 1)) (ys.take j)) (distance (xs.take i) (ys.take j)))))

-- PBT: table_prop, including every admissible i,j in each bounded input pair.
example : smallWords.all (fun xs => smallWords.all (fun ys =>
    tableCheck xs ys)) = true := by native_decide

instance : Inhabited Atom := ⟨.integer 0⟩
def atomWords : List (List Atom) := words [.integer 0, .integer 1, .text "a", .text "é"] 2
def sampleStrings : List String := ["", "a", "b", "ab", "ba", "aa", "é", "🐈", "é🐈"]
def inputCases : List (Input Atom) :=
  .invalid :: (sampleStrings.map Input.str ++ atomWords.map Input.list)

def admissible {α : Type*} : Input α → Bool
  | .invalid => false
  | _ => true

-- PBT: validation_prop, including invalid inputs in either or both positions.
example : inputCases.all (fun s₁ => inputCases.all (fun s₂ =>
    (edit_distance s₁ s₂ == .error "Inputs must be str or list") ==
      !(admissible s₁ && admissible s₂))) = true := by native_decide

-- PBT: conversion_prop, including Unicode and mixed string/list calls.
example : sampleStrings.all (fun s => inputCases.all (fun other =>
    (edit_distance (.str s) other == edit_distance (chars s) other) &&
    (edit_distance other (.str s) == edit_distance other (chars s)))) = true := by native_decide

/-- The executable conjunction corresponding to Post_prop on the bounded corpus. -/
def postCheck (s₁ s₂ : Input Atom) : Bool :=
  match normalize atomChar s₁, normalize atomChar s₂ with
  | some xs, some ys =>
      let d := distance xs ys
      (edit_distance s₁ s₂ == .ok d) && minimumCheck xs ys &&
      decide (xs.length ≤ ys.length + d) && decide (ys.length ≤ xs.length + d) &&
      decide (d ≤ max xs.length ys.length) && ((d == 0) == (xs == ys)) &&
      (d == distance ys xs) && (distance [] xs == xs.length) &&
      (distance xs [] == xs.length) && (distance [] ys == ys.length) &&
      (distance ys [] == ys.length) && (distance xs.reverse ys.reverse == d) &&
      tableCheck xs ys && atomWords.all (fun zs => decide (distance xs zs ≤ d + distance ys zs))
  | _, _ => false

-- PBT: Post_prop under precisely Pre. The quantified triangle and minimum clauses
-- use the bounded executable counterparts above; the theorem keeps their full domains.
example : inputCases.all (fun s₁ => inputCases.all (fun s₂ =>
    !(admissible s₁ && admissible s₂) || postCheck s₁ s₂)) = true := by native_decide

-- Randomized PBTs also exercise arbitrary natural-number lists beyond the binary corpus.
#eval Plausible.Testable.check (∀ xs ys : List Nat,
  distance xs ys = distance ys xs ∧ (distance xs ys = 0 ↔ xs = ys))
#eval Plausible.Testable.check (∀ xs ys zs : List Nat,
  distance xs zs ≤ distance xs ys + distance ys zs)
#eval Plausible.Testable.check (∀ xs ys : List Nat,
  xs.length ≤ ys.length + distance xs ys ∧ ys.length ≤ xs.length + distance xs ys ∧
  distance xs ys ≤ max xs.length ys.length)

/-- Total correctness on exactly the source precondition. -/
theorem correctness_thm {α : Type*} [DecidableEq α] (ofChar : Char → α)
    (s₁ s₂ : Input α) : Pre s₁ s₂ → Post_prop ofChar s₁ s₂ (run ofChar s₁ s₂) := by
  intro h
  cases s₁ <;> cases s₂ <;> simp only [Pre] at h
  all_goals try contradiction
  all_goals
    exact ⟨rfl, minimum_thm _ _, bounds_thm _ _, zero_thm _ _, symmetry_thm _ _,
      empty_thm _, empty_thm _, reverse_thm _ _, table_thm _ _, triangle_thm _ _⟩

/-- Correctness specialized to the concrete Python-facing adapter. -/
theorem edit_distance_correct (s₁ s₂ : Input Atom) :
    Pre s₁ s₂ → Post_prop atomChar s₁ s₂ (edit_distance s₁ s₂) :=
  correctness_thm atomChar s₁ s₂

/-- A nonempty row; the proof permits safe access to its first and last cells. -/
abbrev Row := { r : List Nat // 0 < r.length }

/-- The inner DP loop. Cells contain an element and the two adjacent previous-row values. -/
def rowImperative {α : Type*} [DecidableEq α]
    (xs : List α) (b : α) (previous : Row) : Row := Id.run do
  let mut row : Row := ⟨[1 + previous.val.getLast (List.length_pos_iff.mp previous.property)], by simp⟩
  for cell in (xs.zip (previous.val.zip previous.val.tail)).reverse do
    let value := min (1 + row.val[0])
      (min (1 + cell.2.1) ((if cell.1 = b then 0 else 1) + cell.2.2))
    row := ⟨value :: row.val, by simp⟩
  return row

/-- Mutable initialization and outer loop, retaining one DP row at a time. -/
def distanceImperative {α : Type*} [DecidableEq α] (xs ys : List α) : Nat := Id.run do
  let mut row : Row := ⟨[0], by simp⟩
  for _ in xs.reverse do
    row := ⟨(1 + row.val[0]) :: row.val, by simp⟩
  for b in ys.reverse do
    row := rowImperative xs b row
  return row.val[0]

def runImperative {α : Type*} [DecidableEq α] (ofChar : Char → α)
    (s₁ s₂ : Input α) : Except String Nat := Id.run do
  let mut result : Except String Nat := .error "Inputs must be str or list"
  match normalize ofChar s₁, normalize ofChar s₂ with
  | some xs, some ys => result := .ok (distanceImperative xs ys)
  | _, _ => pure ()
  return result

def edit_distance_imperative : Input Atom → Input Atom → Except String Nat :=
  runImperative atomChar

-- Imperative unit tests and bounded comparison tests.
example : stringCases.all (fun (x, y, d) =>
    edit_distance_imperative (.str x) (.str y) == .ok d) = true := by native_decide
example : edit_distance_imperative (ints [1, 2, 3, 4, 5]) (ints [6, 7, 8]) = .ok 5 := by
  native_decide
example : edit_distance_imperative (chars "cat") (chars "cats") = .ok 1 := by native_decide
example : edit_distance_imperative .invalid (.str "abc") =
    .error "Inputs must be str or list" := by native_decide
example : smallWords.all (fun xs => smallWords.all (fun ys =>
    distance xs ys == distanceImperative xs ys)) = true := by native_decide
example : inputCases.all (fun s₁ => inputCases.all (fun s₂ =>
    edit_distance s₁ s₂ == edit_distance_imperative s₁ s₂)) = true := by native_decide
#eval edit_distance_imperative (.str "saturday") (.str "sunday")
#eval edit_distance_imperative .invalid (.str "abc")

/-- Each mutable inner loop equals the functional row transition. -/
theorem rowImperative_eq {α : Type*} [DecidableEq α] (xs : List α) (b : α) (r : Row) :
    rowImperative xs b r = Levenshtein.impl Levenshtein.defaultCost xs b r := by
  simp [rowImperative, Levenshtein.impl, Levenshtein.defaultCost, List.foldl_reverse]

/-- Equality of the functional and imperative algorithms for every element type and input. -/
theorem equivalence_thm {α : Type*} [DecidableEq α] (xs ys : List α) :
    distance xs ys = distanceImperative xs ys := by
  simp [distance, distanceImperative, rowImperative_eq, levenshtein, suffixLevenshtein,
    Levenshtein.defaultCost, List.foldl_reverse]

/-- The equivalence includes strings, lists, mixed inputs, and the error behavior. -/
theorem input_equivalence_thm {α : Type*} [DecidableEq α] (ofChar : Char → α)
    (s₁ s₂ : Input α) : run ofChar s₁ s₂ = runImperative ofChar s₁ s₂ := by
  cases s₁ <;> cases s₂ <;> simp [run, runImperative, normalize, equivalence_thm]

theorem edit_distance_equivalence (s₁ s₂ : Input Atom) :
    edit_distance s₁ s₂ = edit_distance_imperative s₁ s₂ :=
  input_equivalence_thm atomChar s₁ s₂

end EditDistance
