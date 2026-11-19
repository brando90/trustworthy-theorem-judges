import Mathlib
namespace Agent

/-!
# Longest substring without repeated characters

Strings are lists of Unicode characters, as in Python's iteration over `str`.
This functional translation replaces the last-position dictionary optimization
by finite enumeration of contiguous substrings. It preserves the observable
result, including the empty string. `Input` and `ValueError` explicitly model
the dynamically checked input boundary; the typed string entry point cannot
receive a non-string. The specification below states both attainability and
optimality, not just numerical bounds.
-/

namespace LongestSubstring

/-- All contiguous substrings, including the empty substring. -/
def substrings (xs : List Char) : List (List Char) :=
  xs.tails.flatMap List.inits

/-- Maximum length among repetition-free candidates. -/
def best : List (List Char) → Nat
  | [] => 0
  | xs :: rest => max (if xs.Nodup then xs.length else 0) (best rest)

/-- Functional, exact finite-search translation. -/
def lengthOfLongestSubstring (s : String) : Nat :=
  best (substrings s.toList)

def verifyUniqueChars (s : String) : Bool := decide s.toList.Nodup

inductive Input where
  | string (s : String)
  | nonString
  deriving DecidableEq, Repr

/-- Executable Python-style type test. -/
def pre : Input → Bool
  | .string _ => true
  | .nonString => false

inductive ValueError where
  | inputMustBeAString
  deriving DecidableEq, Repr

deriving instance DecidableEq for Except

def checked (x : Input) : Except ValueError Nat :=
  match x with
  | .string s => .ok (lengthOfLongestSubstring s)
  | .nonString => .error .inputMustBeAString

/-- The three assertions of Python's public `check`, including the exception. -/
def check (candidate : Input → Except ValueError Nat) : Bool :=
  decide (candidate (.string "abcabcbb") = .ok 3) &&
  decide (candidate (.string "") = .ok 0) &&
  decide (candidate .nonString = .error .inputMustBeAString)

example : check checked = true := by native_decide
#eval check checked

example : lengthOfLongestSubstring "abcabcbb" = 3 := by native_decide
example : lengthOfLongestSubstring "bbbbb" = 1 := by native_decide
example : lengthOfLongestSubstring "pwwkew" = 3 := by native_decide
example : lengthOfLongestSubstring "" = 0 := by native_decide
example : lengthOfLongestSubstring " " = 1 := by native_decide
example : lengthOfLongestSubstring "au" = 2 := by native_decide
example : lengthOfLongestSubstring "aab" = 2 := by native_decide
example : lengthOfLongestSubstring "dvdf" = 3 := by native_decide
example : lengthOfLongestSubstring "αβγα" = 3 := by native_decide
example : checked .nonString = .error .inputMustBeAString := by native_decide
example : verifyUniqueChars "abc" = true := by native_decide
example : verifyUniqueChars "aba" = false := by native_decide
#eval lengthOfLongestSubstring "abcabcbb"
#eval checked .nonString

/-- Exactly the Python precondition; `nonString` represents any non-`str` object. -/
def Pre : Input → Prop
  | .string _ => True
  | .nonString => False

/-! ## Enumeration and maximum lemmas -/

theorem mem_substrings (t xs : List Char) :
    t ∈ substrings xs ↔ t <:+: xs := by
  simp only [substrings, List.mem_flatMap, List.mem_tails, List.mem_inits,
    List.infix_iff_prefix_suffix]
  constructor
  · rintro ⟨u, hu, ht⟩
    exact ⟨u, ht, hu⟩
  · rintro ⟨u, ht, hu⟩
    exact ⟨u, hu, ht⟩

theorem length_le_best {t : List Char} {cs : List (List Char)}
    (hm : t ∈ cs) (hu : t.Nodup) : t.length ≤ best cs := by
  induction cs with
  | nil => simp at hm
  | cons u us ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · simp only [best, if_pos hu]
      exact Nat.le_max_left _ _
    · exact (ih hm).trans (Nat.le_max_right _ _)

theorem best_zero_or_attained (cs : List (List Char)) :
    best cs = 0 ∨ ∃ t ∈ cs, t.Nodup ∧ t.length = best cs := by
  induction cs with
  | nil => exact Or.inl rfl
  | cons t ts ih =>
    by_cases h : t.Nodup ∧ best ts ≤ t.length
    · right
      refine ⟨t, by simp, h.1, ?_⟩
      simp [best, h.1, Nat.max_eq_left h.2]
    · have he : best (t :: ts) = best ts := by
        simp only [best]
        by_cases hu : t.Nodup
        · rw [if_pos hu, Nat.max_eq_right]
          exact Nat.le_of_lt (Nat.lt_of_not_ge (fun hb => h ⟨hu, hb⟩))
        · simp [hu]
      rcases ih with hz | ⟨u, hm, hu, hl⟩
      · exact Or.inl (he.trans hz)
      · exact Or.inr ⟨u, List.mem_cons_of_mem _ hm, hu, hl.trans he.symm⟩

theorem longest_attained (s : String) :
    ∃ t : List Char, t <:+: s.toList ∧ t.Nodup ∧
      t.length = lengthOfLongestSubstring s := by
  rcases best_zero_or_attained (substrings s.toList) with hz | ⟨t, hm, hu, hl⟩
  · exact ⟨[], List.nil_infix, List.nodup_nil, hz.symm⟩
  · exact ⟨t, (mem_substrings _ _).mp hm, hu, hl⟩

/-! ## Properties -/

/-- The answer is a feasible substring length and dominates every feasible length. -/
def optimal_prop (s : String) (n : Nat) : Prop :=
  (∃ t : List Char, t <:+: s.toList ∧ t.Nodup ∧ t.length = n) ∧
  (∀ t : List Char, t <:+: s.toList → t.Nodup → t.length ≤ n)

theorem optimal_thm (s : String) : optimal_prop s (lengthOfLongestSubstring s) := by
  refine ⟨longest_attained s, ?_⟩
  intro t hi hu
  exact length_le_best ((mem_substrings _ _).mpr hi) hu

/-- In particular, the result lies between zero and the number of characters. -/
def bounds_prop (s : String) (n : Nat) : Prop := 0 ≤ n ∧ n ≤ s.toList.length

theorem bounds_thm (s : String) : bounds_prop s (lengthOfLongestSubstring s) := by
  obtain ⟨t, hi, _, hl⟩ := longest_attained s
  exact ⟨Nat.zero_le _, hl ▸ hi.length_le⟩

def empty_prop (s : String) (n : Nat) : Prop := s = "" → n = 0

theorem empty_thm (s : String) : empty_prop s (lengthOfLongestSubstring s) := by
  intro hs
  subst s
  rfl

/-- A nonempty string always has a repetition-free singleton substring. -/
def zero_prop (s : String) (n : Nat) : Prop := n = 0 ↔ s = ""

theorem zero_thm (s : String) : zero_prop s (lengthOfLongestSubstring s) := by
  constructor
  · intro hz
    have hb := (optimal_thm s).2
    cases hs : s.toList with
    | nil => exact String.toList_inj.mp (by simpa using hs)
    | cons c cs =>
      have hi : [c] <:+: s.toList := by
        rw [hs]
        exact ⟨[], cs, rfl⟩
      have hp := hb [c] hi (by simp)
      simp [hz] at hp
  · exact empty_thm s

/-- The whole string is a longest admissible substring exactly when it is unique. -/
def full_length_prop (s : String) (n : Nat) : Prop :=
  n = s.toList.length ↔ s.toList.Nodup

theorem full_length_thm (s : String) :
    full_length_prop s (lengthOfLongestSubstring s) := by
  constructor
  · intro he
    obtain ⟨t, hi, hu, hl⟩ := longest_attained s
    have ht : t = s.toList := hi.eq_of_length (hl.trans he)
    simpa [ht] using hu
  · intro hu
    apply Nat.le_antisymm (bounds_thm s).2
    exact (optimal_thm s).2 s.toList (List.infix_refl _) hu

/-- `dedup.length` is Python's `len(set(s))`. -/
def verify_prop (s : String) : Prop :=
  verifyUniqueChars s = true ↔ s.toList.length = s.toList.dedup.length

theorem verify_thm (s : String) : verify_prop s := by
  change decide s.toList.Nodup = true ↔ _
  rw [decide_eq_true_eq]
  constructor
  · intro hu
    rw [List.dedup_eq_self.mpr hu]
  · intro he
    exact List.dedup_eq_self.mp ((List.dedup_sublist _).eq_of_length he.symm)

/-- Every non-string value raises the modeled ValueError, rather than returning zero. -/
def invalid_prop (x : Input) : Prop :=
  ¬ Pre x → checked x = .error .inputMustBeAString

theorem invalid_thm (x : Input) : invalid_prop x := by
  cases x <;> simp [invalid_prop, Pre, checked]

/-- A conjunction covering the successful result and the exceptional boundary. -/
def Post_prop (x : Input) (r : Except ValueError Nat) : Prop :=
  (∀ s, x = .string s → ∃ n, r = .ok n ∧
    optimal_prop s n ∧ bounds_prop s n ∧ empty_prop s n ∧
    zero_prop s n ∧ full_length_prop s n ∧ verify_prop s) ∧
  (¬ Pre x → r = .error .inputMustBeAString)

/-! ## Property-based tests

The bounded corpus contains **all** 1,365 strings of lengths 0 through 5 over
`a`, `b`, space, and `α`. This includes empty, all-equal, all-unique, and repeated
window-boundary cases. `mem_substrings` justifies using finite candidate checks
for the existential and universal quantifiers in `optimal_prop`.
-/

def wordsUpTo : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 => [] :: ['a', 'b', ' ', 'α'].flatMap
      (fun c => (wordsUpTo n).map (fun w => c :: w))

def testStrings : List String := (wordsUpTo 5).map String.mk

def testInputs : List Input := .nonString :: testStrings.map Input.string

def optimalCheck (s : String) (n : Nat) : Bool :=
  (substrings s.toList).any (fun t => decide t.Nodup && decide (t.length = n)) &&
  (substrings s.toList).all (fun t => !decide t.Nodup || decide (t.length ≤ n))

def boundsCheck (s : String) (n : Nat) : Bool :=
  decide (0 ≤ n ∧ n ≤ s.toList.length)

def emptyCheck (s : String) (n : Nat) : Bool := decide (s = "" → n = 0)

def zeroCheck (s : String) (n : Nat) : Bool := decide (n = 0 ↔ s = "")

def fullLengthCheck (s : String) (n : Nat) : Bool :=
  decide (n = s.toList.length ↔ s.toList.Nodup)

def verifyCheck (s : String) : Bool :=
  decide (verifyUniqueChars s = true ↔ s.toList.length = s.toList.dedup.length)

def invalidCheck (x : Input) : Bool :=
  pre x || decide (checked x = .error .inputMustBeAString)

def postCheck (x : Input) (r : Except ValueError Nat) : Bool :=
  match x, r with
  | .string s, .ok n =>
    optimalCheck s n && boundsCheck s n && emptyCheck s n &&
    zeroCheck s n && fullLengthCheck s n && verifyCheck s
  | .nonString, .error .inputMustBeAString => true
  | _, _ => false

-- PBT for optimal_prop: attainment AND domination of every unique substring.
example : testStrings.all (fun s => optimalCheck s (lengthOfLongestSubstring s)) = true := by
  native_decide
-- PBT for bounds_prop.
example : testStrings.all (fun s => boundsCheck s (lengthOfLongestSubstring s)) = true := by
  native_decide
-- PBT for empty_prop (the empty input is included, so this is not wholly vacuous).
example : testStrings.all (fun s => emptyCheck s (lengthOfLongestSubstring s)) = true := by
  native_decide
-- PBT for zero_prop.
example : testStrings.all (fun s => zeroCheck s (lengthOfLongestSubstring s)) = true := by
  native_decide
-- PBT for full_length_prop.
example : testStrings.all (fun s => fullLengthCheck s (lengthOfLongestSubstring s)) = true := by
  native_decide
-- PBT for verify_prop, including both Boolean outcomes.
example : testStrings.all verifyCheck = true := by native_decide
-- PBT for invalid_prop; includes the non-string input class.
example : testInputs.all invalidCheck = true := by native_decide
-- PBT for Post_prop, on both the normal and exceptional paths.
example : testInputs.all (fun x => postCheck x (checked x)) = true := by native_decide
#eval (testStrings.length, testInputs.all (fun x => postCheck x (checked x)))

/-! ## Correctness -/

theorem pre_thm (x : Input) : pre x = true ↔ Pre x := by
  cases x <;> simp [pre, Pre]

/-- The checked implementation satisfies the entire postcondition, even for invalid inputs. -/
theorem post_thm (x : Input) : Post_prop x (checked x) := by
  constructor
  · intro s hx
    subst x
    exact ⟨lengthOfLongestSubstring s, rfl, optimal_thm s, bounds_thm s,
      empty_thm s, zero_thm s, full_length_thm s, verify_thm s⟩
  · exact invalid_thm x

/-- The requested Hoare-style correctness implication, with exactly Python's Pre. -/
theorem correctness_thm (x : Input) : Pre x → Post_prop x (checked x) := by
  intro _
  exact post_thm x

/-- The optimality specification determines a unique numerical answer. -/
theorem optimal_unique {s : String} {m n : Nat}
    (hm : optimal_prop s m) (hn : optimal_prop s n) : m = n := by
  obtain ⟨u, hui, hun, hul⟩ := hm.1
  obtain ⟨v, hvi, hvn, hvl⟩ := hn.1
  apply Nat.le_antisymm
  · simpa [hul] using hn.2 u hui hun
  · simpa [hvl] using hm.2 v hvi hvn

/-! ## Imperative implementation

The loop maintains the maximum length seen so far. Unlike the functional
right-recursive maximum, this is a mutable left-to-right scan. The dictionary
optimization of the Python source is not needed for semantic equivalence.
-/

def bestImperative (cs : List (List Char)) (initial : Nat) : Nat := Id.run do
  let mut maxLen := initial
  for t in cs do
    if t.Nodup then
      maxLen := max maxLen t.length
  return maxLen

def lengthOfLongestSubstringImperative (s : String) : Nat :=
  bestImperative (substrings s.toList) 0

def checkedImperative (x : Input) : Except ValueError Nat :=
  match x with
  | .string s => .ok (lengthOfLongestSubstringImperative s)
  | .nonString => .error .inputMustBeAString

example : check checkedImperative = true := by native_decide
example : lengthOfLongestSubstringImperative "abcabcbb" = 3 := by native_decide
example : lengthOfLongestSubstringImperative "bbbbb" = 1 := by native_decide
example : lengthOfLongestSubstringImperative "pwwkew" = 3 := by native_decide
example : lengthOfLongestSubstringImperative "" = 0 := by native_decide
example : lengthOfLongestSubstringImperative " " = 1 := by native_decide
example : lengthOfLongestSubstringImperative "au" = 2 := by native_decide
example : lengthOfLongestSubstringImperative "aab" = 2 := by native_decide
example : lengthOfLongestSubstringImperative "dvdf" = 3 := by native_decide
example : lengthOfLongestSubstringImperative "αβγα" = 3 := by native_decide
example : checkedImperative .nonString = .error .inputMustBeAString := by native_decide
example : testInputs.all (fun x => decide (checked x = checkedImperative x)) = true := by
  native_decide
#eval lengthOfLongestSubstringImperative "pwwkew"
#eval check checkedImperative

/-! ## Equivalence proofs -/

theorem bestImperative_cons (t : List Char) (ts : List (List Char)) (initial : Nat) :
    bestImperative (t :: ts) initial =
      bestImperative ts (if t.Nodup then max initial t.length else initial) := by
  by_cases hu : t.Nodup <;> simp [bestImperative, hu]

/-- The loop invariant includes an arbitrary previous maximum. -/
theorem bestImperative_eq (cs : List (List Char)) (initial : Nat) :
    bestImperative cs initial = max initial (best cs) := by
  induction cs generalizing initial with
  | nil => simp [bestImperative, best]
  | cons t ts ih =>
    rw [bestImperative_cons]
    by_cases hu : t.Nodup <;> simp [best, hu, ih, Nat.max_assoc]

theorem equivalence_thm (s : String) :
    lengthOfLongestSubstring s = lengthOfLongestSubstringImperative s := by
  simp [lengthOfLongestSubstring, lengthOfLongestSubstringImperative, bestImperative_eq]

/-- Equivalence also preserves the exceptional result on every non-string. -/
theorem checked_equivalence_thm (x : Input) : checked x = checkedImperative x := by
  cases x <;> simp [checked, checkedImperative, equivalence_thm]

theorem imperative_correctness_thm (x : Input) :
    Pre x → Post_prop x (checkedImperative x) := by
  rw [← checked_equivalence_thm]
  exact correctness_thm x

end LongestSubstring
end Agent
