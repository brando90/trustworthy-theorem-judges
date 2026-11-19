import Mathlib
namespace Agent

/-!
# Longest common subsequence

The core works on reversed character lists: removing a head then means removing
one character from the end of a Python prefix. On unequal characters it chooses
`up` when the lengths tie, exactly as in the source program. Reversing the answer
restores the original order. Characters are compared case-sensitively.

`Input` below distinguishes strings from non-strings, and the checked interface
models Python's ValueError. The untagged interface is the total string function.
-/

namespace LongestCommonSubsequence

/-- LCS in reverse order, with the Python program's deterministic tie rule. -/
def lcsRev : List Char → List Char → List Char
  | [], _ => []
  | _, [] => []
  | a :: xs, b :: ys =>
      if a = b then a :: lcsRev xs ys
      else
        let up := lcsRev xs (b :: ys)
        let left := lcsRev (a :: xs) ys
        if left.length ≤ up.length then up else left
termination_by xs ys => xs.length + ys.length

def longest_common_subsequence (s1 s2 : String) : String :=
  String.mk (lcsRev s1.toList.reverse s2.toList.reverse).reverse

/-- The two-pointer greedy scan, expressed by consuming list heads. -/
def verifyList : List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: xs, b :: ys =>
      if a = b then verifyList xs ys else verifyList (a :: xs) ys
termination_by _ ys => ys.length

/-- Executable, case-sensitive subsequence verification. -/
def verify_subsequence (sub sup : String) : Bool :=
  verifyList sub.toList sup.toList

/-- All non-string Python values have the same behavior at this interface. -/
inductive Input where
  | string : String → Input
  | nonString : Input
  deriving DecidableEq, Repr

/-- Python's `isinstance(s1, str) and isinstance(s2, str)`. -/
def pre : Input → Input → Bool
  | .string _, .string _ => true
  | _, _ => false

inductive ValueError where
  | inputsMustBeStrings
  deriving DecidableEq, Repr

def ValueError.message (_ : ValueError) : String := "Inputs must be strings"

deriving instance DecidableEq for Except

def checkedLCS : Input → Input → Except ValueError String
  | .string a, .string b => .ok (longest_common_subsequence a b)
  | _, _ => .error .inputsMustBeStrings

/-- Boolean pass/fail version of the Python public `check` assertions. -/
def check (candidate : Input → Input → Except ValueError String) : Bool :=
  decide (candidate (.string "abcde") (.string "ace") = .ok "ace") &&
  decide (candidate (.string "") (.string "") = .ok "") &&
  decide (candidate .nonString (.string "abc") = .error .inputsMustBeStrings)

example : check checkedLCS = true := by native_decide
example : pre (.string "") (.string "abc") = true := by native_decide
example : pre .nonString (.string "abc") = false := by native_decide
example : ValueError.inputsMustBeStrings.message = "Inputs must be strings" := by native_decide
example : verify_subsequence "ace" "abcde" = true := by native_decide
example : verify_subsequence "ca" "abc" = false := by native_decide
example : verify_subsequence "" "" = true := by native_decide
example : verify_subsequence "a" "" = false := by native_decide
example : verify_subsequence "h" "Hello" = false := by native_decide
#eval check checkedLCS

example : longest_common_subsequence "abcde" "ace" = "ace" := by native_decide
example : longest_common_subsequence "abc" "abc" = "abc" := by native_decide
example : longest_common_subsequence "abc" "def" = "" := by native_decide
example : longest_common_subsequence "" "" = "" := by native_decide
example : longest_common_subsequence "ABCDGH" "AEDFHR" = "ADH" := by native_decide
example : longest_common_subsequence "AGGTAB" "GXTXAYB" = "GTAB" := by native_decide
example : longest_common_subsequence "Hello" "HELLO" = "H" := by native_decide
example : longest_common_subsequence "ab" "ba" = "a" := by native_decide
example : checkedLCS .nonString (.string "abc") = .error .inputsMustBeStrings := by native_decide
#eval longest_common_subsequence "abcde" "ace"
#eval checkedLCS .nonString (.string "abc")

/-- Precisely the Python precondition: both arguments are strings. -/
def Pre (a b : Input) : Prop :=
  (∃ s, a = .string s) ∧ (∃ t, b = .string t)

def pre_prop (a b : Input) : Prop := pre a b = true ↔ Pre a b

theorem pre_thm (a b : Input) : pre_prop a b := by
  cases a <;> cases b <;> simp [pre_prop, pre, Pre]

/-- Greedy matching is equivalent to the order-preserving sublist relation. -/
theorem verifyList_correct (xs ys : List Char) :
    verifyList xs ys = true ↔ xs.Sublist ys := by
  induction ys generalizing xs with
  | nil => cases xs <;> simp [verifyList]
  | cons b ys ih =>
    cases xs with
    | nil => simp [verifyList]
    | cons a xs =>
      by_cases hab : a = b
      · subst b
        simp [verifyList, ih]
      · simp [verifyList, hab, ih, List.sublist_cons_iff]

/-- Mathematical specification: common and maximum-length, not merely maximal. -/
def IsLCS (xs ys result : List Char) : Prop :=
  result.Sublist xs ∧ result.Sublist ys ∧
    ∀ z : List Char, z.Sublist xs → z.Sublist ys → z.length ≤ result.length

/-- Every recurrence branch preserves commonness and global optimality. -/
theorem lcsRev_spec (xs ys : List Char) : IsLCS xs ys (lcsRev xs ys) := by
  cases xs with
  | nil => simp [lcsRev, IsLCS]
  | cons a xs =>
    cases ys with
    | nil => simp [lcsRev, IsLCS]
    | cons b ys =>
      by_cases hab : a = b
      · subst b
        have ih := lcsRev_spec xs ys
        rw [lcsRev, if_pos rfl]
        refine ⟨ih.1.cons₂ a, ih.2.1.cons₂ a, ?_⟩
        intro z hx hy
        cases z with
        | nil => simp
        | cons c zs =>
          by_cases hca : c = a
          · subst c
            exact Nat.succ_le_succ
              (ih.2.2 zs (List.cons_sublist_cons.mp hx) (List.cons_sublist_cons.mp hy))
          · have hx' : (c :: zs).Sublist xs := by
              rcases List.sublist_cons_iff.mp hx with h | ⟨r, hr, _⟩
              · exact h
              · exact (hca (List.cons.inj hr).1).elim
            have hy' : (c :: zs).Sublist ys := by
              rcases List.sublist_cons_iff.mp hy with h | ⟨r, hr, _⟩
              · exact h
              · exact (hca (List.cons.inj hr).1).elim
            exact le_trans (ih.2.2 _ hx' hy') (by simp)
      · have hu := lcsRev_spec xs (b :: ys)
        have hl := lcsRev_spec (a :: xs) ys
        have bound : ∀ z : List Char, z.Sublist (a :: xs) → z.Sublist (b :: ys) →
            z.length ≤ max (lcsRev xs (b :: ys)).length (lcsRev (a :: xs) ys).length := by
          intro z hx hy
          rcases List.sublist_cons_iff.mp hx with hx' | ⟨r, rfl, hr⟩
          · exact le_trans (hu.2.2 z hx' hy) (Nat.le_max_left _ _)
          · have hy' : (a :: r).Sublist ys := by
              rcases List.sublist_cons_iff.mp hy with h | ⟨t, ht, _⟩
              · exact h
              · exact (hab (List.cons.inj ht).1).elim
            exact le_trans (hl.2.2 _ hx hy') (Nat.le_max_right _ _)
        rw [lcsRev, if_neg hab]
        dsimp only
        split_ifs with hlen
        · refine ⟨hu.1.cons a, hu.2.1, ?_⟩
          intro z hx hy
          simpa only [Nat.max_eq_left hlen] using bound z hx hy
        · refine ⟨hl.1, hl.2.1.cons b, ?_⟩
          intro z hx hy
          have hle : (lcsRev xs (b :: ys)).length ≤ (lcsRev (a :: xs) ys).length := by omega
          simpa only [Nat.max_eq_right hle] using bound z hx hy
termination_by xs.length + ys.length

/-- Reversal transfers the list specification to the original input order. -/
theorem string_spec (a b : String) :
    IsLCS a.toList b.toList (longest_common_subsequence a b).toList := by
  have h := lcsRev_spec a.toList.reverse b.toList.reverse
  refine ⟨?_, ?_, ?_⟩
  · simpa [longest_common_subsequence] using h.1.reverse
  · simpa [longest_common_subsequence] using h.2.1.reverse
  · intro z hx hy
    have hz := h.2.2 z.reverse hx.reverse hy.reverse
    simpa [longest_common_subsequence] using hz

def common_prop (a b result : String) : Prop :=
  result.toList.Sublist a.toList ∧ result.toList.Sublist b.toList

theorem common_thm (a b : String) : common_prop a b (longest_common_subsequence a b) :=
  ⟨(string_spec a b).1, (string_spec a b).2.1⟩

def optimal_prop (a b result : String) : Prop :=
  ∀ candidate : String, candidate.toList.Sublist a.toList →
    candidate.toList.Sublist b.toList → candidate.length ≤ result.length

theorem optimal_thm (a b : String) : optimal_prop a b (longest_common_subsequence a b) := by
  intro candidate ha hb
  exact (string_spec a b).2.2 candidate.toList ha hb

def length_bound_prop (a b result : String) : Prop :=
  result.length ≤ min a.length b.length

theorem length_bound_thm (a b : String) :
    length_bound_prop a b (longest_common_subsequence a b) := by
  exact le_min (string_spec a b).1.length_le (string_spec a b).2.1.length_le

def empty_prop (a b result : String) : Prop :=
  (a = "" ∨ b = "") → result = ""

theorem empty_thm (a b : String) : empty_prop a b (longest_common_subsequence a b) := by
  intro h
  rcases h with rfl | rfl
  · apply String.ext
    exact List.sublist_nil.mp (string_spec "" b).1
  · apply String.ext
    exact List.sublist_nil.mp (string_spec a "").2.1

def identity_prop (a b result : String) : Prop :=
  a = b → result = a

theorem identity_thm (a b : String) : identity_prop a b (longest_common_subsequence a b) := by
  intro h
  subst b
  apply String.ext
  exact (string_spec a a).1.eq_of_length_le
    ((string_spec a a).2.2 a.toList (List.Sublist.refl _) (List.Sublist.refl _))

def disjoint_prop (a b result : String) : Prop :=
  (∀ c ∈ a.toList, c ∉ b.toList) → result = ""

theorem disjoint_thm (a b : String) : disjoint_prop a b (longest_common_subsequence a b) := by
  intro h
  apply String.ext
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro c hc
  exact h c ((string_spec a b).1.subset hc) ((string_spec a b).2.1.subset hc)

/-- Exposes the exact diagonal / up-on-ties / left reconstruction rule. -/
def recurrence_prop (xs ys : List Char) : Prop :=
  lcsRev xs ys = match xs, ys with
    | [], _ => []
    | _, [] => []
    | a :: as, b :: bs =>
      if a = b then a :: lcsRev as bs
      else if (lcsRev (a :: as) bs).length ≤ (lcsRev as (b :: bs)).length
        then lcsRev as (b :: bs) else lcsRev (a :: as) bs

theorem recurrence_thm (xs ys : List Char) : recurrence_prop xs ys := by
  cases xs <;> cases ys <;> simp [recurrence_prop, lcsRev]

def verification_prop (sub sup : String) : Prop :=
  verify_subsequence sub sup = true ↔ sub.toList.Sublist sup.toList

theorem verification_thm (sub sup : String) : verification_prop sub sup := by
  simp [verification_prop, verify_subsequence, verifyList_correct]

def rejection_prop (a b : Input) : Prop :=
  ¬ Pre a b → checkedLCS a b = .error .inputsMustBeStrings

theorem rejection_thm (a b : Input) : rejection_prop a b := by
  cases a <;> cases b <;> simp [rejection_prop, Pre, checkedLCS]

/-- Success entails all semantic properties; a precondition violation raises ValueError. -/
def Post_prop (a b : Input) (result : Except ValueError String) : Prop :=
  (∀ s t : String, a = .string s → b = .string t →
    ∃ r : String, result = .ok r ∧
      common_prop s t r ∧ optimal_prop s t r ∧ length_bound_prop s t r ∧
      empty_prop s t r ∧ identity_prop s t r ∧ disjoint_prop s t r) ∧
  (¬ Pre a b → result = .error .inputsMustBeStrings)

/-! ## Property-based tests

The corpus contains *every* word of length at most three over `a,b,A,é`:
85 strings and 7,225 ordered pairs. It includes empty strings, repeated
characters, case distinctions, Unicode and ties. For optimality we enumerate
all subsequences of the first input, not just candidate strings in the corpus.
-/

def commonCheck (a b r : String) : Bool :=
  verify_subsequence r a && verify_subsequence r b

def optimalCheck (a b r : String) : Bool :=
  a.toList.sublists.all fun z => decide (z.Sublist b.toList → z.length ≤ r.length)

theorem commonCheck_iff (a b r : String) :
    commonCheck a b r = true ↔ common_prop a b r := by
  simp [commonCheck, verify_subsequence, verifyList_correct, common_prop]

theorem optimalCheck_iff (a b r : String) :
    optimalCheck a b r = true ↔ optimal_prop a b r := by
  simp only [optimalCheck, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h candidate ha hb
    exact h candidate.toList (List.mem_sublists.mpr ha) hb
  · intro h z hz hb
    exact h (String.mk z) (List.mem_sublists.mp hz) hb

-- These instances unfold only finite, computable predicates; no classical
-- decision procedure is used by the property tests.
instance (a b r : String) : Decidable (length_bound_prop a b r) := by
  unfold length_bound_prop
  infer_instance
instance (a b r : String) : Decidable (empty_prop a b r) := by
  unfold empty_prop
  infer_instance
instance (a b r : String) : Decidable (identity_prop a b r) := by
  unfold identity_prop
  infer_instance
instance (a b r : String) : Decidable (disjoint_prop a b r) := by
  unfold disjoint_prop
  infer_instance
instance (xs ys : List Char) : Decidable (recurrence_prop xs ys) := by
  unfold recurrence_prop
  infer_instance

/-- Executable Boolean form of the entire postcondition, including errors. -/
def postCheck (a b : Input) (result : Except ValueError String) : Bool :=
  match a, b, result with
  | .string s, .string t, .ok r =>
    commonCheck s t r && optimalCheck s t r &&
      decide (length_bound_prop s t r) && decide (empty_prop s t r) &&
      decide (identity_prop s t r) && decide (disjoint_prop s t r)
  | .string _, .string _, .error _ => false
  | _, _, .error .inputsMustBeStrings => true
  | _, _, .ok _ => false

theorem postCheck_iff (a b : Input) (result : Except ValueError String) :
    postCheck a b result = true ↔ Post_prop a b result := by
  cases a <;> cases b <;> cases result <;>
    simp [postCheck, Post_prop, Pre, commonCheck_iff, optimalCheck_iff, and_assoc]

def smallWords : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 => [] :: ['a', 'b', 'A', 'é'].flatMap (fun c => (smallWords n).map (c :: ·))

def testStrings : List String := (smallWords 3).map String.mk

def allPairs (p : String → String → Bool) : Bool :=
  testStrings.all fun a => testStrings.all fun b => p a b

def testInputs : List Input := .nonString :: testStrings.map Input.string

-- PBT: pre_prop. Inspecting the tags is the executable form of Pre.
example : testInputs.all (fun a => testInputs.all (fun b =>
    pre a b == (match a, b with
      | .string _, .string _ => true
      | _, _ => false))) = true := by
  native_decide

-- PBT: common_prop (both ordered-subsequence obligations).
example : allPairs (fun a b => commonCheck a b (longest_common_subsequence a b)) = true := by
  native_decide

-- PBT: optimal_prop (exhaustive candidate enumeration for each pair).
example : allPairs (fun a b => optimalCheck a b (longest_common_subsequence a b)) = true := by
  native_decide

-- PBT: length_bound_prop.
example : allPairs (fun a b => decide (length_bound_prop a b (longest_common_subsequence a b))) = true := by
  native_decide

-- PBT: empty_prop; all empty/nonempty pairs occur in the corpus.
example : allPairs (fun a b => decide (empty_prop a b (longest_common_subsequence a b))) = true := by
  native_decide

-- PBT: identity_prop; all 85 equal pairs occur in the corpus.
example : allPairs (fun a b => decide (identity_prop a b (longest_common_subsequence a b))) = true := by
  native_decide

-- PBT: disjoint_prop, including case-sensitive disjointness.
example : allPairs (fun a b => decide (disjoint_prop a b (longest_common_subsequence a b))) = true := by
  native_decide

-- PBT: recurrence_prop, including the up-on-ties branch.
example : allPairs (fun a b => decide (recurrence_prop a.toList b.toList)) = true := by
  native_decide

-- PBT: verification_prop. Membership in the enumerated sublists is an
-- independent executable characterization of the subsequence relation.
example : allPairs (fun sub sup =>
    verify_subsequence sub sup == sup.toList.sublists.contains sub.toList) = true := by
  native_decide

-- PBT: rejection_prop, for invalid values in either or both argument positions.
example : testInputs.all (fun a => testInputs.all (fun b =>
    match a, b with
    | .string _, .string _ => true
    | _, _ => decide (checkedLCS a b = .error .inputsMustBeStrings))) = true := by
  native_decide

-- PBT: Post_prop, using its proved equivalent Boolean form.
example : testInputs.all (fun a => testInputs.all (fun b =>
    postCheck a b (checkedLCS a b))) = true := by
  native_decide

#eval (testStrings.length, allPairs (fun a b =>
  commonCheck a b (longest_common_subsequence a b) &&
  optimalCheck a b (longest_common_subsequence a b)))

/-- Total correctness, including the specified exceptional behavior. -/
theorem total_correctness_thm (a b : Input) : Post_prop a b (checkedLCS a b) := by
  refine ⟨?_, rejection_thm a b⟩
  intro s t ha hb
  subst a
  subst b
  exact ⟨longest_common_subsequence s t, rfl, common_thm s t, optimal_thm s t,
    length_bound_thm s t, empty_thm s t, identity_thm s t, disjoint_thm s t⟩

/-- The requested precondition-to-postcondition correctness theorem. -/
theorem correctness_thm (a b : Input) : Pre a b → Post_prop a b (checkedLCS a b) := by
  intro _
  exact total_correctness_thm a b

/-! ## Imperative implementation

This implementation uses mutable result state and the same recursive subproblems.
Like the functional version, it does not memoize: the DP table is an optimization
of this recurrence, not a change to the returned string or its tie-breaking rule.
-/

def lcsRevImperative (xs ys : List Char) : List Char := Id.run do
  let mut result : List Char := []
  match xs, ys with
  | a :: as, b :: bs =>
    if a = b then
      result := a :: lcsRevImperative as bs
    else
      let up := lcsRevImperative as (b :: bs)
      let left := lcsRevImperative (a :: as) bs
      result := up
      if up.length < left.length then
        result := left
  | _, _ => pure ()
  return result
termination_by xs.length + ys.length

def longest_common_subsequenceImperative (a b : String) : String := Id.run do
  let mut result := lcsRevImperative a.toList.reverse b.toList.reverse
  result := result.reverse
  return String.mk result

def checkedLCSImperative : Input → Input → Except ValueError String
  | .string a, .string b => .ok (longest_common_subsequenceImperative a b)
  | _, _ => .error .inputsMustBeStrings

example : check checkedLCSImperative = true := by native_decide
example : longest_common_subsequenceImperative "abcde" "ace" = "ace" := by native_decide
example : longest_common_subsequenceImperative "abc" "abc" = "abc" := by native_decide
example : longest_common_subsequenceImperative "abc" "def" = "" := by native_decide
example : longest_common_subsequenceImperative "" "" = "" := by native_decide
example : longest_common_subsequenceImperative "ABCDGH" "AEDFHR" = "ADH" := by native_decide
example : longest_common_subsequenceImperative "AGGTAB" "GXTXAYB" = "GTAB" := by native_decide
example : longest_common_subsequenceImperative "Hello" "HELLO" = "H" := by native_decide
example : longest_common_subsequenceImperative "ab" "ba" = "a" := by native_decide
example : checkedLCSImperative .nonString (.string "abc") = .error .inputsMustBeStrings := by
  native_decide
example : allPairs (fun a b =>
    longest_common_subsequence a b == longest_common_subsequenceImperative a b) = true := by
  native_decide
#eval longest_common_subsequenceImperative "AGGTAB" "GXTXAYB"

/-- Kernel-checked equivalence for arbitrary lists, including every tie. -/
theorem lcsRev_equivalence (xs ys : List Char) : lcsRev xs ys = lcsRevImperative xs ys := by
  cases xs with
  | nil => simp [lcsRev, lcsRevImperative]
  | cons a as =>
    cases ys with
    | nil => simp [lcsRev, lcsRevImperative]
    | cons b bs =>
      have hd := lcsRev_equivalence as bs
      have hu := lcsRev_equivalence as (b :: bs)
      have hl := lcsRev_equivalence (a :: as) bs
      rw [lcsRev, lcsRevImperative]
      by_cases hab : a = b
      · simp [hab, hd]
      · by_cases hlen : (lcsRevImperative (a :: as) bs).length ≤
            (lcsRevImperative as (b :: bs)).length
        · simp [hab, hu, hl, hlen, Nat.not_lt.mpr hlen]
        · have hlt := Nat.lt_of_not_ge hlen
          simp [hab, hu, hl, hlen, hlt]
termination_by xs.length + ys.length

theorem equivalence_thm (a b : String) :
    longest_common_subsequence a b = longest_common_subsequenceImperative a b := by
  simp [longest_common_subsequence, longest_common_subsequenceImperative, lcsRev_equivalence]

/-- The checked interfaces agree on both valid and invalid Python inputs. -/
theorem checked_equivalence_thm (a b : Input) : checkedLCS a b = checkedLCSImperative a b := by
  cases a <;> cases b <;> simp [checkedLCS, checkedLCSImperative, equivalence_thm]

theorem imperative_correctness_thm (a b : Input) :
    Pre a b → Post_prop a b (checkedLCSImperative a b) := by
  rw [← checked_equivalence_thm]
  exact correctness_thm a b

end LongestCommonSubsequence
end Agent
