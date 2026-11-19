import Mathlib
namespace Agent

/-!
# Unsafe timing comparison

Python `bytes` are represented by finite lists of `UInt8`. The comparison first
rejects unequal lengths, then stops at the first unequal byte. `comparisonCount`
counts only byte equality tests, not length tests or wall-clock time. Its exact
formula exposes the common-prefix-dependent work of this unsafe algorithm.
All byte values and all finite lengths are admissible.
-/

namespace UnsafeTimingComparison

abbrev Bytes := List UInt8

/-- The early-exit loop, with a total definition also on unequal lengths. -/
def earlyCompare : Bytes → Bytes → Bool
  | [], [] => true
  | e :: es, a :: as => if e = a then earlyCompare es as else false
  | _, _ => false

/-- The Python function: length rejection happens before the byte loop. -/
def unsafeTimingCompare (expected actual : Bytes) : Bool :=
  if expected.length = actual.length then earlyCompare expected actual else false

/-- Number of byte tests performed by the early-exit loop. -/
def byteComparisons : Bytes → Bytes → Nat
  | e :: es, a :: as => if e = a then 1 + byteComparisons es as else 1
  | _, _ => 0

def comparisonCount (expected actual : Bytes) : Nat :=
  if expected.length = actual.length then byteComparisons expected actual else 0

/-- Length of the longest common prefix. -/
def commonPrefixLength : Bytes → Bytes → Nat
  | e :: es, a :: as => if e = a then 1 + commonPrefixLength es as else 0
  | _, _ => 0

/-- UTF-8 is used only to spell the ASCII byte strings in the source tests. -/
def bytes (s : String) : Bytes := s.toUTF8.data.toList

-- The ten assertions in the Python `check` function.
example : unsafeTimingCompare (bytes "secret") (bytes "secret") = true := by native_decide
example : unsafeTimingCompare (bytes "secret") (bytes "Xecret") = false := by native_decide
example : unsafeTimingCompare (bytes "secret") (bytes "secrex") = false := by native_decide
example : unsafeTimingCompare (bytes "abc") (bytes "ab") = false := by native_decide
example : unsafeTimingCompare (bytes "ab") (bytes "abc") = false := by native_decide
example : unsafeTimingCompare (bytes "") (bytes "") = true := by native_decide
example : unsafeTimingCompare (bytes "a") (bytes "") = false := by native_decide
example : unsafeTimingCompare (bytes "") (bytes "a") = false := by native_decide
example : unsafeTimingCompare (bytes "x") (bytes "x") = true := by native_decide
example : unsafeTimingCompare (bytes "x") (bytes "y") = false := by native_decide

/-- Executable translation of the supplied test harness. -/
def check (candidate : Bytes → Bytes → Bool) : Bool :=
  candidate (bytes "secret") (bytes "secret") &&
  !candidate (bytes "secret") (bytes "Xecret") &&
  !candidate (bytes "secret") (bytes "secrex") &&
  !candidate (bytes "abc") (bytes "ab") &&
  !candidate (bytes "ab") (bytes "abc") &&
  candidate [] [] && !candidate (bytes "a") [] && !candidate [] (bytes "a") &&
  candidate (bytes "x") (bytes "x") && !candidate (bytes "x") (bytes "y")

#eval check unsafeTimingCompare
#eval (comparisonCount (bytes "secret") (bytes "Xecret"),
       comparisonCount (bytes "secret") (bytes "secrex"))
example : comparisonCount (bytes "secret") (bytes "Xecret") = 1 := by native_decide
example : comparisonCount (bytes "secret") (bytes "secrex") = 6 := by native_decide

/-- There are no restrictions beyond being byte strings. -/
def Pre (_expected _actual : Bytes) : Prop := True


-- Universal properties and their proofs.
def equality_prop (expected actual : Bytes) : Prop :=
  unsafeTimingCompare expected actual = true ↔ expected = actual

def inequality_prop (expected actual : Bytes) : Prop :=
  unsafeTimingCompare expected actual = false ↔ expected ≠ actual

def lengthMismatch_prop (expected actual : Bytes) : Prop :=
  expected.length ≠ actual.length →
    unsafeTimingCompare expected actual = false ∧ comparisonCount expected actual = 0

def reflexive_prop (expected : Bytes) : Prop :=
  unsafeTimingCompare expected expected = true ∧
    comparisonCount expected expected = expected.length

def symmetry_prop (expected actual : Bytes) : Prop :=
  unsafeTimingCompare expected actual = unsafeTimingCompare actual expected ∧
    comparisonCount expected actual = comparisonCount actual expected

/-- Equal-length inputs inspect the first mismatching byte, if there is one. -/
def prefixTiming_prop (expected actual : Bytes) : Prop :=
  expected.length = actual.length →
    comparisonCount expected actual =
      min (commonPrefixLength expected actual + 1) expected.length

def workBound_prop (expected actual : Bytes) : Prop :=
  comparisonCount expected actual ≤ min expected.length actual.length

lemma earlyCompare_true_iff (expected actual : Bytes) :
    earlyCompare expected actual = true ↔ expected = actual := by
  induction expected generalizing actual with
  | nil => cases actual <;> simp [earlyCompare]
  | cons e es ih =>
    cases actual with
    | nil => simp [earlyCompare]
    | cons a as =>
      by_cases h : e = a <;> simp [earlyCompare, h, ih, List.cons.injEq]

theorem equality_thm (expected actual : Bytes) : equality_prop expected actual := by
  unfold equality_prop unsafeTimingCompare
  by_cases h : expected.length = actual.length
  · simp [h, earlyCompare_true_iff]
  · have hne : expected ≠ actual := fun he => h (congrArg List.length he)
    simp [h, hne]

theorem inequality_thm (expected actual : Bytes) : inequality_prop expected actual := by
  change (unsafeTimingCompare expected actual = false ↔ expected ≠ actual)
  rw [Bool.eq_false_iff]
  exact not_congr (equality_thm expected actual)

theorem lengthMismatch_thm (expected actual : Bytes) :
    lengthMismatch_prop expected actual := by
  intro h
  simp [unsafeTimingCompare, comparisonCount, h]

lemma byteComparisons_self (xs : Bytes) : byteComparisons xs xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [byteComparisons, ih, Nat.add_comm]

theorem reflexive_thm (expected : Bytes) : reflexive_prop expected := by
  constructor
  · exact (equality_thm expected expected).2 rfl
  · simpa [comparisonCount] using byteComparisons_self expected

lemma earlyCompare_symm (xs ys : Bytes) : earlyCompare xs ys = earlyCompare ys xs := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      by_cases h : x = y
      · subst y; simp [earlyCompare, ih]
      · simp [earlyCompare, h, Ne.symm h]

lemma byteComparisons_symm (xs ys : Bytes) :
    byteComparisons xs ys = byteComparisons ys xs := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      by_cases h : x = y
      · subst y; simp [byteComparisons, ih]
      · simp [byteComparisons, h, Ne.symm h]

theorem symmetry_thm (expected actual : Bytes) : symmetry_prop expected actual := by
  unfold symmetry_prop unsafeTimingCompare comparisonCount
  by_cases h : expected.length = actual.length
  · simp only [if_pos h, if_pos h.symm]
    exact ⟨earlyCompare_symm expected actual, byteComparisons_symm expected actual⟩
  · simp [h, Ne.symm h]

lemma byteComparisons_exact (expected actual : Bytes)
    (h : expected.length = actual.length) :
    byteComparisons expected actual =
      min (commonPrefixLength expected actual + 1) expected.length := by
  induction expected generalizing actual with
  | nil => cases actual <;> simp_all [byteComparisons, commonPrefixLength]
  | cons e es ih =>
    cases actual with
    | nil => simp at h
    | cons a as =>
      have ht : es.length = as.length := by simpa using h
      by_cases he : e = a
      · simp only [byteComparisons, commonPrefixLength, if_pos he, List.length_cons]
        rw [ih as ht]
        omega
      · simp only [byteComparisons, commonPrefixLength, if_neg he, List.length_cons]
        omega

theorem prefixTiming_thm (expected actual : Bytes) : prefixTiming_prop expected actual := by
  intro h
  simpa [comparisonCount, h] using byteComparisons_exact expected actual h

theorem workBound_thm (expected actual : Bytes) : workBound_prop expected actual := by
  unfold workBound_prop
  by_cases h : expected.length = actual.length
  · simp only [comparisonCount, if_pos h]
    rw [byteComparisons_exact expected actual h, ← h, Nat.min_self]
    exact Nat.min_le_right _ _
  · simp [comparisonCount, h]

lemma byteComparisons_shared_prefix (p xs ys : Bytes) :
    byteComparisons (p ++ xs) (p ++ ys) = p.length + byteComparisons xs ys := by
  induction p with
  | nil => simp
  | cons b p ih => simp [byteComparisons, ih, Nat.add_assoc, Nat.add_left_comm]

lemma earlyCompare_shared_prefix (p xs ys : Bytes) :
    earlyCompare (p ++ xs) (p ++ ys) = earlyCompare xs ys := by
  induction p with
  | nil => rfl
  | cons b p ih => simpa [earlyCompare] using ih

/-- Arbitrary suffixes are never inspected after the first unequal byte. -/
theorem firstMismatch_thm (p : Bytes) (e a : UInt8) (es as : Bytes)
    (hne : e ≠ a) (hlen : es.length = as.length) :
    unsafeTimingCompare (p ++ e :: es) (p ++ a :: as) = false ∧
    comparisonCount (p ++ e :: es) (p ++ a :: as) = p.length + 1 := by
  have h : (p ++ e :: es).length = (p ++ a :: as).length := by simp [hlen]
  simp [unsafeTimingCompare, comparisonCount, h, earlyCompare_shared_prefix,
    byteComparisons_shared_prefix, earlyCompare, byteComparisons, hne]

/-- Functional result and the work/early-exit specification, on every input. -/
def Post_prop (expected actual : Bytes) : Prop :=
  equality_prop expected actual ∧ inequality_prop expected actual ∧
  lengthMismatch_prop expected actual ∧ reflexive_prop expected ∧
  symmetry_prop expected actual ∧ prefixTiming_prop expected actual ∧
  workBound_prop expected actual


/-! ## Bounded property-based tests

These are executable Boolean versions of the propositions above, not uses of
proved theorems as test oracles. All 85 strings of length at most three over
`{0, 1, 97, 255}` are tested in all 7225 ordered pairs. The shared-prefix test
also constructs longer strings and varies both uninspected suffixes.
-/

def testAlphabet : Bytes := [0, 1, 97, 255]

def wordsOfLength : Nat → List Bytes
  | 0 => [[]]
  | n + 1 => testAlphabet.flatMap fun b => (wordsOfLength n).map (b :: ·)

def testStrings : List Bytes := (List.range 4).flatMap wordsOfLength

def allPairs (test : Bytes → Bytes → Bool) : Bool :=
  testStrings.all fun e => testStrings.all fun a => test e a

def equalityTest (e a : Bytes) : Bool :=
  unsafeTimingCompare e a == decide (e = a)

def inequalityTest (e a : Bytes) : Bool :=
  (!unsafeTimingCompare e a) == decide (e ≠ a)

def lengthMismatchTest (e a : Bytes) : Bool :=
  if e.length ≠ a.length then
    !unsafeTimingCompare e a && (comparisonCount e a == 0)
  else true

def reflexiveTest (e : Bytes) : Bool :=
  unsafeTimingCompare e e && (comparisonCount e e == e.length)

def symmetryTest (e a : Bytes) : Bool :=
  (unsafeTimingCompare e a == unsafeTimingCompare a e) &&
    (comparisonCount e a == comparisonCount a e)

def prefixTimingTest (e a : Bytes) : Bool :=
  if e.length = a.length then
    comparisonCount e a == min (commonPrefixLength e a + 1) e.length
  else true

def workBoundTest (e a : Bytes) : Bool :=
  decide (comparisonCount e a ≤ min e.length a.length)

def postTest (e a : Bytes) : Bool :=
  equalityTest e a && inequalityTest e a && lengthMismatchTest e a &&
  reflexiveTest e && symmetryTest e a && prefixTimingTest e a && workBoundTest e a

-- PBT: equality_prop.
example : allPairs equalityTest = true := by native_decide
-- PBT: inequality_prop.
example : allPairs inequalityTest = true := by native_decide
-- PBT: lengthMismatch_prop (unequal-length pairs are included).
example : allPairs lengthMismatchTest = true := by native_decide
-- PBT: reflexive_prop.
example : testStrings.all reflexiveTest = true := by native_decide
-- PBT: symmetry_prop.
example : allPairs symmetryTest = true := by native_decide
-- PBT: prefixTiming_prop (every equal-length pair is included).
example : allPairs prefixTimingTest = true := by native_decide
-- PBT: workBound_prop.
example : allPairs workBoundTest = true := by native_decide
-- PBT: the complete Post_prop.
example : allPairs postTest = true := by native_decide

-- Also cover the entire byte domain, not just the short-string alphabet.
example : (List.range 256).all (fun x =>
    (List.range 256).all (fun y => postTest [UInt8.ofNat x] [UInt8.ofNat y])) = true := by
  native_decide

-- PBT: firstMismatch_thm, varying the shared prefix and both arbitrary suffixes.
def firstMismatchTest : Bool :=
  testStrings.all fun p =>
    testAlphabet.all fun e => testAlphabet.all fun a =>
      testStrings.all fun es => testStrings.all fun as =>
        if e ≠ a ∧ es.length = as.length then
          !unsafeTimingCompare (p ++ e :: es) (p ++ a :: as) &&
            (comparisonCount (p ++ e :: es) (p ++ a :: as) == p.length + 1)
        else true

example : firstMismatchTest = true := by native_decide
#eval (testStrings.length, allPairs postTest, firstMismatchTest)

/-- Every admissible pair meets the complete functional and work specification. -/
theorem correctness_thm (expected actual : Bytes) :
    Pre expected actual → Post_prop expected actual := by
  intro _
  exact ⟨equality_thm expected actual, inequality_thm expected actual,
    lengthMismatch_thm expected actual, reflexive_thm expected,
    symmetry_thm expected actual, prefixTiming_thm expected actual,
    workBound_thm expected actual⟩


/-! ## Imperative translation -/

/-- A direct length check followed by a mutable, early-breaking zip loop. -/
def unsafeTimingCompareImp (expected actual : Bytes) : Bool := Id.run do
  if expected.length != actual.length then
    return false
  let mut equal := true
  for pair in expected.zip actual do
    if pair.1 != pair.2 then
      equal := false
      break
  return equal

-- All ten original assertions are also checked against the imperative code.
example : check unsafeTimingCompareImp = true := by native_decide
example : unsafeTimingCompareImp (bytes "secret") (bytes "secret") = true := by native_decide
example : unsafeTimingCompareImp (bytes "secret") (bytes "Xecret") = false := by native_decide
example : unsafeTimingCompareImp (bytes "secret") (bytes "secrex") = false := by native_decide
example : unsafeTimingCompareImp (bytes "abc") (bytes "ab") = false := by native_decide
example : unsafeTimingCompareImp (bytes "ab") (bytes "abc") = false := by native_decide
example : unsafeTimingCompareImp [] [] = true := by native_decide
example : unsafeTimingCompareImp (bytes "a") [] = false := by native_decide
example : unsafeTimingCompareImp [] (bytes "a") = false := by native_decide
example : unsafeTimingCompareImp (bytes "x") (bytes "x") = true := by native_decide
example : unsafeTimingCompareImp (bytes "x") (bytes "y") = false := by native_decide
#eval check unsafeTimingCompareImp

-- PBT: functional–imperative equivalence, including unequal lengths.
example : allPairs (fun e a => unsafeTimingCompare e a == unsafeTimingCompareImp e a) =
    true := by native_decide
#eval allPairs (fun e a => unsafeTimingCompare e a == unsafeTimingCompareImp e a)

/-- The same imperative loop, isolated to prove its transition equations. -/
private def scanImp (pairs : List (UInt8 × UInt8)) : Bool := Id.run do
  let mut equal := true
  for pair in pairs do
    if pair.1 != pair.2 then
      equal := false
      break
  return equal

private lemma scanImp_cons (e a : UInt8) (tail : List (UInt8 × UInt8)) :
    scanImp ((e, a) :: tail) = if e = a then scanImp tail else false := by
  unfold scanImp
  simp only [List.forIn_cons]
  split <;> simp_all

private lemma scanImp_zip (expected actual : Bytes)
    (h : expected.length = actual.length) :
    scanImp (expected.zip actual) = earlyCompare expected actual := by
  induction expected generalizing actual with
  | nil =>
    cases actual with
    | nil => rfl
    | cons a as => simp at h
  | cons e es ih =>
    cases actual with
    | nil => simp at h
    | cons a as =>
      have ht : es.length = as.length := by simpa using h
      by_cases he : e = a <;>
        simp [List.zip_cons_cons, scanImp_cons, earlyCompare, he, ih as ht]

private lemma unsafeTimingCompareImp_eq (expected actual : Bytes) :
    unsafeTimingCompareImp expected actual =
      if expected.length = actual.length then scanImp (expected.zip actual) else false := by
  by_cases h : expected.length = actual.length <;>
    simp [unsafeTimingCompareImp, scanImp, h]

/-- The actual mutable-state program equals the functional model on all bytes. -/
theorem equivalence_thm (expected actual : Bytes) :
    unsafeTimingCompare expected actual = unsafeTimingCompareImp expected actual := by
  rw [unsafeTimingCompareImp_eq]
  unfold unsafeTimingCompare
  by_cases h : expected.length = actual.length
  · simp only [if_pos h]
    exact (scanImp_zip expected actual h).symm
  · simp [h]

end UnsafeTimingComparison
end Agent
