import Mathlib
namespace Agent

/-!
# Unsafe passcode KDF

A translation of the supplied Python program. `simpleHash` sums Unicode code
points (not UTF-8 bytes), adds 37 times the character count, and renders the
natural number in decimal. The KDF intentionally ignores the device UID.
Consequently an extracted ciphertext permits offline guessing: the returned
attack flag is exactly the extraction flag, regardless of the iteration count.

Iteration counts are `Int`, preserving Python's empty `range` for negative
counts. Strings use Lean's Unicode scalar values. The simplified hash is not
cryptographic or injective; the distinct-passcode test is only about the two
particular passcodes in the Python tests.
-/

namespace UnsafePasscodeKdf

/-- Python's `simple_hash`, using unbounded natural arithmetic. -/
def simpleHash (s : String) : String :=
  toString (s.length * 37 + (s.toList.map (fun c => c.toNat * 31)).sum)

/-- Apply the hash exactly `n` times, starting with the passcode itself. -/
def deriveKey (passcode : String) : Nat → String
  | 0 => passcode
  | n + 1 => simpleHash (deriveKey passcode n)

/-- The UID is deliberately unused, exactly as in the vulnerable Python code. -/
def unsafePasscodeKdf (passcode _uid : String) (iterations : Int)
    (canExtractData : Bool) : String × Bool :=
  (deriveKey passcode iterations.toNat, canExtractData)

-- The original Python unit tests.
example : (unsafePasscodeKdf "1234" "device-uid" 100 false).1.length > 0 ∧
    (unsafePasscodeKdf "1234" "device-uid" 100 false).2 = false := by
  native_decide
example : (unsafePasscodeKdf "1234" "device-uid" 100 true).1.length > 0 ∧
    (unsafePasscodeKdf "1234" "device-uid" 100 true).2 = true := by
  native_decide
example : (unsafePasscodeKdf "1234" "uid1" 10 false).1 =
    (unsafePasscodeKdf "1234" "uid2" 10 false).1 := by native_decide
example : (unsafePasscodeKdf "1234" "uid" 10 false).1 ≠
    (unsafePasscodeKdf "5678" "uid" 10 false).1 := by native_decide
example : simpleHash "" = "0" ∧ simpleHash "é" = "7260" ∧
    simpleHash "🔑" = "3976500" := by native_decide
example : unsafePasscodeKdf "" "uid" (-3) true = ("", true) ∧
    unsafePasscodeKdf "" "uid" 1 false = ("0", false) := by native_decide
example : simpleHash "ab" = simpleHash "ba" := by native_decide
#eval unsafePasscodeKdf "1234" "device-uid" 100 true
#eval unsafePasscodeKdf "5678" "uid" 10 false

/-- No restrictions: in particular, empty passcodes and negative counts are legal. -/
def Pre (_passcode _uid : String) (_iterations : Int)
    (_canExtractData : Bool) : Prop := True

/-- UID independence is the central vulnerability. -/
def uid_independent_prop (passcode uid otherUid : String) (iterations : Int)
    (canExtractData : Bool) : Prop :=
  unsafePasscodeKdf passcode uid iterations canExtractData =
    unsafePasscodeKdf passcode otherUid iterations canExtractData

theorem uid_independent_thm (passcode uid otherUid : String) (iterations : Int)
    (canExtractData : Bool) :
    uid_independent_prop passcode uid otherUid iterations canExtractData := by
  rfl

/-- The offline-attack flag is neither suppressed nor introduced by the KDF. -/
def offline_attack_prop (passcode uid : String) (iterations : Int)
    (canExtractData : Bool) : Prop :=
  (unsafePasscodeKdf passcode uid iterations canExtractData).2 = canExtractData

theorem offline_attack_thm (passcode uid : String) (iterations : Int)
    (canExtractData : Bool) :
    offline_attack_prop passcode uid iterations canExtractData := by
  rfl

/-- Data extraction affects the flag only, not the derived key. -/
def extraction_independent_prop (passcode uid : String) (iterations : Int)
    (first second : Bool) : Prop :=
  (unsafePasscodeKdf passcode uid iterations first).1 =
    (unsafePasscodeKdf passcode uid iterations second).1

theorem extraction_independent_thm (passcode uid : String) (iterations : Int)
    (first second : Bool) :
    extraction_independent_prop passcode uid iterations first second := by
  rfl

/-- Nonpositive Python ranges do not perform a hash operation. -/
def nonpositive_prop (passcode uid : String) (iterations : Int)
    (canExtractData : Bool) : Prop :=
  iterations ≤ 0 →
    unsafePasscodeKdf passcode uid iterations canExtractData = (passcode, canExtractData)

theorem nonpositive_thm (passcode uid : String) (iterations : Int)
    (canExtractData : Bool) :
    nonpositive_prop passcode uid iterations canExtractData := by
  intro h
  have hz : iterations.toNat = 0 := by omega
  simp [unsafePasscodeKdf, hz, deriveKey]

/-- A positive iteration step hashes the previous key without mixing in a UID. -/
def step_prop (passcode uid : String) (iterations : Int)
    (canExtractData : Bool) : Prop :=
  0 ≤ iterations →
    unsafePasscodeKdf passcode uid (iterations + 1) canExtractData =
      (simpleHash (unsafePasscodeKdf passcode uid iterations canExtractData).1,
        canExtractData)

theorem step_thm (passcode uid : String) (iterations : Int)
    (canExtractData : Bool) : step_prop passcode uid iterations canExtractData := by
  intro h
  have hs : (iterations + 1).toNat = iterations.toNat + 1 := by omega
  simp [unsafePasscodeKdf, hs, deriveKey]

-- Decimal rendering always emits at least one digit. These helper proofs use
-- the kernel-visible implementation of Nat.toDigitsCore, not native evaluation.
private theorem digits_preserve_nonempty (base fuel n : Nat) (acc : List Char)
    (h : acc ≠ []) : Nat.toDigitsCore base fuel n acc ≠ [] := by
  induction fuel generalizing n acc with
  | zero => exact h
  | succ fuel ih =>
    simp only [Nat.toDigitsCore]
    split_ifs
    · exact List.cons_ne_nil _ _
    · exact ih _ _ (List.cons_ne_nil _ _)

private theorem decimal_nonempty (n : Nat) : toString n ≠ "" := by
  intro h
  have hd : Nat.toDigitsCore 10 (n + 1) n [] = [] := congrArg String.toList h
  simp only [Nat.toDigitsCore] at hd
  split_ifs at hd
  exact digits_preserve_nonempty _ _ _ _ (List.cons_ne_nil _ _) hd

private theorem string_length_pos_iff (s : String) : 0 < s.length ↔ s ≠ "" := by
  cases s with
  | mk cs =>
    change 0 < cs.length ↔ String.mk cs ≠ String.mk []
    cases cs with
    | nil => simp
    | cons c cs =>
      constructor
      · intro _ h
        have heq : c :: cs = [] := congrArg String.toList h
        exact List.cons_ne_nil _ _ heq
      · intro _
        exact Nat.succ_pos _

theorem simpleHash_nonempty (s : String) : simpleHash s ≠ "" := by
  exact decimal_nonempty _

/-- Exact nonemptiness criterion, including the empty-passcode/empty-range case. -/
def nonempty_prop (passcode uid : String) (iterations : Int)
    (canExtractData : Bool) : Prop :=
  0 < (unsafePasscodeKdf passcode uid iterations canExtractData).1.length ↔
    passcode ≠ "" ∨ 0 < iterations

theorem nonempty_thm (passcode uid : String) (iterations : Int)
    (canExtractData : Bool) : nonempty_prop passcode uid iterations canExtractData := by
  unfold nonempty_prop unsafePasscodeKdf
  simp only [string_length_pos_iff]
  cases hi : iterations.toNat with
  | zero =>
    have hn : ¬ 0 < iterations := by omega
    simp [deriveKey, hn]
  | succ n =>
    have hp : 0 < iterations := by omega
    simp [deriveKey, simpleHash_nonempty, hp]

/-- This is the specific distinction tested by Python, not injectivity of the KDF. -/
def passcode_examples_prop (uid : String) (canExtractData : Bool) : Prop :=
  (unsafePasscodeKdf "1234" uid 10 canExtractData).1 ≠
    (unsafePasscodeKdf "5678" uid 10 canExtractData).1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem passcode_examples_thm (uid : String) (canExtractData : Bool) :
    passcode_examples_prop uid canExtractData := by
  change deriveKey "1234" 10 ≠ deriveKey "5678" 10
  -- Check each hash step in the kernel, then compose the equalities.
  -- Sharing the intermediate facts avoids repeated nested normalization.
  have h0 : simpleHash "1234" = "6410" := by decide
  have h1 : simpleHash "6410" = "6441" := by decide
  have h2 : simpleHash "6441" = "6565" := by decide
  have h3 : simpleHash "6565" = "6782" := by decide
  have h4 : simpleHash "6782" = "6813" := by decide
  have h5 : simpleHash "6813" = "6658" := by decide
  have h6 : simpleHash "6658" = "6875" := by decide
  have h7 : simpleHash "6875" = "6906" := by decide
  have h8 : simpleHash "6906" = "6751" := by decide
  have h9 : simpleHash "6751" = "6689" := by decide
  have h10 : simpleHash "5678" = "6906" := by decide
  have h11 : simpleHash "6689" = "6999" := by decide
  have h12 : simpleHash "6999" = "7123" := by decide
  have h13 : simpleHash "7123" = "6503" := by decide
  have h14 : simpleHash "6503" = "6534" := by decide
  have h15 : simpleHash "6534" = "6658" := by decide
  simp only [deriveKey, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11, h12, h13, h14, h15]
  decide

/-- The postcondition compares arbitrary UIDs and extraction flags. All inputs,
including the comparison inputs, remain universally quantified in correctness. -/
def Post_prop (passcode uid otherUid : String) (iterations : Int)
    (canExtractData otherExtraction : Bool) : Prop :=
  uid_independent_prop passcode uid otherUid iterations canExtractData ∧
  offline_attack_prop passcode uid iterations canExtractData ∧
  extraction_independent_prop passcode uid iterations canExtractData otherExtraction ∧
  nonpositive_prop passcode uid iterations canExtractData ∧
  step_prop passcode uid iterations canExtractData ∧
  nonempty_prop passcode uid iterations canExtractData ∧
  passcode_examples_prop uid canExtractData

/-! ## Bounded property-based tests

Every executable `_prop`, including `Post_prop`, has a Boolean check below.
The corpus includes all strings of length one and two over a four-character
ASCII/Unicode alphabet, additional Python examples, empty strings, four UIDs,
negative and zero counts, positive counts through 12, and 25 and 100 rounds.
These exhaustive finite checks are evidence only; the proofs above and below
are independent of all `native_decide` tests.
-/

def testAlphabet : List Char := ['0', '1', 'é', '🔑']
def testPasscodes : List String :=
  ["", "1234", "5678", "ab", "ba", "passcode", String.mk [Char.ofNat 0]] ++
  testAlphabet.map (fun c => String.mk [c]) ++
  testAlphabet.flatMap (fun a => testAlphabet.map (fun b => String.mk [a, b]))
def testUids : List String := ["", "uid1", "uid2", "device-uid"]
def testIterations : List Int :=
  (List.range 16).map (fun n => (n : Int) - 3) ++ [25, 100]
def testFlags : List Bool := [false, true]

def allCases (test : String → String → Int → Bool → Bool) : Bool :=
  testPasscodes.all fun passcode =>
    testUids.all fun uid =>
      testIterations.all fun iterations =>
        testFlags.all fun extracted => test passcode uid iterations extracted

def uidCheck (p u v : String) (i : Int) (b : Bool) : Bool :=
  unsafePasscodeKdf p u i b == unsafePasscodeKdf p v i b
def offlineCheck (p u : String) (i : Int) (b : Bool) : Bool :=
  (unsafePasscodeKdf p u i b).2 == b
def extractionCheck (p u : String) (i : Int) (b c : Bool) : Bool :=
  (unsafePasscodeKdf p u i b).1 == (unsafePasscodeKdf p u i c).1
def nonpositiveCheck (p u : String) (i : Int) (b : Bool) : Bool :=
  decide (0 < i) || (unsafePasscodeKdf p u i b == (p, b))
def stepCheck (p u : String) (i : Int) (b : Bool) : Bool :=
  decide (i < 0) ||
    (unsafePasscodeKdf p u (i + 1) b ==
      (simpleHash (unsafePasscodeKdf p u i b).1, b))
def nonemptyCheck (p u : String) (i : Int) (b : Bool) : Bool :=
  decide (0 < (unsafePasscodeKdf p u i b).1.length) ==
    (decide (p ≠ "") || decide (0 < i))
def passcodeExamplesCheck (u : String) (b : Bool) : Bool :=
  (unsafePasscodeKdf "1234" u 10 b).1 != (unsafePasscodeKdf "5678" u 10 b).1

def postCheck (p u v : String) (i : Int) (b c : Bool) : Bool :=
  uidCheck p u v i b && offlineCheck p u i b && extractionCheck p u i b c &&
  nonpositiveCheck p u i b && stepCheck p u i b && nonemptyCheck p u i b &&
  passcodeExamplesCheck u b

-- PBT: uid_independent_prop, for every pair of sampled UIDs.
example : allCases (fun p u i b => testUids.all fun v => uidCheck p u v i b) = true := by
  native_decide
-- PBT: offline_attack_prop.
example : allCases offlineCheck = true := by native_decide
-- PBT: extraction_independent_prop, exhaustively covering both Boolean inputs.
example : allCases (fun p u i b => testFlags.all fun c => extractionCheck p u i b c) = true := by
  native_decide
-- PBT: nonpositive_prop (the implication is checked, not just positive inputs).
example : allCases nonpositiveCheck = true := by native_decide
-- PBT: step_prop, including the boundary at zero.
example : allCases stepCheck = true := by native_decide
-- PBT: nonempty_prop, testing both directions of the equivalence.
example : allCases nonemptyCheck = true := by native_decide
-- PBT: passcode_examples_prop, over all sampled UIDs and both flags.
example : (testUids.all fun u => testFlags.all fun b => passcodeExamplesCheck u b) = true := by
  native_decide
-- PBT: Post_prop, over the full Cartesian product of comparison inputs too.
example : allCases (fun p u i b => testUids.all fun v =>
    testFlags.all fun c => postCheck p u v i b c) = true := by native_decide
-- PBT for the executable helper property that hashing itself is nonempty.
example : (testPasscodes.all fun p => decide (0 < (simpleHash p).length)) = true := by
  native_decide
#eval allCases (fun p u i b => testUids.all fun v =>
  testFlags.all fun c => postCheck p u v i b c)

/-- Correctness holds without excluding any iteration count or passcode. -/
theorem correctness_thm (passcode uid otherUid : String) (iterations : Int)
    (canExtractData otherExtraction : Bool) :
    Pre passcode uid iterations canExtractData →
      Post_prop passcode uid otherUid iterations canExtractData otherExtraction := by
  intro _
  exact ⟨uid_independent_thm passcode uid otherUid iterations canExtractData,
    offline_attack_thm passcode uid iterations canExtractData,
    extraction_independent_thm passcode uid iterations canExtractData otherExtraction,
    nonpositive_thm passcode uid iterations canExtractData,
    step_thm passcode uid iterations canExtractData,
    nonempty_thm passcode uid iterations canExtractData,
    passcode_examples_thm uid canExtractData⟩

/-! ## Imperative translation -/

/-- Direct mutable translation of the character-sum loop in Python. -/
def simpleHashImperative (s : String) : String := Id.run do
  let mut charSum := 0
  for c in s.toList do
    charSum := charSum + c.toNat * 31
  return toString (s.length * 37 + charSum)

/-- `List.range iterations.toNat` has exactly Python's `range` behavior here. -/
def unsafePasscodeKdfImperative (passcode _uid : String) (iterations : Int)
    (canExtractData : Bool) : String × Bool := Id.run do
  let mut key := passcode
  for _ in List.range iterations.toNat do
    key := simpleHashImperative key
  return (key, canExtractData)

-- Imperative versions of the original checks, plus empty/negative boundaries.
example : (unsafePasscodeKdfImperative "1234" "device-uid" 100 false).1.length > 0 ∧
    (unsafePasscodeKdfImperative "1234" "device-uid" 100 false).2 = false := by
  native_decide
example : (unsafePasscodeKdfImperative "1234" "device-uid" 100 true).1.length > 0 ∧
    (unsafePasscodeKdfImperative "1234" "device-uid" 100 true).2 = true := by
  native_decide
example : (unsafePasscodeKdfImperative "1234" "uid1" 10 false).1 =
    (unsafePasscodeKdfImperative "1234" "uid2" 10 false).1 := by native_decide
example : (unsafePasscodeKdfImperative "1234" "uid" 10 false).1 ≠
    (unsafePasscodeKdfImperative "5678" "uid" 10 false).1 := by native_decide
example : unsafePasscodeKdfImperative "" "uid" (-3) true = ("", true) ∧
    unsafePasscodeKdfImperative "" "uid" 1 false = ("0", false) := by native_decide
example : (testPasscodes.all fun p => simpleHash p == simpleHashImperative p) = true := by
  native_decide
example : allCases (fun p u i b =>
    unsafePasscodeKdf p u i b == unsafePasscodeKdfImperative p u i b) = true := by
  native_decide
#eval unsafePasscodeKdfImperative "1234" "device-uid" 100 true
#eval unsafePasscodeKdfImperative "5678" "uid" 10 false

-- Accumulator invariant for the inner (character) loop.
private theorem char_sum_fold (cs : List Char) (acc : Nat) :
    cs.foldl (fun a c => a + c.toNat * 31) acc =
      acc + (cs.map (fun c => c.toNat * 31)).sum := by
  induction cs generalizing acc with
  | nil => simp
  | cons c cs ih => simp [List.foldl_cons, ih, Nat.add_assoc]

theorem simpleHashImperative_eq (s : String) : simpleHashImperative s = simpleHash s := by
  simp [simpleHashImperative, simpleHash, List.forIn_pure_yield_eq_foldl, char_sum_fold]

-- After n iterations the mutable key is precisely deriveKey passcode n.
private theorem rounds_fold (n : Nat) (passcode : String) :
    (List.range n).foldl (fun key _ => simpleHash key) passcode = deriveKey passcode n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.range_succ, List.foldl_append, ih, deriveKey]

/-- Full functional/imperative equivalence, including the character-sum loop,
all integer iteration counts, the ignored UID, and both extraction flags. -/
theorem equivalence_thm (passcode uid : String) (iterations : Int)
    (canExtractData : Bool) :
    unsafePasscodeKdf passcode uid iterations canExtractData =
      unsafePasscodeKdfImperative passcode uid iterations canExtractData := by
  symm
  simp [unsafePasscodeKdfImperative, unsafePasscodeKdf, simpleHashImperative_eq,
    List.forIn_pure_yield_eq_foldl, rounds_fold]

end UnsafePasscodeKdf
end Agent
