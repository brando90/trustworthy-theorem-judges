import Mathlib
namespace Agent

/-!
# Unsafe secure boot chain

Translation of the Python `unsafe_boot_chain` example from the IoT secure-boot
lecture. Each stage contains a firmware hash and a signature. The implementation
never inspects either field and unconditionally returns `true`: it is deliberately
unsafe, not a verified secure-boot implementation.

`Int` models Python's arbitrary-precision signed integers, and lists preserve the
entire input domain, including empty chains. Numerical hash/signature inequality
below describes the mismatched fixtures in the Python tests; it is not a model of
cryptographic signature verification. No verifier or trusted key is provided by
the source program.
-/

namespace UnsafeBootChain

abbrev Stage := Int × Int
abbrev Stages := List Stage

/-! ## Functional implementation and the Python test harness -/

/-- Boot without examining the stages, their hashes, or their signatures. -/
def unsafe_boot_chain (_stages : Stages) : Bool :=
  true

/-- The forged input used by the Python assertion harness. -/
def forged_stages : Stages :=
  [(0xC0DE, 0xFFFF), (0xBAD0, 0x0000)]

/-- Boolean conjunction of the assertions in Python's `check`. -/
def check (candidate : Stages → Bool) : Bool :=
  candidate [] &&
  candidate [(0xABCD, 0xABCD)] &&
  candidate [(0xABCD, 0x0000)] &&
  candidate [(0xDEAD, 0xBEEF), (0x1234, 0x0000)] &&
  candidate forged_stages

/-! ## Unit tests -/

example : unsafe_boot_chain [] = true := by native_decide
example : unsafe_boot_chain [(0xABCD, 0xABCD)] = true := by native_decide
example : unsafe_boot_chain [(0xABCD, 0x0000)] = true := by native_decide
example : unsafe_boot_chain [(0xDEAD, 0xBEEF), (0x1234, 0x0000)] = true := by
  native_decide
example : unsafe_boot_chain forged_stages = true := by native_decide
example : check unsafe_boot_chain = true := by native_decide
-- Negative integers are admissible too; the hexadecimal examples do not restrict the domain.
example : unsafe_boot_chain [(-1, -2), (0, -3)] = true := by native_decide

#eval unsafe_boot_chain []
#eval unsafe_boot_chain forged_stages
#eval check unsafe_boot_chain
#eval if check unsafe_boot_chain then "All tests passed." else "Test failure."

/-! ## Preconditions and proved behavioral properties -/

/-- The source has no restrictions on stages or signature validity. -/
def Pre (_stages : Stages) : Prop := True

/-- Every chain, including an empty chain, is accepted. -/
def always_boots_prop (stages : Stages) : Prop :=
  unsafe_boot_chain stages = true

theorem always_boots_thm (stages : Stages) : always_boots_prop stages := by
  rfl

/-- Even changing hashes, signatures, order, or chain length cannot affect the answer. -/
def input_independent_prop (stages other : Stages) : Prop :=
  unsafe_boot_chain stages = unsafe_boot_chain other

theorem input_independent_thm (stages other : Stages) :
    input_independent_prop stages other := by
  rfl

/-- Arbitrary changes to signatures, with the firmware hashes fixed, are ignored. -/
def signatures_ignored_prop (stages other : Stages) : Prop :=
  stages.map Prod.fst = other.map Prod.fst →
    unsafe_boot_chain stages = unsafe_boot_chain other

theorem signatures_ignored_thm (stages other : Stages) :
    signatures_ignored_prop stages other := by
  intro _
  rfl

/-- A chain containing a numerical hash/signature mismatch is still accepted. -/
def mismatched_signature_accepted_prop (stages : Stages) : Prop :=
  stages.any (fun stage => stage.1 != stage.2) = true →
    unsafe_boot_chain stages = true

theorem mismatched_signature_accepted_thm (stages : Stages) :
    mismatched_signature_accepted_prop stages := by
  intro _
  rfl

/-! ## Postcondition -/

/-- The returned value is exactly the unconditional acceptance result, and all
input/signature-independence and mismatch-acceptance properties hold. -/
def Post_prop (stages : Stages) (result : Bool) : Prop :=
  result = unsafe_boot_chain stages ∧
  result = true ∧
  always_boots_prop stages ∧
  (∀ other : Stages, input_independent_prop stages other) ∧
  (∀ other : Stages, signatures_ignored_prop stages other) ∧
  mismatched_signature_accepted_prop stages

/-! ## Property-based tests

Exhaustively enumerate every chain of length zero, one, or two over four integer
values. This gives 273 chains, including negative values, matching signatures,
and mismatches. Binary properties are tested on all 74,529 ordered pairs.
These are bounded tests, not restrictions on the universally quantified theorems.
Each test checks an executable Boolean counterpart of the named property.
-/

private def testValues : List Int := [-1, 0, 1, 0xABCD]

private def testStages : List Stage :=
  testValues.flatMap (fun hash => testValues.map (fun signature => (hash, signature)))

private def testChains : List Stages :=
  [[]] ++ testStages.map (fun stage => [stage]) ++
    testStages.flatMap (fun first => testStages.map (fun second => [first, second]))

-- PBT: always_boots_prop.
example : testChains.all (fun stages => unsafe_boot_chain stages == true) = true := by
  native_decide

-- PBT: input_independent_prop, including different lengths and firmware hashes.
example :
    testChains.all (fun stages =>
      testChains.all (fun other =>
        unsafe_boot_chain stages == unsafe_boot_chain other)) = true := by
  native_decide

-- PBT: signatures_ignored_prop. Boolean implication also includes every pair
-- with identical hashes and independently chosen signatures in the bounded domain.
example :
    testChains.all (fun stages =>
      testChains.all (fun other =>
        (!(stages.map Prod.fst == other.map Prod.fst)) ||
          (unsafe_boot_chain stages == unsafe_boot_chain other))) = true := by
  native_decide

-- PBT: mismatched_signature_accepted_prop. Many enumerated chains contain mismatches.
example :
    testChains.all (fun stages =>
      (!(stages.any (fun stage => stage.1 != stage.2))) ||
        (unsafe_boot_chain stages == true)) = true := by
  native_decide

-- PBT: Post_prop. Its universally quantified `other` conjuncts are checked
-- exhaustively over the same bounded domain; every other conjunct is checked too.
example :
    testChains.all (fun stages =>
      let result := unsafe_boot_chain stages
      (result == unsafe_boot_chain stages) &&
      (result == true) &&
      (unsafe_boot_chain stages == true) &&
      (testChains.all (fun other =>
        unsafe_boot_chain stages == unsafe_boot_chain other)) &&
      (testChains.all (fun other =>
        (!(stages.map Prod.fst == other.map Prod.fst)) ||
          (unsafe_boot_chain stages == unsafe_boot_chain other))) &&
      ((!(stages.any (fun stage => stage.1 != stage.2))) ||
        (unsafe_boot_chain stages == true))) = true := by
  native_decide

#eval testChains.length
#eval testChains.all (fun stages => unsafe_boot_chain stages == true)

/-! ## Correctness with respect to the deliberately unsafe specification -/

theorem correctness_thm (stages : Stages) :
    Pre stages → Post_prop stages (unsafe_boot_chain stages) := by
  intro _
  refine ⟨rfl, rfl, always_boots_thm stages, ?_, ?_,
    mismatched_signature_accepted_thm stages⟩
  · intro other
    exact input_independent_thm stages other
  · intro other
    exact signatures_ignored_thm stages other

/-! ## Imperative implementation -/

/-- The mutable boot decision is set unconditionally; no signature check occurs. -/
def unsafe_boot_chain_imperative (_stages : Stages) : Bool := Id.run do
  let mut bootAllowed := false
  bootAllowed := true
  return bootAllowed

/-! ## Imperative tests -/

example : unsafe_boot_chain_imperative [] = true := by native_decide
example : unsafe_boot_chain_imperative [(0xABCD, 0xABCD)] = true := by native_decide
example : unsafe_boot_chain_imperative [(0xABCD, 0x0000)] = true := by native_decide
example :
    unsafe_boot_chain_imperative [(0xDEAD, 0xBEEF), (0x1234, 0x0000)] = true := by
  native_decide
example : unsafe_boot_chain_imperative forged_stages = true := by native_decide
example : check unsafe_boot_chain_imperative = true := by native_decide

#eval unsafe_boot_chain_imperative forged_stages
#eval check unsafe_boot_chain_imperative

-- Bounded PBT for functional/imperative agreement.
example :
    testChains.all (fun stages =>
      unsafe_boot_chain stages == unsafe_boot_chain_imperative stages) = true := by
  native_decide

/-! ## Kernel-checked functional/imperative equivalence -/

theorem functional_eq_imperative_thm (stages : Stages) :
    unsafe_boot_chain stages = unsafe_boot_chain_imperative stages := by
  rfl

end UnsafeBootChain
end Agent
