import Mathlib
namespace Agent

/-!
# Unsafe authenticated encryption: nonce reuse is accepted

A faithful translation of the Python `unsafeNonceReuse` function and its tests.
Python integers are modeled by unbounded `Int`. The function always returns
`true`: neither nonce freshness nor ciphertext identifier equality is checked.
This file describes the vulnerability; it deliberately does not repair it.

The specifications cover unconditional acceptance, independence from both pairs
of inputs, acceptance of reused and stale nonces, and acceptance of mismatched
identifiers. Bounded property-based tests include negative, zero, and positive
integers. The general correctness and equivalence proofs are kernel-checked;
`native_decide` is used only for executable tests.
-/

namespace UnsafeNonceReuse

/-! ## Functional implementation -/

/-- The four arguments are intentionally ignored, exactly as in Python. -/
def unsafeNonceReuse
    (_nonce _last_nonce _ciphertext_id _expected_id : Int) : Bool :=
  true

/-! ## Unit tests and the Python `check` harness -/

example : unsafeNonceReuse 5 10 42 42 = true := by native_decide
example : unsafeNonceReuse 5 10 42 99 = true := by native_decide
example : unsafeNonceReuse 0 100 1 1 = true := by native_decide

-- Equal nonces, genuinely fresh nonces, negative inputs, and large integers.
example : unsafeNonceReuse 10 10 42 42 = true := by native_decide
example : unsafeNonceReuse 11 10 42 99 = true := by native_decide
example : unsafeNonceReuse (-5) (-1) (-42) 99 = true := by native_decide
example : unsafeNonceReuse (10 ^ 100) (10 ^ 101) (-1) 0 = true := by native_decide

#eval unsafeNonceReuse 5 10 42 42
#eval unsafeNonceReuse 5 10 42 99
#eval unsafeNonceReuse 0 100 1 1

/-- Executable counterpart of the source program's assertion harness. -/
def check : IO Unit := do
  unless unsafeNonceReuse 5 10 42 42 do
    throw (IO.userError "normal case failed")
  unless unsafeNonceReuse 5 10 42 99 do
    throw (IO.userError "vuln: replayed nonce accepted")
  unless unsafeNonceReuse 0 100 1 1 do
    throw (IO.userError "vuln: stale nonce accepted")
  IO.println "All tests passed."

#eval check

/-! ## Precondition -/

/-- No freshness, sign, size, or identifier restriction is imposed by Python. -/
def Pre (_nonce _last_nonce _ciphertext_id _expected_id : Int) : Prop :=
  True

/-! ## Properties and proofs -/

def alwaysAccepts_prop (nonce last_nonce ciphertext_id expected_id : Int) : Prop :=
  unsafeNonceReuse nonce last_nonce ciphertext_id expected_id = true

theorem alwaysAccepts_thm (nonce last_nonce ciphertext_id expected_id : Int) :
    alwaysAccepts_prop nonce last_nonce ciphertext_id expected_id := by
  rfl

/-- Changing either nonce cannot affect the result. -/
def nonceIndependent_prop (nonce last_nonce ciphertext_id expected_id : Int) : Prop :=
  ∀ nonce' last_nonce' : Int,
    unsafeNonceReuse nonce last_nonce ciphertext_id expected_id =
      unsafeNonceReuse nonce' last_nonce' ciphertext_id expected_id

theorem nonceIndependent_thm (nonce last_nonce ciphertext_id expected_id : Int) :
    nonceIndependent_prop nonce last_nonce ciphertext_id expected_id := by
  intro nonce' last_nonce'
  rfl

/-- Changing either identifier cannot affect the result either. -/
def idIndependent_prop (nonce last_nonce ciphertext_id expected_id : Int) : Prop :=
  ∀ ciphertext_id' expected_id' : Int,
    unsafeNonceReuse nonce last_nonce ciphertext_id expected_id =
      unsafeNonceReuse nonce last_nonce ciphertext_id' expected_id'

theorem idIndependent_thm (nonce last_nonce ciphertext_id expected_id : Int) :
    idIndependent_prop nonce last_nonce ciphertext_id expected_id := by
  intro ciphertext_id' expected_id'
  rfl

/-- Exact reuse of the last nonce is accepted. -/
def reusedNonceAccepted_prop (nonce last_nonce ciphertext_id expected_id : Int) : Prop :=
  nonce = last_nonce →
    unsafeNonceReuse nonce last_nonce ciphertext_id expected_id = true

theorem reusedNonceAccepted_thm (nonce last_nonce ciphertext_id expected_id : Int) :
    reusedNonceAccepted_prop nonce last_nonce ciphertext_id expected_id := by
  intro _hReuse
  rfl

/-- Even a nonce strictly older than the last nonce is accepted. -/
def staleNonceAccepted_prop (nonce last_nonce ciphertext_id expected_id : Int) : Prop :=
  nonce < last_nonce →
    unsafeNonceReuse nonce last_nonce ciphertext_id expected_id = true

theorem staleNonceAccepted_thm (nonce last_nonce ciphertext_id expected_id : Int) :
    staleNonceAccepted_prop nonce last_nonce ciphertext_id expected_id := by
  intro _hStale
  rfl

/-- The identifier mismatch from the second Python assertion is also accepted. -/
def mismatchedIdAccepted_prop (nonce last_nonce ciphertext_id expected_id : Int) : Prop :=
  ciphertext_id ≠ expected_id →
    unsafeNonceReuse nonce last_nonce ciphertext_id expected_id = true

theorem mismatchedIdAccepted_thm (nonce last_nonce ciphertext_id expected_id : Int) :
    mismatchedIdAccepted_prop nonce last_nonce ciphertext_id expected_id := by
  intro _hMismatch
  rfl

/-! ## Postcondition -/

/-- All properties concern the actual returned value of the implementation. -/
def Post_prop (nonce last_nonce ciphertext_id expected_id : Int) : Prop :=
  alwaysAccepts_prop nonce last_nonce ciphertext_id expected_id ∧
  nonceIndependent_prop nonce last_nonce ciphertext_id expected_id ∧
  idIndependent_prop nonce last_nonce ciphertext_id expected_id ∧
  reusedNonceAccepted_prop nonce last_nonce ciphertext_id expected_id ∧
  staleNonceAccepted_prop nonce last_nonce ciphertext_id expected_id ∧
  mismatchedIdAccepted_prop nonce last_nonce ciphertext_id expected_id

/-! ## Property-based tests

Each test exhausts the Cartesian product of the integers from -3 through 3.
The independence tests also exhaust all replacement pairs in that range.
These are executable bounded counterparts of the unbounded specifications,
not restrictions on the domains of the specifications or their proofs.
Implication checks include both vacuous and nonvacuous cases, with no discarded
samples. Each named property, including `Post_prop`, has its own PBT below.
-/

private def testIntegers : List Int :=
  (List.range 7).map (fun n => (n : Int) - 3)

private def allTestInputs (p : Int → Int → Int → Int → Bool) : Bool :=
  testIntegers.all fun nonce =>
    testIntegers.all fun last_nonce =>
      testIntegers.all fun ciphertext_id =>
        testIntegers.all fun expected_id =>
          p nonce last_nonce ciphertext_id expected_id

private def testNonceIndependence (nonce last_nonce ciphertext_id expected_id : Int) : Bool :=
  testIntegers.all fun nonce' =>
    testIntegers.all fun last_nonce' =>
      unsafeNonceReuse nonce last_nonce ciphertext_id expected_id ==
        unsafeNonceReuse nonce' last_nonce' ciphertext_id expected_id

private def testIdIndependence (nonce last_nonce ciphertext_id expected_id : Int) : Bool :=
  testIntegers.all fun ciphertext_id' =>
    testIntegers.all fun expected_id' =>
      unsafeNonceReuse nonce last_nonce ciphertext_id expected_id ==
        unsafeNonceReuse nonce last_nonce ciphertext_id' expected_id'

-- PBT: alwaysAccepts_prop, on 7^4 input tuples.
example : allTestInputs (fun n l c e => unsafeNonceReuse n l c e == true) = true := by
  native_decide

-- PBT: nonceIndependent_prop, on 7^6 input/replacement tuples.
example : allTestInputs testNonceIndependence = true := by native_decide

-- PBT: idIndependent_prop, on 7^6 input/replacement tuples.
example : allTestInputs testIdIndependence = true := by native_decide

-- PBT: reusedNonceAccepted_prop, including every equal-nonce pair in the range.
example : allTestInputs (fun n l c e =>
    decide (n = l → unsafeNonceReuse n l c e = true)) = true := by
  native_decide

-- PBT: staleNonceAccepted_prop, including all strict orderings in the range.
example : allTestInputs (fun n l c e =>
    decide (n < l → unsafeNonceReuse n l c e = true)) = true := by
  native_decide

-- PBT: mismatchedIdAccepted_prop, including all unequal identifier pairs.
example : allTestInputs (fun n l c e =>
    decide (c ≠ e → unsafeNonceReuse n l c e = true)) = true := by
  native_decide

/-- Boolean form of the entire postcondition, with bounded universal clauses. -/
private def testPost (n l c e : Int) : Bool :=
  (unsafeNonceReuse n l c e == true) &&
  testNonceIndependence n l c e &&
  testIdIndependence n l c e &&
  decide (n = l → unsafeNonceReuse n l c e = true) &&
  decide (n < l → unsafeNonceReuse n l c e = true) &&
  decide (c ≠ e → unsafeNonceReuse n l c e = true)

-- PBT: Post_prop. Pre is True, so every test tuple is admissible.
example : allTestInputs testPost = true := by native_decide

#eval allTestInputs testPost

/-! ## Correctness: the precondition implies the full postcondition -/

theorem unsafeNonceReuse_correct (nonce last_nonce ciphertext_id expected_id : Int) :
    Pre nonce last_nonce ciphertext_id expected_id →
      Post_prop nonce last_nonce ciphertext_id expected_id := by
  intro _hPre
  exact ⟨alwaysAccepts_thm nonce last_nonce ciphertext_id expected_id,
    nonceIndependent_thm nonce last_nonce ciphertext_id expected_id,
    idIndependent_thm nonce last_nonce ciphertext_id expected_id,
    reusedNonceAccepted_thm nonce last_nonce ciphertext_id expected_id,
    staleNonceAccepted_thm nonce last_nonce ciphertext_id expected_id,
    mismatchedIdAccepted_thm nonce last_nonce ciphertext_id expected_id⟩

/-! ## Imperative implementation -/

/-- A mutable return-value register; no input checks are performed. -/
def unsafeNonceReuseImperative
    (_nonce _last_nonce _ciphertext_id _expected_id : Int) : Bool := Id.run do
  let mut accepted := false
  accepted := true
  return accepted

/-! ## Imperative tests -/

example : unsafeNonceReuseImperative 5 10 42 42 = true := by native_decide
example : unsafeNonceReuseImperative 5 10 42 99 = true := by native_decide
example : unsafeNonceReuseImperative 0 100 1 1 = true := by native_decide
example : unsafeNonceReuseImperative 10 10 42 99 = true := by native_decide
example : unsafeNonceReuseImperative (-5) (-1) (-42) 99 = true := by native_decide

#eval unsafeNonceReuseImperative 5 10 42 42
#eval unsafeNonceReuseImperative 5 10 42 99
#eval unsafeNonceReuseImperative 0 100 1 1

-- Bounded cross-implementation test, in addition to the universal proof below.
example : allTestInputs (fun n l c e =>
    unsafeNonceReuse n l c e == unsafeNonceReuseImperative n l c e) = true := by
  native_decide

/-! ## Functional-imperative equivalence -/

theorem unsafeNonceReuse_equiv (nonce last_nonce ciphertext_id expected_id : Int) :
    unsafeNonceReuse nonce last_nonce ciphertext_id expected_id =
      unsafeNonceReuseImperative nonce last_nonce ciphertext_id expected_id := by
  rfl

end UnsafeNonceReuse
end Agent
