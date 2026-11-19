/-!
# Safe certificate-chain status check

Translation of the Python program `safe_cert_chain`.

The function models a certificate-chain status using an integer: it returns `true`
for a positive `caSignature` and `false` otherwise. No cryptographic signature or
certificate chain is verified.
-/

/-- Return `true` if `caSignature` is greater than zero, otherwise `false`.
This integer status check does not verify a cryptographic signature or certificate chain. -/
def safeCertChain (caSignature : Int) : Bool :=
  decide (caSignature > 0)

/-- Run the fixed examples from the Python `check` function. Returns `true` exactly
when every example matches (Python raised `AssertionError` on a mismatch). -/
def check (candidate : Int → Bool) : Bool :=
  candidate 12345 == true &&
  candidate 0 == false &&
  candidate 1 == true &&
  candidate 2 == true &&
  candidate (-1) == false

/-! ## The fixed examples -/

example : safeCertChain 12345 = true := by decide
example : safeCertChain 0 = false := by decide
example : safeCertChain 1 = true := by decide
example : safeCertChain 2 = true := by decide
example : safeCertChain (-1) = false := by decide

/-! ## Specification theorems -/

/-- `safeCertChain` accepts exactly the positive integers. -/
theorem safeCertChain_iff (x : Int) : safeCertChain x = true ↔ 0 < x := by
  simp [safeCertChain]

/-- `safeCertChain` rejects exactly the non-positive integers. -/
theorem safeCertChain_false_iff (x : Int) : safeCertChain x = false ↔ x ≤ 0 := by
  rw [← Bool.not_eq_true, safeCertChain_iff]
  constructor
  · intro h
    omega
  · intro h h'
    omega

/-- Zero is never accepted. -/
theorem safeCertChain_zero : safeCertChain 0 = false := by decide

/-- Every positive value is accepted. -/
theorem safeCertChain_of_pos {x : Int} (h : 0 < x) : safeCertChain x = true :=
  (safeCertChain_iff x).2 h

/-- Every non-positive value is rejected. -/
theorem safeCertChain_of_nonpos {x : Int} (h : x ≤ 0) : safeCertChain x = false :=
  (safeCertChain_false_iff x).2 h

/-- Acceptance is monotone: raising an accepted value keeps it accepted. -/
theorem safeCertChain_mono {x y : Int} (hxy : x ≤ y) (hx : safeCertChain x = true) :
    safeCertChain y = true := by
  rw [safeCertChain_iff] at hx ⊢
  omega

/-- Every successor of a natural number is accepted. -/
theorem safeCertChain_natCast_succ (n : Nat) : safeCertChain ((n : Int) + 1) = true := by
  rw [safeCertChain_iff]
  omega

/-- Negating an accepted value always yields a rejected value. -/
theorem safeCertChain_neg_of_accepted {x : Int} (h : safeCertChain x = true) :
    safeCertChain (-x) = false := by
  rw [safeCertChain_iff] at h
  rw [safeCertChain_false_iff]
  omega

/-! ## The test harness -/

/-- Any candidate meeting the specification "accept exactly the positive integers"
passes `check`. -/
theorem check_of_spec (c : Int → Bool) (hc : ∀ x, c x = true ↔ 0 < x) :
    check c = true := by
  have h1 : c 12345 = true := (hc 12345).2 (by decide)
  have h2 : c 0 = false := by
    rw [← Bool.not_eq_true, hc]
    decide
  have h3 : c 1 = true := (hc 1).2 (by decide)
  have h4 : c 2 = true := (hc 2).2 (by decide)
  have h5 : c (-1) = false := by
    rw [← Bool.not_eq_true, hc]
    decide
  simp [check, h1, h2, h3, h4, h5]

/-- `safeCertChain` passes the fixed tests (Python: `assert check(safe_cert_chain)`). -/
theorem check_safeCertChain : check safeCertChain = true :=
  check_of_spec safeCertChain safeCertChain_iff

/-- The same result, checked by direct evaluation. -/
example : check safeCertChain = true := by decide

#eval if check safeCertChain then "All tests passed." else "Candidate failed tests"

-- TL;DR: `safeCertChain` returns `decide (x > 0)`; the theorems prove it accepts exactly
-- the positive integers, prove that acceptance is monotone, and prove it passes the
-- Python test cases. This file was not compiled in this session because no shell was available.
