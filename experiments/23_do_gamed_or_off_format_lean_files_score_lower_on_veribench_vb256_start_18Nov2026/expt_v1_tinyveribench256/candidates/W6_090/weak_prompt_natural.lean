/-!
# Unsafe certificate-chain validation (toy model)

Lean 4 translation of a Python toy certificate-chain check. It returns `true`
without looking at the supplied certificate authority (CA) signature value.
It verifies no signature and validates no certificate chain.

The theorems below state this insecurity formally: the check accepts every
signature, including any signature that a validity specification rejects.
-/

namespace UnsafeCertChain

/-- Return `true` regardless of `caSignature`. The supplied value is ignored.
No CA signature or certificate chain is verified. -/
def unsafeCertChain (_caSignature : Int) : Bool := true

/-- The fixed example inputs used by the Python `check`. -/
def testInputs : List Int := [12345, 0, 1, 2, 3]

/-- Run the fixed examples. Returns `true` exactly when every example passes.
The Python version raises `AssertionError` on a failure; here a failure gives `false`. -/
def check (candidate : Int → Bool) : Bool :=
  testInputs.all candidate

/-- Mirrors the Python top-level `assert` and `print`. -/
def main : IO Unit := do
  unless check unsafeCertChain do
    throw <| IO.userError "Candidate failed tests"
  IO.println "All tests passed."

/-! ## Behavior of `unsafeCertChain` -/

/-- Every CA signature is accepted. -/
theorem unsafeCertChain_eq_true (caSignature : Int) :
    unsafeCertChain caSignature = true := rfl

/-- The function is the constant `true` function. -/
theorem unsafeCertChain_eq_const : unsafeCertChain = fun _ => true := rfl

/-- The output does not depend on the signature: any two inputs give the same result. -/
theorem unsafeCertChain_ignores_signature (s t : Int) :
    unsafeCertChain s = unsafeCertChain t := rfl

/-- No signature is ever rejected. -/
theorem unsafeCertChain_never_rejects :
    ¬ ∃ caSignature : Int, unsafeCertChain caSignature = false := by
  intro ⟨caSignature, h⟩
  simp [unsafeCertChain] at h

/-- A forged signature that differs from the expected one is still accepted. -/
theorem unsafeCertChain_accepts_forged (expected forged : Int)
    (_hne : forged ≠ expected) : unsafeCertChain forged = true := rfl

/-! ## Insecurity against any validity specification -/

/-- For any validity predicate with at least one invalid signature,
`unsafeCertChain` accepts an invalid signature. -/
theorem unsafeCertChain_accepts_invalid (isValid : Int → Prop)
    (h : ∃ s, ¬ isValid s) : ∃ s, ¬ isValid s ∧ unsafeCertChain s = true :=
  h.elim fun s hs => ⟨s, hs, rfl⟩

/-- `unsafeCertChain` is unsound for any validity predicate that rejects
some signature: acceptance does not imply validity. -/
theorem unsafeCertChain_unsound (isValid : Int → Prop)
    (h : ∃ s, ¬ isValid s) : ¬ ∀ s, unsafeCertChain s = true → isValid s :=
  fun hsound => h.elim fun s hs => hs (hsound s rfl)

/-! ## Behavior of `check` -/

/-- The Python test suite passes for `unsafeCertChain`. -/
theorem check_unsafeCertChain : check unsafeCertChain = true := rfl

/-- `check` passes exactly when the candidate accepts every fixed example. -/
theorem check_iff (candidate : Int → Bool) :
    check candidate = true ↔ ∀ x ∈ testInputs, candidate x = true := by
  simp [check]

/-- `check` is not trivial: a candidate that rejects everything fails it. -/
theorem check_reject_all : check (fun _ => false) = false := rfl

end UnsafeCertChain

-- TL;DR: Lean 4 port of `unsafe_cert_chain` plus `check`/`main`, with theorems proving it
-- accepts every signature (including forged/invalid ones) and that the fixed tests pass.
