import Mathlib
namespace Agent

/-!
# Safe OCSP stapling

Exact integer/Boolean model of `safe_ocsp_stapled` from the Python program.
The server supplies a pre-fetched stapled response: a positive response accepts
its certificate; a zero or negative response rejects it. The second result is
always false, representing that the CA does not learn the browser's visit.
Neither the certificate serial nor the server domain affects the result.

Python's unbounded integers are modeled by `Int`, including negative inputs.
The source has no network operations; its privacy claim is represented by the
returned flag, not by a separate model of a network protocol.
-/

namespace «109_unsafeOcspPrivacyLeak_safe»

-- Functional implementation.
def safe_ocsp_stapled (_cert_serial : Int) (stapled_response : Int)
    (_server_domain : Int) : Bool × Bool :=
  let cert_valid := decide (stapled_response > 0)
  let ca_learns_visit := false
  (cert_valid, ca_learns_visit)

-- The source's `check` ignores its candidate argument. Its fixed assertions
-- are expressed as an executable conjunction here.
def check (_candidate : Int → Int → Int → Bool × Bool) : Bool :=
  (safe_ocsp_stapled 123 1 456 == (true, false)) &&
  (safe_ocsp_stapled 123 0 456 == (false, false)) &&
  (safe_ocsp_stapled 999 100 1 == (true, false))

-- Unit tests: the three original tests and negative-input coverage.
example : safe_ocsp_stapled 123 1 456 = (true, false) := by native_decide
example : safe_ocsp_stapled 123 0 456 = (false, false) := by native_decide
example : safe_ocsp_stapled 999 100 1 = (true, false) := by native_decide
example : safe_ocsp_stapled (-123) (-7) (-456) = (false, false) := by native_decide
example : safe_ocsp_stapled (-123) 1 (-456) = (true, false) := by native_decide
example : check safe_ocsp_stapled = true := by native_decide

#eval safe_ocsp_stapled 123 1 456
#eval safe_ocsp_stapled 123 0 456
#eval safe_ocsp_stapled 999 100 1
#eval check safe_ocsp_stapled

-- All integer arguments are admissible; no positivity assumption is imposed.
def Pre (_cert_serial _stapled_response _server_domain : Int) : Prop := True

-- Exact acceptance criterion, in both directions.
def acceptance_prop (cert_serial stapled_response server_domain : Int) : Prop :=
  (safe_ocsp_stapled cert_serial stapled_response server_domain).1 = true ↔
    0 < stapled_response

theorem acceptance_thm (cert_serial stapled_response server_domain : Int) :
    acceptance_prop cert_serial stapled_response server_domain := by
  simp [acceptance_prop, safe_ocsp_stapled]

-- Missing and negative staples are rejected, and only those are rejected.
def rejection_prop (cert_serial stapled_response server_domain : Int) : Prop :=
  (safe_ocsp_stapled cert_serial stapled_response server_domain).1 = false ↔
    stapled_response ≤ 0

theorem rejection_thm (cert_serial stapled_response server_domain : Int) :
    rejection_prop cert_serial stapled_response server_domain := by
  simp [rejection_prop, safe_ocsp_stapled]

-- Privacy holds regardless of whether the certificate is accepted.
def privacy_prop (cert_serial stapled_response server_domain : Int) : Prop :=
  (safe_ocsp_stapled cert_serial stapled_response server_domain).2 = false

theorem privacy_thm (cert_serial stapled_response server_domain : Int) :
    privacy_prop cert_serial stapled_response server_domain := by
  rfl

-- Any simultaneous changes to the two unused identifiers preserve the result.
def identifiers_irrelevant_prop (cert_serial stapled_response server_domain : Int) : Prop :=
  ∀ other_serial other_domain : Int,
    safe_ocsp_stapled cert_serial stapled_response server_domain =
      safe_ocsp_stapled other_serial stapled_response other_domain

theorem identifiers_irrelevant_thm (cert_serial stapled_response server_domain : Int) :
    identifiers_irrelevant_prop cert_serial stapled_response server_domain := by
  intro other_serial other_domain
  rfl

-- The postcondition combines every behavioral property above.
def Post_prop (cert_serial stapled_response server_domain : Int) : Prop :=
  acceptance_prop cert_serial stapled_response server_domain ∧
  rejection_prop cert_serial stapled_response server_domain ∧
  privacy_prop cert_serial stapled_response server_domain ∧
  identifiers_irrelevant_prop cert_serial stapled_response server_domain

/-! ## Property-based tests

These checks use executable Boolean forms directly, not Decidable instances
for the specifications. `Pre` is always true, so no samples are discarded.
The universally quantified alternate identifiers in the postcondition are
sampled as additional inputs. These tests are evidence, not theorem proofs.
-/

-- PBT for acceptance_prop: the acceptance bit equals the positivity test.
#eval Plausible.Testable.check (∀ c r d : Int,
  (safe_ocsp_stapled c r d).1 = decide (0 < r))

-- PBT for rejection_prop: the rejection bit equals the nonpositivity test.
#eval Plausible.Testable.check (∀ c r d : Int,
  decide ((safe_ocsp_stapled c r d).1 = false) = decide (r ≤ 0))

-- PBT for privacy_prop.
#eval Plausible.Testable.check (∀ c r d : Int,
  (safe_ocsp_stapled c r d).2 = false)

-- PBT for identifiers_irrelevant_prop.
#eval Plausible.Testable.check (∀ c r d other_c other_d : Int,
  safe_ocsp_stapled c r d = safe_ocsp_stapled other_c r other_d)

-- Boolean form of the conjunction in Post_prop, at two alternate identifiers.
def postCheck (c r d other_c other_d : Int) : Bool :=
  ((safe_ocsp_stapled c r d).1 == decide (0 < r)) &&
  (decide ((safe_ocsp_stapled c r d).1 = false) == decide (r ≤ 0)) &&
  ((safe_ocsp_stapled c r d).2 == false) &&
  (safe_ocsp_stapled c r d == safe_ocsp_stapled other_c r other_d)

-- Randomized PBT for Post_prop, with its identifier quantifiers made explicit.
#eval Plausible.Testable.check (∀ c r d other_c other_d : Int,
  postCheck c r d other_c other_d = true)

-- Exhaustive small-domain PBT for Post_prop: all signs and the zero boundary,
-- together with larger positive/negative samples; all five inputs vary.
def pbtInputs : List Int :=
  (List.range 9).map (fun n => (n : Int) - 4) ++ [-100, 100]

example :
    pbtInputs.all (fun c =>
      pbtInputs.all (fun r =>
        pbtInputs.all (fun d =>
          pbtInputs.all (fun other_c =>
            pbtInputs.all (fun other_d => postCheck c r d other_c other_d))))) = true := by
  native_decide

-- Kernel-checked correctness for the entire unrestricted input domain.
theorem correctness_thm (cert_serial stapled_response server_domain : Int) :
    Pre cert_serial stapled_response server_domain →
      Post_prop cert_serial stapled_response server_domain := by
  intro _hpre
  exact ⟨acceptance_thm cert_serial stapled_response server_domain,
    rejection_thm cert_serial stapled_response server_domain,
    privacy_thm cert_serial stapled_response server_domain,
    identifiers_irrelevant_thm cert_serial stapled_response server_domain⟩

-- Imperative implementation: mutable acceptance state, no CA contact.
def safe_ocsp_stapled_imp (_cert_serial : Int) (stapled_response : Int)
    (_server_domain : Int) : Bool × Bool := Id.run do
  let mut cert_valid := false
  if stapled_response > 0 then
    cert_valid := true
  let ca_learns_visit := false
  return (cert_valid, ca_learns_visit)

-- Imperative tests, including the original harness.
example : safe_ocsp_stapled_imp 123 1 456 = (true, false) := by native_decide
example : safe_ocsp_stapled_imp 123 0 456 = (false, false) := by native_decide
example : safe_ocsp_stapled_imp 999 100 1 = (true, false) := by native_decide
example : safe_ocsp_stapled_imp (-123) (-7) (-456) = (false, false) := by native_decide
example :
    (safe_ocsp_stapled_imp 123 1 456 == (true, false)) &&
    (safe_ocsp_stapled_imp 123 0 456 == (false, false)) &&
    (safe_ocsp_stapled_imp 999 100 1 == (true, false)) = true := by
  native_decide

#eval safe_ocsp_stapled_imp 123 1 456
#eval safe_ocsp_stapled_imp 123 0 456
#eval safe_ocsp_stapled_imp 999 100 1

-- Extra randomized differential test over all three input positions.
#eval Plausible.Testable.check (∀ c r d : Int,
  safe_ocsp_stapled c r d = safe_ocsp_stapled_imp c r d)

-- Equivalence is proved independently of all executable tests.
theorem functional_eq_imperative_thm (cert_serial stapled_response server_domain : Int) :
    safe_ocsp_stapled cert_serial stapled_response server_domain =
      safe_ocsp_stapled_imp cert_serial stapled_response server_domain := by
  by_cases h : 0 < stapled_response <;>
    simp [safe_ocsp_stapled, safe_ocsp_stapled_imp, h]

end «109_unsafeOcspPrivacyLeak_safe»
end Agent
