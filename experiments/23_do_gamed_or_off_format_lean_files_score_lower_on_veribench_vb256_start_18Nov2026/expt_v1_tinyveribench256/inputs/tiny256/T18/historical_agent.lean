import Mathlib
namespace Agent

/-!
# Unsafe OAuth redirect validation

This file formalizes an OAuth redirect check that unconditionally accepts its
input.  Consequently, valid, malicious, unknown, and empty redirect URLs are
all accepted, independently of the client identifier and allowlist.
-/

namespace UnsafeOAuthRedirect126

/-! ## Functional implementation -/

/-- The vulnerable redirect check: none of its arguments are inspected. -/
def unsafeOAuthRedirect
    (_redirectUrl : String) (_clientId : String) (_allowedUrls : List String) : Bool :=
  true

/-! ## Functional unit tests -/

def testAllowedUrls : List String :=
  ["https://rp1.example.com/cb", "https://rp2.example.com/cb"]

example :
    unsafeOAuthRedirect "https://rp1.example.com/cb" "rp1" testAllowedUrls = true := by
  native_decide

example :
    unsafeOAuthRedirect "https://evil.com/steal" "rp1" testAllowedUrls = true := by
  native_decide

example :
    unsafeOAuthRedirect "https://rp3.com/cb" "rp1" testAllowedUrls = true := by
  native_decide

example : unsafeOAuthRedirect "" "rp1" testAllowedUrls = true := by
  native_decide

#eval unsafeOAuthRedirect "https://rp1.example.com/cb" "rp1" testAllowedUrls
#eval unsafeOAuthRedirect "https://evil.com/steal" "rp1" testAllowedUrls
#eval unsafeOAuthRedirect "https://rp3.com/cb" "rp1" testAllowedUrls
#eval unsafeOAuthRedirect "" "rp1" testAllowedUrls

/-! ## Specification and functional correctness -/

/-- The Python function imposes no precondition on its inputs. -/
def Pre (_redirectUrl : String) (_clientId : String) (_allowedUrls : List String) : Prop :=
  True

/-- Every redirect destination is accepted, including destinations off the allowlist. -/
def acceptsAnyRedirect_prop : Prop :=
  ∀ redirectUrl clientId allowedUrls,
    unsafeOAuthRedirect redirectUrl clientId allowedUrls = true

theorem acceptsAnyRedirect_thm : acceptsAnyRedirect_prop := by
  intro redirectUrl clientId allowedUrls
  rfl

/-- Changing the client identifier cannot affect the result. -/
def ignoresClientId_prop : Prop :=
  ∀ redirectUrl clientId₁ clientId₂ allowedUrls,
    unsafeOAuthRedirect redirectUrl clientId₁ allowedUrls =
      unsafeOAuthRedirect redirectUrl clientId₂ allowedUrls

theorem ignoresClientId_thm : ignoresClientId_prop := by
  intro redirectUrl clientId₁ clientId₂ allowedUrls
  rfl

/-- Changing the allowlist cannot affect the result. -/
def ignoresAllowedUrls_prop : Prop :=
  ∀ redirectUrl clientId allowedUrls₁ allowedUrls₂,
    unsafeOAuthRedirect redirectUrl clientId allowedUrls₁ =
      unsafeOAuthRedirect redirectUrl clientId allowedUrls₂

theorem ignoresAllowedUrls_thm : ignoresAllowedUrls_prop := by
  intro redirectUrl clientId allowedUrls₁ allowedUrls₂
  rfl

/-- The postcondition records unconditional acceptance and both ignored inputs. -/
def Post_prop : Prop :=
  acceptsAnyRedirect_prop ∧ ignoresClientId_prop ∧ ignoresAllowedUrls_prop

theorem correctness_thm
    (redirectUrl clientId : String) (allowedUrls : List String) :
    Pre redirectUrl clientId allowedUrls → Post_prop := by
  intro _hPre
  exact ⟨acceptsAnyRedirect_thm, ignoresClientId_thm, ignoresAllowedUrls_thm⟩

/-! ## Imperative implementation -/

/-- An imperative rendering of the Python body using mutable state. -/
def unsafeOAuthRedirectImperative
    (_redirectUrl : String) (_clientId : String) (_allowedUrls : List String) : Bool :=
  Id.run do
    let mut accepted := false
    accepted := true
    return accepted

/-! ## Imperative unit tests -/

example :
    unsafeOAuthRedirectImperative
      "https://rp1.example.com/cb" "rp1" testAllowedUrls = true := by
  native_decide

example :
    unsafeOAuthRedirectImperative
      "https://evil.com/steal" "rp1" testAllowedUrls = true := by
  native_decide

example :
    unsafeOAuthRedirectImperative
      "https://rp3.com/cb" "rp1" testAllowedUrls = true := by
  native_decide

example : unsafeOAuthRedirectImperative "" "rp1" testAllowedUrls = true := by
  native_decide

#eval unsafeOAuthRedirectImperative
  "https://rp1.example.com/cb" "rp1" testAllowedUrls
#eval unsafeOAuthRedirectImperative
  "https://evil.com/steal" "rp1" testAllowedUrls
#eval unsafeOAuthRedirectImperative
  "https://rp3.com/cb" "rp1" testAllowedUrls
#eval unsafeOAuthRedirectImperative "" "rp1" testAllowedUrls

/-! ## Functional/imperative equivalence -/

theorem functional_imperative_equivalence_thm
    (redirectUrl clientId : String) (allowedUrls : List String) :
    unsafeOAuthRedirect redirectUrl clientId allowedUrls =
      unsafeOAuthRedirectImperative redirectUrl clientId allowedUrls := by
  rfl

end UnsafeOAuthRedirect126
end Agent
