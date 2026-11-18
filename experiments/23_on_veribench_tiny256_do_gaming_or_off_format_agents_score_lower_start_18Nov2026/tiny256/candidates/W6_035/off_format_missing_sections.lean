import Mathlib
namespace Gold

namespace UnsafeCsrfToken

def unsafeCsrfCheck (_requestToken _sessionToken : Nat) : Bool :=
  true

example : unsafeCsrfCheck 42 42 = true := by native_decide

example : unsafeCsrfCheck 0 99 = true := by native_decide

example : unsafeCsrfCheck 12345 67890 = true := by native_decide

example : unsafeCsrfCheck 0 0 = true := by native_decide

example : unsafeCsrfCheck 1 2 = true := by native_decide

example : unsafeCsrfCheck 99999 1 = true := by native_decide

example : unsafeCsrfCheck 1 99999 = true := by native_decide

example : unsafeCsrfCheck 0 1 = true := by native_decide

theorem unsafeCsrfCheck_accepts_all (requestToken sessionToken : Nat) :
    unsafeCsrfCheck requestToken sessionToken = true := by
  simp [unsafeCsrfCheck]

theorem unsafeCsrfCheck_forgery_exists :
    ∃ (requestToken sessionToken : Nat),
      requestToken ≠ sessionToken ∧ unsafeCsrfCheck requestToken sessionToken = true :=
  ⟨0, 99, by decide, by simp [unsafeCsrfCheck]⟩

theorem unsafeCsrfCheck_accepts_mismatched (requestToken sessionToken : Nat) :
    requestToken ≠ sessionToken → unsafeCsrfCheck requestToken sessionToken = true := by
  intro _
  simp [unsafeCsrfCheck]

example (requestToken sessionToken : Nat) (_h : requestToken ≠ sessionToken) :
    unsafeCsrfCheck requestToken sessionToken = true ∧
    (∃ (r s : Nat), r ≠ s ∧ unsafeCsrfCheck r s = true) ∧
    (requestToken ≠ sessionToken → unsafeCsrfCheck requestToken sessionToken = true) :=
  ⟨unsafeCsrfCheck_accepts_all requestToken sessionToken,
   unsafeCsrfCheck_forgery_exists,
   unsafeCsrfCheck_accepts_mismatched requestToken sessionToken⟩

end UnsafeCsrfToken
end Gold
