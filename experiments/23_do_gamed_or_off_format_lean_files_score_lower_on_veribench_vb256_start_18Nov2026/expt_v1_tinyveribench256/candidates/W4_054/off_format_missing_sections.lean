import Mathlib

namespace Gold
namespace SafeSigPerm

def safeSigPermGrant (appCert ownerCert : Nat) : Bool :=
  appCert == ownerCert

example : safeSigPermGrant 5 5 = true := by native_decide
#eval safeSigPermGrant 5 5

example : safeSigPermGrant 1 2 = false := by native_decide
#eval safeSigPermGrant 1 2

example : safeSigPermGrant 0 999 = false := by native_decide
#eval safeSigPermGrant 0 999

example : safeSigPermGrant 0 0 = true := by native_decide
#eval safeSigPermGrant 0 0

example : safeSigPermGrant 42 42 = true := by native_decide

example : safeSigPermGrant 99999 99999 = true := by native_decide

example : safeSigPermGrant 1 99999 = false := by native_decide

example : safeSigPermGrant 99998 99999 = false := by native_decide

theorem safeSigPermGrant_self (c : Nat) :
    safeSigPermGrant c c = true := by
  simp [safeSigPermGrant]

theorem safeSigPermGrant_of_ne (appCert ownerCert : Nat)
    (hne : appCert ≠ ownerCert) :
    safeSigPermGrant appCert ownerCert = false := by
  simp [safeSigPermGrant, hne]

theorem safeSigPermGrant_eq_of_true (ownerCert k : Nat)
    (hk : safeSigPermGrant k ownerCert = true) :
    k = ownerCert := by
  simp [safeSigPermGrant] at hk
  exact_mod_cast hk

end SafeSigPerm
end Gold
