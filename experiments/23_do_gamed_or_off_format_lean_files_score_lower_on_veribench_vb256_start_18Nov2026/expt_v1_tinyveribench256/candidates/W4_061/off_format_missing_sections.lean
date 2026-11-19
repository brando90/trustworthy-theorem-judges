import Mathlib
namespace Gold

namespace SafeCookieDomain

def safeCookieDomain (cookieDomain currentDomain : Nat) : Bool :=
  cookieDomain == currentDomain

example : safeCookieDomain 5 5 = true := by native_decide

example : safeCookieDomain 1 2 = false := by native_decide

example : safeCookieDomain 0 999 = false := by native_decide

example : safeCookieDomain 0 0 = true := by native_decide

example : safeCookieDomain 42 42 = true := by native_decide

example : safeCookieDomain 99999 99999 = true := by native_decide

example : safeCookieDomain 1 99999 = false := by native_decide

example : safeCookieDomain 99998 99999 = false := by native_decide

theorem safeCookieDomain_self_true (d : Nat) : safeCookieDomain d d = true := by
  simp [safeCookieDomain]

theorem safeCookieDomain_false_of_ne (cookieDomain currentDomain : Nat)
    (hne : cookieDomain ≠ currentDomain) :
    safeCookieDomain cookieDomain currentDomain = false := by
  simp [safeCookieDomain, hne]

theorem eq_of_safeCookieDomain_true (cookieDomain currentDomain : Nat)
    (h : safeCookieDomain cookieDomain currentDomain = true) :
    cookieDomain = currentDomain := by
  simp [safeCookieDomain] at h
  exact_mod_cast h

end SafeCookieDomain
end Gold
