import Mathlib

namespace Gold
namespace SafeArpResponse

def safeArpResponse (responseIp expectedIp : Nat) : Bool :=
  responseIp == expectedIp

example : safeArpResponse 42 42 = true := by native_decide
example : safeArpResponse 0 99 = false := by native_decide
example : safeArpResponse 12345 67890 = false := by native_decide
example : safeArpResponse 0 0 = true := by native_decide
example : safeArpResponse 99 99 = true := by native_decide
example : safeArpResponse 99999 99999 = true := by native_decide
example : safeArpResponse 1 99999 = false := by native_decide
example : safeArpResponse 99998 99999 = false := by native_decide

theorem safeArpResponse_self (ip : Nat) :
    safeArpResponse ip ip = true := by
  simp [safeArpResponse]

theorem safeArpResponse_of_ne (responseIp expectedIp : Nat)
    (hne : responseIp ≠ expectedIp) :
    safeArpResponse responseIp expectedIp = false := by
  simp [safeArpResponse, hne]

theorem eq_of_safeArpResponse (expectedIp k : Nat)
    (hk : safeArpResponse k expectedIp = true) :
    k = expectedIp := by
  simp [safeArpResponse] at hk
  exact_mod_cast hk

end SafeArpResponse
end Gold
