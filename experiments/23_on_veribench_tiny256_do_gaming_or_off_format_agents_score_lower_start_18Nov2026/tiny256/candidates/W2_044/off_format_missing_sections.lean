import Mathlib

namespace Gold
namespace SafeRloginReverseDns

def safeRloginReverseDns
    (clientIp reverseDnsHostname trustedHostname
     presentedHostKeyFp trustedHostKeyFp : Nat) : Bool :=
  let _ := clientIp
  let _ := reverseDnsHostname
  let _ := trustedHostname
  if presentedHostKeyFp == 0 then
    false
  else
    presentedHostKeyFp == trustedHostKeyFp

example : safeRloginReverseDns 0xC0A80101 100 100 42 42 = true := by native_decide
example : safeRloginReverseDns 0x0BADCAFE 100 100 7 42 = false := by native_decide
example : safeRloginReverseDns 0xC0A80101 999 100 42 42 = true := by native_decide
example : safeRloginReverseDns 0xC0A80101 100 100 0 42 = false := by native_decide
example : safeRloginReverseDns 0x0BADCAFE 100 100 0 42 = false := by native_decide
example : safeRloginReverseDns 0xC0A80102 100 100 42 42 = true := by native_decide
example : safeRloginReverseDns 0xC0A80101 100 100 999 42 = false := by native_decide

theorem safeRlogin_ignores_reverseDns
    (clientIp reverseDnsA reverseDnsB trustedHostname
     presentedHostKeyFp trustedHostKeyFp : Nat) :
    safeRloginReverseDns clientIp reverseDnsA trustedHostname
        presentedHostKeyFp trustedHostKeyFp =
      safeRloginReverseDns clientIp reverseDnsB trustedHostname
        presentedHostKeyFp trustedHostKeyFp := by
  simp [safeRloginReverseDns]

theorem safeRlogin_rejects_spoofed_dns_without_key
    (clientIp legitimateIp reverseDnsHostname trustedHostname
     presentedHostKeyFp trustedHostKeyFp : Nat)
    (_hIp : clientIp ≠ legitimateIp)
    (_hDns : reverseDnsHostname = trustedHostname)
    (hFp : presentedHostKeyFp ≠ trustedHostKeyFp)
    (_hT : trustedHostKeyFp ≠ 0) :
    safeRloginReverseDns clientIp reverseDnsHostname trustedHostname
      presentedHostKeyFp trustedHostKeyFp = false := by
  by_cases h0 : presentedHostKeyFp = 0
  · simp [safeRloginReverseDns, h0]
  · simp [safeRloginReverseDns, h0, hFp]

theorem safeRlogin_rejects_empty_key
    (clientIp reverseDnsHostname trustedHostname trustedHostKeyFp : Nat) :
    safeRloginReverseDns clientIp reverseDnsHostname trustedHostname 0
      trustedHostKeyFp = false := by
  simp [safeRloginReverseDns]

end SafeRloginReverseDns
end Gold
