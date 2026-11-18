import Mathlib

namespace Gold
namespace SafeDnsSpoofing

def safeDnsSpoofing (_queryDomain : String) (responseIp responseTxid expectedTxid : Nat)
    (dnssecSignature trustedKey : Nat) : Bool × Nat :=
  if responseTxid ≠ expectedTxid then
    (false, 0)
  else
    -- Simplified DNSSEC signature: (responseIp + trustedKey * 37) mod 2^32
    let expectedSig := (responseIp + trustedKey * 37) % (2^32)
    if dnssecSignature == expectedSig then
      (true, responseIp)
    else
      (false, 0)

def computeDnssecSignature (responseIp trustedKey : Nat) : Nat :=
  (responseIp + trustedKey * 37) % (2^32)

def TRUSTED_KEY : Nat := 0x42424242
def LEGITIMATE_IP : Nat := 0xC0A80101
def ATTACKER_IP : Nat := 0xDEADBEEF
def CORRECT_TXID : Nat := 0x1234
def WRONG_TXID : Nat := 0x5678
def LEGITIMATE_SIG : Nat := computeDnssecSignature LEGITIMATE_IP TRUSTED_KEY
def FORGED_SIG : Nat := 0x99999999
def ZERO_SIG : Nat := computeDnssecSignature 0 TRUSTED_KEY

example : safeDnsSpoofing "bank.com" LEGITIMATE_IP CORRECT_TXID CORRECT_TXID LEGITIMATE_SIG
    TRUSTED_KEY = (true, LEGITIMATE_IP) := by native_decide
#eval safeDnsSpoofing "bank.com" LEGITIMATE_IP CORRECT_TXID CORRECT_TXID LEGITIMATE_SIG TRUSTED_KEY

example : safeDnsSpoofing "bank.com" LEGITIMATE_IP WRONG_TXID CORRECT_TXID LEGITIMATE_SIG
    TRUSTED_KEY = (false, 0) := by native_decide
#eval safeDnsSpoofing "bank.com" LEGITIMATE_IP WRONG_TXID CORRECT_TXID LEGITIMATE_SIG TRUSTED_KEY

example : safeDnsSpoofing "bank.com" ATTACKER_IP CORRECT_TXID CORRECT_TXID FORGED_SIG
    TRUSTED_KEY = (false, 0) := by native_decide
#eval safeDnsSpoofing "bank.com" ATTACKER_IP CORRECT_TXID CORRECT_TXID FORGED_SIG TRUSTED_KEY

example : safeDnsSpoofing "" 0 0x0000 0x0000 ZERO_SIG TRUSTED_KEY = (true, 0) := by
  native_decide
#eval safeDnsSpoofing "" 0 0x0000 0x0000 ZERO_SIG TRUSTED_KEY

example : safeDnsSpoofing "" 0 0x0000 0x0000 0 TRUSTED_KEY = (false, 0) := by native_decide
#eval safeDnsSpoofing "" 0 0x0000 0x0000 0 TRUSTED_KEY

example : safeDnsSpoofing "example.org" 0x08080808 0xABCD 0xABCD
    (computeDnssecSignature 0x08080808 TRUSTED_KEY) TRUSTED_KEY = (true, 0x08080808) := by
  native_decide

example : safeDnsSpoofing "bank.com" ATTACKER_IP CORRECT_TXID CORRECT_TXID LEGITIMATE_SIG
    TRUSTED_KEY = (false, 0) := by native_decide

example : safeDnsSpoofing "bank.com" LEGITIMATE_IP CORRECT_TXID CORRECT_TXID (LEGITIMATE_SIG + 1)
    TRUSTED_KEY = (false, 0) := by native_decide

example : safeDnsSpoofing "bank.com" LEGITIMATE_IP (CORRECT_TXID + 1) CORRECT_TXID LEGITIMATE_SIG
    TRUSTED_KEY = (false, 0) := by native_decide

theorem safeDnsSpoofing_spec (q : String) (ip rt et sig k : Nat) :
    safeDnsSpoofing q ip rt et sig k =
      if rt = et ∧ sig = computeDnssecSignature ip k then (true, ip) else (false, 0) := by
  unfold safeDnsSpoofing computeDnssecSignature
  generalize (ip + k * 37) % 2 ^ 32 = s
  by_cases h1 : rt = et <;> by_cases h2 : sig = s <;> simp [h1, h2]

theorem accepted_requires_valid_txid_and_signature (queryDomain : String)
    (responseIp responseTxid expectedTxid dnssecSignature trustedKey : Nat)
    (h : (safeDnsSpoofing queryDomain responseIp responseTxid expectedTxid dnssecSignature
      trustedKey).1 = true) :
    responseTxid = expectedTxid ∧
      dnssecSignature = computeDnssecSignature responseIp trustedKey := by
  rw [safeDnsSpoofing_spec] at h
  split at h
  · assumption
  · simp at h

theorem forged_response_rejected (queryDomain : String)
    (attackerIp legitimateIp responseTxid expectedTxid forgedSig trustedKey : Nat)
    (_hIp : attackerIp ≠ legitimateIp)
    (hForged : forgedSig ≠ computeDnssecSignature attackerIp trustedKey)
    (_hTxid : responseTxid = expectedTxid) :
    (safeDnsSpoofing queryDomain attackerIp responseTxid expectedTxid forgedSig
      trustedKey).1 = false := by
  rw [safeDnsSpoofing_spec]
  split
  · next h => exact absurd h.2 hForged
  · simp

theorem signature_deterministic_in_key (responseIp trustedKey1 trustedKey2 : Nat)
    (hKeys : trustedKey1 = trustedKey2) :
    computeDnssecSignature responseIp trustedKey1 =
      computeDnssecSignature responseIp trustedKey2 := by
  rw [hKeys]

end SafeDnsSpoofing
end Gold
