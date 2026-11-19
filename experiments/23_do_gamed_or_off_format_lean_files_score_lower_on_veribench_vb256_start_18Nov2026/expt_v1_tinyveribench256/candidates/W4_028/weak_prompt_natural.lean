/-!
# Safe DNS response handling (toy simulation)

Lean 4 translation of a Python program that decides whether to accept a DNS response. It checks
two things: the transaction ID matches, and an arithmetic "signature" word computed from
`(ip, trusted_key)` matches.

* `safeDnsSpoofing` returns `(true, responseIp)` when both checks pass. Otherwise it returns
  `(false, 0)`.
* The query domain is ignored.
* This is **not** cryptographic DNSSEC verification, and it updates no cache.

Python integers are unbounded and can be negative, so they are modelled as `Int`. With a positive
modulus, Python's `%` always returns a value in `[0, modulus)`. Lean's `%` on `Int` (`Int.emod`)
behaves the same way, so the arithmetic matches exactly.

Only core Lean 4 is used: no Mathlib, and the proofs use only `decide`, `omega` and `simp`.
This file was written without a Lean toolchain, so it has not been compiled. Check it with
`lean SafeDns.lean`.
-/

namespace SafeDns

/-! ## Translation -/

/-- The modulus `2 ** 32` that reduces the signature word. -/
def wordModulus : Int := 2 ^ 32

/-- The simulated DNS signature word: `responseIp` plus 37 times `trustedKey`, modulo `2 ^ 32`.
Mirrors the Python helper `_compute_dnssec_signature`. -/
def computeDnssecSignature (responseIp trustedKey : Int) : Int :=
  (responseIp + trustedKey * 37) % wordModulus

/-- Returns `(true, responseIp)` when `responseTxid = expectedTxid` and
`dnssecSignature = (responseIp + 37 * trustedKey) % 2 ^ 32`. Otherwise returns `(false, 0)`.
The query domain is ignored. This toy arithmetic check does not verify DNSSEC cryptographically
and does not update a cache. Mirrors the Python `safe_dns_spoofing`. -/
def safeDnsSpoofing (_queryDomain : String) (responseIp responseTxid expectedTxid
    dnssecSignature trustedKey : Int) : Bool × Int :=
  if responseTxid ≠ expectedTxid then
    (false, 0)
  else
    let expectedSig := computeDnssecSignature responseIp trustedKey
    if dnssecSignature = expectedSig then
      (true, responseIp)
    else
      (false, 0)

/-- `Bool` version of the Python `check`, which runs the five fixed examples. Python raises
`AssertionError` on a mismatch; here a mismatch makes the result `false`. -/
def check (candidate : String → Int → Int → Int → Int → Int → Bool × Int) : Bool :=
  candidate "bank.com" 3735928559 4660 4660 2576980377 1111638594 == (false, 0) &&
  candidate "" 0 0 0 0 1111638594 == (false, 0) &&
  candidate "example.org" 42 17 17 79 1 == (true, 42) &&
  candidate "" 0 0 0 0 0 == (true, 0) &&
  candidate "e" 1 1 1 1 1 == (false, 0)

/-! ## The Python test suite, as theorems -/

/-- All five assertions from the Python `check` hold. -/
theorem check_safeDnsSpoofing : check safeDnsSpoofing = true := by decide

-- Python-compatible modulo on a negative input: `(-1 + 0 * 37) % 2**32 == 4294967295`.
example : computeDnssecSignature (-1) 0 = 4294967295 := by decide

/-! ## Facts about the modulus -/

theorem wordModulus_eq : wordModulus = 4294967296 := by decide

theorem wordModulus_pos : 0 < wordModulus := by
  rw [wordModulus_eq]
  omega

/-! ## Facts about the signature word -/

/-- The signature is "`responseIp` plus 37 times `trustedKey`, modulo `2 ^ 32`", as the
docstring says. -/
theorem computeDnssecSignature_spec (ip k : Int) :
    computeDnssecSignature ip k = (ip + 37 * k) % wordModulus := by
  simp only [computeDnssecSignature, wordModulus_eq]
  omega

/-- The signature is always a 32-bit word. -/
theorem computeDnssecSignature_range (ip k : Int) :
    0 ≤ computeDnssecSignature ip k ∧ computeDnssecSignature ip k < wordModulus := by
  simp only [computeDnssecSignature, wordModulus_eq]
  constructor <;> omega

/-- Reducing the signature again changes nothing. -/
theorem computeDnssecSignature_emod (ip k : Int) :
    computeDnssecSignature ip k % wordModulus = computeDnssecSignature ip k := by
  simp only [computeDnssecSignature, wordModulus_eq]
  omega

/-- With key `0`, the signature of an in-range IP is the IP itself. -/
theorem computeDnssecSignature_zero_key (ip : Int) (h₀ : 0 ≤ ip) (h₁ : ip < wordModulus) :
    computeDnssecSignature ip 0 = ip := by
  rw [wordModulus_eq] at h₁
  simp only [computeDnssecSignature, wordModulus_eq]
  omega

/-- Collision in the IP: IPs that differ by `2 ^ 32` get the same signature. -/
theorem computeDnssecSignature_ip_periodic (ip k : Int) :
    computeDnssecSignature (ip + wordModulus) k = computeDnssecSignature ip k := by
  simp only [computeDnssecSignature, wordModulus_eq]
  omega

/-- Collision in the key: keys that differ by `2 ^ 32` produce the same signature. -/
theorem computeDnssecSignature_key_periodic (ip k : Int) :
    computeDnssecSignature ip (k + wordModulus) = computeDnssecSignature ip k := by
  simp only [computeDnssecSignature, wordModulus_eq]
  omega

/-! ## Facts about `safeDnsSpoofing` -/

/-- Closed form: the response is accepted exactly when both checks pass. -/
theorem safeDnsSpoofing_eq (d : String) (ip t e s k : Int) :
    safeDnsSpoofing d ip t e s k =
      if t = e ∧ s = computeDnssecSignature ip k then (true, ip) else (false, 0) := by
  by_cases h₁ : t = e <;> by_cases h₂ : s = computeDnssecSignature ip k <;>
    simp [safeDnsSpoofing, h₁, h₂]

/-- The query domain has no effect on the result. -/
theorem safeDnsSpoofing_ignores_domain (d₁ d₂ : String) (ip t e s k : Int) :
    safeDnsSpoofing d₁ ip t e s k = safeDnsSpoofing d₂ ip t e s k := rfl

/-- The only possible outputs are `(true, responseIp)` and `(false, 0)`. -/
theorem safeDnsSpoofing_cases (d : String) (ip t e s k : Int) :
    safeDnsSpoofing d ip t e s k = (true, ip) ∨ safeDnsSpoofing d ip t e s k = (false, 0) := by
  rw [safeDnsSpoofing_eq]
  by_cases h : t = e ∧ s = computeDnssecSignature ip k
  · left
    rw [if_pos h]
  · right
    rw [if_neg h]

/-- A transaction-ID mismatch is always rejected, whatever the signature is. -/
theorem safeDnsSpoofing_txid_mismatch (d : String) (ip t e s k : Int) (h : t ≠ e) :
    safeDnsSpoofing d ip t e s k = (false, 0) := by
  have hc : ¬ (t = e ∧ s = computeDnssecSignature ip k) := fun hc => h hc.1
  rw [safeDnsSpoofing_eq, if_neg hc]

/-- A wrong signature is always rejected, even when the transaction ID matches. -/
theorem safeDnsSpoofing_bad_signature (d : String) (ip t e s k : Int)
    (hs : s ≠ computeDnssecSignature ip k) :
    safeDnsSpoofing d ip t e s k = (false, 0) := by
  have hc : ¬ (t = e ∧ s = computeDnssecSignature ip k) := fun hc => hs hc.2
  rw [safeDnsSpoofing_eq, if_neg hc]

/-- With a matching transaction ID and the correct signature, the response IP is accepted. -/
theorem safeDnsSpoofing_accepts (d : String) (ip t k : Int) :
    safeDnsSpoofing d ip t t (computeDnssecSignature ip k) k = (true, ip) := by
  have hc : t = t ∧ computeDnssecSignature ip k = computeDnssecSignature ip k := ⟨rfl, rfl⟩
  rw [safeDnsSpoofing_eq, if_pos hc]

/-- The acceptance flag is `true` exactly when both checks pass. -/
theorem safeDnsSpoofing_accepted_iff (d : String) (ip t e s k : Int) :
    (safeDnsSpoofing d ip t e s k).1 = true ↔ t = e ∧ s = computeDnssecSignature ip k := by
  rw [safeDnsSpoofing_eq]
  by_cases h : t = e ∧ s = computeDnssecSignature ip k
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]
    exact ⟨fun h' => absurd h' (by simp), fun h' => absurd h' h⟩

/-- Every accepted response has a matching transaction ID. -/
theorem safeDnsSpoofing_accepted_txid (d : String) (ip t e s k : Int)
    (h : (safeDnsSpoofing d ip t e s k).1 = true) : t = e :=
  ((safeDnsSpoofing_accepted_iff d ip t e s k).mp h).1

/-- An accepted response returns the response IP unchanged. -/
theorem safeDnsSpoofing_accepted_snd (d : String) (ip t e s k : Int)
    (h : (safeDnsSpoofing d ip t e s k).1 = true) :
    (safeDnsSpoofing d ip t e s k).2 = ip := by
  rcases safeDnsSpoofing_cases d ip t e s k with hr | hr
  · simp [hr]
  · simp [hr] at h

/-- A rejected response never exposes an IP: its second component is `0`. -/
theorem safeDnsSpoofing_rejected_snd (d : String) (ip t e s k : Int)
    (h : (safeDnsSpoofing d ip t e s k).1 = false) :
    (safeDnsSpoofing d ip t e s k).2 = 0 := by
  rcases safeDnsSpoofing_cases d ip t e s k with hr | hr
  · simp [hr] at h
  · simp [hr]

/-- A signature outside the 32-bit range can never be accepted. -/
theorem safeDnsSpoofing_out_of_range_rejected (d : String) (ip t e s k : Int)
    (hs : s < 0 ∨ wordModulus ≤ s) :
    safeDnsSpoofing d ip t e s k = (false, 0) := by
  apply safeDnsSpoofing_bad_signature
  intro heq
  have hr := computeDnssecSignature_range ip k
  rw [← heq] at hr
  omega

/-- This is not cryptographic: a signature computed for `ip` is also accepted for
`ip + 2 ^ 32`. -/
theorem safeDnsSpoofing_accepts_colliding_ip (d : String) (ip t k : Int) :
    safeDnsSpoofing d (ip + wordModulus) t t (computeDnssecSignature ip k) k =
      (true, ip + wordModulus) := by
  have h := safeDnsSpoofing_accepts d (ip + wordModulus) t k
  rw [computeDnssecSignature_ip_periodic] at h
  exact h

-- Concrete collision: signature 79 (from the test case with IP 42) also accepts IP 42 + 2^32.
example : safeDnsSpoofing "example.org" 4294967338 17 17 79 1 = (true, 4294967338) := by decide

end SafeDns

/-- Mirrors the Python `if __name__ == "__main__":` block. -/
def main : IO Unit := do
  if SafeDns.check SafeDns.safeDnsSpoofing then
    IO.println "All tests passed."
  else
    throw <| IO.userError "check failed"

-- TLDR-end: [safe-dns-lean: translate + theorems] A faithful port using Int (Python-compatible
-- %), the 5 Python asserts proved by `decide`, and proved theorems: an accept-iff
-- characterization, rejection returns (false, 0), signatures lie in [0, 2^32), and collisions
-- at period 2^32. Not compiled here because no Lean toolchain was available.
