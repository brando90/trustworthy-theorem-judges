/-!
# Safe rlogin host-key check

Model host-key acceptance by requiring a nonempty presented fingerprint string equal to the
trusted fingerprint string. IP and hostname arguments are ignored. No cryptographic verification
is performed.

Translated from the Python function `safe_rlogin_reverse_dns` and its `check` harness.
-/

namespace SafeRlogin

/-- Return `false` for an empty presented fingerprint. Otherwise return whether the two supplied
fingerprint strings are equal. Ignore `clientIp` and both hostname arguments (reverse DNS is for
logging/display only). This comparison performs no cryptographic verification. -/
def safeRloginReverseDns
    (_clientIp : Int)
    (_reverseDnsHostname : String)
    (_trustedHostname : String)
    (presentedHostKeyFingerprint : String)
    (trustedHostKeyFingerprint : String) : Bool :=
  if presentedHostKeyFingerprint = "" then
    false  -- No host key presented: reject.
  else
    decide (presentedHostKeyFingerprint = trustedHostKeyFingerprint)

/-- Lean counterpart of the Python `check`: run the fixed examples and return `true` when all of
them match. Python raises `AssertionError` on a mismatch; here a mismatch makes the result
`false`. -/
def check (candidate : Int → String → String → String → String → Bool) : Bool :=
  (candidate 3232235777 "trusted.example.com" "trusted.example.com"
      "SHA256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
      "SHA256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" == true) &&
  (candidate 195939070 "trusted.example.com" "trusted.example.com"
      "SHA256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
      "SHA256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" == false) &&
  (candidate 3232235777 "wrong.reverse.dns" "trusted.example.com"
      "SHA256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
      "SHA256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" == true) &&
  (candidate 3232235777 "trusted.example.com" "trusted.example.com"
      ""
      "SHA256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" == false) &&
  (candidate 195939070 "trusted.example.com" "trusted.example.com"
      ""
      "SHA256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" == false)

/-! ## General theorems -/

/-- Full characterization of acceptance: accept exactly when the presented fingerprint is
nonempty and equal to the trusted fingerprint. -/
theorem safe_eq_true_iff (ip : Int) (r t p k : String) :
    safeRloginReverseDns ip r t p k = true ↔ p ≠ "" ∧ p = k := by
  unfold safeRloginReverseDns
  by_cases h : p = ""
  · simp [h]
  · simp [h]

/-- Full characterization of rejection: reject exactly when the presented fingerprint is empty
or differs from the trusted fingerprint. -/
theorem safe_eq_false_iff (ip : Int) (r t p k : String) :
    safeRloginReverseDns ip r t p k = false ↔ p = "" ∨ p ≠ k := by
  unfold safeRloginReverseDns
  by_cases h : p = ""
  · simp [h]
  · simp [h]

/-- The client IP and both hostname arguments never influence the decision, so a spoofed or
mismatched reverse-DNS hostname can neither grant nor deny access. -/
theorem ignores_ip_and_hostnames (ip₁ ip₂ : Int) (r₁ r₂ t₁ t₂ p k : String) :
    safeRloginReverseDns ip₁ r₁ t₁ p k = safeRloginReverseDns ip₂ r₂ t₂ p k := rfl

/-- An empty presented fingerprint is always rejected. -/
theorem reject_empty_presented (ip : Int) (r t k : String) :
    safeRloginReverseDns ip r t "" k = false := by
  simp [safeRloginReverseDns]

/-- In particular, two empty fingerprints do not authenticate. -/
theorem reject_both_empty (ip : Int) (r t : String) :
    safeRloginReverseDns ip r t "" "" = false :=
  reject_empty_presented ip r t ""

/-- An empty trusted fingerprint is never matched by any presented fingerprint. -/
theorem reject_empty_trusted (ip : Int) (r t p : String) :
    safeRloginReverseDns ip r t p "" = false := by
  rw [safe_eq_false_iff]
  by_cases h : p = ""
  · exact Or.inl h
  · exact Or.inr h

/-- A presented fingerprint that differs from the trusted one is rejected. -/
theorem reject_mismatch (ip : Int) (r t p k : String) (h : p ≠ k) :
    safeRloginReverseDns ip r t p k = false :=
  (safe_eq_false_iff ip r t p k).mpr (Or.inr h)

/-- A nonempty presented fingerprint equal to the trusted one is accepted. -/
theorem accept_match (ip : Int) (r t p : String) (hp : p ≠ "") :
    safeRloginReverseDns ip r t p p = true :=
  (safe_eq_true_iff ip r t p p).mpr ⟨hp, rfl⟩

/-- Soundness: acceptance implies the fingerprints are equal. -/
theorem eq_of_accept {ip : Int} {r t p k : String}
    (h : safeRloginReverseDns ip r t p k = true) : p = k :=
  ((safe_eq_true_iff ip r t p k).mp h).2

/-- Soundness: acceptance implies a nonempty fingerprint was presented. -/
theorem nonempty_of_accept {ip : Int} {r t p k : String}
    (h : safeRloginReverseDns ip r t p k = true) : p ≠ "" :=
  ((safe_eq_true_iff ip r t p k).mp h).1

/-- Acceptance also implies the trusted fingerprint is nonempty. -/
theorem trusted_nonempty_of_accept {ip : Int} {r t p k : String}
    (h : safeRloginReverseDns ip r t p k = true) : k ≠ "" := by
  have hpk := eq_of_accept h
  have hp := nonempty_of_accept h
  rw [← hpk]
  exact hp

/-- When both fingerprints are nonempty, the check is symmetric in them. -/
theorem symm_of_nonempty (ip : Int) (r t p k : String) (hp : p ≠ "") (hk : k ≠ "") :
    safeRloginReverseDns ip r t p k = safeRloginReverseDns ip r t k p := by
  by_cases h : p = k
  · subst h
    rfl
  · simp [safeRloginReverseDns, hp, hk, h, Ne.symm h]

/-! ## The fixed examples from the Python `check` -/

theorem check_example_1 :
    safeRloginReverseDns 3232235777 "trusted.example.com" "trusted.example.com"
      "SHA256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
      "SHA256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" = true := by
  simp [safeRloginReverseDns]

theorem check_example_2 :
    safeRloginReverseDns 195939070 "trusted.example.com" "trusted.example.com"
      "SHA256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
      "SHA256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" = false := by
  simp [safeRloginReverseDns]

theorem check_example_3 :
    safeRloginReverseDns 3232235777 "wrong.reverse.dns" "trusted.example.com"
      "SHA256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
      "SHA256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" = true := by
  simp [safeRloginReverseDns]

theorem check_example_4 :
    safeRloginReverseDns 3232235777 "trusted.example.com" "trusted.example.com"
      ""
      "SHA256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" = false := by
  simp [safeRloginReverseDns]

theorem check_example_5 :
    safeRloginReverseDns 195939070 "trusted.example.com" "trusted.example.com"
      ""
      "SHA256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" = false := by
  simp [safeRloginReverseDns]

/-- The Python `__main__` block: `check(safe_rlogin_reverse_dns)` succeeds. -/
theorem check_passes : check safeRloginReverseDns = true := by
  simp [check, safeRloginReverseDns]

#eval check safeRloginReverseDns  -- expected: true

end SafeRlogin

-- TL;DR: Lean 4 translation of `safe_rlogin_reverse_dns` and `check`, with theorems that
-- characterize when it accepts and rejects, show the IP and hostname arguments are ignored,
-- and prove the five fixed examples and `check`. Not compiled here because no Lean toolchain
-- was available in this session.
