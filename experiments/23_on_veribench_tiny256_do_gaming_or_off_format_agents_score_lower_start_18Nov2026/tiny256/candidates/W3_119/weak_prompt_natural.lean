/-!
# Safe ARP response handling

Translated from Python. The check confirms that an ARP response IP matches the
requested IP. Python `int` is unbounded, so IPs are modelled as `Int`.

This is only an integer comparison. It does **not** authenticate the sender and
does **not** prevent ARP cache poisoning (see `spoofed_reply_accepted` below).
-/

/-- Return `true` when `responseIp` equals `expectedIp`, and `false` otherwise.
This integer comparison does not authenticate the sender or prevent ARP cache poisoning. -/
def safeArpResponse (responseIp expectedIp : Int) : Bool :=
  responseIp == expectedIp

/-- The fixed examples from the Python `check()`. Every one of them must hold. -/
def check : Bool :=
  safeArpResponse 10 10 == true &&
  safeArpResponse 99 10 == false &&
  safeArpResponse 0 1 == false &&
  safeArpResponse 0 0 == true &&
  safeArpResponse 2 1 == false

/-- Mirrors `if __name__ == "__main__": check()`: fails like an `AssertionError`. -/
def main : IO Unit := do
  unless check do
    throw (IO.userError "AssertionError: safeArpResponse check failed")

/-! ## The fixed examples, proved -/

theorem ex_match_10 : safeArpResponse 10 10 = true := by decide
theorem ex_mismatch_99_10 : safeArpResponse 99 10 = false := by decide
theorem ex_mismatch_0_1 : safeArpResponse 0 1 = false := by decide
theorem ex_match_0 : safeArpResponse 0 0 = true := by decide
theorem ex_mismatch_2_1 : safeArpResponse 2 1 = false := by decide

/-- `check` passes, so running `main` never raises. -/
theorem check_eq_true : check = true := by decide

/-! ## Specification -/

/-- The function accepts exactly when the two IPs are equal. -/
theorem safeArpResponse_eq_true_iff (r e : Int) :
    safeArpResponse r e = true ↔ r = e := by
  simp [safeArpResponse]

/-- The function rejects exactly when the two IPs differ. -/
theorem safeArpResponse_eq_false_iff (r e : Int) :
    safeArpResponse r e = false ↔ r ≠ e := by
  simp [safeArpResponse]

/-- The result is the decision of the proposition `r = e`. -/
theorem safeArpResponse_eq_decide (r e : Int) :
    safeArpResponse r e = decide (r = e) := by
  by_cases h : r = e <;> simp [safeArpResponse, h]

/-- A mismatched response is always rejected. -/
theorem rejects_mismatch {r e : Int} (h : r ≠ e) : safeArpResponse r e = false :=
  (safeArpResponse_eq_false_iff r e).mpr h

/-- An accepted response carries exactly the expected IP. -/
theorem accepted_implies_eq {r e : Int} (h : safeArpResponse r e = true) : r = e :=
  (safeArpResponse_eq_true_iff r e).mp h

/-! ## Algebraic properties -/

/-- Reflexivity: a response with the expected IP is always accepted. -/
theorem safeArpResponse_self (ip : Int) : safeArpResponse ip ip = true := by
  simp [safeArpResponse]

/-- Symmetry: swapping the response and expected IPs does not change the result. -/
theorem safeArpResponse_comm (a b : Int) :
    safeArpResponse a b = safeArpResponse b a := by
  by_cases h : a = b
  · subst h
    rfl
  · have h' : b ≠ a := fun hba => h hba.symm
    rw [(safeArpResponse_eq_false_iff a b).mpr h,
        (safeArpResponse_eq_false_iff b a).mpr h']

/-- Transitivity: acceptance chains. -/
theorem safeArpResponse_trans {a b c : Int}
    (h₁ : safeArpResponse a b = true) (h₂ : safeArpResponse b c = true) :
    safeArpResponse a c = true := by
  have hab := (safeArpResponse_eq_true_iff a b).mp h₁
  have hbc := (safeArpResponse_eq_true_iff b c).mp h₂
  exact (safeArpResponse_eq_true_iff a c).mpr (hab.trans hbc)

/-- For a fixed expected IP, exactly one response IP is accepted. -/
theorem unique_accepted_ip (e : Int) :
    ∃ r, safeArpResponse r e = true ∧ ∀ r', safeArpResponse r' e = true → r' = r :=
  ⟨e, safeArpResponse_self e, fun _ h => accepted_implies_eq h⟩

/-! ## The documented limitation: no sender authentication -/

/-- A minimal ARP reply: the claimed sender IP and the sender hardware (MAC) address. -/
structure ArpReply where
  senderIp : Int
  senderMac : Nat
  deriving Repr

/-- Accepting a reply uses only its IP field. -/
def acceptsReply (reply : ArpReply) (expectedIp : Int) : Bool :=
  safeArpResponse reply.senderIp expectedIp

/-- The decision ignores the sender MAC: two replies that differ only in MAC are
treated identically, so the check cannot tell a genuine host from an impostor. -/
theorem acceptsReply_ignores_mac (ip expectedIp : Int) (mac₁ mac₂ : Nat) :
    acceptsReply ⟨ip, mac₁⟩ expectedIp = acceptsReply ⟨ip, mac₂⟩ expectedIp :=
  rfl

/-- Any attacker who claims the expected IP is accepted, whatever MAC they use.
This formalizes why the check does not prevent ARP cache poisoning. -/
theorem spoofed_reply_accepted (expectedIp : Int) (attackerMac : Nat) :
    acceptsReply ⟨expectedIp, attackerMac⟩ expectedIp = true :=
  safeArpResponse_self expectedIp

-- TLDR-end: [arp-lean: translate safe_arp_response] Lean 4 port of `safe_arp_response`
-- and `check`, with proofs of the examples, its exact spec (accept ↔ IPs equal),
-- reflexivity/symmetry/transitivity, and a theorem that spoofed replies are accepted.
-- Not machine-checked in this session (no shell was available to run `lean`).
