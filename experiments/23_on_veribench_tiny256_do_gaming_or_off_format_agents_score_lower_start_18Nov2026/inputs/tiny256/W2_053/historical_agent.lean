import Mathlib
namespace Agent

/-!
# Safe DHCP client with an authorized-server whitelist

Translation of `safe_dhcp_spoofing` and its Python test harness. The result is
`(accepted, assigned_ip, gateway, dns)`. An unconfigured (zero) authorized
server, or a source different from the authorized server, causes rejection
with all output fields zero. Otherwise the offered configuration is returned
unchanged.

Python integers are represented by `Int`, with no positivity or IPv4-range
restriction. In particular, the function's checks concern server identity,
not the validity or trustworthiness of the configuration fields. Identity is
modelled strictly by source-IP equality: actual DHCP snooping, authenticated
ports and trusted relays are environmental controls, not extra guarantees of
this function.

The specification covers every integer input, including the unconfigured
case. Bounded property-based tests are executable evidence only; all named
theorems have separate kernel-checked proofs.
-/

namespace SafeDhcpSpoofing

abbrev DhcpResult := Bool × Int × Int × Int
abbrev DhcpCandidate := Int → Int → Int → Int → Int → DhcpResult

/-- Functional translation, preserving the order of the two Python guards. -/
def safe_dhcp_spoofing
    (offer_server_ip offer_client_ip offer_gateway_ip offer_dns_ip
      authorized_server_ip : Int) : DhcpResult :=
  if authorized_server_ip = 0 then
    (false, 0, 0, 0)
  else if offer_server_ip ≠ authorized_server_ip then
    (false, 0, 0, 0)
  else
    (true, offer_client_ip, offer_gateway_ip, offer_dns_ip)

/-! ## The original Python unit tests -/

def AUTH_SERVER : Int := 0xC0A80101
def LEGIT_GATEWAY : Int := 0xC0A80101
def LEGIT_DNS : Int := 0x08080808
def ROGUE_SERVER : Int := 0xC0A80199
def ATTACKER_GATEWAY : Int := 0xC0A80199
def ATTACKER_DNS : Int := 0xC0A80199
def CLIENT_IP : Int := 0xC0A8010A

/-- Pure Boolean version of the five assertions in Python's `check`. -/
def check (candidate : DhcpCandidate) : Bool :=
  (candidate AUTH_SERVER CLIENT_IP LEGIT_GATEWAY LEGIT_DNS AUTH_SERVER ==
      (true, CLIENT_IP, LEGIT_GATEWAY, LEGIT_DNS)) &&
  (candidate ROGUE_SERVER CLIENT_IP ATTACKER_GATEWAY ATTACKER_DNS AUTH_SERVER ==
      (false, 0, 0, 0)) &&
  (candidate AUTH_SERVER CLIENT_IP LEGIT_GATEWAY LEGIT_DNS 0 ==
      (false, 0, 0, 0)) &&
  (candidate 0 CLIENT_IP LEGIT_GATEWAY LEGIT_DNS AUTH_SERVER ==
      (false, 0, 0, 0)) &&
  (candidate AUTH_SERVER 0xC0A8010B LEGIT_GATEWAY LEGIT_DNS AUTH_SERVER ==
      (true, 0xC0A8010B, LEGIT_GATEWAY, LEGIT_DNS))

-- Test 1: legitimate OFFER.
example : safe_dhcp_spoofing AUTH_SERVER CLIENT_IP LEGIT_GATEWAY LEGIT_DNS
    AUTH_SERVER = (true, CLIENT_IP, LEGIT_GATEWAY, LEGIT_DNS) := by
  native_decide

-- Test 2: unauthorized OFFER and malicious configuration.
example : safe_dhcp_spoofing ROGUE_SERVER CLIENT_IP ATTACKER_GATEWAY ATTACKER_DNS
    AUTH_SERVER = (false, 0, 0, 0) := by
  native_decide

-- Test 3a: authorized server not configured.
example : safe_dhcp_spoofing AUTH_SERVER CLIENT_IP LEGIT_GATEWAY LEGIT_DNS 0 =
    (false, 0, 0, 0) := by
  native_decide

-- Test 3b: source zero does not match a nonzero authorized server.
example : safe_dhcp_spoofing 0 CLIENT_IP LEGIT_GATEWAY LEGIT_DNS AUTH_SERVER =
    (false, 0, 0, 0) := by
  native_decide

-- Test 3c: the accepted client address is the one in the OFFER.
example : safe_dhcp_spoofing AUTH_SERVER 0xC0A8010B LEGIT_GATEWAY LEGIT_DNS
    AUTH_SERVER = (true, 0xC0A8010B, LEGIT_GATEWAY, LEGIT_DNS) := by
  native_decide

-- Matching zero server addresses still reject: the first guard takes priority.
example : safe_dhcp_spoofing 0 17 18 19 0 = (false, 0, 0, 0) := by
  native_decide

-- No additional positivity check or payload validation is present in Python.
example : safe_dhcp_spoofing (-7) (-10) 0 (-8) (-7) =
    (true, -10, 0, -8) := by
  native_decide

example : safe_dhcp_spoofing 1 0 0 0 1 = (true, 0, 0, 0) := by
  native_decide

example : check safe_dhcp_spoofing = true := by native_decide

#eval safe_dhcp_spoofing AUTH_SERVER CLIENT_IP LEGIT_GATEWAY LEGIT_DNS AUTH_SERVER
#eval safe_dhcp_spoofing ROGUE_SERVER CLIENT_IP ATTACKER_GATEWAY ATTACKER_DNS AUTH_SERVER
#eval if check safe_dhcp_spoofing then "All tests passed." else "Tests failed."

/-! ## Precondition and universally quantified properties -/

/-- The program is total. Zero authorization is handled, not excluded. -/
def Pre (_s _c _g _d _a : Int) : Prop := True

/-- Without a configured authorized server, the complete result is rejection. -/
def no_authorized_server_prop (s c g d a : Int) : Prop :=
  a = 0 → safe_dhcp_spoofing s c g d a = (false, 0, 0, 0)

theorem no_authorized_server_thm (s c g d a : Int) :
    no_authorized_server_prop s c g d a := by
  unfold no_authorized_server_prop
  intro ha
  simp [safe_dhcp_spoofing, ha]

/-- Every OFFER from a different server is rejected, regardless of payload. -/
def unauthorized_server_prop (s c g d a : Int) : Prop :=
  s ≠ a → safe_dhcp_spoofing s c g d a = (false, 0, 0, 0)

theorem unauthorized_server_thm (s c g d a : Int) :
    unauthorized_server_prop s c g d a := by
  unfold unauthorized_server_prop
  intro hs
  simp [safe_dhcp_spoofing, hs]

/-- A matching, nonzero server causes acceptance of exactly the offered data. -/
def authorized_server_prop (s c g d a : Int) : Prop :=
  a ≠ 0 → s = a → safe_dhcp_spoofing s c g d a = (true, c, g, d)

theorem authorized_server_thm (s c g d a : Int) :
    authorized_server_prop s c g d a := by
  unfold authorized_server_prop
  intro ha hs
  simp [safe_dhcp_spoofing, ha, hs]

/-- Acceptance is equivalent to both authorization checks passing. -/
def acceptance_iff_prop (s c g d a : Int) : Prop :=
  (safe_dhcp_spoofing s c g d a).1 = true ↔ a ≠ 0 ∧ s = a

theorem acceptance_iff_thm (s c g d a : Int) :
    acceptance_iff_prop s c g d a := by
  unfold acceptance_iff_prop
  by_cases ha : a = 0 <;> by_cases hs : s = a <;>
    simp [safe_dhcp_spoofing, ha, hs]

/-- These are exactly the two reasons for rejection, including their overlap. -/
def rejection_iff_prop (s c g d a : Int) : Prop :=
  (safe_dhcp_spoofing s c g d a).1 = false ↔ a = 0 ∨ s ≠ a

theorem rejection_iff_thm (s c g d a : Int) :
    rejection_iff_prop s c g d a := by
  unfold rejection_iff_prop
  by_cases ha : a = 0 <;> by_cases hs : s = a <;>
    simp [safe_dhcp_spoofing, ha, hs]

/-- Accepted OFFERs preserve all three configuration fields without sanitizing. -/
def accepted_configuration_prop (s c g d a : Int) : Prop :=
  (safe_dhcp_spoofing s c g d a).1 = true →
    (safe_dhcp_spoofing s c g d a).2 = (c, g, d)

theorem accepted_configuration_thm (s c g d a : Int) :
    accepted_configuration_prop s c g d a := by
  unfold accepted_configuration_prop
  by_cases ha : a = 0 <;> by_cases hs : s = a <;>
    simp [safe_dhcp_spoofing, ha, hs]

/-- Rejection never exposes any of the offered configuration in the result. -/
def rejected_configuration_prop (s c g d a : Int) : Prop :=
  (safe_dhcp_spoofing s c g d a).1 = false →
    (safe_dhcp_spoofing s c g d a).2 = (0, 0, 0)

theorem rejected_configuration_thm (s c g d a : Int) :
    rejected_configuration_prop s c g d a := by
  unfold rejected_configuration_prop
  by_cases ha : a = 0 <;> by_cases hs : s = a <;>
    simp [safe_dhcp_spoofing, ha, hs]

/-! ## Postcondition -/

/-- Complete behavioral and security guarantees for the returned result. -/
def Post_prop (s c g d a : Int) : Prop :=
  no_authorized_server_prop s c g d a ∧
  unauthorized_server_prop s c g d a ∧
  authorized_server_prop s c g d a ∧
  acceptance_iff_prop s c g d a ∧
  rejection_iff_prop s c g d a ∧
  accepted_configuration_prop s c g d a ∧
  rejected_configuration_prop s c g d a

/-! ## Bounded property-based tests

Each test exhausts the five-fold Cartesian product of a finite integer set:
59,049 inputs per property. Besides zero and signed small values, this set
includes the authorized server, rogue server, client address and DNS address.
Both matching and nonmatching servers are generated deliberately, so the
implication tests include nonvacuous cases. We choose exhaustive bounded PBTs
rather than relying on random generation to produce matching server addresses.
The Boolean forms below are the executable counterparts of the named Props;
they do not require Decidable instances for those specification definitions.
-/

def pbtValues : List Int :=
  [-2, -1, 0, 1, 2, AUTH_SERVER, ROGUE_SERVER, CLIENT_IP, LEGIT_DNS]

def allSmallInputs (p : Int → Int → Int → Int → Int → Bool) : Bool :=
  pbtValues.all fun s =>
    pbtValues.all fun c =>
      pbtValues.all fun g =>
        pbtValues.all fun d =>
          pbtValues.all fun a => p s c g d a

-- PBT for no_authorized_server_prop.
example : allSmallInputs (fun s c g d a =>
    decide (a = 0 → safe_dhcp_spoofing s c g d a = (false, 0, 0, 0))) = true := by
  native_decide

-- PBT for unauthorized_server_prop.
example : allSmallInputs (fun s c g d a =>
    decide (s ≠ a → safe_dhcp_spoofing s c g d a = (false, 0, 0, 0))) = true := by
  native_decide

-- PBT for authorized_server_prop.
example : allSmallInputs (fun s c g d a =>
    decide (a ≠ 0 → s = a → safe_dhcp_spoofing s c g d a = (true, c, g, d))) =
    true := by
  native_decide

-- PBT for acceptance_iff_prop.
example : allSmallInputs (fun s c g d a =>
    decide ((safe_dhcp_spoofing s c g d a).1 = true ↔ a ≠ 0 ∧ s = a)) = true := by
  native_decide

-- PBT for rejection_iff_prop.
example : allSmallInputs (fun s c g d a =>
    decide ((safe_dhcp_spoofing s c g d a).1 = false ↔ a = 0 ∨ s ≠ a)) = true := by
  native_decide

-- PBT for accepted_configuration_prop.
example : allSmallInputs (fun s c g d a =>
    let result := safe_dhcp_spoofing s c g d a
    decide (result.1 = true → result.2 = (c, g, d))) = true := by
  native_decide

-- PBT for rejected_configuration_prop.
example : allSmallInputs (fun s c g d a =>
    let result := safe_dhcp_spoofing s c g d a
    decide (result.1 = false → result.2 = (0, 0, 0))) = true := by
  native_decide

/-- Executable Boolean form of the complete conjunction in Post_prop. -/
def postCheck (s c g d a : Int) : Bool :=
  let result := safe_dhcp_spoofing s c g d a
  decide (a = 0 → result = (false, 0, 0, 0)) &&
  decide (s ≠ a → result = (false, 0, 0, 0)) &&
  decide (a ≠ 0 → s = a → result = (true, c, g, d)) &&
  decide (result.1 = true ↔ a ≠ 0 ∧ s = a) &&
  decide (result.1 = false ↔ a = 0 ∨ s ≠ a) &&
  decide (result.1 = true → result.2 = (c, g, d)) &&
  decide (result.1 = false → result.2 = (0, 0, 0))

-- PBT for Post_prop: test the entire conjunction, not just one consequence.
example : allSmallInputs postCheck = true := by native_decide
#eval allSmallInputs postCheck

/-! ## Correctness -/

theorem correctness_thm (s c g d a : Int) :
    Pre s c g d a → Post_prop s c g d a := by
  intro _
  exact ⟨no_authorized_server_thm s c g d a,
    unauthorized_server_thm s c g d a,
    authorized_server_thm s c g d a,
    acceptance_iff_thm s c g d a,
    rejection_iff_thm s c g d a,
    accepted_configuration_thm s c g d a,
    rejected_configuration_thm s c g d a⟩

/-! ## Imperative translation with mutable output fields and early returns -/

def safe_dhcp_spoofing_imperative
    (offer_server_ip offer_client_ip offer_gateway_ip offer_dns_ip
      authorized_server_ip : Int) : DhcpResult := Id.run do
  let mut accepted := false
  let mut assigned_ip : Int := 0
  let mut gateway : Int := 0
  let mut dns : Int := 0
  if authorized_server_ip = 0 then
    return (accepted, assigned_ip, gateway, dns)
  if offer_server_ip ≠ authorized_server_ip then
    return (accepted, assigned_ip, gateway, dns)
  accepted := true
  assigned_ip := offer_client_ip
  gateway := offer_gateway_ip
  dns := offer_dns_ip
  return (accepted, assigned_ip, gateway, dns)

/-! ## Imperative tests -/

example : safe_dhcp_spoofing_imperative AUTH_SERVER CLIENT_IP LEGIT_GATEWAY LEGIT_DNS
    AUTH_SERVER = (true, CLIENT_IP, LEGIT_GATEWAY, LEGIT_DNS) := by
  native_decide

example : safe_dhcp_spoofing_imperative ROGUE_SERVER CLIENT_IP ATTACKER_GATEWAY
    ATTACKER_DNS AUTH_SERVER = (false, 0, 0, 0) := by
  native_decide

example : safe_dhcp_spoofing_imperative AUTH_SERVER CLIENT_IP LEGIT_GATEWAY
    LEGIT_DNS 0 = (false, 0, 0, 0) := by
  native_decide

example : safe_dhcp_spoofing_imperative 0 CLIENT_IP LEGIT_GATEWAY LEGIT_DNS
    AUTH_SERVER = (false, 0, 0, 0) := by
  native_decide

example : safe_dhcp_spoofing_imperative AUTH_SERVER 0xC0A8010B LEGIT_GATEWAY LEGIT_DNS
    AUTH_SERVER = (true, 0xC0A8010B, LEGIT_GATEWAY, LEGIT_DNS) := by
  native_decide

example : safe_dhcp_spoofing_imperative 0 17 18 19 0 = (false, 0, 0, 0) := by
  native_decide

example : safe_dhcp_spoofing_imperative (-7) (-10) 0 (-8) (-7) =
    (true, -10, 0, -8) := by
  native_decide

example : check safe_dhcp_spoofing_imperative = true := by native_decide

#eval safe_dhcp_spoofing_imperative AUTH_SERVER CLIENT_IP LEGIT_GATEWAY LEGIT_DNS
  AUTH_SERVER
#eval if check safe_dhcp_spoofing_imperative then "All tests passed." else "Tests failed."

-- Additional bounded cross-check of the two implementations.
example : allSmallInputs (fun s c g d a =>
    decide (safe_dhcp_spoofing s c g d a =
      safe_dhcp_spoofing_imperative s c g d a)) = true := by
  native_decide

/-! ## Functional-imperative equivalence -/

theorem functional_imperative_equivalence_thm (s c g d a : Int) :
    safe_dhcp_spoofing s c g d a = safe_dhcp_spoofing_imperative s c g d a := by
  by_cases ha : a = 0 <;> by_cases hs : s = a <;>
    simp [safe_dhcp_spoofing, safe_dhcp_spoofing_imperative, ha, hs]

theorem functional_eq_imperative_thm :
    safe_dhcp_spoofing = safe_dhcp_spoofing_imperative := by
  funext s c g d a
  exact functional_imperative_equivalence_thm s c g d a

end SafeDhcpSpoofing
end Agent
