import Mathlib
import Plausible

/-!
# Unsafe TLS version downgrade

MIT 6.858 Lecture 14 — TLS / Downgrade.

A correct TLS server picks min(client_offered_max, server_max): the highest
common version. An on-path attacker can strip strong versions from the
ClientHello before it reaches the server. Without a sentinel binding the true
client capability into the negotiation, the server happily picks the highest
common version of the tampered offer — typically a much weaker protocol than
client and server actually share.

Versions are integers (higher = newer):
0 = SSL 3.0, 1 = TLS 1.0, 2 = TLS 1.1, 3 = TLS 1.2, 4 = TLS 1.3.

Python int is modeled as Lean Int (unbounded). The function is total and does
not reject codes outside 0..4; the lecture encoding uses those non-negative codes.
The vulnerability is not a wrong min: it is that client_offered_max is trusted
even when an attacker has removed stronger versions the client actually supports.
-/

namespace «95_unsafeTlsDowngrade»

/-- SSL 3.0. -/
def ssl30 : Int := 0
/-- TLS 1.0. -/
def tls10 : Int := 1
/-- TLS 1.1. -/
def tls11 : Int := 2
/-- TLS 1.2. -/
def tls12 : Int := 3
/-- TLS 1.3. -/
def tls13 : Int := 4

/-- Unsafe TLS negotiation.

Returns min(client_offered_max, server_max), the highest version present in both
the visible client offer and the server maximum. There is no check that
client_offered_max equals the client true capability.
-/
def unsafe_tls_downgrade (client_offered_max server_max : Int) : Int :=
  min client_offered_max server_max

/-- Version that client and server actually share, using the client true maximum. -/
def shared_capability (true_client_max server_max : Int) : Int :=
  min true_client_max server_max

/-- Lecture version code: SSL 3.0 through TLS 1.3. -/
def ValidVersion (v : Int) : Prop :=
  0 ≤ v ∧ v ≤ 4

instance {v : Int} : Decidable (ValidVersion v) := by
  unfold ValidVersion
  exact inferInstance

/-- Server entry point that is given the client true maximum but ignores it.

true_client_max - true_client_max is identically zero, so the true capability
cannot change the negotiated version. This is the missing sentinel check.
-/
def unsafe_negotiate (true_client_max client_offered_max server_max : Int) : Int :=
  unsafe_tls_downgrade client_offered_max server_max + (true_client_max - true_client_max)

/-! ## Unit tests -/

example : unsafe_tls_downgrade 4 4 = 4 := by native_decide
example : unsafe_tls_downgrade 1 4 = 1 := by native_decide
example : unsafe_tls_downgrade 4 2 = 2 := by native_decide
example : unsafe_tls_downgrade 3 3 = 3 := by native_decide
example : unsafe_tls_downgrade 4 0 = 0 := by native_decide
example : unsafe_tls_downgrade 2 4 ≥ unsafe_tls_downgrade 1 4 := by native_decide

example : unsafe_tls_downgrade tls13 tls13 = tls13 := by native_decide
example : unsafe_tls_downgrade tls10 tls13 = tls10 := by native_decide
example : unsafe_tls_downgrade tls13 tls11 = tls11 := by native_decide
example : unsafe_tls_downgrade tls12 tls12 = tls12 := by native_decide
example : unsafe_tls_downgrade tls13 ssl30 = ssl30 := by native_decide
example : unsafe_negotiate 4 1 4 = 1 := by native_decide
example : unsafe_negotiate 4 1 4 = unsafe_negotiate 100 1 4 := by native_decide

#eval unsafe_tls_downgrade 4 4
#eval unsafe_tls_downgrade 1 4
#eval unsafe_tls_downgrade 4 2
#eval unsafe_tls_downgrade 3 3
#eval unsafe_tls_downgrade 4 0
#eval unsafe_tls_downgrade 2 4 ≥ unsafe_tls_downgrade 1 4
#eval unsafe_negotiate 4 1 4

/-- Python check: the six source assertions, as a Boolean. -/
def check (candidate : Int → Int → Int) : Bool :=
  (candidate 4 4 == 4) &&
  (candidate 1 4 == 1) &&
  (candidate 4 2 == 2) &&
  (candidate 3 3 == 3) &&
  (candidate 4 0 == 0) &&
  decide (candidate 2 4 ≥ candidate 1 4)

example : check unsafe_tls_downgrade = true := by native_decide
#eval check unsafe_tls_downgrade

/-! ## Pre-condition -/

/-- The Python function is total on every pair of integers; it performs no range check. -/
def Pre (_client_offered_max _server_max : Int) : Prop := True

/-! ## Property propositions and theorems -/

/-- Negotiated version equals min of the visible offer and the server max. -/
def eq_min_prop (client_offered_max server_max : Int) : Prop :=
  unsafe_tls_downgrade client_offered_max server_max = min client_offered_max server_max

theorem eq_min_thm (client_offered_max server_max : Int) :
    eq_min_prop client_offered_max server_max := by
  unfold eq_min_prop unsafe_tls_downgrade
  rfl

/-- Result never exceeds the visible client offer. -/
def le_offer_prop (client_offered_max server_max : Int) : Prop :=
  unsafe_tls_downgrade client_offered_max server_max ≤ client_offered_max

theorem le_offer_thm (client_offered_max server_max : Int) :
    le_offer_prop client_offered_max server_max := by
  unfold le_offer_prop unsafe_tls_downgrade
  omega

/-- Result never exceeds the server maximum. -/
def le_server_prop (client_offered_max server_max : Int) : Prop :=
  unsafe_tls_downgrade client_offered_max server_max ≤ server_max

theorem le_server_thm (client_offered_max server_max : Int) :
    le_server_prop client_offered_max server_max := by
  unfold le_server_prop unsafe_tls_downgrade
  omega

/-- The result is a greatest integer bounded by both inputs. -/
def greatest_common_prop (client_offered_max server_max : Int) : Prop :=
  ∀ v : Int, v ≤ client_offered_max → v ≤ server_max →
    v ≤ unsafe_tls_downgrade client_offered_max server_max

theorem greatest_common_thm (client_offered_max server_max : Int) :
    greatest_common_prop client_offered_max server_max := by
  unfold greatest_common_prop unsafe_tls_downgrade
  intro v hvOffer hvServer
  omega

/-- Highest common version of the visible offer and the server max. -/
def highest_common_prop (client_offered_max server_max : Int) : Prop :=
  unsafe_tls_downgrade client_offered_max server_max ≤ client_offered_max ∧
    unsafe_tls_downgrade client_offered_max server_max ≤ server_max ∧
      ∀ v : Int, v ≤ client_offered_max → v ≤ server_max →
        v ≤ unsafe_tls_downgrade client_offered_max server_max

theorem highest_common_thm (client_offered_max server_max : Int) :
    highest_common_prop client_offered_max server_max := by
  unfold highest_common_prop unsafe_tls_downgrade
  constructor
  · omega
  · constructor
    · omega
    · intro v hvOffer hvServer
      omega

/-- If the visible offer does not exceed the server max, that offer is accepted. -/
def offer_limited_prop (client_offered_max server_max : Int) : Prop :=
  client_offered_max ≤ server_max →
    unsafe_tls_downgrade client_offered_max server_max = client_offered_max

theorem offer_limited_thm (client_offered_max server_max : Int) :
    offer_limited_prop client_offered_max server_max := by
  unfold offer_limited_prop unsafe_tls_downgrade
  intro h
  omega

/-- If the server max does not exceed the visible offer, the server cap wins. -/
def server_limited_prop (client_offered_max server_max : Int) : Prop :=
  server_max ≤ client_offered_max →
    unsafe_tls_downgrade client_offered_max server_max = server_max

theorem server_limited_thm (client_offered_max server_max : Int) :
    server_limited_prop client_offered_max server_max := by
  unfold server_limited_prop unsafe_tls_downgrade
  intro h
  omega

/-- The negotiated version is exactly one of the two caps. -/
def result_eq_one_arg_prop (client_offered_max server_max : Int) : Prop :=
  unsafe_tls_downgrade client_offered_max server_max = client_offered_max ∨
    unsafe_tls_downgrade client_offered_max server_max = server_max

theorem result_eq_one_arg_thm (client_offered_max server_max : Int) :
    result_eq_one_arg_prop client_offered_max server_max := by
  unfold result_eq_one_arg_prop unsafe_tls_downgrade
  by_cases h : client_offered_max ≤ server_max
  · left
    omega
  · right
    have hlt : server_max < client_offered_max := Int.not_le.mp h
    omega

/-- A larger visible offer never negotiates a weaker version. -/
def mono_offer_prop (offer1 offer2 server_max : Int) : Prop :=
  offer1 ≤ offer2 →
    unsafe_tls_downgrade offer1 server_max ≤ unsafe_tls_downgrade offer2 server_max

theorem mono_offer_thm (offer1 offer2 server_max : Int) :
    mono_offer_prop offer1 offer2 server_max := by
  unfold mono_offer_prop unsafe_tls_downgrade
  intro h
  omega

/-- Raising the server maximum never negotiates a weaker version. -/
def mono_server_prop (client_offered_max server1 server2 : Int) : Prop :=
  server1 ≤ server2 →
    unsafe_tls_downgrade client_offered_max server1 ≤
      unsafe_tls_downgrade client_offered_max server2

theorem mono_server_thm (client_offered_max server1 server2 : Int) :
    mono_server_prop client_offered_max server1 server2 := by
  unfold mono_server_prop unsafe_tls_downgrade
  intro h
  omega

/-- Highest-common-version negotiation is symmetric in the two caps. -/
def comm_prop (a b : Int) : Prop :=
  unsafe_tls_downgrade a b = unsafe_tls_downgrade b a

theorem comm_thm (a b : Int) : comm_prop a b := by
  unfold comm_prop unsafe_tls_downgrade
  omega

/-- Equal advertised capabilities negotiate that version. -/
def equal_versions_prop (v : Int) : Prop :=
  unsafe_tls_downgrade v v = v

theorem equal_versions_thm (v : Int) : equal_versions_prop v := by
  unfold equal_versions_prop unsafe_tls_downgrade
  omega

/-- Stripping the offer strictly below both the true client max and the server max
forces a strictly weaker result than the capability client and server actually share. -/
def strict_downgrade_prop (true_client_max tampered_offer server_max : Int) : Prop :=
  tampered_offer < true_client_max →
    tampered_offer < server_max →
      unsafe_tls_downgrade tampered_offer server_max <
        shared_capability true_client_max server_max

theorem strict_downgrade_thm (true_client_max tampered_offer server_max : Int) :
    strict_downgrade_prop true_client_max tampered_offer server_max := by
  unfold strict_downgrade_prop unsafe_tls_downgrade shared_capability
  intro hClient hServer
  omega

/-- Missing sentinel: a visible offer strictly below the client true max is still
accepted whenever it does not exceed the server max. -/
def missing_sentinel_prop (true_client_max client_offered_max server_max : Int) : Prop :=
  client_offered_max < true_client_max →
    client_offered_max ≤ server_max →
      unsafe_tls_downgrade client_offered_max server_max = client_offered_max ∧
        unsafe_tls_downgrade client_offered_max server_max < true_client_max

theorem missing_sentinel_thm (true_client_max client_offered_max server_max : Int) :
    missing_sentinel_prop true_client_max client_offered_max server_max := by
  unfold missing_sentinel_prop unsafe_tls_downgrade
  intro hStrip hAccept
  constructor
  · omega
  · omega

/-- Stripping cannot produce a version stronger than what client and server share. -/
def tamper_weakens_prop (true_client_max client_offered_max server_max : Int) : Prop :=
  client_offered_max ≤ true_client_max →
    unsafe_tls_downgrade client_offered_max server_max ≤
      shared_capability true_client_max server_max

theorem tamper_weakens_thm (true_client_max client_offered_max server_max : Int) :
    tamper_weakens_prop true_client_max client_offered_max server_max := by
  unfold tamper_weakens_prop unsafe_tls_downgrade shared_capability
  intro h
  omega

/-- An offer strictly below the true shared capability is accepted verbatim and is
a strict downgrade relative to what client and server actually share. -/
def downgrade_gap_prop (true_client_max client_offered_max server_max : Int) : Prop :=
  client_offered_max < shared_capability true_client_max server_max →
    unsafe_tls_downgrade client_offered_max server_max = client_offered_max ∧
      unsafe_tls_downgrade client_offered_max server_max <
        shared_capability true_client_max server_max

theorem downgrade_gap_thm (true_client_max client_offered_max server_max : Int) :
    downgrade_gap_prop true_client_max client_offered_max server_max := by
  unfold downgrade_gap_prop unsafe_tls_downgrade shared_capability
  intro h
  constructor
  · omega
  · omega

/-- Two different true client capabilities yield the same unsafe negotiation when
the visible offer and server max are unchanged. -/
def oblivious_prop (true1 true2 offer server : Int) : Prop :=
  unsafe_negotiate true1 offer server = unsafe_negotiate true2 offer server

theorem oblivious_thm (true1 true2 offer server : Int) :
    oblivious_prop true1 true2 offer server := by
  unfold oblivious_prop unsafe_negotiate unsafe_tls_downgrade
  omega

/-- The true client maximum does not affect unsafe_negotiate. -/
def negotiate_ignores_true_prop (true_client_max client_offered_max server_max : Int) : Prop :=
  unsafe_negotiate true_client_max client_offered_max server_max =
    unsafe_tls_downgrade client_offered_max server_max

theorem negotiate_ignores_true_thm (true_client_max client_offered_max server_max : Int) :
    negotiate_ignores_true_prop true_client_max client_offered_max server_max := by
  unfold negotiate_ignores_true_prop unsafe_negotiate
  omega

/-- Negotiation of lecture version codes stays inside the lecture encoding. -/
def result_valid_prop (client_offered_max server_max : Int) : Prop :=
  ValidVersion client_offered_max →
    ValidVersion server_max →
      ValidVersion (unsafe_tls_downgrade client_offered_max server_max)

theorem result_valid_thm (client_offered_max server_max : Int) :
    result_valid_prop client_offered_max server_max := by
  unfold result_valid_prop ValidVersion unsafe_tls_downgrade
  intro hc hs
  rcases hc with ⟨hc0, hc4⟩
  rcases hs with ⟨hs0, hs4⟩
  constructor <;> omega

/-- The six Python assertions, kernel-checked. -/
theorem python_asserts_thm :
    unsafe_tls_downgrade 4 4 = 4 ∧
      unsafe_tls_downgrade 1 4 = 1 ∧
        unsafe_tls_downgrade 4 2 = 2 ∧
          unsafe_tls_downgrade 3 3 = 3 ∧
            unsafe_tls_downgrade 4 0 = 0 ∧
              unsafe_tls_downgrade 1 4 ≤ unsafe_tls_downgrade 2 4 := by
  unfold unsafe_tls_downgrade
  omega

/-- Lecture attack: both sides support TLS 1.3, the attacker strips the offer to
TLS 1.0, and the unsafe server negotiates TLS 1.0 instead of the shared TLS 1.3. -/
theorem lecture_attack_thm :
    unsafe_tls_downgrade tls13 tls13 = tls13 ∧
      unsafe_tls_downgrade tls10 tls13 = tls10 ∧
        shared_capability tls13 tls13 = tls13 ∧
          unsafe_tls_downgrade tls10 tls13 < shared_capability tls13 tls13 := by
  unfold unsafe_tls_downgrade shared_capability tls10 tls13
  omega

/-! ## Post-condition -/

/-- Single-call contract: the output is the highest common version of the visible
offer and the server max, including the offer-limited and server-limited cases. -/
def Post_prop (client_offered_max server_max : Int) : Prop :=
  eq_min_prop client_offered_max server_max ∧
    le_offer_prop client_offered_max server_max ∧
      le_server_prop client_offered_max server_max ∧
        greatest_common_prop client_offered_max server_max ∧
          highest_common_prop client_offered_max server_max ∧
            offer_limited_prop client_offered_max server_max ∧
              server_limited_prop client_offered_max server_max ∧
                result_eq_one_arg_prop client_offered_max server_max

/-! ## Property-based tests -/

-- PBT for eq_min_prop
#eval Plausible.Testable.check
  (∀ client_offered_max server_max : Int,
    unsafe_tls_downgrade client_offered_max server_max = min client_offered_max server_max)

-- PBT for le_offer_prop
#eval Plausible.Testable.check
  (∀ client_offered_max server_max : Int,
    unsafe_tls_downgrade client_offered_max server_max ≤ client_offered_max)

-- PBT for le_server_prop
#eval Plausible.Testable.check
  (∀ client_offered_max server_max : Int,
    unsafe_tls_downgrade client_offered_max server_max ≤ server_max)

-- PBT for greatest_common_prop
#eval Plausible.Testable.check
  (∀ client_offered_max server_max v : Int,
    v ≤ client_offered_max → v ≤ server_max →
      v ≤ unsafe_tls_downgrade client_offered_max server_max)
  { numRetries := 200 }

-- PBT for highest_common_prop
#eval Plausible.Testable.check
  (∀ client_offered_max server_max : Int,
    unsafe_tls_downgrade client_offered_max server_max ≤ client_offered_max ∧
      unsafe_tls_downgrade client_offered_max server_max ≤ server_max ∧
        ∀ v : Int, v ≤ client_offered_max → v ≤ server_max →
          v ≤ unsafe_tls_downgrade client_offered_max server_max)
  { numRetries := 200 }

-- PBT for offer_limited_prop
#eval Plausible.Testable.check
  (∀ client_offered_max server_max : Int,
    client_offered_max ≤ server_max →
      unsafe_tls_downgrade client_offered_max server_max = client_offered_max)

-- PBT for server_limited_prop
#eval Plausible.Testable.check
  (∀ client_offered_max server_max : Int,
    server_max ≤ client_offered_max →
      unsafe_tls_downgrade client_offered_max server_max = server_max)

-- PBT for result_eq_one_arg_prop
#eval Plausible.Testable.check
  (∀ client_offered_max server_max : Int,
    unsafe_tls_downgrade client_offered_max server_max = client_offered_max ∨
      unsafe_tls_downgrade client_offered_max server_max = server_max)

-- PBT for mono_offer_prop
#eval Plausible.Testable.check
  (∀ offer1 offer2 server_max : Int,
    offer1 ≤ offer2 →
      unsafe_tls_downgrade offer1 server_max ≤ unsafe_tls_downgrade offer2 server_max)

-- PBT for mono_server_prop
#eval Plausible.Testable.check
  (∀ client_offered_max server1 server2 : Int,
    server1 ≤ server2 →
      unsafe_tls_downgrade client_offered_max server1 ≤
        unsafe_tls_downgrade client_offered_max server2)

-- PBT for comm_prop
#eval Plausible.Testable.check
  (∀ a b : Int, unsafe_tls_downgrade a b = unsafe_tls_downgrade b a)

-- PBT for equal_versions_prop
#eval Plausible.Testable.check
  (∀ v : Int, unsafe_tls_downgrade v v = v)

-- PBT for strict_downgrade_prop
#eval Plausible.Testable.check
  (∀ true_client_max tampered_offer server_max : Int,
    tampered_offer < true_client_max →
      tampered_offer < server_max →
        unsafe_tls_downgrade tampered_offer server_max <
          shared_capability true_client_max server_max)
  { numRetries := 200 }

-- PBT for missing_sentinel_prop
#eval Plausible.Testable.check
  (∀ true_client_max client_offered_max server_max : Int,
    client_offered_max < true_client_max →
      client_offered_max ≤ server_max →
        unsafe_tls_downgrade client_offered_max server_max = client_offered_max ∧
          unsafe_tls_downgrade client_offered_max server_max < true_client_max)
  { numRetries := 200 }

-- PBT for tamper_weakens_prop
#eval Plausible.Testable.check
  (∀ true_client_max client_offered_max server_max : Int,
    client_offered_max ≤ true_client_max →
      unsafe_tls_downgrade client_offered_max server_max ≤
        shared_capability true_client_max server_max)

-- PBT for downgrade_gap_prop
#eval Plausible.Testable.check
  (∀ true_client_max client_offered_max server_max : Int,
    client_offered_max < shared_capability true_client_max server_max →
      unsafe_tls_downgrade client_offered_max server_max = client_offered_max ∧
        unsafe_tls_downgrade client_offered_max server_max <
          shared_capability true_client_max server_max)
  { numRetries := 200 }

-- PBT for oblivious_prop
#eval Plausible.Testable.check
  (∀ true1 true2 offer server : Int,
    unsafe_negotiate true1 offer server = unsafe_negotiate true2 offer server)

-- PBT for negotiate_ignores_true_prop
#eval Plausible.Testable.check
  (∀ true_client_max client_offered_max server_max : Int,
    unsafe_negotiate true_client_max client_offered_max server_max =
      unsafe_tls_downgrade client_offered_max server_max)

-- PBT for result_valid_prop
-- Inputs are reduced mod 5 so every sample is a lecture version code.
#eval Plausible.Testable.check
  (∀ c s : Nat,
    ValidVersion (unsafe_tls_downgrade (Int.ofNat (c % 5)) (Int.ofNat (s % 5))))

-- PBT for Post_prop
-- Unguarded executable form. The implication clauses of Post_prop are equivalent
-- to the if-expression below, so this check does not discard samples.
-- greatest_common_prop is also tested by its own PBT and the bounded triple check.
#eval Plausible.Testable.check
  (∀ client_offered_max server_max : Int,
    unsafe_tls_downgrade client_offered_max server_max = min client_offered_max server_max ∧
      unsafe_tls_downgrade client_offered_max server_max ≤ client_offered_max ∧
        unsafe_tls_downgrade client_offered_max server_max ≤ server_max ∧
          unsafe_tls_downgrade client_offered_max server_max =
            (if client_offered_max ≤ server_max then client_offered_max else server_max) ∧
            (unsafe_tls_downgrade client_offered_max server_max = client_offered_max ∨
              unsafe_tls_downgrade client_offered_max server_max = server_max))

def pbtInts : List Int := [-5, -1, 0, 1, 2, 3, 4, 5, 8]

def pbtAll2 (p : Int → Int → Bool) : Bool :=
  pbtInts.all fun a => pbtInts.all fun b => p a b

def pbtAll3 (p : Int → Int → Int → Bool) : Bool :=
  pbtInts.all fun a => pbtInts.all fun b => pbtInts.all fun c => p a b c

def pbtAll4 (p : Int → Int → Int → Int → Bool) : Bool :=
  pbtInts.all fun a => pbtInts.all fun b =>
    pbtInts.all fun c => pbtInts.all fun d => p a b c d

example : pbtAll2 (fun c s => unsafe_tls_downgrade c s == min c s) = true := by
  native_decide

example : pbtAll2 (fun c s => decide (unsafe_tls_downgrade c s ≤ c)) = true := by
  native_decide

example : pbtAll2 (fun c s => decide (unsafe_tls_downgrade c s ≤ s)) = true := by
  native_decide

example : pbtAll3 (fun c s v =>
    !(decide (v ≤ c) && decide (v ≤ s)) || decide (v ≤ unsafe_tls_downgrade c s)) = true := by
  native_decide

example : pbtAll2 (fun c s =>
    !(decide (c ≤ s)) || unsafe_tls_downgrade c s == c) = true := by
  native_decide

example : pbtAll2 (fun c s =>
    !(decide (s ≤ c)) || unsafe_tls_downgrade c s == s) = true := by
  native_decide

example : pbtAll2 (fun c s =>
    decide (unsafe_tls_downgrade c s = c ∨ unsafe_tls_downgrade c s = s)) = true := by
  native_decide

example : pbtAll3 (fun o1 o2 s =>
    !(decide (o1 ≤ o2)) ||
      decide (unsafe_tls_downgrade o1 s ≤ unsafe_tls_downgrade o2 s)) = true := by
  native_decide

example : pbtAll3 (fun c s1 s2 =>
    !(decide (s1 ≤ s2)) ||
      decide (unsafe_tls_downgrade c s1 ≤ unsafe_tls_downgrade c s2)) = true := by
  native_decide

example : pbtAll2 (fun a b => unsafe_tls_downgrade a b == unsafe_tls_downgrade b a) = true := by
  native_decide

example : pbtInts.all (fun v => unsafe_tls_downgrade v v == v) = true := by
  native_decide

example : pbtAll3 (fun t o s =>
    !(decide (o < t) && decide (o < s)) ||
      decide (unsafe_tls_downgrade o s < shared_capability t s)) = true := by
  native_decide

example : pbtAll3 (fun t o s =>
    !(decide (o < t) && decide (o ≤ s)) ||
      (unsafe_tls_downgrade o s == o && decide (unsafe_tls_downgrade o s < t))) = true := by
  native_decide

example : pbtAll3 (fun t o s =>
    !(decide (o ≤ t)) ||
      decide (unsafe_tls_downgrade o s ≤ shared_capability t s)) = true := by
  native_decide

example : pbtAll3 (fun t o s =>
    !(decide (o < shared_capability t s)) ||
      (unsafe_tls_downgrade o s == o &&
        decide (unsafe_tls_downgrade o s < shared_capability t s))) = true := by
  native_decide

example : pbtAll4 (fun t1 t2 o s =>
    unsafe_negotiate t1 o s == unsafe_negotiate t2 o s) = true := by
  native_decide

example : pbtAll3 (fun t o s =>
    unsafe_negotiate t o s == unsafe_tls_downgrade o s) = true := by
  native_decide

example : (List.range 5).all (fun c =>
    (List.range 5).all (fun s =>
      unsafe_tls_downgrade (Int.ofNat c) (Int.ofNat s) ==
        min (Int.ofNat c) (Int.ofNat s))) = true := by
  native_decide

example : (List.range 5).all (fun c =>
    (List.range 5).all (fun s =>
      decide (ValidVersion (unsafe_tls_downgrade (Int.ofNat c) (Int.ofNat s))))) = true := by
  native_decide

example : pbtAll2 (fun c s =>
    unsafe_tls_downgrade c s == min c s &&
      decide (unsafe_tls_downgrade c s ≤ c) &&
        decide (unsafe_tls_downgrade c s ≤ s) &&
          (!(decide (c ≤ s)) || unsafe_tls_downgrade c s == c) &&
            (!(decide (s ≤ c)) || unsafe_tls_downgrade c s == s) &&
              decide (unsafe_tls_downgrade c s = c ∨ unsafe_tls_downgrade c s = s)) = true := by
  native_decide

/-! ## Correctness theorem -/

theorem correctness_thm
    (client_offered_max server_max : Int)
    (hPre : Pre client_offered_max server_max) :
    Post_prop client_offered_max server_max := by
  unfold Pre at hPre
  cases hPre
  exact ⟨
    eq_min_thm client_offered_max server_max,
    le_offer_thm client_offered_max server_max,
    le_server_thm client_offered_max server_max,
    greatest_common_thm client_offered_max server_max,
    highest_common_thm client_offered_max server_max,
    offer_limited_thm client_offered_max server_max,
    server_limited_thm client_offered_max server_max,
    result_eq_one_arg_thm client_offered_max server_max
  ⟩

/-! ## Imperative implementation -/

/-- Imperative min: mutable result, replaced when the server max is strictly smaller. -/
def unsafe_tls_downgradeImp (client_offered_max server_max : Int) : Int :=
  Id.run do
    let mut result : Int := client_offered_max
    if server_max < result then
      result := server_max
    return result

/-! ## Imperative tests -/

example : unsafe_tls_downgradeImp 4 4 = 4 := by native_decide
example : unsafe_tls_downgradeImp 1 4 = 1 := by native_decide
example : unsafe_tls_downgradeImp 4 2 = 2 := by native_decide
example : unsafe_tls_downgradeImp 3 3 = 3 := by native_decide
example : unsafe_tls_downgradeImp 4 0 = 0 := by native_decide
example : unsafe_tls_downgradeImp 2 4 ≥ unsafe_tls_downgradeImp 1 4 := by native_decide
example : check unsafe_tls_downgradeImp = true := by native_decide
example : unsafe_tls_downgradeImp (-3) 2 = -3 := by native_decide
example : unsafe_tls_downgradeImp 2 (-3) = -3 := by native_decide

#eval unsafe_tls_downgradeImp 4 4
#eval unsafe_tls_downgradeImp 1 4
#eval unsafe_tls_downgradeImp 4 2
#eval unsafe_tls_downgradeImp 3 3
#eval unsafe_tls_downgradeImp 4 0
#eval check unsafe_tls_downgradeImp

/-! ## Equivalence theorem -/

theorem equivalence_thm (client_offered_max server_max : Int) :
    unsafe_tls_downgrade client_offered_max server_max =
      unsafe_tls_downgradeImp client_offered_max server_max := by
  have himp :
      unsafe_tls_downgradeImp client_offered_max server_max =
        (if server_max < client_offered_max then server_max else client_offered_max) := by
    simp only [unsafe_tls_downgradeImp, Id.run, bind, pure]
  have hmin :
      (if server_max < client_offered_max then server_max else client_offered_max) =
        min client_offered_max server_max := by
    unfold min Int.instMin minOfLe
    by_cases h : server_max < client_offered_max
    · have hle : ¬ client_offered_max ≤ server_max := Int.not_le.mpr h
      simp [h, hle]
    · have hle : client_offered_max ≤ server_max := Int.not_lt.mp h
      simp [h, hle]
  unfold unsafe_tls_downgrade
  calc
    min client_offered_max server_max =
        (if server_max < client_offered_max then server_max else client_offered_max) := hmin.symm
    _ = unsafe_tls_downgradeImp client_offered_max server_max := himp.symm

end «95_unsafeTlsDowngrade»
