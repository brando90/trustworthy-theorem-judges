import Mathlib

/-!
# Unsafe TLS Version Downgrade (MIT 6.858 Lecture 14)

Formalization of `unsafe_tls_downgrade`:
A TLS server picks `min(client_offered_max, server_max)` — the highest common protocol
version between the client's offered maximum and the server's maximum supported version.
Without a sentinel binding the client's true capability into the negotiation, an on-path
attacker who strips strong versions from the `ClientHello` causes the server to pick the
highest common version of the tampered offer, downgrading the connection.

Protocol version encoding (higher = newer):
- `0` = SSL 3.0
- `1` = TLS 1.0
- `2` = TLS 1.1
- `3` = TLS 1.2
- `4` = TLS 1.3
-/

namespace «95_unsafeTlsDowngrade»

/-! ## 1. Functional Implementation -/

/-- Return `min(client_offered_max, server_max)` — the highest common version.
The vulnerability is the lack of a check that `client_offered_max` matches the
client's true capability. -/
def unsafe_tls_downgrade (client_offered_max server_max : Int) : Int :=
  min client_offered_max server_max

/-- CamelCase alias for `unsafe_tls_downgrade`. -/
abbrev unsafeTlsDowngrade (client_offered_max server_max : Int) : Int :=
  unsafe_tls_downgrade client_offered_max server_max

/-- Executable check bundle translating the Python `check(candidate)` test suite. -/
def check (candidate : Int → Int → Int) : Bool :=
  -- 1) No attack: TLS 1.3 negotiated.
  (candidate 4 4 == 4) &&
  -- 2) VULNERABILITY: attacker stripped offer to TLS 1.0; server picks 1.
  (candidate 1 4 == 1) &&
  -- 3) Server caps the result.
  (candidate 4 2 == 2) &&
  -- 4) Match: full version negotiated.
  (candidate 3 3 == 3) &&
  -- 5) Edge: legacy-only server.
  (candidate 4 0 == 0) &&
  -- 6) Monotone in offer: more visible offer ≥ less visible offer.
  (candidate 2 4 ≥ candidate 1 4)

/-! ## 2. Unit Tests -/

#eval unsafe_tls_downgrade 4 4
#eval unsafe_tls_downgrade 1 4
#eval unsafe_tls_downgrade 4 2
#eval unsafe_tls_downgrade 3 3
#eval unsafe_tls_downgrade 4 0
#eval check unsafe_tls_downgrade

-- 1) No attack: TLS 1.3 negotiated.
example : unsafe_tls_downgrade 4 4 = 4 := by native_decide

-- 2) VULNERABILITY: attacker stripped offer to TLS 1.0; server picks 1.
example : unsafe_tls_downgrade 1 4 = 1 := by native_decide

-- 3) Server caps the result.
example : unsafe_tls_downgrade 4 2 = 2 := by native_decide

-- 4) Match: full version negotiated.
example : unsafe_tls_downgrade 3 3 = 3 := by native_decide

-- 5) Edge: legacy-only server.
example : unsafe_tls_downgrade 4 0 = 0 := by native_decide

-- 6) Monotone in offer: more visible offer ≥ less visible offer.
example : unsafe_tls_downgrade 2 4 ≥ unsafe_tls_downgrade 1 4 := by native_decide

-- Full Python `check` suite passes.
example : check unsafe_tls_downgrade = true := by native_decide

/-! ## 3. Pre-condition -/

/-- Pre-condition for `unsafe_tls_downgrade`: any pair of integer versions is admissible. -/
def Pre (_client_offered_max _server_max : Int) : Prop := True

instance (c s : Int) : Decidable (Pre c s) := by
  unfold Pre
  infer_instance

/-- Predicate characterizing the standard TLS protocol version numbers `0..4`
(0 = SSL 3.0, 1 = TLS 1.0, 2 = TLS 1.1, 3 = TLS 1.2, 4 = TLS 1.3). -/
def ValidTlsVersion (v : Int) : Prop := 0 ≤ v ∧ v ≤ 4

instance (v : Int) : Decidable (ValidTlsVersion v) := by
  unfold ValidTlsVersion
  infer_instance

/-! ## 4. Properties and Theorems -/

/-- Exact specification property: result equals `min client_offered_max server_max`. -/
def exact_min_prop (client_offered_max server_max : Int) : Prop :=
  unsafe_tls_downgrade client_offered_max server_max = min client_offered_max server_max

instance (c s : Int) : Decidable (exact_min_prop c s) := by
  unfold exact_min_prop; infer_instance

theorem exact_min_thm (client_offered_max server_max : Int) :
    exact_min_prop client_offered_max server_max := by
  rfl

/-- Upper-bound by client offer: negotiated version never exceeds `client_offered_max`. -/
def le_client_offer_prop (client_offered_max server_max : Int) : Prop :=
  unsafe_tls_downgrade client_offered_max server_max ≤ client_offered_max

instance (c s : Int) : Decidable (le_client_offer_prop c s) := by
  unfold le_client_offer_prop; infer_instance

theorem le_client_offer_thm (client_offered_max server_max : Int) :
    le_client_offer_prop client_offered_max server_max := by
  unfold le_client_offer_prop unsafe_tls_downgrade
  exact Int.min_le_left client_offered_max server_max

/-- Server-cap property: negotiated version never exceeds `server_max`. -/
def le_server_max_prop (client_offered_max server_max : Int) : Prop :=
  unsafe_tls_downgrade client_offered_max server_max ≤ server_max

instance (c s : Int) : Decidable (le_server_max_prop c s) := by
  unfold le_server_max_prop; infer_instance

theorem le_server_max_thm (client_offered_max server_max : Int) :
    le_server_max_prop client_offered_max server_max := by
  unfold le_server_max_prop unsafe_tls_downgrade
  exact Int.min_le_right client_offered_max server_max

/-- Choice property: the negotiated version is either `client_offered_max` or `server_max`. -/
def choice_prop (client_offered_max server_max : Int) : Prop :=
  unsafe_tls_downgrade client_offered_max server_max = client_offered_max ∨
  unsafe_tls_downgrade client_offered_max server_max = server_max

instance (c s : Int) : Decidable (choice_prop c s) := by
  unfold choice_prop; infer_instance

theorem choice_thm (client_offered_max server_max : Int) :
    choice_prop client_offered_max server_max := by
  unfold choice_prop unsafe_tls_downgrade
  exact min_choice client_offered_max server_max

/-- Highest common version (greatest lower bound) property: any version `v` supported by
both the offer and the server is at most the negotiated version. -/
def highest_common_prop (client_offered_max server_max v : Int) : Prop :=
  v ≤ client_offered_max → v ≤ server_max →
    v ≤ unsafe_tls_downgrade client_offered_max server_max

instance (c s v : Int) : Decidable (highest_common_prop c s v) := by
  unfold highest_common_prop; infer_instance

theorem highest_common_thm (client_offered_max server_max v : Int) :
    highest_common_prop client_offered_max server_max v := by
  unfold highest_common_prop unsafe_tls_downgrade
  intro hc hs
  exact le_min hc hs

/-- Offer-determines-result when `client_offered_max ≤ server_max` (including when an
attacker strips strong versions below `server_max`). -/
def offer_caps_when_le_prop (client_offered_max server_max : Int) : Prop :=
  client_offered_max ≤ server_max →
    unsafe_tls_downgrade client_offered_max server_max = client_offered_max

instance (c s : Int) : Decidable (offer_caps_when_le_prop c s) := by
  unfold offer_caps_when_le_prop; infer_instance

theorem offer_caps_when_le_thm (client_offered_max server_max : Int) :
    offer_caps_when_le_prop client_offered_max server_max := by
  unfold offer_caps_when_le_prop unsafe_tls_downgrade
  intro h
  exact min_eq_left h

/-- Server-caps-result when `server_max ≤ client_offered_max`. -/
def server_caps_when_le_prop (client_offered_max server_max : Int) : Prop :=
  server_max ≤ client_offered_max →
    unsafe_tls_downgrade client_offered_max server_max = server_max

instance (c s : Int) : Decidable (server_caps_when_le_prop c s) := by
  unfold server_caps_when_le_prop; infer_instance

theorem server_caps_when_le_thm (client_offered_max server_max : Int) :
    server_caps_when_le_prop client_offered_max server_max := by
  unfold server_caps_when_le_prop unsafe_tls_downgrade
  intro h
  exact min_eq_right h

/-- Idempotence / matching version property: when client offer and server max match,
that exact version is negotiated. -/
def matching_version_prop (v : Int) : Prop :=
  unsafe_tls_downgrade v v = v

instance (v : Int) : Decidable (matching_version_prop v) := by
  unfold matching_version_prop; infer_instance

theorem matching_version_thm (v : Int) :
    matching_version_prop v := by
  unfold matching_version_prop unsafe_tls_downgrade
  exact min_self v

/-- Symmetry / commutativity of `unsafe_tls_downgrade`. -/
def comm_prop (client_offered_max server_max : Int) : Prop :=
  unsafe_tls_downgrade client_offered_max server_max =
    unsafe_tls_downgrade server_max client_offered_max

instance (c s : Int) : Decidable (comm_prop c s) := by
  unfold comm_prop; infer_instance

theorem comm_thm (client_offered_max server_max : Int) :
    comm_prop client_offered_max server_max := by
  unfold comm_prop unsafe_tls_downgrade
  exact min_comm client_offered_max server_max

/-- Monotonicity in the client offer: a higher or equal visible offer yields a higher
or equal negotiated version for a fixed `server_max`. -/
def monotone_offer_prop (offer₁ offer₂ server_max : Int) : Prop :=
  offer₁ ≤ offer₂ →
    unsafe_tls_downgrade offer₁ server_max ≤ unsafe_tls_downgrade offer₂ server_max

instance (o₁ o₂ s : Int) : Decidable (monotone_offer_prop o₁ o₂ s) := by
  unfold monotone_offer_prop; infer_instance

theorem monotone_offer_thm (offer₁ offer₂ server_max : Int) :
    monotone_offer_prop offer₁ offer₂ server_max := by
  unfold monotone_offer_prop unsafe_tls_downgrade
  intro h
  omega

/-- Monotonicity in the server maximum: a higher or equal `server_max` yields a higher
or equal negotiated version for a fixed `client_offered_max`. -/
def monotone_server_prop (client_offered_max server₁ server₂ : Int) : Prop :=
  server₁ ≤ server₂ →
    unsafe_tls_downgrade client_offered_max server₁ ≤
      unsafe_tls_downgrade client_offered_max server₂

instance (c s₁ s₂ : Int) : Decidable (monotone_server_prop c s₁ s₂) := by
  unfold monotone_server_prop; infer_instance

theorem monotone_server_thm (client_offered_max server₁ server₂ : Int) :
    monotone_server_prop client_offered_max server₁ server₂ := by
  unfold monotone_server_prop unsafe_tls_downgrade
  intro h
  omega

/-- Joint monotonicity in both arguments. -/
def monotone_both_prop (offer₁ offer₂ server₁ server₂ : Int) : Prop :=
  offer₁ ≤ offer₂ →
  server₁ ≤ server₂ →
    unsafe_tls_downgrade offer₁ server₁ ≤ unsafe_tls_downgrade offer₂ server₂

instance (o₁ o₂ s₁ s₂ : Int) : Decidable (monotone_both_prop o₁ o₂ s₁ s₂) := by
  unfold monotone_both_prop; infer_instance

theorem monotone_both_thm (offer₁ offer₂ server₁ server₂ : Int) :
    monotone_both_prop offer₁ offer₂ server₁ server₂ := by
  unfold monotone_both_prop unsafe_tls_downgrade
  intro ho hs
  omega

/-- Attacker stripping weak-downgrade property: if an attacker strips strong versions so
`tampered_offer ≤ client_true_max`, the negotiated version is at most the honest
negotiated version. -/
def attacker_strip_weakens_prop (tampered_offer client_true_max server_max : Int) : Prop :=
  tampered_offer ≤ client_true_max →
    unsafe_tls_downgrade tampered_offer server_max ≤
      unsafe_tls_downgrade client_true_max server_max

instance (t c s : Int) : Decidable (attacker_strip_weakens_prop t c s) := by
  unfold attacker_strip_weakens_prop; infer_instance

theorem attacker_strip_weakens_thm (tampered_offer client_true_max server_max : Int) :
    attacker_strip_weakens_prop tampered_offer client_true_max server_max := by
  exact monotone_offer_thm tampered_offer client_true_max server_max

/-- Strict downgrade vulnerability property: when an on-path attacker strips strong versions
from `client_true_max` down to `tampered_offer` with `tampered_offer < client_true_max`
and `tampered_offer < server_max`, the server negotiates `tampered_offer`, which is
strictly weaker than the honest negotiated version `unsafe_tls_downgrade client_true_max server_max`. -/
def downgrade_vulnerability_prop (tampered_offer client_true_max server_max : Int) : Prop :=
  tampered_offer < client_true_max →
  tampered_offer < server_max →
    unsafe_tls_downgrade tampered_offer server_max = tampered_offer ∧
    unsafe_tls_downgrade tampered_offer server_max <
      unsafe_tls_downgrade client_true_max server_max

instance (t c s : Int) : Decidable (downgrade_vulnerability_prop t c s) := by
  unfold downgrade_vulnerability_prop; infer_instance

theorem downgrade_vulnerability_thm (tampered_offer client_true_max server_max : Int) :
    downgrade_vulnerability_prop tampered_offer client_true_max server_max := by
  unfold downgrade_vulnerability_prop unsafe_tls_downgrade
  intro h_client h_server
  omega

/-- Non-negativity preservation: non-negative version inputs yield a non-negative
negotiated version. -/
def nonneg_preserved_prop (client_offered_max server_max : Int) : Prop :=
  0 ≤ client_offered_max →
  0 ≤ server_max →
    0 ≤ unsafe_tls_downgrade client_offered_max server_max

instance (c s : Int) : Decidable (nonneg_preserved_prop c s) := by
  unfold nonneg_preserved_prop; infer_instance

theorem nonneg_preserved_thm (client_offered_max server_max : Int) :
    nonneg_preserved_prop client_offered_max server_max := by
  unfold nonneg_preserved_prop unsafe_tls_downgrade
  intro hc hs
  omega

/-- Legacy-server edge property: if `0 ≤ client_offered_max` and `server_max = 0`
(SSL 3.0 only), the server always negotiates `0`. -/
def legacy_server_zero_prop (client_offered_max : Int) : Prop :=
  0 ≤ client_offered_max → unsafe_tls_downgrade client_offered_max 0 = 0

instance (c : Int) : Decidable (legacy_server_zero_prop c) := by
  unfold legacy_server_zero_prop; infer_instance

theorem legacy_server_zero_thm (client_offered_max : Int) :
    legacy_server_zero_prop client_offered_max := by
  unfold legacy_server_zero_prop unsafe_tls_downgrade
  intro h
  omega

/-- Version range preservation: if both `client_offered_max` and `server_max` are valid
TLS versions in `[0, 4]`, the negotiated version is also a valid TLS version in `[0, 4]`. -/
def valid_version_preserved_prop (client_offered_max server_max : Int) : Prop :=
  ValidTlsVersion client_offered_max →
  ValidTlsVersion server_max →
    ValidTlsVersion (unsafe_tls_downgrade client_offered_max server_max)

instance (c s : Int) : Decidable (valid_version_preserved_prop c s) := by
  unfold valid_version_preserved_prop; infer_instance

theorem valid_version_preserved_thm (client_offered_max server_max : Int) :
    valid_version_preserved_prop client_offered_max server_max := by
  unfold valid_version_preserved_prop ValidTlsVersion unsafe_tls_downgrade
  intro hc hs
  omega

/-- Complete greatest-lower-bound characterization: a version `r` equals
`unsafe_tls_downgrade client_offered_max server_max` if and only if `r` is supported by
both offer and server and is at least as new as every common version `v`. -/
theorem greatest_common_iff_thm (client_offered_max server_max r : Int) :
    r = unsafe_tls_downgrade client_offered_max server_max ↔
      (r ≤ client_offered_max ∧ r ≤ server_max ∧
        ∀ v : Int, v ≤ client_offered_max → v ≤ server_max → v ≤ r) := by
  unfold unsafe_tls_downgrade
  constructor
  · intro hr
    refine ⟨by omega, by omega, ?_⟩
    intro v hvc hvs
    omega
  · rintro ⟨hrc, hrs, hmax⟩
    have hmin : min client_offered_max server_max ≤ r :=
      hmax (min client_offered_max server_max)
        (Int.min_le_left client_offered_max server_max)
        (Int.min_le_right client_offered_max server_max)
    omega

/-- The Python test suite `check` is satisfied by `unsafe_tls_downgrade`. -/
theorem check_unsafe_tls_downgrade_thm : check unsafe_tls_downgrade = true := by
  rfl

/-! ## 5. Post-condition -/

/-- Post-condition combining the core functional and security properties of `unsafe_tls_downgrade`. -/
def Post_prop (client_offered_max server_max : Int) : Prop :=
  exact_min_prop client_offered_max server_max ∧
  le_client_offer_prop client_offered_max server_max ∧
  le_server_max_prop client_offered_max server_max ∧
  choice_prop client_offered_max server_max ∧
  offer_caps_when_le_prop client_offered_max server_max ∧
  server_caps_when_le_prop client_offered_max server_max ∧
  comm_prop client_offered_max server_max ∧
  nonneg_preserved_prop client_offered_max server_max ∧
  valid_version_preserved_prop client_offered_max server_max

instance (c s : Int) : Decidable (Post_prop c s) := by
  unfold Post_prop; infer_instance

/-! ## 6. Property-Based Tests -/

-- PBT for `exact_min_prop`
#eval Plausible.Testable.check
  (∀ client_offered_max server_max : Int,
    exact_min_prop client_offered_max server_max)

-- PBT for `le_client_offer_prop`
#eval Plausible.Testable.check
  (∀ client_offered_max server_max : Int,
    le_client_offer_prop client_offered_max server_max)

-- PBT for `le_server_max_prop`
#eval Plausible.Testable.check
  (∀ client_offered_max server_max : Int,
    le_server_max_prop client_offered_max server_max)

-- PBT for `choice_prop`
#eval Plausible.Testable.check
  (∀ client_offered_max server_max : Int,
    choice_prop client_offered_max server_max)

-- PBT for `highest_common_prop` (general and constructive non-vacuous)
#eval Plausible.Testable.check
  (∀ client_offered_max server_max v : Int,
    decide (highest_common_prop client_offered_max server_max v) = true)

#eval Plausible.Testable.check
  (∀ v : Int, ∀ dc ds : Nat,
    let client_offered_max := v + Int.ofNat dc
    let server_max := v + Int.ofNat ds
    v ≤ unsafe_tls_downgrade client_offered_max server_max)

-- Bounded exhaustive PBT for `highest_common_prop` across version range [-2..6]
example :
    (List.range 9).all (fun i =>
      (List.range 9).all (fun j =>
        (List.range 9).all (fun k =>
          let c : Int := Int.ofNat i - 2
          let s : Int := Int.ofNat j - 2
          let v : Int := Int.ofNat k - 2
          decide (highest_common_prop c s v)))) = true := by
  native_decide

-- PBT for `offer_caps_when_le_prop` (general and constructive non-vacuous)
#eval Plausible.Testable.check
  (∀ client_offered_max server_max : Int,
    decide (offer_caps_when_le_prop client_offered_max server_max) = true)

#eval Plausible.Testable.check
  (∀ client_offered_max : Int, ∀ d : Nat,
    unsafe_tls_downgrade client_offered_max (client_offered_max + Int.ofNat d) =
      client_offered_max)

-- PBT for `server_caps_when_le_prop` (general and constructive non-vacuous)
#eval Plausible.Testable.check
  (∀ client_offered_max server_max : Int,
    decide (server_caps_when_le_prop client_offered_max server_max) = true)

#eval Plausible.Testable.check
  (∀ server_max : Int, ∀ d : Nat,
    unsafe_tls_downgrade (server_max + Int.ofNat d) server_max = server_max)

-- PBT for `matching_version_prop`
#eval Plausible.Testable.check
  (∀ v : Int, matching_version_prop v)

-- PBT for `comm_prop`
#eval Plausible.Testable.check
  (∀ client_offered_max server_max : Int,
    comm_prop client_offered_max server_max)

-- PBT for `monotone_offer_prop` (general, constructive non-vacuous, and bounded exhaustive)
#eval Plausible.Testable.check
  (∀ offer₁ offer₂ server_max : Int,
    decide (monotone_offer_prop offer₁ offer₂ server_max) = true)

#eval Plausible.Testable.check
  (∀ offer₁ server_max : Int, ∀ d : Nat,
    unsafe_tls_downgrade offer₁ server_max ≤
      unsafe_tls_downgrade (offer₁ + Int.ofNat d) server_max)

example :
    (List.range 5).all (fun o₁ =>
      (List.range 5).all (fun o₂ =>
        (List.range 5).all (fun s =>
          decide (monotone_offer_prop (Int.ofNat o₁) (Int.ofNat o₂) (Int.ofNat s))))) = true := by
  native_decide

-- PBT for `monotone_server_prop`
#eval Plausible.Testable.check
  (∀ client_offered_max server₁ server₂ : Int,
    decide (monotone_server_prop client_offered_max server₁ server₂) = true)

#eval Plausible.Testable.check
  (∀ client_offered_max server₁ : Int, ∀ d : Nat,
    unsafe_tls_downgrade client_offered_max server₁ ≤
      unsafe_tls_downgrade client_offered_max (server₁ + Int.ofNat d))

-- PBT for `monotone_both_prop`
#eval Plausible.Testable.check
  (∀ offer₁ offer₂ server₁ server₂ : Int,
    decide (monotone_both_prop offer₁ offer₂ server₁ server₂) = true)

#eval Plausible.Testable.check
  (∀ offer₁ server₁ : Int, ∀ doff dser : Nat,
    unsafe_tls_downgrade offer₁ server₁ ≤
      unsafe_tls_downgrade (offer₁ + Int.ofNat doff) (server₁ + Int.ofNat dser))

-- PBT for `attacker_strip_weakens_prop`
#eval Plausible.Testable.check
  (∀ tampered_offer client_true_max server_max : Int,
    decide (attacker_strip_weakens_prop tampered_offer client_true_max server_max) = true)

-- PBT for `downgrade_vulnerability_prop` (general, constructive non-vacuous, and bounded exhaustive)
#eval Plausible.Testable.check
  (∀ tampered_offer client_true_max server_max : Int,
    decide (downgrade_vulnerability_prop tampered_offer client_true_max server_max) = true)

#eval Plausible.Testable.check
  (∀ tampered_offer : Int, ∀ dc ds : Nat,
    let client_true_max := tampered_offer + Int.ofNat dc + 1
    let server_max := tampered_offer + Int.ofNat ds + 1
    unsafe_tls_downgrade tampered_offer server_max = tampered_offer ∧
    unsafe_tls_downgrade tampered_offer server_max <
      unsafe_tls_downgrade client_true_max server_max)

example :
    (List.range 5).all (fun t =>
      (List.range 5).all (fun c =>
        (List.range 5).all (fun s =>
          decide (downgrade_vulnerability_prop (Int.ofNat t) (Int.ofNat c) (Int.ofNat s))))) = true := by
  native_decide

-- PBT for `nonneg_preserved_prop`
#eval Plausible.Testable.check
  (∀ client_offered_max server_max : Int,
    decide (nonneg_preserved_prop client_offered_max server_max) = true)

#eval Plausible.Testable.check
  (∀ c s : Nat, 0 ≤ unsafe_tls_downgrade (Int.ofNat c) (Int.ofNat s))

-- PBT for `legacy_server_zero_prop`
#eval Plausible.Testable.check
  (∀ client_offered_max : Int,
    decide (legacy_server_zero_prop client_offered_max) = true)

#eval Plausible.Testable.check
  (∀ n : Nat, unsafe_tls_downgrade (Int.ofNat n) 0 = 0)

-- PBT for `valid_version_preserved_prop`
#eval Plausible.Testable.check
  (∀ client_offered_max server_max : Int,
    decide (valid_version_preserved_prop client_offered_max server_max) = true)

example :
    (List.range 5).all (fun c =>
      (List.range 5).all (fun s =>
        decide (valid_version_preserved_prop (Int.ofNat c) (Int.ofNat s)))) = true := by
  native_decide

-- PBT for `Post_prop`
#eval Plausible.Testable.check
  (∀ client_offered_max server_max : Int,
    decide (Post_prop client_offered_max server_max) = true)

example :
    (List.range 9).all (fun i =>
      (List.range 9).all (fun j =>
        let c : Int := Int.ofNat i - 2
        let s : Int := Int.ofNat j - 2
        decide (Post_prop c s))) = true := by
  native_decide

/-! ## 7. Correctness Theorem (`Pre → Post`) -/

/-- Main correctness theorem: for all inputs satisfying `Pre`, `Post_prop` holds. -/
theorem unsafe_tls_downgrade_correct (client_offered_max server_max : Int)
    (_hPre : Pre client_offered_max server_max) :
    Post_prop client_offered_max server_max := by
  unfold Post_prop
  refine ⟨exact_min_thm client_offered_max server_max,
          le_client_offer_thm client_offered_max server_max,
          le_server_max_thm client_offered_max server_max,
          choice_thm client_offered_max server_max,
          offer_caps_when_le_thm client_offered_max server_max,
          server_caps_when_le_thm client_offered_max server_max,
          comm_thm client_offered_max server_max,
          nonneg_preserved_thm client_offered_max server_max,
          valid_version_preserved_thm client_offered_max server_max⟩

/-! ## 8. Imperative Implementation -/

/-- Imperative implementation of `unsafe_tls_downgrade` using `Id.run do` and mutable state. -/
def unsafe_tls_downgrade_imp (client_offered_max server_max : Int) : Int := Id.run do
  let mut negotiated : Int := client_offered_max
  if server_max < negotiated then
    negotiated := server_max
  return negotiated

/-- CamelCase alias for `unsafe_tls_downgrade_imp`. -/
abbrev unsafeTlsDowngradeImp (client_offered_max server_max : Int) : Int :=
  unsafe_tls_downgrade_imp client_offered_max server_max

/-! ## 9. Imperative Tests -/

#eval unsafe_tls_downgrade_imp 4 4
#eval unsafe_tls_downgrade_imp 1 4
#eval unsafe_tls_downgrade_imp 4 2
#eval unsafe_tls_downgrade_imp 3 3
#eval unsafe_tls_downgrade_imp 4 0
#eval check unsafe_tls_downgrade_imp

example : unsafe_tls_downgrade_imp 4 4 = 4 := by native_decide
example : unsafe_tls_downgrade_imp 1 4 = 1 := by native_decide
example : unsafe_tls_downgrade_imp 4 2 = 2 := by native_decide
example : unsafe_tls_downgrade_imp 3 3 = 3 := by native_decide
example : unsafe_tls_downgrade_imp 4 0 = 0 := by native_decide
example : unsafe_tls_downgrade_imp 2 4 ≥ unsafe_tls_downgrade_imp 1 4 := by native_decide
example : check unsafe_tls_downgrade_imp = true := by native_decide

#eval Plausible.Testable.check
  (∀ client_offered_max server_max : Int,
    unsafe_tls_downgrade client_offered_max server_max =
      unsafe_tls_downgrade_imp client_offered_max server_max)

/-! ## 10. Equivalence Theorem -/

/-- Equivalence theorem: the functional and imperative implementations produce identical results
for all integer inputs. -/
theorem unsafe_tls_downgrade_equiv (client_offered_max server_max : Int) :
    unsafe_tls_downgrade client_offered_max server_max =
      unsafe_tls_downgrade_imp client_offered_max server_max := by
  simp only [unsafe_tls_downgrade, unsafe_tls_downgrade_imp, Id.run, Bind.bind, Pure.pure]
  split_ifs <;> omega

/-- The imperative implementation also satisfies the full `Post_prop` specification. -/
theorem unsafe_tls_downgrade_imp_correct (client_offered_max server_max : Int) :
    unsafe_tls_downgrade_imp client_offered_max server_max =
      min client_offered_max server_max := by
  rw [← unsafe_tls_downgrade_equiv]
  rfl

/-- The imperative implementation satisfies the Python `check` suite. -/
theorem check_unsafe_tls_downgrade_imp_thm : check unsafe_tls_downgrade_imp = true := by
  rfl

end «95_unsafeTlsDowngrade»
