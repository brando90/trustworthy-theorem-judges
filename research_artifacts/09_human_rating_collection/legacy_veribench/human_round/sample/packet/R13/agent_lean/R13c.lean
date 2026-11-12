import Mathlib

namespace UnsafeTlsDowngrade

/-- Versions are integers (higher = newer):
    0 = SSL 3.0, 1 = TLS 1.0, 2 = TLS 1.1, 3 = TLS 1.2, 4 = TLS 1.3.

    The server picks the highest common version of the (possibly attacker
    tampered) offer: `min client_offered_max server_max`. -/
def unsafeTlsDowngrade (clientOfferedMax serverMax : Int) : Int :=
  min clientOfferedMax serverMax

/-! ### Test cases from `check` -/

-- 1) No attack: TLS 1.3 negotiated.
example : unsafeTlsDowngrade 4 4 = 4 := by native_decide
-- 2) VULNERABILITY: attacker stripped offer to TLS 1.0; server picks 1.
example : unsafeTlsDowngrade 1 4 = 1 := by native_decide
-- 3) Server caps the result.
example : unsafeTlsDowngrade 4 2 = 2 := by native_decide
-- 4) Match: full version negotiated.
example : unsafeTlsDowngrade 3 3 = 3 := by native_decide
-- 5) Edge: legacy-only server.
example : unsafeTlsDowngrade 4 0 = 0 := by native_decide
-- 6) Monotone in offer.
example : unsafeTlsDowngrade 2 4 ≥ unsafeTlsDowngrade 1 4 := by native_decide

/-! ### Specification -/

def Pre (_clientOfferedMax _serverMax : Int) : Prop := True

/-- The negotiated version never exceeds what the client offered. -/
def le_client_prop (c s : Int) : Prop := unsafeTlsDowngrade c s ≤ c

/-- The negotiated version never exceeds what the server supports. -/
def le_server_prop (c s : Int) : Prop := unsafeTlsDowngrade c s ≤ s

/-- The negotiated version is one of the two inputs. -/
def is_one_of_prop (c s : Int) : Prop :=
  unsafeTlsDowngrade c s = c ∨ unsafeTlsDowngrade c s = s

/-- It is the *greatest* common version: anything supported by both is ≤ it. -/
def greatest_common_prop (c s : Int) : Prop :=
  ∀ v : Int, v ≤ c → v ≤ s → v ≤ unsafeTlsDowngrade c s

/-- Monotone in the (attacker-visible) client offer: this is exactly what makes
    the downgrade attack profitable — stripping versions lowers the result. -/
def monotone_in_offer_prop (c₁ c₂ s : Int) : Prop :=
  c₁ ≤ c₂ → unsafeTlsDowngrade c₁ s ≤ unsafeTlsDowngrade c₂ s

/-- Symmetry of the choice rule. -/
def comm_prop (c s : Int) : Prop :=
  unsafeTlsDowngrade c s = unsafeTlsDowngrade s c

/-- When the client's offer does not exceed the server's max, the offer wins:
    a tampered offer of `1` yields exactly `1`. -/
def attack_prop (c s : Int) : Prop :=
  c ≤ s → unsafeTlsDowngrade c s = c

theorem le_client_thm (c s : Int) : le_client_prop c s := by
  simp [le_client_prop, unsafeTlsDowngrade]

theorem le_server_thm (c s : Int) : le_server_prop c s := by
  simp [le_server_prop, unsafeTlsDowngrade]

theorem is_one_of_thm (c s : Int) : is_one_of_prop c s := by
  simpa [is_one_of_prop, unsafeTlsDowngrade] using min_choice c s

theorem greatest_common_thm (c s : Int) : greatest_common_prop c s := by
  intro v hc hs
  exact le_min hc hs

theorem monotone_in_offer_thm (c₁ c₂ s : Int) : monotone_in_offer_prop c₁ c₂ s := by
  intro h
  exact min_le_min h (le_refl s)

theorem comm_thm (c s : Int) : comm_prop c s := by
  simp [comm_prop, unsafeTlsDowngrade, min_comm]

theorem attack_thm (c s : Int) : attack_prop c s := by
  intro h
  simp [attack_prop, unsafeTlsDowngrade, min_eq_left h]

def Post (c s : Int) : Prop :=
  le_client_prop c s ∧ le_server_prop c s ∧ is_one_of_prop c s ∧
  greatest_common_prop c s ∧ comm_prop c s ∧ attack_prop c s ∧
  (∀ c' : Int, monotone_in_offer_prop c' c s)

theorem correctness (c s : Int) : Pre c s → Post c s := by
  intro _
  exact ⟨le_client_thm c s, le_server_thm c s, is_one_of_thm c s,
         greatest_common_thm c s, comm_thm c s, attack_thm c s,
         fun c' => monotone_in_offer_thm c' c s⟩

end UnsafeTlsDowngrade