import Mathlib

/-!
# Unsafe TLS version downgrade

Lean 4 formalization of the Python program `unsafe_tls_downgrade`
(MIT 6.858 Lecture 14 — TLS / Downgrade).

A TLS server picks the *highest common version* between the version the client
appears to offer and its own maximum, i.e. `min(client_offered_max, server_max)`.
The vulnerability is that nothing binds `client_offered_max` to the client's
*true* capability: an on-path attacker may strip strong versions from the
ClientHello, and the server obliviously negotiates the highest common version of
the *tampered* offer.

Versions are integers (higher = newer):
`0 = SSL 3.0`, `1 = TLS 1.0`, `2 = TLS 1.1`, `3 = TLS 1.2`, `4 = TLS 1.3`.

The file contains:
* a functional implementation `unsafeTlsDowngrade`,
* unit tests mirroring the Python `check` function,
* a precondition `Pre`, property predicates with proofs, and a postcondition
  `Post_prop` together with the correctness theorem `correctness_thm`,
* an imperative implementation `unsafeTlsDowngradeImp` using `Id.run do` with
  mutable state, plus the equivalence theorem.
-/

namespace UnsafeTlsDowngrade

/-! ## Functional implementation -/

/-- `unsafeTlsDowngrade c s` returns `min c s`, the highest version supported by
both the (possibly attacker-modified) client offer `c` and the server `s`. -/
def unsafeTlsDowngrade (clientOfferedMax serverMax : Int) : Int :=
  min clientOfferedMax serverMax

/-! ## Unit tests (mirroring the Python `check`) -/

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
-- 6) Monotone in offer: more visible offer ≥ less visible offer.
example : unsafeTlsDowngrade 2 4 ≥ unsafeTlsDowngrade 1 4 := by native_decide

#eval unsafeTlsDowngrade 4 4
#eval unsafeTlsDowngrade 1 4
#eval unsafeTlsDowngrade 4 2
#eval unsafeTlsDowngrade 3 3
#eval unsafeTlsDowngrade 4 0

/-! ## Pre-condition

The Python function is total: it accepts any pair of integers, so the
precondition is trivially true. -/

def Pre (_clientOfferedMax _serverMax : Int) : Prop := True

/-- A version number is a legal TLS version tag (`0 … 4`); used only to state
that the negotiated result stays inside the legal range. -/
def IsVersion (v : Int) : Prop := 0 ≤ v ∧ v ≤ 4

/-! ## Properties -/

/-- The result never exceeds the client's offer. -/
def leClient_prop (c s : Int) : Prop := unsafeTlsDowngrade c s ≤ c

theorem leClient_thm (c s : Int) : leClient_prop c s := by
  unfold leClient_prop unsafeTlsDowngrade
  exact min_le_left c s

/-- The result never exceeds the server's maximum. -/
def leServer_prop (c s : Int) : Prop := unsafeTlsDowngrade c s ≤ s

theorem leServer_thm (c s : Int) : leServer_prop c s := by
  unfold leServer_prop unsafeTlsDowngrade
  exact min_le_right c s

/-- The result is exactly one of the two inputs (no version is invented). -/
def isOneOf_prop (c s : Int) : Prop :=
  unsafeTlsDowngrade c s = c ∨ unsafeTlsDowngrade c s = s

theorem isOneOf_thm (c s : Int) : isOneOf_prop c s := by
  unfold isOneOf_prop unsafeTlsDowngrade
  rcases le_total c s with h | h
  · exact Or.inl (min_eq_left h)
  · exact Or.inr (min_eq_right h)

/-- The result is the *greatest* common version: any version supported by both
sides is at most the negotiated one. -/
def greatestCommon_prop (c s : Int) : Prop :=
  ∀ v : Int, v ≤ c → v ≤ s → v ≤ unsafeTlsDowngrade c s

theorem greatestCommon_thm (c s : Int) : greatestCommon_prop c s := by
  intro v hc hs
  unfold unsafeTlsDowngrade
  exact le_min hc hs

/-- Monotonicity in the offer (Python test 6): a less-stripped offer never
yields a worse negotiated version. -/
def monotoneInOffer_prop (c c' s : Int) : Prop :=
  c ≤ c' → unsafeTlsDowngrade c s ≤ unsafeTlsDowngrade c' s

theorem monotoneInOffer_thm (c c' s : Int) : monotoneInOffer_prop c c' s := by
  intro h
  unfold unsafeTlsDowngrade
  exact min_le_min h le_rfl

/-- Monotonicity in the server maximum. -/
def monotoneInServer_prop (c s s' : Int) : Prop :=
  s ≤ s' → unsafeTlsDowngrade c s ≤ unsafeTlsDowngrade c s'

theorem monotoneInServer_thm (c s s' : Int) : monotoneInServer_prop c s s' := by
  intro h
  unfold unsafeTlsDowngrade
  exact min_le_min le_rfl h

/-- When client and server agree on the same maximum, that version is chosen
(Python tests 1 and 4). -/
def agree_prop (v : Int) : Prop := unsafeTlsDowngrade v v = v

theorem agree_thm (v : Int) : agree_prop v := by
  unfold agree_prop unsafeTlsDowngrade
  exact min_self v

/-- The negotiated version stays a legal TLS version tag whenever both inputs
are legal version tags. -/
def rangeClosed_prop (c s : Int) : Prop :=
  IsVersion c → IsVersion s → IsVersion (unsafeTlsDowngrade c s)

theorem rangeClosed_thm (c s : Int) : rangeClosed_prop c s := by
  rintro ⟨hc0, hc4⟩ ⟨hs0, _⟩
  unfold IsVersion unsafeTlsDowngrade
  constructor
  · exact le_min hc0 hs0
  · exact le_trans (min_le_left c s) hc4

/-! ### The vulnerability

An on-path attacker replaces the client's true maximum `c` by a stripped offer
`c' ≤ c`.  The server has no way to notice: it just negotiates `min c' s`, which
can be *strictly weaker* than the version the honest parties share. -/

/-- Stripping the offer can only weaken (never strengthen) the negotiated
version — the attack is always "safe" for the attacker. -/
def attackerWeakens_prop (cTrue cStripped s : Int) : Prop :=
  cStripped ≤ cTrue →
    unsafeTlsDowngrade cStripped s ≤ unsafeTlsDowngrade cTrue s

theorem attackerWeakens_thm (cTrue cStripped s : Int) :
    attackerWeakens_prop cTrue cStripped s := by
  intro h
  unfold unsafeTlsDowngrade
  exact min_le_min h le_rfl

/-- The downgrade actually happens: there is a configuration in which client and
server both support TLS 1.3 (`4`) yet the negotiated version is SSL 3.0 (`0`),
because the attacker stripped the offer.  This is the missing-sentinel bug. -/
def downgradeExploitable_prop : Prop :=
  ∃ cTrue cStripped s : Int,
    IsVersion cTrue ∧ IsVersion cStripped ∧ IsVersion s ∧
    cStripped < cTrue ∧
    unsafeTlsDowngrade cStripped s < unsafeTlsDowngrade cTrue s

theorem downgradeExploitable_thm : downgradeExploitable_prop := by
  refine ⟨4, 0, 4, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num⟩, by norm_num, ?_⟩
  unfold unsafeTlsDowngrade
  norm_num

/-- A *safe* server (one binding the true client capability into the
negotiation, e.g. via a downgrade sentinel) would always end up at
`min cTrue serverMax`.  `unsafeTlsDowngrade` does **not** have this property:
it negotiates from the tampered offer alone. -/
def noCapabilityCheck_prop : Prop :=
  ¬ ∀ cTrue cStripped s : Int,
      cStripped ≤ cTrue → unsafeTlsDowngrade cStripped s = min cTrue s

theorem noCapabilityCheck_thm : noCapabilityCheck_prop := by
  intro h
  have := h 4 1 4 (by norm_num)
  unfold unsafeTlsDowngrade at this
  norm_num at this

/-! ## Post-condition -/

/-- Full functional specification: the result is the highest common version. -/
def Post_prop (c s : Int) : Prop :=
  leClient_prop c s ∧
  leServer_prop c s ∧
  isOneOf_prop c s ∧
  greatestCommon_prop c s ∧
  rangeClosed_prop c s ∧
  unsafeTlsDowngrade c s = min c s

theorem correctness_thm (c s : Int) : Pre c s → Post_prop c s := by
  intro _
  exact ⟨leClient_thm c s, leServer_thm c s, isOneOf_thm c s,
    greatestCommon_thm c s, rangeClosed_thm c s, rfl⟩

/-! ## Imperative implementation -/

/-- Imperative version: start from the client's offer, then cap it at the
server's maximum. -/
def unsafeTlsDowngradeImp (clientOfferedMax serverMax : Int) : Int := Id.run do
  let mut negotiated : Int := clientOfferedMax
  if serverMax < negotiated then
    negotiated := serverMax
  return negotiated

/-! ### Imperative tests -/

example : unsafeTlsDowngradeImp 4 4 = 4 := by native_decide
example : unsafeTlsDowngradeImp 1 4 = 1 := by native_decide
example : unsafeTlsDowngradeImp 4 2 = 2 := by native_decide
example : unsafeTlsDowngradeImp 3 3 = 3 := by native_decide
example : unsafeTlsDowngradeImp 4 0 = 0 := by native_decide
example : unsafeTlsDowngradeImp 2 4 ≥ unsafeTlsDowngradeImp 1 4 := by native_decide

#eval unsafeTlsDowngradeImp 4 4
#eval unsafeTlsDowngradeImp 1 4
#eval unsafeTlsDowngradeImp 4 2
#eval unsafeTlsDowngradeImp 3 3
#eval unsafeTlsDowngradeImp 4 0

/-! ## Equivalence -/

def equiv_prop (c s : Int) : Prop :=
  unsafeTlsDowngrade c s = unsafeTlsDowngradeImp c s

theorem equiv_thm (c s : Int) : equiv_prop c s := by
  unfold equiv_prop unsafeTlsDowngrade unsafeTlsDowngradeImp Id.run
  simp only []
  split <;> rename_i h
  · exact min_eq_right (le_of_lt h)
  · exact min_eq_left (not_lt.mp h)

theorem equiv_thm' : unsafeTlsDowngrade = unsafeTlsDowngradeImp := by
  funext c s
  exact equiv_thm c s

end UnsafeTlsDowngrade
