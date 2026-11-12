import Mathlib

/-!
# Unsafe TLS version downgrade (VeriBench 95)

Formalization of the Python program

```python
def unsafe_tls_downgrade(client_offered_max: int, server_max: int) -> int:
    return min(client_offered_max, server_max)
```

A correct TLS server picks `min(client_offered_max, server_max)` — the highest
common version.  An on-path attacker can strip strong versions from the
ClientHello before it reaches the server; the server then happily picks the
highest common version of the *tampered* offer.  Versions are integers
(higher = newer): 0 = SSL 3.0, 1 = TLS 1.0, 2 = TLS 1.1, 3 = TLS 1.2,
4 = TLS 1.3.

This file provides: the functional implementation, unit tests matching the six
checks of the Python `check`, a precondition restricting to genuine versions,
safety/liveness properties (including monotonicity in the visible offer — the
exact property the downgrade attacker exploits), a postcondition, bounded and
randomized property-based tests, a correctness theorem, an imperative
`Id.run` implementation with mutable state, and an equivalence theorem.
-/

namespace «95_unsafeTlsDowngrade»

/-- Functional implementation: the highest common version of the (possibly
attacker-tampered) client offer and the server's own maximum.  Mirrors the
Python `min(client_offered_max, server_max)`. -/
def unsafeTlsDowngrade (clientOfferedMax serverMax : Int) : Int :=
  min clientOfferedMax serverMax

/-! ## Unit tests: the six checks of the Python `check` -/

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

#eval unsafeTlsDowngrade 4 4   -- 4 (TLS 1.3, no attack)
#eval unsafeTlsDowngrade 1 4   -- 1 (downgrade to TLS 1.0!)
#eval unsafeTlsDowngrade 4 2   -- 2 (server caps at TLS 1.1)
#eval unsafeTlsDowngrade 4 0   -- 0 (legacy-only server)

/-! ## Precondition -/

/-- Admissible inputs: genuine protocol versions in 0–4, as fixed by the
Python docstring.  (The function itself is total on all integers.) -/
def Pre (clientOfferedMax serverMax : Int) : Prop :=
  0 ≤ clientOfferedMax ∧ clientOfferedMax ≤ 4 ∧ 0 ≤ serverMax ∧ serverMax ≤ 4

/-! ## Properties -/

/-- The negotiated version never exceeds the (visible) client offer. -/
def leOffer_prop (c s : Int) : Prop := unsafeTlsDowngrade c s ≤ c

/-- The negotiated version never exceeds the server maximum (server caps). -/
def leServer_prop (c s : Int) : Prop := unsafeTlsDowngrade c s ≤ s

/-- The negotiated version is the *greatest* commonly supported version: any
version supported by both endpoints is ≤ the result. -/
def greatestCommon_prop (c s v : Int) : Prop :=
  v ≤ c → v ≤ s → v ≤ unsafeTlsDowngrade c s

/-- Monotonicity in the visible offer — the property the on-path attacker
exploits: lowering the visible offer can only lower (or keep) the result. -/
def monoOffer_prop (c₁ c₂ s : Int) : Prop :=
  c₁ ≤ c₂ → unsafeTlsDowngrade c₁ s ≤ unsafeTlsDowngrade c₂ s

/-- The server always picks one of the two endpoints (the offer or the cap). -/
def picksCommon_prop (c s : Int) : Prop :=
  unsafeTlsDowngrade c s = c ∨ unsafeTlsDowngrade c s = s

theorem leOffer_thm (c s : Int) : leOffer_prop c s := by
  unfold leOffer_prop unsafeTlsDowngrade; omega

theorem leServer_thm (c s : Int) : leServer_prop c s := by
  unfold leServer_prop unsafeTlsDowngrade; omega

theorem greatestCommon_thm (c s v : Int) : greatestCommon_prop c s v := by
  unfold greatestCommon_prop unsafeTlsDowngrade; omega

theorem monoOffer_thm (c₁ c₂ s : Int) : monoOffer_prop c₁ c₂ s := by
  unfold monoOffer_prop unsafeTlsDowngrade; omega

theorem picksCommon_thm (c s : Int) : picksCommon_prop c s := by
  unfold picksCommon_prop unsafeTlsDowngrade
  rcases le_total c s with h | h
  · exact Or.inl (min_eq_left h)
  · exact Or.inr (min_eq_right h)

/-! ## Postcondition -/

/-- Postcondition: conjunction of all the stated properties. -/
def Post_prop (c s : Int) : Prop :=
  leOffer_prop c s ∧ leServer_prop c s ∧ (∀ v, greatestCommon_prop c s v) ∧
    picksCommon_prop c s

/-! ## Property-based tests -/

/-- Small exhaustive sample set, including out-of-spec values (negative and
above 4) to stress-test the properties beyond the admissible range. -/
def samples : List Int := [-2, -1, 0, 1, 2, 3, 4, 5, 6]

-- PBT (bounded, exhaustive) for `leOffer_prop`
example : samples.all (fun c => samples.all (fun s =>
    decide (unsafeTlsDowngrade c s ≤ c))) = true := by native_decide

-- PBT (bounded, exhaustive) for `leServer_prop`
example : samples.all (fun c => samples.all (fun s =>
    decide (unsafeTlsDowngrade c s ≤ s))) = true := by native_decide

-- PBT (bounded, exhaustive) for `greatestCommon_prop`
example : samples.all (fun c => samples.all (fun s => samples.all (fun v =>
    decide (v ≤ c → v ≤ s → v ≤ unsafeTlsDowngrade c s)))) = true := by
  native_decide

-- PBT (bounded, exhaustive) for `monoOffer_prop`
example : samples.all (fun c₁ => samples.all (fun c₂ => samples.all (fun s =>
    decide (c₁ ≤ c₂ → unsafeTlsDowngrade c₁ s ≤ unsafeTlsDowngrade c₂ s)))) = true := by
  native_decide

-- PBT (bounded, exhaustive) for `picksCommon_prop`
example : samples.all (fun c => samples.all (fun s =>
    decide (unsafeTlsDowngrade c s = c ∨ unsafeTlsDowngrade c s = s))) = true := by
  native_decide

/-- Executable Boolean form of the postcondition: the universally quantified
`greatestCommon` conjunct is checked over the sample set (its unrestricted
form over `Int` is proved in `correctness` below). -/
def postCheck (c s : Int) : Bool :=
  decide (unsafeTlsDowngrade c s ≤ c) &&
  decide (unsafeTlsDowngrade c s ≤ s) &&
  samples.all (fun v => decide (v ≤ c → v ≤ s → v ≤ unsafeTlsDowngrade c s)) &&
  decide (unsafeTlsDowngrade c s = c ∨ unsafeTlsDowngrade c s = s)

-- PBT (bounded, exhaustive) for `Post_prop` via its Boolean form
example : samples.all (fun c => samples.all (fun s => postCheck c s)) = true := by
  native_decide

-- Randomized PBTs (Plausible) for each property
#eval Plausible.Testable.check (∀ a b : Int, unsafeTlsDowngrade a b ≤ a)
#eval Plausible.Testable.check (∀ a b : Int, unsafeTlsDowngrade a b ≤ b)
#eval Plausible.Testable.check (∀ a b v : Nat, (v : Int) ≤ a → (v : Int) ≤ b →
  (v : Int) ≤ unsafeTlsDowngrade a b)
#eval Plausible.Testable.check (∀ a₁ a₂ b : Int, a₁ ≤ a₂ →
  unsafeTlsDowngrade a₁ b ≤ unsafeTlsDowngrade a₂ b)
#eval Plausible.Testable.check (∀ a b : Int,
  unsafeTlsDowngrade a b = a ∨ unsafeTlsDowngrade a b = b)

/-! ## Correctness theorem: Pre → Post -/

theorem correctness (c s : Int) (_hpre : Pre c s) : Post_prop c s :=
  ⟨leOffer_thm c s, leServer_thm c s, fun v => greatestCommon_thm c s v,
   picksCommon_thm c s⟩

/-! ## Imperative implementation (Id.run with mutable state) -/

/-- Imperative implementation: start from the visible client offer, then clamp
down to the server cap — exactly `min`, computed with mutable state. -/
def unsafeTlsDowngradeImp (clientOfferedMax serverMax : Int) : Int := Id.run do
  let mut negotiated : Int := clientOfferedMax
  if serverMax ≤ negotiated then
    negotiated := serverMax
  return negotiated

/-- The do-block reduces definitionally to the if-expression. -/
theorem imp_eq_ite (c s : Int) :
    unsafeTlsDowngradeImp c s = (if s ≤ c then s else c) := rfl

/-! ## Imperative tests -/

example : unsafeTlsDowngradeImp 4 4 = 4 := by native_decide
example : unsafeTlsDowngradeImp 1 4 = 1 := by native_decide
example : unsafeTlsDowngradeImp 4 2 = 2 := by native_decide
example : unsafeTlsDowngradeImp 3 3 = 3 := by native_decide
example : unsafeTlsDowngradeImp 4 0 = 0 := by native_decide
example : unsafeTlsDowngradeImp 2 4 ≥ unsafeTlsDowngradeImp 1 4 := by native_decide

#eval unsafeTlsDowngradeImp 4 4   -- 4
#eval unsafeTlsDowngradeImp 1 4   -- 1 (downgrade!)
#eval unsafeTlsDowngradeImp 4 2   -- 2
#eval unsafeTlsDowngradeImp 4 0   -- 0

/-! ## Equivalence: functional = imperative -/

theorem functional_eq_imperative (c s : Int) :
    unsafeTlsDowngrade c s = unsafeTlsDowngradeImp c s := by
  rw [imp_eq_ite]
  by_cases h : s ≤ c
  · rw [if_pos h]
    exact min_eq_right h
  · rw [if_neg h]
    exact min_eq_left (le_of_not_ge h)

end «95_unsafeTlsDowngrade»
