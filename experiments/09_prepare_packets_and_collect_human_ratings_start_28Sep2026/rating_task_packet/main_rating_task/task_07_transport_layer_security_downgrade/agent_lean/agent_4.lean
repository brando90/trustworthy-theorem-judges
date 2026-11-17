import Mathlib
import Plausible

/-!
# Unsafe TLS version downgrade

MIT 6.858 Lecture 14 — TLS / Downgrade.

A TLS server that selects `min(client_offered_max, server_max)` negotiates the
highest version present in the offer it actually receives. An on-path attacker
can strip strong versions from the ClientHello before it reaches the server.
Without a sentinel binding the client's true capability into the negotiation,
the server returns the highest common version of the *tampered* offer — often
a much weaker protocol than client and server actually share.

Versions are integers (higher = newer):
`0` = SSL 3.0, `1` = TLS 1.0, `2` = TLS 1.1, `3` = TLS 1.2, `4` = TLS 1.3.

Python's `unsafe_tls_downgrade` is total on arbitrary-precision `int` and does
no range check, so the model is `Int`. The lecture labels above are names for
five of those integers, not a restriction of the domain.
-/

namespace «95_unsafeTlsDowngrade»

/-- SSL 3.0 -/
def ssl30 : Int := 0
/-- TLS 1.0 -/
def tls10 : Int := 1
/-- TLS 1.1 -/
def tls11 : Int := 2
/-- TLS 1.2 -/
def tls12 : Int := 3
/-- TLS 1.3 -/
def tls13 : Int := 4

/-- Highest common version of a (possibly attacker-modified) client offer and
the server's maximum.

The vulnerability is the lack of a check that `client_offered_max` matches the
client's true capability. Stripping strong versions leaves the server
oblivious: it still returns `min` of whatever offer it was shown.
-/
def unsafe_tls_downgrade (client_offered_max server_max : Int) : Int :=
  min client_offered_max server_max

/-- Python `check`: the six lecture assertions on a candidate negotiation. -/
def check (candidate : Int → Int → Int) : Bool :=
  ((candidate 4 4 == 4) &&
    (candidate 1 4 == 1) &&
    (candidate 4 2 == 2) &&
    (candidate 3 3 == 3) &&
    (candidate 4 0 == 0) &&
    decide (candidate 2 4 ≥ candidate 1 4))

/-! ## Unit tests -/

-- 1) No attack: TLS 1.3 negotiated.
example : unsafe_tls_downgrade 4 4 = 4 := by native_decide
#eval unsafe_tls_downgrade 4 4

-- 2) VULNERABILITY: attacker stripped the offer to TLS 1.0; server picks 1.
example : unsafe_tls_downgrade 1 4 = 1 := by native_decide
#eval unsafe_tls_downgrade 1 4

-- 3) Server caps the result.
example : unsafe_tls_downgrade 4 2 = 2 := by native_decide
#eval unsafe_tls_downgrade 4 2

-- 4) Match: full version negotiated.
example : unsafe_tls_downgrade 3 3 = 3 := by native_decide
#eval unsafe_tls_downgrade 3 3

-- 5) Edge: legacy-only server (SSL 3.0).
example : unsafe_tls_downgrade 4 0 = 0 := by native_decide
#eval unsafe_tls_downgrade 4 0

-- 6) Monotone in the visible offer: a richer offer negotiates at least as high.
example : unsafe_tls_downgrade 2 4 ≥ unsafe_tls_downgrade 1 4 := by native_decide
#eval decide (unsafe_tls_downgrade 2 4 ≥ unsafe_tls_downgrade 1 4)

-- Python `int` is unbounded: values outside the named version range still use `min`.
example : unsafe_tls_downgrade (-2) 4 = -2 := by native_decide
#eval unsafe_tls_downgrade (-2) 4

example : unsafe_tls_downgrade 9 6 = 6 := by native_decide
#eval unsafe_tls_downgrade 9 6

example : check unsafe_tls_downgrade = true := by native_decide
#eval check unsafe_tls_downgrade

/-! ## Pre-condition -/

/-- The negotiation is total. Any integer offer and any integer server maximum
are admissible: the Python function performs no range check. -/
def Pre (client_offered_max server_max : Int) : Prop :=
  client_offered_max = client_offered_max ∧ server_max = server_max

/-! ## Properties -/

/-- The negotiated version is `min` of the visible offer and the server maximum,
as in the Python return expression. -/
def min_spec_prop (client_offered_max server_max : Int) : Prop :=
  unsafe_tls_downgrade client_offered_max server_max = min client_offered_max server_max

theorem min_spec_thm (client_offered_max server_max : Int) :
    min_spec_prop client_offered_max server_max := by
  unfold min_spec_prop unsafe_tls_downgrade
  rfl

/-- The result never exceeds the client's visible offer. -/
def offer_upper_bound_prop (client_offered_max server_max : Int) : Prop :=
  unsafe_tls_downgrade client_offered_max server_max ≤ client_offered_max

theorem offer_upper_bound_thm (client_offered_max server_max : Int) :
    offer_upper_bound_prop client_offered_max server_max := by
  unfold offer_upper_bound_prop unsafe_tls_downgrade
  exact min_le_left _ _

/-- The result never exceeds the server's maximum. The server is a hard cap. -/
def server_upper_bound_prop (client_offered_max server_max : Int) : Prop :=
  unsafe_tls_downgrade client_offered_max server_max ≤ server_max

theorem server_upper_bound_thm (client_offered_max server_max : Int) :
    server_upper_bound_prop client_offered_max server_max := by
  unfold server_upper_bound_prop unsafe_tls_downgrade
  exact min_le_right _ _

/-- Highest common version: every version supported by both the visible offer
and the server is at most the negotiated result. Together with the two upper
bounds, this is the lecture's "highest common version" rule. -/
def highest_common_prop (client_offered_max server_max : Int) : Prop :=
  ∀ v : Int, v ≤ client_offered_max → v ≤ server_max →
    v ≤ unsafe_tls_downgrade client_offered_max server_max

theorem highest_common_thm (client_offered_max server_max : Int) :
    highest_common_prop client_offered_max server_max := by
  unfold highest_common_prop unsafe_tls_downgrade
  intro v hvOffer hvServer
  exact le_min hvOffer hvServer

/-- If the visible offer does not exceed the server maximum, the server adopts
it. An attacker who strips the ClientHello down to such an offer forces that
version: the server never consults a hidden true capability. -/
def offer_selected_prop (client_offered_max server_max : Int) : Prop :=
  client_offered_max ≤ server_max →
    unsafe_tls_downgrade client_offered_max server_max = client_offered_max

theorem offer_selected_thm (client_offered_max server_max : Int) :
    offer_selected_prop client_offered_max server_max := by
  unfold offer_selected_prop unsafe_tls_downgrade
  intro h
  exact min_eq_left h

/-- If the server maximum is the smaller of the two inputs, it is selected.
This is test 3 (`candidate(4, 2) == 2`) and test 5 (`candidate(4, 0) == 0`). -/
def server_caps_prop (client_offered_max server_max : Int) : Prop :=
  server_max ≤ client_offered_max →
    unsafe_tls_downgrade client_offered_max server_max = server_max

theorem server_caps_thm (client_offered_max server_max : Int) :
    server_caps_prop client_offered_max server_max := by
  unfold server_caps_prop unsafe_tls_downgrade
  intro h
  exact min_eq_right h

/-- The negotiated version equals one of the two inputs. -/
def achieves_endpoint_prop (client_offered_max server_max : Int) : Prop :=
  unsafe_tls_downgrade client_offered_max server_max = client_offered_max ∨
    unsafe_tls_downgrade client_offered_max server_max = server_max

theorem achieves_endpoint_thm (client_offered_max server_max : Int) :
    achieves_endpoint_prop client_offered_max server_max := by
  unfold achieves_endpoint_prop unsafe_tls_downgrade
  rcases min_cases client_offered_max server_max with ⟨heq, _⟩ | ⟨heq, _⟩
  · exact Or.inl heq
  · exact Or.inr heq

/-- Repeating the negotiation against the same server, offering the version
just chosen, does not change the result. -/
def stable_prop (client_offered_max server_max : Int) : Prop :=
  unsafe_tls_downgrade (unsafe_tls_downgrade client_offered_max server_max) server_max =
    unsafe_tls_downgrade client_offered_max server_max

theorem stable_thm (client_offered_max server_max : Int) : stable_prop client_offered_max server_max := by
  unfold stable_prop unsafe_tls_downgrade
  exact min_eq_left (min_le_right client_offered_max server_max)

/-- Nonnegative version numbers stay nonnegative. The lecture's labels are
`≥ 0`; the function does not invent a negative protocol from nonnegative inputs. -/
def preserves_nonneg_prop (client_offered_max server_max : Int) : Prop :=
  0 ≤ client_offered_max → 0 ≤ server_max →
    0 ≤ unsafe_tls_downgrade client_offered_max server_max

theorem preserves_nonneg_thm (client_offered_max server_max : Int) :
    preserves_nonneg_prop client_offered_max server_max := by
  unfold preserves_nonneg_prop unsafe_tls_downgrade
  intro hOffer hServer
  exact le_min hOffer hServer

/-- Monotone in the visible offer (test 6, generalized).

A richer visible offer negotiates a version at least as high. Consequently an
attacker who only strips versions (`stripped ≤ true_client_max`) cannot make
the unsafe server pick something stronger than the honest ClientHello would
have negotiated — and the server has no separate check that would reject the
weaker offer.
-/
def monotone_offer_prop (offer₁ offer₂ server_max : Int) : Prop :=
  offer₁ ≤ offer₂ →
    unsafe_tls_downgrade offer₁ server_max ≤ unsafe_tls_downgrade offer₂ server_max

theorem monotone_offer_thm (offer₁ offer₂ server_max : Int) :
    monotone_offer_prop offer₁ offer₂ server_max := by
  unfold monotone_offer_prop unsafe_tls_downgrade
  intro h
  exact min_le_min_right server_max h

/-- Monotone in the server maximum: raising the server cap cannot lower the
negotiated version. -/
def monotone_server_prop (client_offered_max server₁ server₂ : Int) : Prop :=
  server₁ ≤ server₂ →
    unsafe_tls_downgrade client_offered_max server₁ ≤
      unsafe_tls_downgrade client_offered_max server₂

theorem monotone_server_thm (client_offered_max server₁ server₂ : Int) :
    monotone_server_prop client_offered_max server₁ server₂ := by
  unfold monotone_server_prop unsafe_tls_downgrade
  intro h
  exact min_le_min_left client_offered_max h

/-- Equal endpoints negotiate that version (tests 1 and 4, generalized). -/
def agree_prop (version : Int) : Prop :=
  unsafe_tls_downgrade version version = version

theorem agree_thm (version : Int) : agree_prop version := by
  unfold agree_prop unsafe_tls_downgrade
  exact min_self version

/-- Strict downgrade. If the visible offer lies strictly below the version that
the true client maximum and the server would have negotiated, the unsafe server
returns something strictly weaker. The hypothesis already forces the visible
offer to be a strict strip: it is `< min(true_client_max, server_max)`, hence
below the client's real capability. There is no transcript sentinel to stop it.
-/
def downgrade_strict_prop (true_client_max stripped server_max : Int) : Prop :=
  stripped < unsafe_tls_downgrade true_client_max server_max →
    unsafe_tls_downgrade stripped server_max <
      unsafe_tls_downgrade true_client_max server_max

theorem downgrade_strict_thm (true_client_max stripped server_max : Int) :
    downgrade_strict_prop true_client_max stripped server_max := by
  unfold downgrade_strict_prop
  intro h
  unfold unsafe_tls_downgrade at *
  have hServer : stripped < server_max := lt_of_lt_of_le h (min_le_right _ _)
  rw [min_eq_left (le_of_lt hServer)]
  exact h

/-- The two upper bounds and maximality characterize `min`: any integer meeting
them is the highest common version. -/
theorem highest_common_unique_thm (client_offered_max server_max result : Int)
    (hOffer : result ≤ client_offered_max) (hServer : result ≤ server_max)
    (hMax : ∀ v : Int, v ≤ client_offered_max → v ≤ server_max → v ≤ result) :
    result = min client_offered_max server_max := by
  apply le_antisymm
  · exact le_min hOffer hServer
  · exact hMax (min client_offered_max server_max)
      (min_le_left _ _) (min_le_right _ _)

/-- `unsafe_tls_downgrade` is the unique function that always returns the
highest common version of its two arguments. -/
theorem spec_uniqueness_thm (f : Int → Int → Int)
    (hOffer : ∀ c s, f c s ≤ c) (hServer : ∀ c s, f c s ≤ s)
    (hMax : ∀ c s v, v ≤ c → v ≤ s → v ≤ f c s) :
    ∀ c s, f c s = unsafe_tls_downgrade c s := by
  intro c s
  have hmin : f c s = min c s :=
    highest_common_unique_thm c s (f c s) (hOffer c s) (hServer c s)
      (fun v hvC hvS => hMax c s v hvC hvS)
  unfold unsafe_tls_downgrade
  exact hmin

/-- Lecture scenario, packed as the six Python asserts.

Both sides support TLS 1.3. An on-path attacker strips the ClientHello to
TLS 1.0. The unsafe server negotiates TLS 1.0, strictly below the honest
TLS 1.3 result. The other conjuncts are the server cap, the equal-version
match, the legacy server, and monotonicity of the visible offer.
-/
theorem lecture_downgrade_thm :
    unsafe_tls_downgrade tls13 tls13 = tls13 ∧
    unsafe_tls_downgrade tls10 tls13 = tls10 ∧
    unsafe_tls_downgrade tls10 tls13 < unsafe_tls_downgrade tls13 tls13 ∧
    unsafe_tls_downgrade tls13 tls11 = tls11 ∧
    unsafe_tls_downgrade tls12 tls12 = tls12 ∧
    unsafe_tls_downgrade tls13 ssl30 = ssl30 ∧
    unsafe_tls_downgrade tls11 tls13 ≥ unsafe_tls_downgrade tls10 tls13 := by
  decide

/-- The Python `check` accepts `unsafe_tls_downgrade`. -/
theorem check_thm : check unsafe_tls_downgrade = true := by
  decide

/-! ## Post-condition -/

/-- What the unsafe negotiation guarantees for one call: it is the minimum,
hence the unique highest common version, it selects the offer or the server
cap accordingly, it is stable under re-offer, and it preserves nonnegativity. -/
def Post_prop (client_offered_max server_max : Int) : Prop :=
  min_spec_prop client_offered_max server_max ∧
    offer_upper_bound_prop client_offered_max server_max ∧
      server_upper_bound_prop client_offered_max server_max ∧
        highest_common_prop client_offered_max server_max ∧
          offer_selected_prop client_offered_max server_max ∧
            server_caps_prop client_offered_max server_max ∧
              achieves_endpoint_prop client_offered_max server_max ∧
                stable_prop client_offered_max server_max ∧
                  preserves_nonneg_prop client_offered_max server_max

/-! ## Property-based tests

Unit tests above fix the lecture constants. These checks run each executable
property on many inputs. Plausible draws random `Int`s (retrying until a
guard such as `offer₁ ≤ offer₂` holds). The bounded tests exhaust every
combination in `pbtSamples` (`-5` through `8`), which includes the lecture
versions `0..4`. A passing check is evidence, not a proof.
-/

/-- Sample window `-5, -4, …, 8`. -/
def pbtSamples : List Int :=
  (List.range 14).map fun i => (i : Int) - 5

/-- Plausible configuration. `numRetries` is high so implication guards are met. -/
def pbtCfg : Plausible.Configuration where
  numInst := 100
  numRetries := 50

-- min_spec_prop
#eval Plausible.Testable.check
  (∀ c s : Int, unsafe_tls_downgrade c s = min c s) pbtCfg
example : pbtSamples.all (fun c =>
    pbtSamples.all (fun s => unsafe_tls_downgrade c s == min c s)) = true := by
  native_decide

-- offer_upper_bound_prop
#eval Plausible.Testable.check
  (∀ c s : Int, unsafe_tls_downgrade c s ≤ c) pbtCfg
example : pbtSamples.all (fun c =>
    pbtSamples.all (fun s => decide (unsafe_tls_downgrade c s ≤ c))) = true := by
  native_decide

-- server_upper_bound_prop
#eval Plausible.Testable.check
  (∀ c s : Int, unsafe_tls_downgrade c s ≤ s) pbtCfg
example : pbtSamples.all (fun c =>
    pbtSamples.all (fun s => decide (unsafe_tls_downgrade c s ≤ s))) = true := by
  native_decide

-- highest_common_prop
#eval Plausible.Testable.check
  (∀ c s v : Int, v ≤ c → v ≤ s → v ≤ unsafe_tls_downgrade c s) pbtCfg
example : pbtSamples.all (fun c =>
    pbtSamples.all (fun s =>
      pbtSamples.all (fun v =>
        decide (v ≤ c → v ≤ s → v ≤ unsafe_tls_downgrade c s)))) = true := by
  native_decide

-- offer_selected_prop
#eval Plausible.Testable.check
  (∀ c s : Int, c ≤ s → unsafe_tls_downgrade c s = c) pbtCfg
example : pbtSamples.all (fun c =>
    pbtSamples.all (fun s => decide (c ≤ s → unsafe_tls_downgrade c s = c))) = true := by
  native_decide

-- server_caps_prop
#eval Plausible.Testable.check
  (∀ c s : Int, s ≤ c → unsafe_tls_downgrade c s = s) pbtCfg
example : pbtSamples.all (fun c =>
    pbtSamples.all (fun s => decide (s ≤ c → unsafe_tls_downgrade c s = s))) = true := by
  native_decide

-- achieves_endpoint_prop
#eval Plausible.Testable.check
  (∀ c s : Int, unsafe_tls_downgrade c s = c ∨ unsafe_tls_downgrade c s = s) pbtCfg
example : pbtSamples.all (fun c =>
    pbtSamples.all (fun s =>
      decide (unsafe_tls_downgrade c s = c ∨ unsafe_tls_downgrade c s = s))) = true := by
  native_decide

-- stable_prop
#eval Plausible.Testable.check
  (∀ c s : Int,
    unsafe_tls_downgrade (unsafe_tls_downgrade c s) s = unsafe_tls_downgrade c s) pbtCfg
example : pbtSamples.all (fun c =>
    pbtSamples.all (fun s =>
      unsafe_tls_downgrade (unsafe_tls_downgrade c s) s == unsafe_tls_downgrade c s)) = true := by
  native_decide

-- preserves_nonneg_prop
#eval Plausible.Testable.check
  (∀ c s : Int, 0 ≤ c → 0 ≤ s → 0 ≤ unsafe_tls_downgrade c s) pbtCfg
example : pbtSamples.all (fun c =>
    pbtSamples.all (fun s =>
      decide (0 ≤ c → 0 ≤ s → 0 ≤ unsafe_tls_downgrade c s))) = true := by
  native_decide

-- monotone_offer_prop
#eval Plausible.Testable.check
  (∀ offer₁ offer₂ server_max : Int,
    offer₁ ≤ offer₂ →
      unsafe_tls_downgrade offer₁ server_max ≤ unsafe_tls_downgrade offer₂ server_max) pbtCfg
example : pbtSamples.all (fun offer₁ =>
    pbtSamples.all (fun offer₂ =>
      pbtSamples.all (fun server_max =>
        decide (offer₁ ≤ offer₂ →
          unsafe_tls_downgrade offer₁ server_max ≤
            unsafe_tls_downgrade offer₂ server_max)))) = true := by
  native_decide

-- monotone_server_prop
#eval Plausible.Testable.check
  (∀ c s₁ s₂ : Int,
    s₁ ≤ s₂ → unsafe_tls_downgrade c s₁ ≤ unsafe_tls_downgrade c s₂) pbtCfg
example : pbtSamples.all (fun c =>
    pbtSamples.all (fun s₁ =>
      pbtSamples.all (fun s₂ =>
        decide (s₁ ≤ s₂ →
          unsafe_tls_downgrade c s₁ ≤ unsafe_tls_downgrade c s₂)))) = true := by
  native_decide

-- agree_prop
#eval Plausible.Testable.check
  (∀ version : Int, unsafe_tls_downgrade version version = version) pbtCfg
example : pbtSamples.all (fun version =>
    unsafe_tls_downgrade version version == version) = true := by
  native_decide

-- downgrade_strict_prop
-- Boolean form: a strict `<` guard is false for every size-0 sample, so the
-- implication is evaluated with `decide` instead of discarded as a precondition.
#eval Plausible.Testable.check
  (∀ true_client_max stripped server_max : Int,
    decide (stripped < unsafe_tls_downgrade true_client_max server_max →
      unsafe_tls_downgrade stripped server_max <
        unsafe_tls_downgrade true_client_max server_max) = true) pbtCfg
example : pbtSamples.all (fun true_client_max =>
    pbtSamples.all (fun stripped =>
      pbtSamples.all (fun server_max =>
        decide (stripped < unsafe_tls_downgrade true_client_max server_max →
          unsafe_tls_downgrade stripped server_max <
            unsafe_tls_downgrade true_client_max server_max)))) = true := by
  native_decide

-- Post_prop, executable Boolean form of the conjunction.
-- `highest_common_prop`'s `∀ v : Int` is not a finite `decide` goal; it is checked
-- by the `highest_common_prop` tests above (random `v`, and every triple in
-- `pbtSamples`). Implications are inside `decide`, so a false guard is a
-- vacuous success rather than a discarded sample.
#eval Plausible.Testable.check
  (∀ c s : Int,
    decide (
      unsafe_tls_downgrade c s = min c s ∧
        unsafe_tls_downgrade c s ≤ c ∧
          unsafe_tls_downgrade c s ≤ s ∧
            (c ≤ s → unsafe_tls_downgrade c s = c) ∧
              (s ≤ c → unsafe_tls_downgrade c s = s) ∧
                (unsafe_tls_downgrade c s = c ∨ unsafe_tls_downgrade c s = s) ∧
                  unsafe_tls_downgrade (unsafe_tls_downgrade c s) s =
                    unsafe_tls_downgrade c s ∧
                    (0 ≤ c → 0 ≤ s → 0 ≤ unsafe_tls_downgrade c s)) = true) pbtCfg
example : pbtSamples.all (fun c =>
    pbtSamples.all (fun s =>
      decide (
        unsafe_tls_downgrade c s = min c s ∧
          unsafe_tls_downgrade c s ≤ c ∧
            unsafe_tls_downgrade c s ≤ s ∧
              (∀ v ∈ pbtSamples, v ≤ c → v ≤ s → v ≤ unsafe_tls_downgrade c s) ∧
                (c ≤ s → unsafe_tls_downgrade c s = c) ∧
                  (s ≤ c → unsafe_tls_downgrade c s = s) ∧
                    (unsafe_tls_downgrade c s = c ∨ unsafe_tls_downgrade c s = s) ∧
                      unsafe_tls_downgrade (unsafe_tls_downgrade c s) s =
                        unsafe_tls_downgrade c s ∧
                        (0 ≤ c → 0 ≤ s → 0 ≤ unsafe_tls_downgrade c s)))) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (client_offered_max server_max : Int)
    (hPre : Pre client_offered_max server_max) :
    Post_prop client_offered_max server_max := by
  unfold Pre at hPre
  obtain ⟨_, _⟩ := hPre
  unfold Post_prop
  exact ⟨min_spec_thm client_offered_max server_max,
    offer_upper_bound_thm client_offered_max server_max,
    server_upper_bound_thm client_offered_max server_max,
    highest_common_thm client_offered_max server_max,
    offer_selected_thm client_offered_max server_max,
    server_caps_thm client_offered_max server_max,
    achieves_endpoint_thm client_offered_max server_max,
    stable_thm client_offered_max server_max,
    preserves_nonneg_thm client_offered_max server_max⟩

/-! ## Imperative implementation

The server starts from the visible client offer and, when its own maximum is
lower, overwrites the negotiated version with that cap. Mutable state makes
the lack of a true-capability check obvious: the only cell is the visible offer.
-/

def unsafe_tls_downgradeImp (client_offered_max server_max : Int) : Int :=
  Id.run do
    let mut negotiated := client_offered_max
    if server_max < negotiated then
      negotiated := server_max
    return negotiated

/-! ## Imperative tests -/

example : unsafe_tls_downgradeImp 4 4 = 4 := by native_decide
#eval unsafe_tls_downgradeImp 4 4

example : unsafe_tls_downgradeImp 1 4 = 1 := by native_decide
#eval unsafe_tls_downgradeImp 1 4

example : unsafe_tls_downgradeImp 4 2 = 2 := by native_decide
#eval unsafe_tls_downgradeImp 4 2

example : unsafe_tls_downgradeImp 3 3 = 3 := by native_decide
#eval unsafe_tls_downgradeImp 3 3

example : unsafe_tls_downgradeImp 4 0 = 0 := by native_decide
#eval unsafe_tls_downgradeImp 4 0

example : unsafe_tls_downgradeImp 2 4 ≥ unsafe_tls_downgradeImp 1 4 := by native_decide
#eval decide (unsafe_tls_downgradeImp 2 4 ≥ unsafe_tls_downgradeImp 1 4)

example : unsafe_tls_downgradeImp (-2) 4 = -2 := by native_decide
#eval unsafe_tls_downgradeImp (-2) 4

example : unsafe_tls_downgradeImp 9 6 = 6 := by native_decide
#eval unsafe_tls_downgradeImp 9 6

example : check unsafe_tls_downgradeImp = true := by native_decide
#eval check unsafe_tls_downgradeImp

/-! ## Equivalence -/

theorem equiv_thm (client_offered_max server_max : Int) :
    unsafe_tls_downgrade client_offered_max server_max =
      unsafe_tls_downgradeImp client_offered_max server_max := by
  have hIf : unsafe_tls_downgradeImp client_offered_max server_max =
      if server_max < client_offered_max then server_max else client_offered_max := by
    dsimp [unsafe_tls_downgradeImp, Id.run]
    rfl
  rw [hIf]
  unfold unsafe_tls_downgrade
  split_ifs with h
  · exact min_eq_right (le_of_lt h)
  · exact min_eq_left (le_of_not_gt h)

/-- The imperative server computes the same minimum. -/
theorem imp_min_spec_thm (client_offered_max server_max : Int) :
    unsafe_tls_downgradeImp client_offered_max server_max =
      min client_offered_max server_max := by
  rw [← equiv_thm client_offered_max server_max]
  simpa [min_spec_prop] using min_spec_thm client_offered_max server_max

/-- Python `check` accepts the imperative implementation as well. -/
theorem check_imp_thm : check unsafe_tls_downgradeImp = true := by
  have h : check unsafe_tls_downgradeImp = check unsafe_tls_downgrade := by
    unfold check
    simp only [← equiv_thm]
  rw [h]
  exact check_thm

end «95_unsafeTlsDowngrade»
