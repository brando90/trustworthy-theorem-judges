import Mathlib

/-!
# Unsafe TLS Version Downgrade

Formalization of the unsafe TLS version negotiation function from MIT 6.858
Lecture 14 (TLS / Downgrade).

A TLS server picks `min(client_offered_max, server_max)` — the highest common
protocol version. Without a cryptographic sentinel binding the client's true
capability into the negotiation, an on-path attacker can strip strong versions
from `ClientHello` before it reaches the server, causing the server to negotiate
the highest common version of the tampered offer.

Protocol version encoding (higher = newer):
- `0` = SSL 3.0
- `1` = TLS 1.0
- `2` = TLS 1.1
- `3` = TLS 1.2
- `4` = TLS 1.3
-/

namespace «95_unsafeTlsDowngrade»

/-! ## 1. Functional Implementation -/

/-- Return `min clientOfferedMax serverMax` — the highest common TLS version
between the (possibly attacker-modified) client offer and the server's maximum
supported version. -/
def unsafeTlsDowngrade (clientOfferedMax serverMax : Int) : Int :=
  min clientOfferedMax serverMax

/-- Snake-case alias matching the Python function name `unsafe_tls_downgrade`. -/
abbrev unsafe_tls_downgrade : Int → Int → Int := unsafeTlsDowngrade

/-- Executable test harness mirroring the Python `check(candidate)` function. -/
def check (candidate : Int → Int → Int) : Bool :=
  (candidate 4 4 == 4) &&
  (candidate 1 4 == 1) &&
  (candidate 4 2 == 2) &&
  (candidate 3 3 == 3) &&
  (candidate 4 0 == 0) &&
  (candidate 2 4 >= candidate 1 4)

/-! ## 2. Unit Tests -/

-- 1) No attack: TLS 1.3 negotiated.
#eval unsafeTlsDowngrade 4 4
example : unsafeTlsDowngrade 4 4 = 4 := by native_decide

-- 2) VULNERABILITY: attacker stripped offer to TLS 1.0; server picks 1.
#eval unsafeTlsDowngrade 1 4
example : unsafeTlsDowngrade 1 4 = 1 := by native_decide

-- 3) Server caps the result.
#eval unsafeTlsDowngrade 4 2
example : unsafeTlsDowngrade 4 2 = 2 := by native_decide

-- 4) Match: full version negotiated.
#eval unsafeTlsDowngrade 3 3
example : unsafeTlsDowngrade 3 3 = 3 := by native_decide

-- 5) Edge: legacy-only server.
#eval unsafeTlsDowngrade 4 0
example : unsafeTlsDowngrade 4 0 = 0 := by native_decide

-- 6) Monotone in offer: more visible offer ≥ less visible offer.
#eval decide (unsafeTlsDowngrade 2 4 ≥ unsafeTlsDowngrade 1 4)
example : unsafeTlsDowngrade 2 4 ≥ unsafeTlsDowngrade 1 4 := by native_decide

-- Full Python check suite.
#eval check unsafeTlsDowngrade
example : check unsafeTlsDowngrade = true := by native_decide

/-! ## 3. Pre-condition -/

/-- Pre-condition for `unsafeTlsDowngrade`. The Python function accepts any
integer inputs `(client_offered_max, server_max)`. -/
def Pre (_clientOfferedMax _serverMax : Int) : Prop := True

/-! ## 4. Properties and Theorems -/

/-- Property 1: Exact specification as the minimum of `clientOfferedMax` and `serverMax`. -/
def exact_min_prop (clientOfferedMax serverMax : Int) : Prop :=
  unsafeTlsDowngrade clientOfferedMax serverMax = min clientOfferedMax serverMax

theorem exact_min_thm (clientOfferedMax serverMax : Int) :
    exact_min_prop clientOfferedMax serverMax := by
  rfl

/-- Property 2: Conditional branching specification of version negotiation. -/
def ite_spec_prop (clientOfferedMax serverMax : Int) : Prop :=
  unsafeTlsDowngrade clientOfferedMax serverMax =
    if clientOfferedMax ≤ serverMax then clientOfferedMax else serverMax

theorem ite_spec_thm (clientOfferedMax serverMax : Int) :
    ite_spec_prop clientOfferedMax serverMax := by
  unfold ite_spec_prop unsafeTlsDowngrade
  exact min_def clientOfferedMax serverMax

/-- Property 3: The negotiated version never exceeds the client's offered maximum. -/
def le_client_prop (clientOfferedMax serverMax : Int) : Prop :=
  unsafeTlsDowngrade clientOfferedMax serverMax ≤ clientOfferedMax

theorem le_client_thm (clientOfferedMax serverMax : Int) :
    le_client_prop clientOfferedMax serverMax := by
  unfold le_client_prop unsafeTlsDowngrade
  exact min_le_left clientOfferedMax serverMax

/-- Property 4: The negotiated version never exceeds the server's maximum version
(the server caps the result). -/
def le_server_prop (clientOfferedMax serverMax : Int) : Prop :=
  unsafeTlsDowngrade clientOfferedMax serverMax ≤ serverMax

theorem le_server_thm (clientOfferedMax serverMax : Int) :
    le_server_prop clientOfferedMax serverMax := by
  unfold le_server_prop unsafeTlsDowngrade
  exact min_le_right clientOfferedMax serverMax

/-- Property 5: The negotiated version is always equal to either the client's
offered maximum or the server's maximum. -/
def is_input_prop (clientOfferedMax serverMax : Int) : Prop :=
  unsafeTlsDowngrade clientOfferedMax serverMax = clientOfferedMax ∨
  unsafeTlsDowngrade clientOfferedMax serverMax = serverMax

theorem is_input_thm (clientOfferedMax serverMax : Int) :
    is_input_prop clientOfferedMax serverMax := by
  unfold is_input_prop unsafeTlsDowngrade
  exact min_choice clientOfferedMax serverMax

/-- Property 6: Greatest lower bound (highest common version) characterization:
a version `v` is supported by both the offered maximum and the server maximum
if and only if `v` is at most the negotiated version. -/
def highest_common_prop (clientOfferedMax serverMax v : Int) : Prop :=
  (v ≤ unsafeTlsDowngrade clientOfferedMax serverMax) ↔
  (v ≤ clientOfferedMax ∧ v ≤ serverMax)

theorem highest_common_thm (clientOfferedMax serverMax v : Int) :
    highest_common_prop clientOfferedMax serverMax v := by
  unfold highest_common_prop unsafeTlsDowngrade
  exact le_min_iff

/-- Property 7: When the client's offered maximum is at most the server's maximum
(including when an attacker strips higher versions), the server picks `clientOfferedMax`. -/
def client_capped_prop (clientOfferedMax serverMax : Int) : Prop :=
  clientOfferedMax ≤ serverMax →
    unsafeTlsDowngrade clientOfferedMax serverMax = clientOfferedMax

theorem client_capped_thm (clientOfferedMax serverMax : Int) :
    client_capped_prop clientOfferedMax serverMax := by
  intro h
  unfold unsafeTlsDowngrade
  exact min_eq_left h

/-- Property 8: When the server's maximum is at most the client's offered maximum,
the server caps the negotiated version at `serverMax`. -/
def server_capped_prop (clientOfferedMax serverMax : Int) : Prop :=
  serverMax ≤ clientOfferedMax →
    unsafeTlsDowngrade clientOfferedMax serverMax = serverMax

theorem server_capped_thm (clientOfferedMax serverMax : Int) :
    server_capped_prop clientOfferedMax serverMax := by
  intro h
  unfold unsafeTlsDowngrade
  exact min_eq_right h

/-- Property 9: When the client offer equals the server maximum, that full common
version is negotiated. -/
def idempotent_prop (clientOfferedMax serverMax : Int) : Prop :=
  clientOfferedMax = serverMax →
    unsafeTlsDowngrade clientOfferedMax serverMax = serverMax

theorem idempotent_thm (clientOfferedMax serverMax : Int) :
    idempotent_prop clientOfferedMax serverMax := by
  intro h
  unfold unsafeTlsDowngrade
  rw [h, min_self]

/-- Property 10: Symmetry (commutativity) of version selection. -/
def comm_prop (clientOfferedMax serverMax : Int) : Prop :=
  unsafeTlsDowngrade clientOfferedMax serverMax =
  unsafeTlsDowngrade serverMax clientOfferedMax

theorem comm_thm (clientOfferedMax serverMax : Int) :
    comm_prop clientOfferedMax serverMax := by
  unfold comm_prop unsafeTlsDowngrade
  exact min_comm clientOfferedMax serverMax

/-- Property 11: Monotonicity in the client offer: a higher visible offer yields
at least as high a negotiated version. -/
def monotone_offer_prop (c1 c2 serverMax : Int) : Prop :=
  c1 ≤ c2 → unsafeTlsDowngrade c1 serverMax ≤ unsafeTlsDowngrade c2 serverMax

theorem monotone_offer_thm (c1 c2 serverMax : Int) :
    monotone_offer_prop c1 c2 serverMax := by
  intro h
  unfold unsafeTlsDowngrade
  omega

/-- Property 12: Monotonicity in the server capability: a higher server maximum
yields at least as high a negotiated version. -/
def monotone_server_prop (clientOfferedMax s1 s2 : Int) : Prop :=
  s1 ≤ s2 → unsafeTlsDowngrade clientOfferedMax s1 ≤ unsafeTlsDowngrade clientOfferedMax s2

theorem monotone_server_thm (clientOfferedMax s1 s2 : Int) :
    monotone_server_prop clientOfferedMax s1 s2 := by
  intro h
  unfold unsafeTlsDowngrade
  omega

/-- Property 13 (Core Security Vulnerability): If an on-path attacker strips
strong versions from the client offer so that `clientOfferedMax < clientTrueMax`
and `clientOfferedMax < serverMax`, the server negotiates `clientOfferedMax`,
which is strictly weaker than the true highest common version
`unsafeTlsDowngrade clientTrueMax serverMax`. -/
def downgrade_vulnerability_prop (clientOfferedMax clientTrueMax serverMax : Int) : Prop :=
  clientOfferedMax < clientTrueMax ∧ clientOfferedMax < serverMax →
    unsafeTlsDowngrade clientOfferedMax serverMax = clientOfferedMax ∧
    unsafeTlsDowngrade clientOfferedMax serverMax < unsafeTlsDowngrade clientTrueMax serverMax

theorem downgrade_vulnerability_thm (clientOfferedMax clientTrueMax serverMax : Int) :
    downgrade_vulnerability_prop clientOfferedMax clientTrueMax serverMax := by
  intro h
  unfold unsafeTlsDowngrade
  omega

/-- Property 14: Non-negativity preservation for non-negative version numbers. -/
def nonneg_prop (clientOfferedMax serverMax : Int) : Prop :=
  0 ≤ clientOfferedMax ∧ 0 ≤ serverMax →
    0 ≤ unsafeTlsDowngrade clientOfferedMax serverMax

theorem nonneg_thm (clientOfferedMax serverMax : Int) :
    nonneg_prop clientOfferedMax serverMax := by
  intro h
  unfold unsafeTlsDowngrade
  omega

/-- Property 15: Valid TLS version range `[0, 4]` preservation
(0 = SSL 3.0, 1 = TLS 1.0, 2 = TLS 1.1, 3 = TLS 1.2, 4 = TLS 1.3). -/
def tls_range_prop (clientOfferedMax serverMax : Int) : Prop :=
  (0 ≤ clientOfferedMax ∧ clientOfferedMax ≤ 4 ∧ 0 ≤ serverMax ∧ serverMax ≤ 4) →
    (0 ≤ unsafeTlsDowngrade clientOfferedMax serverMax ∧
     unsafeTlsDowngrade clientOfferedMax serverMax ≤ 4)

theorem tls_range_thm (clientOfferedMax serverMax : Int) :
    tls_range_prop clientOfferedMax serverMax := by
  intro h
  unfold unsafeTlsDowngrade
  omega

/-! ## 5. Post-condition -/

/-- Post-condition conjunction combining the specification properties
of `unsafeTlsDowngrade`. -/
def Post_prop (clientOfferedMax serverMax : Int) : Prop :=
  exact_min_prop clientOfferedMax serverMax ∧
  ite_spec_prop clientOfferedMax serverMax ∧
  le_client_prop clientOfferedMax serverMax ∧
  le_server_prop clientOfferedMax serverMax ∧
  is_input_prop clientOfferedMax serverMax ∧
  client_capped_prop clientOfferedMax serverMax ∧
  server_capped_prop clientOfferedMax serverMax ∧
  idempotent_prop clientOfferedMax serverMax ∧
  comm_prop clientOfferedMax serverMax ∧
  nonneg_prop clientOfferedMax serverMax ∧
  tls_range_prop clientOfferedMax serverMax

/-! ## 6. Property-Based Tests (PBTs) -/

instance (a b : Int) : Decidable (exact_min_prop a b) := by unfold exact_min_prop; infer_instance
instance (a b : Int) : Decidable (ite_spec_prop a b) := by unfold ite_spec_prop; infer_instance
instance (a b : Int) : Decidable (le_client_prop a b) := by unfold le_client_prop; infer_instance
instance (a b : Int) : Decidable (le_server_prop a b) := by unfold le_server_prop; infer_instance
instance (a b : Int) : Decidable (is_input_prop a b) := by unfold is_input_prop; infer_instance
instance (a b v : Int) : Decidable (highest_common_prop a b v) := by unfold highest_common_prop; infer_instance
instance (a b : Int) : Decidable (client_capped_prop a b) := by unfold client_capped_prop; infer_instance
instance (a b : Int) : Decidable (server_capped_prop a b) := by unfold server_capped_prop; infer_instance
instance (a b : Int) : Decidable (idempotent_prop a b) := by unfold idempotent_prop; infer_instance
instance (a b : Int) : Decidable (comm_prop a b) := by unfold comm_prop; infer_instance
instance (c1 c2 s : Int) : Decidable (monotone_offer_prop c1 c2 s) := by unfold monotone_offer_prop; infer_instance
instance (c s1 s2 : Int) : Decidable (monotone_server_prop c s1 s2) := by unfold monotone_server_prop; infer_instance
instance (co ct s : Int) : Decidable (downgrade_vulnerability_prop co ct s) := by unfold downgrade_vulnerability_prop; infer_instance
instance (a b : Int) : Decidable (nonneg_prop a b) := by unfold nonneg_prop; infer_instance
instance (a b : Int) : Decidable (tls_range_prop a b) := by unfold tls_range_prop; infer_instance
instance (a b : Int) : Decidable (Post_prop a b) := by unfold Post_prop; infer_instance

-- Randomized PBTs via Plausible
#eval Plausible.Testable.check (∀ a b : Int, exact_min_prop a b)
#eval Plausible.Testable.check (∀ a b : Int, ite_spec_prop a b)
#eval Plausible.Testable.check (∀ a b : Int, le_client_prop a b)
#eval Plausible.Testable.check (∀ a b : Int, le_server_prop a b)
#eval Plausible.Testable.check (∀ a b : Int, is_input_prop a b)
#eval Plausible.Testable.check (∀ a b v : Int, highest_common_prop a b v)
#eval Plausible.Testable.check (∀ a b : Int, client_capped_prop a b)
#eval Plausible.Testable.check (∀ a b : Int, server_capped_prop a b)
#eval Plausible.Testable.check (∀ a b : Int, idempotent_prop a b)
#eval Plausible.Testable.check (∀ a : Int, idempotent_prop a a)
#eval Plausible.Testable.check (∀ a b : Int, comm_prop a b)
#eval Plausible.Testable.check (∀ c1 c2 s : Int, monotone_offer_prop c1 c2 s)
#eval Plausible.Testable.check (∀ c s1 s2 : Int, monotone_server_prop c s1 s2)
#eval Plausible.Testable.check (∀ co ct s : Int, downgrade_vulnerability_prop co ct s)
#eval Plausible.Testable.check (∀ a b : Int, nonneg_prop a b)
#eval Plausible.Testable.check (∀ a b : Int, tls_range_prop a b)
#eval Plausible.Testable.check (∀ a b : Int, Post_prop a b)

-- Bounded exhaustive PBTs over [-5, 5] (including all TLS versions 0..4)
def testDomain : List Int := [-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5]

example : testDomain.all (fun a => testDomain.all (fun b => decide (exact_min_prop a b))) = true := by native_decide
example : testDomain.all (fun a => testDomain.all (fun b => decide (ite_spec_prop a b))) = true := by native_decide
example : testDomain.all (fun a => testDomain.all (fun b => decide (le_client_prop a b))) = true := by native_decide
example : testDomain.all (fun a => testDomain.all (fun b => decide (le_server_prop a b))) = true := by native_decide
example : testDomain.all (fun a => testDomain.all (fun b => decide (is_input_prop a b))) = true := by native_decide
example : testDomain.all (fun a => testDomain.all (fun b => testDomain.all (fun v => decide (highest_common_prop a b v)))) = true := by native_decide
example : testDomain.all (fun a => testDomain.all (fun b => decide (client_capped_prop a b))) = true := by native_decide
example : testDomain.all (fun a => testDomain.all (fun b => decide (server_capped_prop a b))) = true := by native_decide
example : testDomain.all (fun a => testDomain.all (fun b => decide (idempotent_prop a b))) = true := by native_decide
example : testDomain.all (fun a => testDomain.all (fun b => decide (comm_prop a b))) = true := by native_decide
example : testDomain.all (fun c1 => testDomain.all (fun c2 => testDomain.all (fun s => decide (monotone_offer_prop c1 c2 s)))) = true := by native_decide
example : testDomain.all (fun c => testDomain.all (fun s1 => testDomain.all (fun s2 => decide (monotone_server_prop c s1 s2)))) = true := by native_decide
example : testDomain.all (fun co => testDomain.all (fun ct => testDomain.all (fun s => decide (downgrade_vulnerability_prop co ct s)))) = true := by native_decide
example : testDomain.all (fun a => testDomain.all (fun b => decide (nonneg_prop a b))) = true := by native_decide
example : testDomain.all (fun a => testDomain.all (fun b => decide (tls_range_prop a b))) = true := by native_decide
example : testDomain.all (fun a => testDomain.all (fun b => decide (Post_prop a b))) = true := by native_decide

/-! ## 7. Correctness Theorem (Pre → Post) -/

/-- Total correctness theorem: under `Pre`, `unsafeTlsDowngrade` satisfies `Post_prop`. -/
theorem unsafeTlsDowngrade_correct (clientOfferedMax serverMax : Int)
    (_hPre : Pre clientOfferedMax serverMax) :
    Post_prop clientOfferedMax serverMax := by
  unfold Post_prop
  refine ⟨exact_min_thm clientOfferedMax serverMax,
          ite_spec_thm clientOfferedMax serverMax,
          le_client_thm clientOfferedMax serverMax,
          le_server_thm clientOfferedMax serverMax,
          is_input_thm clientOfferedMax serverMax,
          client_capped_thm clientOfferedMax serverMax,
          server_capped_thm clientOfferedMax serverMax,
          idempotent_thm clientOfferedMax serverMax,
          comm_thm clientOfferedMax serverMax,
          nonneg_thm clientOfferedMax serverMax,
          tls_range_thm clientOfferedMax serverMax⟩

/-! ## 8. Imperative Implementation -/

/-- Imperative implementation of `unsafeTlsDowngrade` using `Id.run do` and mutable state. -/
def unsafeTlsDowngradeImp (clientOfferedMax serverMax : Int) : Int := Id.run do
  let mut negotiated : Int := serverMax
  if clientOfferedMax ≤ serverMax then
    negotiated := clientOfferedMax
  return negotiated

/-- Snake-case alias for the imperative implementation. -/
abbrev unsafe_tls_downgrade_imp : Int → Int → Int := unsafeTlsDowngradeImp

/-! ## 9. Imperative Tests -/

#eval unsafeTlsDowngradeImp 4 4
example : unsafeTlsDowngradeImp 4 4 = 4 := by native_decide

#eval unsafeTlsDowngradeImp 1 4
example : unsafeTlsDowngradeImp 1 4 = 1 := by native_decide

#eval unsafeTlsDowngradeImp 4 2
example : unsafeTlsDowngradeImp 4 2 = 2 := by native_decide

#eval unsafeTlsDowngradeImp 3 3
example : unsafeTlsDowngradeImp 3 3 = 3 := by native_decide

#eval unsafeTlsDowngradeImp 4 0
example : unsafeTlsDowngradeImp 4 0 = 0 := by native_decide

#eval decide (unsafeTlsDowngradeImp 2 4 ≥ unsafeTlsDowngradeImp 1 4)
example : unsafeTlsDowngradeImp 2 4 ≥ unsafeTlsDowngradeImp 1 4 := by native_decide

#eval check unsafeTlsDowngradeImp
example : check unsafeTlsDowngradeImp = true := by native_decide

#eval Plausible.Testable.check (∀ a b : Int, unsafeTlsDowngrade a b = unsafeTlsDowngradeImp a b)

/-! ## 10. Equivalence Theorem (Functional = Imperative) -/

/-- The functional and imperative implementations are pointwise equal on all inputs. -/
theorem unsafeTlsDowngrade_equiv (clientOfferedMax serverMax : Int) :
    unsafeTlsDowngrade clientOfferedMax serverMax =
    unsafeTlsDowngradeImp clientOfferedMax serverMax := by
  unfold unsafeTlsDowngrade unsafeTlsDowngradeImp
  simp only [Id.run]
  split_ifs with h
  · exact min_eq_left h
  · exact min_eq_right (le_of_not_ge h)

/-- Function-extensionality form of functional-imperative equivalence. -/
theorem unsafeTlsDowngrade_eq_imp :
    unsafeTlsDowngrade = unsafeTlsDowngradeImp := by
  funext clientOfferedMax serverMax
  exact unsafeTlsDowngrade_equiv clientOfferedMax serverMax

end «95_unsafeTlsDowngrade»
