import Mathlib

/-!
# Unsafe TLS version downgrade

Lean 4 formalization of the Python program `unsafe_tls_downgrade`
(MIT 6.858 Lecture 14 — TLS / Downgrade).

A correct TLS server picks `min(client_offered_max, server_max)`, the highest
version common to the client's offer and its own capability.  An on-path
attacker can strip strong versions from the ClientHello before it reaches the
server.  Without a sentinel binding the true client capability into the
negotiation, the server happily picks the highest common version of the
*tampered* offer — typically a much weaker protocol than client and server
actually share.

Versions are integers (higher = newer):
`0` = SSL 3.0, `1` = TLS 1.0, `2` = TLS 1.1, `3` = TLS 1.2, `4` = TLS 1.3.

Python `int` is modelled by Lean `Int`.  The file contains

* the functional implementation `unsafeTlsDowngrade` and the translated `check` harness,
* unit tests,
* the pre-condition `Pre` (both arguments are version codes),
* properties (`*_prop`) with proofs (`*_thm`), including the downgrade vulnerability,
* the post-condition `Post_prop` and the correctness theorem `Pre → Post_prop`,
* property-based tests,
* an imperative implementation `unsafeTlsDowngradeImp` (`Id.run do` with mutable state)
  and the proof that it agrees with the functional one.
-/

namespace «95_unsafeTlsDowngrade»

/-! ## Version codes -/

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

/-! ## Functional implementation -/

/-- `unsafe_tls_downgrade(client_offered_max, server_max)`:
the server negotiates `min clientOfferedMax serverMax`, the highest version common to
the (possibly attacker-tampered) client offer and the server's capability.

The vulnerability is the lack of any check that `clientOfferedMax` matches the
client's true capability. -/
def unsafeTlsDowngrade (clientOfferedMax serverMax : Int) : Int :=
  min clientOfferedMax serverMax

/-- Translation of the Python `check(candidate)` harness: all six assertions. -/
def check (candidate : Int → Int → Int) : Bool :=
  -- 1) No attack: TLS 1.3 negotiated.
  candidate 4 4 == 4 &&
  -- 2) VULNERABILITY: attacker stripped offer to TLS 1.0; server picks 1.
  candidate 1 4 == 1 &&
  -- 3) Server caps the result.
  candidate 4 2 == 2 &&
  -- 4) Match: full version negotiated.
  candidate 3 3 == 3 &&
  -- 5) Edge: legacy-only server.
  candidate 4 0 == 0 &&
  -- 6) Monotone in offer: more visible offer ≥ less visible offer.
  decide (candidate 2 4 ≥ candidate 1 4)

/-! ## Unit tests -/

example : unsafeTlsDowngrade 4 4 = 4 := by native_decide
example : unsafeTlsDowngrade 1 4 = 1 := by native_decide
example : unsafeTlsDowngrade 4 2 = 2 := by native_decide
example : unsafeTlsDowngrade 3 3 = 3 := by native_decide
example : unsafeTlsDowngrade 4 0 = 0 := by native_decide
example : unsafeTlsDowngrade 2 4 ≥ unsafeTlsDowngrade 1 4 := by native_decide
example : unsafeTlsDowngrade tls13 tls13 = tls13 := by native_decide
example : unsafeTlsDowngrade tls10 tls13 = tls10 := by native_decide
example : check unsafeTlsDowngrade = true := by native_decide

/-- The Python harness `assert check(unsafe_tls_downgrade)` as a kernel-checked theorem. -/
theorem check_thm : check unsafeTlsDowngrade = true := by decide

#eval unsafeTlsDowngrade 4 4   -- 4
#eval unsafeTlsDowngrade 1 4   -- 1  (downgraded by the tampered offer)
#eval unsafeTlsDowngrade 4 2   -- 2
#eval unsafeTlsDowngrade 3 3   -- 3
#eval unsafeTlsDowngrade 4 0   -- 0
#eval check unsafeTlsDowngrade -- true
#eval if check unsafeTlsDowngrade then "All tests passed." else "Candidate failed tests"

/-! ## Pre-condition -/

/-- A protocol version code: `0` = SSL 3.0 … `4` = TLS 1.3. -/
def IsVersion (v : Int) : Prop := 0 ≤ v ∧ v ≤ 4

/-- Pre-condition: the (visible) client offer and the server maximum are version codes. -/
def Pre (clientOfferedMax serverMax : Int) : Prop :=
  IsVersion clientOfferedMax ∧ IsVersion serverMax

/-! ## Properties -/

/-- The negotiated version never exceeds the client's visible offer. -/
def le_client_prop (clientOfferedMax serverMax : Int) : Prop :=
  unsafeTlsDowngrade clientOfferedMax serverMax ≤ clientOfferedMax

theorem le_client_thm (clientOfferedMax serverMax : Int) :
    le_client_prop clientOfferedMax serverMax := by
  unfold le_client_prop unsafeTlsDowngrade
  exact min_le_left _ _

/-- The server caps the negotiated version. -/
def le_server_prop (clientOfferedMax serverMax : Int) : Prop :=
  unsafeTlsDowngrade clientOfferedMax serverMax ≤ serverMax

theorem le_server_thm (clientOfferedMax serverMax : Int) :
    le_server_prop clientOfferedMax serverMax := by
  unfold le_server_prop unsafeTlsDowngrade
  exact min_le_right _ _

/-- Highest common version: every version supported by both the visible offer and the
server is at most the negotiated one. -/
def highest_common_prop (clientOfferedMax serverMax : Int) : Prop :=
  ∀ v : Int, v ≤ clientOfferedMax → v ≤ serverMax →
    v ≤ unsafeTlsDowngrade clientOfferedMax serverMax

theorem highest_common_thm (clientOfferedMax serverMax : Int) :
    highest_common_prop clientOfferedMax serverMax := by
  intro v hc hs
  unfold unsafeTlsDowngrade
  exact le_min hc hs

/-- The negotiated version is one of the two inputs. -/
def picks_input_prop (clientOfferedMax serverMax : Int) : Prop :=
  unsafeTlsDowngrade clientOfferedMax serverMax = clientOfferedMax ∨
  unsafeTlsDowngrade clientOfferedMax serverMax = serverMax

theorem picks_input_thm (clientOfferedMax serverMax : Int) :
    picks_input_prop clientOfferedMax serverMax := by
  unfold picks_input_prop unsafeTlsDowngrade
  exact min_choice _ _

/-- Match: when client offer and server capability agree, that full version is negotiated. -/
def match_prop (clientOfferedMax serverMax : Int) : Prop :=
  clientOfferedMax = serverMax →
    unsafeTlsDowngrade clientOfferedMax serverMax = clientOfferedMax

theorem match_thm (clientOfferedMax serverMax : Int) :
    match_prop clientOfferedMax serverMax := by
  intro h
  unfold unsafeTlsDowngrade
  rw [h, min_self]

/-- Monotone in the offer: a weaker visible offer never yields a stronger version
(assertion 6 of the Python harness, generalised). -/
def monotone_offer_prop (clientOfferedMax serverMax : Int) : Prop :=
  ∀ weaker : Int, weaker ≤ clientOfferedMax →
    unsafeTlsDowngrade weaker serverMax ≤ unsafeTlsDowngrade clientOfferedMax serverMax

theorem monotone_offer_thm (clientOfferedMax serverMax : Int) :
    monotone_offer_prop clientOfferedMax serverMax := by
  intro weaker h
  unfold unsafeTlsDowngrade
  exact min_le_min_right _ h

/-- Monotone in the server capability. -/
def monotone_server_prop (clientOfferedMax serverMax : Int) : Prop :=
  ∀ weaker : Int, weaker ≤ serverMax →
    unsafeTlsDowngrade clientOfferedMax weaker ≤ unsafeTlsDowngrade clientOfferedMax serverMax

theorem monotone_server_thm (clientOfferedMax serverMax : Int) :
    monotone_server_prop clientOfferedMax serverMax := by
  intro weaker h
  unfold unsafeTlsDowngrade
  exact min_le_min_left _ h

/-- VULNERABILITY (downgrade attack): `clientOfferedMax` is the client's *true* capability.
An on-path attacker who rewrites the offer to any `tampered` version at or below the
true highest common version forces the server to negotiate exactly `tampered`. -/
def downgrade_attack_prop (clientOfferedMax serverMax : Int) : Prop :=
  ∀ tampered : Int, tampered ≤ unsafeTlsDowngrade clientOfferedMax serverMax →
    unsafeTlsDowngrade tampered serverMax = tampered

theorem downgrade_attack_thm (clientOfferedMax serverMax : Int) :
    downgrade_attack_prop clientOfferedMax serverMax := by
  intro tampered h
  unfold unsafeTlsDowngrade at *
  exact min_eq_left (le_trans h (min_le_right _ _))

/-- Strict downgrade: stripping the offer strictly below the true highest common version
makes the server pick a strictly weaker protocol than client and server actually share. -/
def strict_downgrade_prop (clientOfferedMax serverMax : Int) : Prop :=
  ∀ tampered : Int, tampered < unsafeTlsDowngrade clientOfferedMax serverMax →
    unsafeTlsDowngrade tampered serverMax < unsafeTlsDowngrade clientOfferedMax serverMax

theorem strict_downgrade_thm (clientOfferedMax serverMax : Int) :
    strict_downgrade_prop clientOfferedMax serverMax := by
  intro tampered h
  unfold unsafeTlsDowngrade at *
  omega

/-- Under the pre-condition the negotiated version is again a version code. -/
def result_version_prop (clientOfferedMax serverMax : Int) : Prop :=
  IsVersion (unsafeTlsDowngrade clientOfferedMax serverMax)

theorem result_version_thm (clientOfferedMax serverMax : Int)
    (h : Pre clientOfferedMax serverMax) :
    result_version_prop clientOfferedMax serverMax := by
  unfold Pre IsVersion at h
  unfold result_version_prop IsVersion unsafeTlsDowngrade
  omega

/-- Explicit specification: the result is the client offer when it does not exceed the
server maximum, and the server maximum otherwise. -/
def min_spec_prop (clientOfferedMax serverMax : Int) : Prop :=
  unsafeTlsDowngrade clientOfferedMax serverMax =
    if clientOfferedMax ≤ serverMax then clientOfferedMax else serverMax

theorem min_spec_thm (clientOfferedMax serverMax : Int) :
    min_spec_prop clientOfferedMax serverMax := by
  unfold min_spec_prop unsafeTlsDowngrade
  exact min_def _ _

/-! ## Post-condition -/

/-- Post-condition: conjunction of all properties above. -/
def Post_prop (clientOfferedMax serverMax : Int) : Prop :=
  le_client_prop clientOfferedMax serverMax ∧
  le_server_prop clientOfferedMax serverMax ∧
  highest_common_prop clientOfferedMax serverMax ∧
  picks_input_prop clientOfferedMax serverMax ∧
  match_prop clientOfferedMax serverMax ∧
  monotone_offer_prop clientOfferedMax serverMax ∧
  monotone_server_prop clientOfferedMax serverMax ∧
  downgrade_attack_prop clientOfferedMax serverMax ∧
  strict_downgrade_prop clientOfferedMax serverMax ∧
  result_version_prop clientOfferedMax serverMax ∧
  min_spec_prop clientOfferedMax serverMax

/-! ## Property-based tests

Each `_prop` is checked in executable Boolean form.  Decidable implications are written
as Boolean disjunctions (`!guard || claim`) so that Plausible never discards samples;
in addition, the admissible version range `0 … 4` is checked exhaustively. -/

-- le_client_prop
#eval Plausible.Testable.check (∀ c s : Int, unsafeTlsDowngrade c s ≤ c)
-- le_server_prop
#eval Plausible.Testable.check (∀ c s : Int, unsafeTlsDowngrade c s ≤ s)
-- highest_common_prop
#eval Plausible.Testable.check (∀ c s v : Int,
  (!(decide (v ≤ c) && decide (v ≤ s)) || decide (v ≤ unsafeTlsDowngrade c s)) = true)
-- picks_input_prop
#eval Plausible.Testable.check (∀ c s : Int,
  unsafeTlsDowngrade c s = c ∨ unsafeTlsDowngrade c s = s)
-- match_prop
#eval Plausible.Testable.check (∀ c : Int, unsafeTlsDowngrade c c = c)
#eval Plausible.Testable.check (∀ c s : Int,
  (!(c == s) || unsafeTlsDowngrade c s == c) = true)
-- monotone_offer_prop
#eval Plausible.Testable.check (∀ c s w : Int,
  (!(decide (w ≤ c)) || decide (unsafeTlsDowngrade w s ≤ unsafeTlsDowngrade c s)) = true)
#eval Plausible.Testable.check (∀ c s : Int, ∀ d : Nat,
  unsafeTlsDowngrade (c - d) s ≤ unsafeTlsDowngrade c s)
-- monotone_server_prop
#eval Plausible.Testable.check (∀ c s w : Int,
  (!(decide (w ≤ s)) || decide (unsafeTlsDowngrade c w ≤ unsafeTlsDowngrade c s)) = true)
#eval Plausible.Testable.check (∀ c s : Int, ∀ d : Nat,
  unsafeTlsDowngrade c (s - d) ≤ unsafeTlsDowngrade c s)
-- downgrade_attack_prop
#eval Plausible.Testable.check (∀ c s t : Int,
  (!(decide (t ≤ unsafeTlsDowngrade c s)) || unsafeTlsDowngrade t s == t) = true)
#eval Plausible.Testable.check (∀ c s : Int, ∀ d : Nat,
  unsafeTlsDowngrade (unsafeTlsDowngrade c s - d) s = unsafeTlsDowngrade c s - d)
-- strict_downgrade_prop
#eval Plausible.Testable.check (∀ c s t : Int,
  (!(decide (t < unsafeTlsDowngrade c s)) ||
    decide (unsafeTlsDowngrade t s < unsafeTlsDowngrade c s)) = true)
#eval Plausible.Testable.check (∀ c s : Int, ∀ d : Nat,
  unsafeTlsDowngrade (unsafeTlsDowngrade c s - (d + 1)) s < unsafeTlsDowngrade c s)
-- result_version_prop (under Pre): random version codes via `Fin 5`
#eval Plausible.Testable.check (∀ a b : Fin 5,
  0 ≤ unsafeTlsDowngrade (a.val : Int) (b.val : Int) ∧
    unsafeTlsDowngrade (a.val : Int) (b.val : Int) ≤ 4)
#eval Plausible.Testable.check (∀ c s : Int,
  (!(decide (0 ≤ c) && decide (c ≤ 4) && decide (0 ≤ s) && decide (s ≤ 4)) ||
    (decide (0 ≤ unsafeTlsDowngrade c s) && decide (unsafeTlsDowngrade c s ≤ 4))) = true)
-- min_spec_prop
#eval Plausible.Testable.check (∀ c s : Int,
  unsafeTlsDowngrade c s = if c ≤ s then c else s)

/-- Executable (bounded) form of `Post_prop`.  Inner universally quantified versions range
over a window of eleven integers around the relevant input, which contains both values
satisfying and values violating each guard. -/
def postCheck (c s : Int) : Bool :=
  let r := unsafeTlsDowngrade c s
  let window (x : Int) : List Int := (List.range 11).map (fun n => x - 5 + (n : Int))
  -- le_client_prop ∧ le_server_prop
  decide (r ≤ c) && decide (r ≤ s) &&
  -- highest_common_prop
  (window r).all (fun v => !(decide (v ≤ c) && decide (v ≤ s)) || decide (v ≤ r)) &&
  -- picks_input_prop
  (r == c || r == s) &&
  -- match_prop
  (!(c == s) || r == c) &&
  -- monotone_offer_prop
  (window c).all (fun w => !(decide (w ≤ c)) || decide (unsafeTlsDowngrade w s ≤ r)) &&
  -- monotone_server_prop
  (window s).all (fun w => !(decide (w ≤ s)) || decide (unsafeTlsDowngrade c w ≤ r)) &&
  -- downgrade_attack_prop
  (window r).all (fun t => !(decide (t ≤ r)) || unsafeTlsDowngrade t s == t) &&
  -- strict_downgrade_prop
  (window r).all (fun t => !(decide (t < r)) || decide (unsafeTlsDowngrade t s < r)) &&
  -- result_version_prop
  decide (0 ≤ r) && decide (r ≤ 4) &&
  -- min_spec_prop
  (r == if c ≤ s then c else s)

-- Post_prop under Pre: exhaustive over all version codes, and random version codes.
example : (List.range 5).all (fun c => (List.range 5).all (fun s =>
    postCheck (c : Int) (s : Int))) = true := by native_decide
#eval Plausible.Testable.check (∀ a b : Fin 5, postCheck (a.val : Int) (b.val : Int) = true)
-- Exhaustive checks of the individual properties over version codes (and a margin).
example : (List.range 9).all (fun c => (List.range 9).all (fun s =>
    let c' : Int := (c : Int) - 2
    let s' : Int := (s : Int) - 2
    let r := unsafeTlsDowngrade c' s'
    decide (r ≤ c') && decide (r ≤ s') && (r == c' || r == s') &&
    (r == if c' ≤ s' then c' else s') &&
    (List.range 9).all (fun t =>
      let t' : Int := (t : Int) - 2
      (!(decide (t' ≤ c') && decide (t' ≤ s')) || decide (t' ≤ r)) &&
      (!(decide (t' ≤ c')) || decide (unsafeTlsDowngrade t' s' ≤ r)) &&
      (!(decide (t' ≤ s')) || decide (unsafeTlsDowngrade c' t' ≤ r)) &&
      (!(decide (t' ≤ r)) || unsafeTlsDowngrade t' s' == t') &&
      (!(decide (t' < r)) || decide (unsafeTlsDowngrade t' s' < r))))) = true := by
  native_decide
#eval (List.range 5).all (fun c => (List.range 5).all (fun s => postCheck (c : Int) (s : Int)))

/-! ## Correctness -/

/-- Correctness: under the pre-condition the implementation satisfies the post-condition. -/
theorem unsafeTlsDowngrade_correct_thm (clientOfferedMax serverMax : Int)
    (h : Pre clientOfferedMax serverMax) : Post_prop clientOfferedMax serverMax :=
  ⟨le_client_thm _ _, le_server_thm _ _, highest_common_thm _ _, picks_input_thm _ _,
    match_thm _ _, monotone_offer_thm _ _, monotone_server_thm _ _, downgrade_attack_thm _ _,
    strict_downgrade_thm _ _, result_version_thm _ _ h, min_spec_thm _ _⟩

/-! ## Imperative implementation -/

/-- Imperative implementation: start from the server's maximum and lower the negotiated
version to the (visible) client offer whenever that offer is weaker.  Like the Python
program, it never checks that the offer reflects the client's true capability. -/
def unsafeTlsDowngradeImp (clientOfferedMax serverMax : Int) : Int := Id.run do
  let mut negotiated : Int := serverMax
  if clientOfferedMax < negotiated then
    negotiated := clientOfferedMax
  return negotiated

/-! ### Imperative tests -/

example : unsafeTlsDowngradeImp 4 4 = 4 := by native_decide
example : unsafeTlsDowngradeImp 1 4 = 1 := by native_decide
example : unsafeTlsDowngradeImp 4 2 = 2 := by native_decide
example : unsafeTlsDowngradeImp 3 3 = 3 := by native_decide
example : unsafeTlsDowngradeImp 4 0 = 0 := by native_decide
example : unsafeTlsDowngradeImp 2 4 ≥ unsafeTlsDowngradeImp 1 4 := by native_decide
example : check unsafeTlsDowngradeImp = true := by native_decide
example : (List.range 9).all (fun c => (List.range 9).all (fun s =>
    unsafeTlsDowngradeImp ((c : Int) - 2) ((s : Int) - 2) ==
      unsafeTlsDowngrade ((c : Int) - 2) ((s : Int) - 2))) = true := by native_decide

/-- The Python harness also accepts the imperative implementation. -/
theorem check_imp_thm : check unsafeTlsDowngradeImp = true := by decide

#eval unsafeTlsDowngradeImp 4 4   -- 4
#eval unsafeTlsDowngradeImp 1 4   -- 1
#eval check unsafeTlsDowngradeImp -- true
#eval Plausible.Testable.check (∀ c s : Int, unsafeTlsDowngradeImp c s = unsafeTlsDowngrade c s)

/-- Second imperative variant, mirroring Python's `min` as a fold over its arguments:
scan the two candidates with a mutable accumulator and keep the smaller one. -/
def unsafeTlsDowngradeLoop (clientOfferedMax serverMax : Int) : Int := Id.run do
  let mut negotiated : Int := clientOfferedMax
  for v in [clientOfferedMax, serverMax] do
    if v < negotiated then
      negotiated := v
  return negotiated

example : unsafeTlsDowngradeLoop 4 4 = 4 := by native_decide
example : unsafeTlsDowngradeLoop 1 4 = 1 := by native_decide
example : unsafeTlsDowngradeLoop 4 2 = 2 := by native_decide
example : unsafeTlsDowngradeLoop 3 3 = 3 := by native_decide
example : unsafeTlsDowngradeLoop 4 0 = 0 := by native_decide
example : unsafeTlsDowngradeLoop 2 4 ≥ unsafeTlsDowngradeLoop 1 4 := by native_decide
example : check unsafeTlsDowngradeLoop = true := by native_decide

theorem check_loop_thm : check unsafeTlsDowngradeLoop = true := by decide

#eval unsafeTlsDowngradeLoop 1 4   -- 1
#eval check unsafeTlsDowngradeLoop -- true
#eval Plausible.Testable.check (∀ c s : Int, unsafeTlsDowngradeLoop c s = unsafeTlsDowngrade c s)

/-! ## Equivalence -/

/-- The functional and imperative implementations agree on all inputs. -/
theorem unsafeTlsDowngrade_eq_imp_thm (clientOfferedMax serverMax : Int) :
    unsafeTlsDowngrade clientOfferedMax serverMax =
      unsafeTlsDowngradeImp clientOfferedMax serverMax := by
  unfold unsafeTlsDowngrade unsafeTlsDowngradeImp
  simp only [Id.run, bind, pure]
  split_ifs <;> omega

/-- Unrolling the two-element loop: the loop variant is the explicit `if` specification. -/
theorem unsafeTlsDowngradeLoop_eq_ite (clientOfferedMax serverMax : Int) :
    unsafeTlsDowngradeLoop clientOfferedMax serverMax =
      if clientOfferedMax ≤ serverMax then clientOfferedMax else serverMax := by
  unfold unsafeTlsDowngradeLoop
  rcases le_or_gt clientOfferedMax serverMax with h | h
  · simp [h, not_lt.mpr h, Id.run, Id.instMonad]
  · simp [h, not_le.mpr h, Id.run, Id.instMonad]

/-- The functional implementation and the loop variant agree on all inputs. -/
theorem unsafeTlsDowngrade_eq_loop_thm (clientOfferedMax serverMax : Int) :
    unsafeTlsDowngrade clientOfferedMax serverMax =
      unsafeTlsDowngradeLoop clientOfferedMax serverMax := by
  rw [unsafeTlsDowngradeLoop_eq_ite]
  exact min_spec_thm _ _

/-- Both imperative implementations agree with each other. -/
theorem unsafeTlsDowngradeImp_eq_loop_thm (clientOfferedMax serverMax : Int) :
    unsafeTlsDowngradeImp clientOfferedMax serverMax =
      unsafeTlsDowngradeLoop clientOfferedMax serverMax := by
  rw [← unsafeTlsDowngrade_eq_imp_thm, unsafeTlsDowngrade_eq_loop_thm]

/-- Consequently the imperative implementation satisfies the post-condition: it is the
highest common version, bounded by both sides, a version code under `Pre`, and it is
just as vulnerable to the downgrade attack. -/
theorem unsafeTlsDowngradeImp_correct_thm (clientOfferedMax serverMax : Int)
    (h : Pre clientOfferedMax serverMax) :
    IsVersion (unsafeTlsDowngradeImp clientOfferedMax serverMax) ∧
    unsafeTlsDowngradeImp clientOfferedMax serverMax ≤ clientOfferedMax ∧
    unsafeTlsDowngradeImp clientOfferedMax serverMax ≤ serverMax ∧
    (∀ v : Int, v ≤ clientOfferedMax → v ≤ serverMax →
      v ≤ unsafeTlsDowngradeImp clientOfferedMax serverMax) ∧
    (∀ tampered : Int, tampered ≤ unsafeTlsDowngradeImp clientOfferedMax serverMax →
      unsafeTlsDowngradeImp tampered serverMax = tampered) := by
  have hd := downgrade_attack_thm clientOfferedMax serverMax
  unfold downgrade_attack_prop at hd
  simp only [← unsafeTlsDowngrade_eq_imp_thm]
  exact ⟨result_version_thm _ _ h, le_client_thm _ _, le_server_thm _ _,
    highest_common_thm _ _, hd⟩

end «95_unsafeTlsDowngrade»
