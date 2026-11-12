import Mathlib

/-!
# Unsafe TLS version downgrade

MIT 6.858 Lecture 14 — TLS / Downgrade.

A correct TLS server picks `min(client_offered_max, server_max)` — the highest
version common to the client's offer and the server's own maximum.  An on-path
attacker can strip strong versions from the ClientHello before it reaches the
server.  Without a sentinel binding the true client capability into the
negotiation, the server happily picks the highest common version of the
*tampered* offer — typically a much weaker protocol than client and server
actually share.

Versions are integers (higher = newer):
`0 = SSL 3.0, 1 = TLS 1.0, 2 = TLS 1.1, 3 = TLS 1.2, 4 = TLS 1.3`.

Contents:
* `unsafeTlsDowngrade` — functional implementation (`min`), with unit tests
  mirroring the Python `check` function;
* `Pre`, the `_prop` properties with their `_thm` proofs, `Post_prop` and the
  correctness theorem `Pre → Post_prop`;
* property-based tests (randomised via Plausible and bounded exhaustive);
* `unsafeTlsDowngradeImp` — imperative implementation using `Id.run do` with
  mutable state, its tests, and the functional/imperative equivalence theorem.
-/

namespace «95_unsafeTlsDowngrade»

/-- Protocol versions are plain integers, exactly as in the Python source
(`int`); higher means newer. -/
abbrev Version := Int

/-- Functional implementation of `unsafe_tls_downgrade`: return
`min(client_offered_max, server_max)`, the highest common version.

The vulnerability is the lack of any check that `clientOfferedMax` matches the
client's true capability: an attacker stripping strong versions from the offer
leaves the server oblivious. -/
def unsafeTlsDowngrade (clientOfferedMax serverMax : Version) : Version :=
  min clientOfferedMax serverMax

/-! ## Unit tests (mirroring `check` in the Python source) -/

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

#eval unsafeTlsDowngrade 4 4  -- 4
#eval unsafeTlsDowngrade 1 4  -- 1
#eval unsafeTlsDowngrade 4 2  -- 2
#eval unsafeTlsDowngrade 3 3  -- 3
#eval unsafeTlsDowngrade 4 0  -- 0
#eval decide (unsafeTlsDowngrade 2 4 ≥ unsafeTlsDowngrade 1 4)  -- true

/-! ## Specification -/

/-- The version numbers named in the Python docstring:
`0 = SSL 3.0, 1 = TLS 1.0, 2 = TLS 1.1, 3 = TLS 1.2, 4 = TLS 1.3`. -/
def ValidVersion (v : Version) : Prop := 0 ≤ v ∧ v ≤ 4

/-- Pre-condition.  The Python function accepts arbitrary integers (there is no
check at all — that absence *is* the vulnerability), so nothing is required of
the inputs. -/
def Pre (_clientOfferedMax _serverMax : Version) : Prop := True

/-- The implementation computes exactly `min(client_offered_max, server_max)`. -/
def spec_prop (c s : Version) : Prop :=
  unsafeTlsDowngrade c s = min c s

theorem spec_thm (c s : Version) : spec_prop c s := by
  unfold spec_prop unsafeTlsDowngrade
  rfl

/-- The negotiated version never exceeds the (visible) client offer. -/
def result_le_client_prop (c s : Version) : Prop :=
  unsafeTlsDowngrade c s ≤ c

theorem result_le_client_thm (c s : Version) : result_le_client_prop c s := by
  unfold result_le_client_prop unsafeTlsDowngrade
  exact min_le_left c s

/-- The negotiated version never exceeds the server maximum ("server caps"). -/
def result_le_server_prop (c s : Version) : Prop :=
  unsafeTlsDowngrade c s ≤ s

theorem result_le_server_thm (c s : Version) : result_le_server_prop c s := by
  unfold result_le_server_prop unsafeTlsDowngrade
  exact min_le_right c s

/-- The negotiated version is one of the two inputs. -/
def result_is_input_prop (c s : Version) : Prop :=
  unsafeTlsDowngrade c s = c ∨ unsafeTlsDowngrade c s = s

theorem result_is_input_thm (c s : Version) : result_is_input_prop c s := by
  unfold result_is_input_prop unsafeTlsDowngrade
  rcases le_total c s with h | h
  · exact Or.inl (min_eq_left h)
  · exact Or.inr (min_eq_right h)

/-- "Highest common version": every version supported by both the (visible)
offer and the server is at most the negotiated one. -/
def highest_common_prop (c s : Version) : Prop :=
  ∀ v : Version, v ≤ c → v ≤ s → v ≤ unsafeTlsDowngrade c s

theorem highest_common_thm (c s : Version) : highest_common_prop c s := by
  unfold highest_common_prop unsafeTlsDowngrade
  intro v hc hs
  exact le_min hc hs

/-- Monotone in the offer: a more visible offer never yields a weaker version
(Python test 6). -/
def monotone_offer_prop (c s : Version) : Prop :=
  ∀ c' : Version, c ≤ c' → unsafeTlsDowngrade c s ≤ unsafeTlsDowngrade c' s

theorem monotone_offer_thm (c s : Version) : monotone_offer_prop c s := by
  unfold monotone_offer_prop unsafeTlsDowngrade
  intro c' h
  exact min_le_min h (le_refl s)

/-- Monotone in the server maximum. -/
def monotone_server_prop (c s : Version) : Prop :=
  ∀ s' : Version, s ≤ s' → unsafeTlsDowngrade c s ≤ unsafeTlsDowngrade c s'

theorem monotone_server_thm (c s : Version) : monotone_server_prop c s := by
  unfold monotone_server_prop unsafeTlsDowngrade
  intro s' h
  exact min_le_min (le_refl c) h

/-- Match: when offer and server maximum agree, that version is negotiated
(Python tests 1 and 4). -/
def match_prop (c s : Version) : Prop :=
  c = s → unsafeTlsDowngrade c s = c

theorem match_thm (c s : Version) : match_prop c s := by
  unfold match_prop unsafeTlsDowngrade
  intro h
  subst h
  exact min_self c

/-- Negotiation is symmetric in its two arguments. -/
def symmetric_prop (c s : Version) : Prop :=
  unsafeTlsDowngrade c s = unsafeTlsDowngrade s c

theorem symmetric_thm (c s : Version) : symmetric_prop c s := by
  unfold symmetric_prop unsafeTlsDowngrade
  exact min_comm c s

/-- If both inputs are versions from the table (`0 … 4`), so is the result. -/
def valid_result_prop (c s : Version) : Prop :=
  ValidVersion c → ValidVersion s → ValidVersion (unsafeTlsDowngrade c s)

theorem valid_result_thm (c s : Version) : valid_result_prop c s := by
  unfold valid_result_prop ValidVersion unsafeTlsDowngrade
  intro hc hs
  exact ⟨le_min hc.1 hs.1, le_trans (min_le_left c s) hc.2⟩

/-- **The vulnerability.**  Suppose the client's true maximum is `trueMax` but an
on-path attacker strips the ClientHello down to `c < trueMax`, where `c` is also
below what the server supports.  The server, oblivious, negotiates a *strictly
weaker* version than it would have with the genuine offer (Python test 2 with
`trueMax = 4`, `c = 1`, `s = 4`). -/
def downgrade_vulnerability_prop (c s : Version) : Prop :=
  ∀ trueMax : Version, c < trueMax → c < s →
    unsafeTlsDowngrade c s < unsafeTlsDowngrade trueMax s

theorem downgrade_vulnerability_thm (c s : Version) :
    downgrade_vulnerability_prop c s := by
  unfold downgrade_vulnerability_prop unsafeTlsDowngrade
  intro trueMax hct hcs
  rw [min_eq_left (le_of_lt hcs)]
  exact lt_min hct hcs

/-- Weak form of the downgrade: a stripped offer (`c ≤ trueMax`) never yields a
stronger version than the genuine offer would, and the server has no way to
notice (the result depends on the visible offer only). -/
def stripped_offer_never_stronger_prop (c s : Version) : Prop :=
  ∀ trueMax : Version, c ≤ trueMax →
    unsafeTlsDowngrade c s ≤ unsafeTlsDowngrade trueMax s

theorem stripped_offer_never_stronger_thm (c s : Version) :
    stripped_offer_never_stronger_prop c s := by
  unfold stripped_offer_never_stronger_prop unsafeTlsDowngrade
  intro trueMax h
  exact min_le_min h (le_refl s)

/-- Post-condition: the conjunction of all properties above. -/
def Post_prop (c s : Version) : Prop :=
  spec_prop c s ∧
  result_le_client_prop c s ∧
  result_le_server_prop c s ∧
  result_is_input_prop c s ∧
  highest_common_prop c s ∧
  monotone_offer_prop c s ∧
  monotone_server_prop c s ∧
  match_prop c s ∧
  symmetric_prop c s ∧
  valid_result_prop c s ∧
  downgrade_vulnerability_prop c s ∧
  stripped_offer_never_stronger_prop c s

/-! ## Property-based tests

Randomised tests via Plausible (compilation fails on a counterexample) and
bounded exhaustive tests via `native_decide` on an `example`. -/

-- spec_prop
#eval Plausible.Testable.check (∀ c s : Int, unsafeTlsDowngrade c s = min c s)
-- result_le_client_prop
#eval Plausible.Testable.check (∀ c s : Int, unsafeTlsDowngrade c s ≤ c)
-- result_le_server_prop
#eval Plausible.Testable.check (∀ c s : Int, unsafeTlsDowngrade c s ≤ s)
-- result_is_input_prop
#eval Plausible.Testable.check
  (∀ c s : Int, unsafeTlsDowngrade c s = c ∨ unsafeTlsDowngrade c s = s)
-- highest_common_prop
#eval Plausible.Testable.check
  (∀ c s v : Int, v ≤ c → v ≤ s → v ≤ unsafeTlsDowngrade c s)
-- monotone_offer_prop
#eval Plausible.Testable.check
  (∀ c s c' : Int, c ≤ c' → unsafeTlsDowngrade c s ≤ unsafeTlsDowngrade c' s)
-- monotone_server_prop
#eval Plausible.Testable.check
  (∀ c s s' : Int, s ≤ s' → unsafeTlsDowngrade c s ≤ unsafeTlsDowngrade c s')
-- match_prop (random `c = s` is rare, so also checked exhaustively below)
#eval Plausible.Testable.check (∀ c s : Int, c = s → unsafeTlsDowngrade c s = c)
-- symmetric_prop
#eval Plausible.Testable.check
  (∀ c s : Int, unsafeTlsDowngrade c s = unsafeTlsDowngrade s c)
-- valid_result_prop (also checked exhaustively below)
#eval Plausible.Testable.check
  (∀ c s : Int, 0 ≤ c → c ≤ 4 → 0 ≤ s → s ≤ 4 →
    0 ≤ unsafeTlsDowngrade c s ∧ unsafeTlsDowngrade c s ≤ 4)
-- downgrade_vulnerability_prop
#eval Plausible.Testable.check
  (∀ c s trueMax : Int, c < trueMax → c < s →
    unsafeTlsDowngrade c s < unsafeTlsDowngrade trueMax s)
-- stripped_offer_never_stronger_prop
#eval Plausible.Testable.check
  (∀ c s trueMax : Int, c ≤ trueMax →
    unsafeTlsDowngrade c s ≤ unsafeTlsDowngrade trueMax s)
/-- Executable Boolean form of `Post_prop` at a single sample: `v` instantiates
the inner quantifier of `highest_common_prop`, `t` those of the monotonicity /
downgrade properties. -/
def postCheckSample (c s v t : Int) : Bool :=
  let r := unsafeTlsDowngrade c s
  decide (r = min c s) &&
  decide (r ≤ c) &&
  decide (r ≤ s) &&
  (decide (r = c) || decide (r = s)) &&
  (!(decide (v ≤ c) && decide (v ≤ s)) || decide (v ≤ r)) &&
  (!decide (c ≤ t) || decide (r ≤ unsafeTlsDowngrade t s)) &&
  (!decide (s ≤ t) || decide (r ≤ unsafeTlsDowngrade c t)) &&
  (!decide (c = s) || decide (r = c)) &&
  decide (r = unsafeTlsDowngrade s c) &&
  (!(decide (0 ≤ c) && decide (c ≤ 4) && decide (0 ≤ s) && decide (s ≤ 4)) ||
    (decide (0 ≤ r) && decide (r ≤ 4))) &&
  (!(decide (c < t) && decide (c < s)) || decide (r < unsafeTlsDowngrade t s)) &&
  (!decide (c ≤ t) || decide (r ≤ unsafeTlsDowngrade t s))

-- Post_prop, randomised (all four versions sampled).
#eval Plausible.Testable.check (∀ c s v t : Int, postCheckSample c s v t = true)

/-- A small window of integers `[-4, 8]` used for bounded exhaustive tests. -/
def testWindow : List Int := (List.range 13).map (fun i => (i : Int) - 4)

-- match_prop, exhaustive on the window.
example : testWindow.all (fun v => unsafeTlsDowngrade v v == v) = true := by
  native_decide

-- valid_result_prop, exhaustive on all table versions 0 … 4.
example : (List.range 5).all (fun c => (List.range 5).all (fun s =>
    let r := unsafeTlsDowngrade (c : Int) (s : Int)
    decide (0 ≤ r) && decide (r ≤ 4))) = true := by
  native_decide

-- downgrade_vulnerability_prop, exhaustive on the window.
example : testWindow.all (fun c => testWindow.all (fun s => testWindow.all (fun t =>
    !(decide (c < t) && decide (c < s)) ||
      decide (unsafeTlsDowngrade c s < unsafeTlsDowngrade t s)))) = true := by
  native_decide

-- highest_common_prop, exhaustive on the window.
example : testWindow.all (fun c => testWindow.all (fun s => testWindow.all (fun v =>
    !(decide (v ≤ c) && decide (v ≤ s)) || decide (v ≤ unsafeTlsDowngrade c s)))) = true := by
  native_decide

-- monotone_offer_prop, exhaustive on the window.
example : testWindow.all (fun c => testWindow.all (fun s => testWindow.all (fun c' =>
    !decide (c ≤ c') || decide (unsafeTlsDowngrade c s ≤ unsafeTlsDowngrade c' s)))) = true := by
  native_decide

-- monotone_server_prop, exhaustive on the window.
example : testWindow.all (fun c => testWindow.all (fun s => testWindow.all (fun s' =>
    !decide (s ≤ s') || decide (unsafeTlsDowngrade c s ≤ unsafeTlsDowngrade c s')))) = true := by
  native_decide

-- stripped_offer_never_stronger_prop, exhaustive on the window.
example : testWindow.all (fun c => testWindow.all (fun s => testWindow.all (fun t =>
    !decide (c ≤ t) || decide (unsafeTlsDowngrade c s ≤ unsafeTlsDowngrade t s)))) = true := by
  native_decide

/-- Executable Boolean form of `Post_prop`, with the inner universally
quantified versions ranging over `testWindow`. -/
def postCheck (c s : Int) : Bool :=
  testWindow.all (fun v => testWindow.all (fun t => postCheckSample c s v t))

-- Post_prop, exhaustive on the window.
example : testWindow.all (fun c => testWindow.all (fun s => postCheck c s)) = true := by
  native_decide

/-! ## Correctness -/

/-- Correctness: the pre-condition implies the post-condition. -/
theorem correctness_thm (c s : Version) (_hpre : Pre c s) : Post_prop c s :=
  ⟨spec_thm c s,
   result_le_client_thm c s,
   result_le_server_thm c s,
   result_is_input_thm c s,
   highest_common_thm c s,
   monotone_offer_thm c s,
   monotone_server_thm c s,
   match_thm c s,
   symmetric_thm c s,
   valid_result_thm c s,
   downgrade_vulnerability_thm c s,
   stripped_offer_never_stronger_thm c s⟩

/-! ## Imperative implementation -/

/-- Imperative implementation: start from the server maximum and lower the
negotiated version to the (visible) client offer when that is smaller.  As in
the Python program, nothing checks that the offer is the client's true
capability. -/
def unsafeTlsDowngradeImp (clientOfferedMax serverMax : Version) : Version := Id.run do
  let mut negotiated := serverMax
  if clientOfferedMax < negotiated then
    negotiated := clientOfferedMax
  return negotiated

-- Imperative unit tests (same six cases as the Python `check`).
example : unsafeTlsDowngradeImp 4 4 = 4 := by native_decide
example : unsafeTlsDowngradeImp 1 4 = 1 := by native_decide
example : unsafeTlsDowngradeImp 4 2 = 2 := by native_decide
example : unsafeTlsDowngradeImp 3 3 = 3 := by native_decide
example : unsafeTlsDowngradeImp 4 0 = 0 := by native_decide
example : unsafeTlsDowngradeImp 2 4 ≥ unsafeTlsDowngradeImp 1 4 := by native_decide

#eval unsafeTlsDowngradeImp 4 4  -- 4
#eval unsafeTlsDowngradeImp 1 4  -- 1
#eval unsafeTlsDowngradeImp 4 2  -- 2
#eval unsafeTlsDowngradeImp 3 3  -- 3
#eval unsafeTlsDowngradeImp 4 0  -- 0

-- Imperative PBTs: agreement with the functional version.
#eval Plausible.Testable.check
  (∀ c s : Int, unsafeTlsDowngradeImp c s = unsafeTlsDowngrade c s)
example : testWindow.all (fun c => testWindow.all (fun s =>
    unsafeTlsDowngradeImp c s == unsafeTlsDowngrade c s)) = true := by
  native_decide

/-! ## Equivalence -/

/-- The imperative implementation agrees with the functional one on all inputs. -/
theorem imp_eq_functional_thm (c s : Version) :
    unsafeTlsDowngradeImp c s = unsafeTlsDowngrade c s := by
  unfold unsafeTlsDowngradeImp unsafeTlsDowngrade
  simp only [Id.run, min_def, bind, pure]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (le_of_lt h1) h2
  · exact le_antisymm (le_of_not_gt h1) h2
  · rfl

/-- Consequently the imperative implementation also satisfies the post-condition. -/
theorem imp_correctness_thm (c s : Version) (hpre : Pre c s) :
    Post_prop c s ∧ unsafeTlsDowngradeImp c s = min c s := by
  refine ⟨correctness_thm c s hpre, ?_⟩
  rw [imp_eq_functional_thm]
  rfl

end «95_unsafeTlsDowngrade»
