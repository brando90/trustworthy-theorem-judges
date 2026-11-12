import Mathlib

/-!
# 95 — Unsafe TLS version downgrade

Formalisation of the Python module `unsafe_tls_downgrade`
(MIT 6.858 Lecture 14 — TLS / Downgrade).

A correct TLS server negotiates `min(client_offered_max, server_max)`, i.e. the
highest protocol version that both peers support.  An on-path attacker can strip
strong versions out of the ClientHello before it reaches the server.  Because
the negotiation carries no sentinel binding the client's *true* capability into
the transcript, the server happily picks the highest common version of the
*tampered* offer — typically a much weaker protocol than client and server
actually share.

Protocol versions are integers, higher = newer:

    0 = SSL 3.0, 1 = TLS 1.0, 2 = TLS 1.1, 3 = TLS 1.2, 4 = TLS 1.3.

The Python `int` domain is modelled with Lean's `Int`: every algebraic property
below is stated for arbitrary integers (the Python function is total on `int`),
and the admissible protocol-version domain is captured by `Pre`.
-/

namespace UnsafeTlsDowngrade

/-! ## Protocol version codes -/

def SSL30 : Int := 0
def TLS10 : Int := 1
def TLS11 : Int := 2
def TLS12 : Int := 3
def TLS13 : Int := 4

/-! ## Functional implementation -/

/-- `unsafe_tls_downgrade(client_offered_max, server_max)`: the highest version
common to the (possibly attacker-modified) client offer and the server's own
maximum.  The vulnerability is the absence of any check that
`client_offered_max` equals the client's true capability. -/
def unsafe_tls_downgrade (client_offered_max server_max : Int) : Int :=
  min client_offered_max server_max

/-! ## Unit tests — the Python `check` harness -/

/-- Direct transcription of the Python `check` function. -/
def check (candidate : Int → Int → Int) : Bool :=
  decide (candidate 4 4 = 4) &&
  decide (candidate 1 4 = 1) &&
  decide (candidate 4 2 = 2) &&
  decide (candidate 3 3 = 3) &&
  decide (candidate 4 0 = 0) &&
  decide (candidate 2 4 >= candidate 1 4)

-- 1) No attack: TLS 1.3 negotiated.
example : unsafe_tls_downgrade TLS13 TLS13 = TLS13 := by native_decide
example : unsafe_tls_downgrade 4 4 = 4 := by native_decide
-- 2) VULNERABILITY: attacker stripped the offer to TLS 1.0; the server picks 1.
example : unsafe_tls_downgrade TLS10 TLS13 = TLS10 := by native_decide
example : unsafe_tls_downgrade 1 4 = 1 := by native_decide
-- 3) Server caps the result.
example : unsafe_tls_downgrade TLS13 TLS11 = TLS11 := by native_decide
example : unsafe_tls_downgrade 4 2 = 2 := by native_decide
-- 4) Match: full version negotiated.
example : unsafe_tls_downgrade TLS12 TLS12 = TLS12 := by native_decide
example : unsafe_tls_downgrade 3 3 = 3 := by native_decide
-- 5) Edge: legacy-only server.
example : unsafe_tls_downgrade TLS13 SSL30 = SSL30 := by native_decide
example : unsafe_tls_downgrade 4 0 = 0 := by native_decide
-- 6) Monotone in offer: more visible offer ≥ less visible offer.
example : unsafe_tls_downgrade 2 4 >= unsafe_tls_downgrade 1 4 := by native_decide
-- The whole Python harness passes for the functional implementation.
example : check unsafe_tls_downgrade = true := by native_decide

#eval unsafe_tls_downgrade 4 4
#eval unsafe_tls_downgrade 1 4
#eval unsafe_tls_downgrade 4 2
#eval unsafe_tls_downgrade 3 3
#eval unsafe_tls_downgrade 4 0
#eval unsafe_tls_downgrade 2 4 >= unsafe_tls_downgrade 1 4
#eval check unsafe_tls_downgrade

/-! ## Properties of the negotiation -/

/-- Branch semantics: the result is the offered version when the offer is the
smaller one, and the server's maximum otherwise. -/
def ite_prop (c s : Int) : Prop :=
  unsafe_tls_downgrade c s = if c ≤ s then c else s

/-- The negotiated version never exceeds the (visible) client offer. -/
def le_client_prop (c s : Int) : Prop := unsafe_tls_downgrade c s ≤ c

/-- The negotiated version never exceeds the server's own maximum. -/
def le_server_prop (c s : Int) : Prop := unsafe_tls_downgrade c s ≤ s

/-- Greatest-lower-bound characterisation: the negotiated version is the
*highest* common version, so every version supported by both peers is ≤ it. -/
def glb_prop (c s : Int) : Prop :=
  (x : Int) → x ≤ c → x ≤ s → x ≤ unsafe_tls_downgrade c s

/-- The negotiation depends only on the unordered pair of maxima. -/
def comm_prop (c s : Int) : Prop :=
  unsafe_tls_downgrade c s = unsafe_tls_downgrade s c

/-- When both peers top out at the same version, exactly that version is
negotiated (Python checks 1 and 4). -/
def idem_prop (c s : Int) : Prop := c = s → unsafe_tls_downgrade c s = c

/-- Python check 6: a more visible offer never negotiates worse. -/
def mono_offer_prop (c1 c2 s : Int) : Prop :=
  c1 ≤ c2 → unsafe_tls_downgrade c1 s ≤ unsafe_tls_downgrade c2 s

/-- A stronger server maximum never negotiates worse. -/
def mono_server_prop (c s1 s2 : Int) : Prop :=
  s1 ≤ s2 → unsafe_tls_downgrade c s1 ≤ unsafe_tls_downgrade c s2

/-- The attacker can only lower the visible offer, and lowering the offer never
raises the negotiated version: the attack never helps the client. -/
def attack_never_helps_prop (c_att c_true s : Int) : Prop :=
  c_att ≤ c_true → unsafe_tls_downgrade c_att s ≤ unsafe_tls_downgrade c_true s

/-- VULNERABILITY: whenever the stripped offer drops below the honest result,
the server silently negotiates a strictly weaker version — no sentinel reveals
the tampering. -/
def attack_downgrades_prop (c_att c_true s : Int) : Prop :=
  c_att < min c_true s → unsafe_tls_downgrade c_att s < unsafe_tls_downgrade c_true s

/-- On admissible inputs the negotiated version is again an admissible version
code (between SSL 3.0 and TLS 1.3). -/
def bounded_prop (c s : Int) : Prop :=
  0 ≤ c → c ≤ 4 → 0 ≤ s → s ≤ 4 →
    0 ≤ unsafe_tls_downgrade c s ∧ unsafe_tls_downgrade c s ≤ 4

/-- Absence of a sentinel: two different client offers can produce exactly the
same server output, so the server cannot detect the downgrade. -/
def no_sentinel_prop : Prop :=
  ∃ c1 c2 s : Int, c1 ≠ c2 ∧ unsafe_tls_downgrade c1 s = unsafe_tls_downgrade c2 s

/-- The negotiated version is always exactly one of the two peers' maxima: the
server either accepts the (possibly tampered) client offer or falls back to its
own maximum. -/
def dichotomy_prop (c s : Int) : Prop :=
  unsafe_tls_downgrade c s = c ∨ unsafe_tls_downgrade c s = s

theorem ite_thm (c s : Int) : ite_prop c s := by
  rw [ite_prop, unsafe_tls_downgrade, min_def]

theorem le_client_thm (c s : Int) : le_client_prop c s :=
  min_le_left c s

theorem le_server_thm (c s : Int) : le_server_prop c s :=
  min_le_right c s

theorem glb_thm (c s : Int) : glb_prop c s := by
  intro x hc hs
  exact le_min hc hs

theorem comm_thm (c s : Int) : comm_prop c s :=
  min_comm c s

theorem idem_thm (c s : Int) : idem_prop c s := by
  intro h
  rw [unsafe_tls_downgrade, h]
  exact min_self s

theorem mono_offer_thm (c1 c2 s : Int) : mono_offer_prop c1 c2 s := by
  intro h
  exact min_le_min h (le_refl s)

theorem mono_server_thm (c s1 s2 : Int) : mono_server_prop c s1 s2 := by
  intro h
  exact min_le_min (le_refl c) h

theorem attack_never_helps_thm (c_att c_true s : Int) :
    attack_never_helps_prop c_att c_true s :=
  mono_offer_thm c_att c_true s

theorem attack_downgrades_thm (c_att c_true s : Int) :
    attack_downgrades_prop c_att c_true s := by
  intro h
  exact lt_of_le_of_lt (min_le_left c_att s) h

theorem bounded_thm (c s : Int) : bounded_prop c s := by
  intro hc0 hc4 hs0 _hs4
  exact ⟨le_min hc0 hs0, le_trans (min_le_left c s) hc4⟩

/-- Concrete witness of the vulnerability: the client truly offers TLS 1.3 and
the server supports TLS 1.3, yet an attacker who strips the offer down to
TLS 1.0 makes the server negotiate TLS 1.0. -/
theorem downgrade_witness :
    unsafe_tls_downgrade TLS13 TLS13 = TLS13 ∧
    unsafe_tls_downgrade TLS10 TLS13 = TLS10 ∧
    TLS10 < unsafe_tls_downgrade TLS13 TLS13 := by
  exact ⟨min_self TLS13, min_eq_left (by decide : TLS10 ≤ TLS13), by decide⟩

theorem no_sentinel_thm : no_sentinel_prop :=
  ⟨TLS10, TLS11, SSL30, by decide, by decide⟩

theorem dichotomy_thm (c s : Int) : dichotomy_prop c s := by
  rcases le_total c s with h | h
  · exact Or.inl (min_eq_left h)
  · exact Or.inr (min_eq_right h)

/-! ## Pre-condition -/

/-- Admissible inputs: both arguments are valid protocol version codes,
`0 = SSL 3.0` … `4 = TLS 1.3`. -/
def Pre (c s : Int) : Prop := 0 ≤ c ∧ c ≤ 4 ∧ 0 ≤ s ∧ s ≤ 4

/-! ## Post-condition -/

/-- Everything the negotiation guarantees on admissible inputs. -/
def Post_prop (c s : Int) : Prop :=
  ite_prop c s ∧
  le_client_prop c s ∧
  le_server_prop c s ∧
  glb_prop c s ∧
  comm_prop c s ∧
  idem_prop c s ∧
  bounded_prop c s ∧
  dichotomy_prop c s ∧
  ((c_att : Int) → c_att ≤ c → unsafe_tls_downgrade c_att s ≤ unsafe_tls_downgrade c s)

/-! ## Property-based tests -/

/-- Small integer probes used by the bounded checks below. -/
def probeInts : List Int := (List.range 13).map (fun i => (i : Int) - 6)

/-- Executable Boolean form of `Post_prop`: every conjunct is checked exactly,
the two universally quantified clauses (`glb_prop` and monotonicity in the
offer) are probed over `probeInts`. -/
def Post_check (c s : Int) : Bool :=
  decide (unsafe_tls_downgrade c s = if c ≤ s then c else s) &&
  decide (unsafe_tls_downgrade c s ≤ c) &&
  decide (unsafe_tls_downgrade c s ≤ s) &&
  decide (unsafe_tls_downgrade c s = unsafe_tls_downgrade s c) &&
  decide (unsafe_tls_downgrade c s = c || unsafe_tls_downgrade c s = s) &&
  (!decide (c = s) || decide (unsafe_tls_downgrade c s = c)) &&
  (!decide (0 ≤ c) || !decide (c ≤ 4) || !decide (0 ≤ s) || !decide (s ≤ 4) ||
    (decide (0 ≤ unsafe_tls_downgrade c s) && decide (unsafe_tls_downgrade c s ≤ 4))) &&
  probeInts.all (fun x => !decide (x ≤ c) || !decide (x ≤ s) || decide (x ≤ unsafe_tls_downgrade c s)) &&
  probeInts.all (fun x => !decide (x ≤ c) || decide (unsafe_tls_downgrade x s ≤ unsafe_tls_downgrade c s))

-- Randomised PBT for the whole post-condition.
#eval Plausible.Testable.check (∀ c s : Int, Post_check c s)
-- Randomised PBTs, one per stated property.
#eval Plausible.Testable.check (∀ c s : Int, unsafe_tls_downgrade c s = if c ≤ s then c else s)
#eval Plausible.Testable.check (∀ c s : Int, unsafe_tls_downgrade c s ≤ c ∧ unsafe_tls_downgrade c s ≤ s)
#eval Plausible.Testable.check (∀ c s x : Int, c < x || s < x || x ≤ unsafe_tls_downgrade c s)
#eval Plausible.Testable.check (∀ c s : Int, unsafe_tls_downgrade c s = unsafe_tls_downgrade s c)
#eval Plausible.Testable.check (∀ c s : Int, unsafe_tls_downgrade c s = c || unsafe_tls_downgrade c s = s)
#eval Plausible.Testable.check (∀ c s : Int, c ≠ s || unsafe_tls_downgrade c s = c)
#eval Plausible.Testable.check (∀ c1 c2 s : Int, c2 < c1 || unsafe_tls_downgrade c1 s ≤ unsafe_tls_downgrade c2 s)
#eval Plausible.Testable.check (∀ c s1 s2 : Int, s2 < s1 || unsafe_tls_downgrade c s1 ≤ unsafe_tls_downgrade c s2)
#eval Plausible.Testable.check (∀ c_att c_true s : Int, c_true < c_att || unsafe_tls_downgrade c_att s ≤ unsafe_tls_downgrade c_true s)
#eval Plausible.Testable.check (∀ c_att c_true s : Int, min c_true s ≤ c_att || unsafe_tls_downgrade c_att s < unsafe_tls_downgrade c_true s)
#eval Plausible.Testable.check (∀ c s : Int, ¬(0 ≤ c ∧ c ≤ 4 ∧ 0 ≤ s ∧ s ≤ 4) || (0 ≤ unsafe_tls_downgrade c s ∧ unsafe_tls_downgrade c s ≤ 4))

-- Bounded (exhaustive small-case) PBTs.
example : (List.range 12).all (fun i =>
    (List.range 12).all (fun j => Post_check ((i:Int) - 5) ((j:Int) - 5))) = true := by native_decide

example : (List.range 6).all (fun i => (List.range 6).all (fun j =>
    decide (unsafe_tls_downgrade (i:Int) (j:Int) = min (i:Int) (j:Int)))) = true := by native_decide

example : (List.range 5).all (fun i => (List.range 5).all (fun j =>
    decide (unsafe_tls_downgrade (i:Int) (j:Int) ≤ (i:Int) ∧ unsafe_tls_downgrade (i:Int) (j:Int) ≤ (j:Int)))) = true := by native_decide

/-- Bounded search witnessing `no_sentinel_prop`: two distinct client offers
that the server cannot tell apart. -/
def no_sentinel_check : Bool :=
  (List.range 5).any (fun i => (List.range 5).any (fun j =>
    decide ((i:Int) ≠ (j:Int)) &&
    decide (unsafe_tls_downgrade (i:Int) SSL30 = unsafe_tls_downgrade (j:Int) SSL30)))

example : no_sentinel_check = true := by native_decide

#eval no_sentinel_check

-- Bounded exhaustive PBTs for the precondition-carrying properties above
-- (the randomised versions are written with a disjunction so that no sample is
-- ever discarded; these check the same clauses exhaustively on `probeInts`).
example : probeInts.all (fun c => probeInts.all (fun s => probeInts.all (fun x =>
    !decide (x ≤ c) || !decide (x ≤ s) || decide (x ≤ unsafe_tls_downgrade c s)))) = true := by native_decide

example : probeInts.all (fun c => probeInts.all (fun s =>
    !decide (c = s) || decide (unsafe_tls_downgrade c s = c))) = true := by native_decide

example : probeInts.all (fun c1 => probeInts.all (fun c2 => probeInts.all (fun s =>
    !decide (c1 ≤ c2) || decide (unsafe_tls_downgrade c1 s ≤ unsafe_tls_downgrade c2 s)))) = true := by native_decide

example : probeInts.all (fun c => probeInts.all (fun s1 => probeInts.all (fun s2 =>
    !decide (s1 ≤ s2) || decide (unsafe_tls_downgrade c s1 ≤ unsafe_tls_downgrade c s2)))) = true := by native_decide

example : probeInts.all (fun c_att => probeInts.all (fun c_true => probeInts.all (fun s =>
    !decide (c_att ≤ c_true) ||
    decide (unsafe_tls_downgrade c_att s ≤ unsafe_tls_downgrade c_true s)))) = true := by native_decide

example : probeInts.all (fun c_att => probeInts.all (fun c_true => probeInts.all (fun s =>
    !decide (c_att < min c_true s) ||
    decide (unsafe_tls_downgrade c_att s < unsafe_tls_downgrade c_true s)))) = true := by native_decide

example : (List.range 5).all (fun i => (List.range 5).all (fun j =>
    decide (0 ≤ unsafe_tls_downgrade (i:Int) (j:Int) ∧ unsafe_tls_downgrade (i:Int) (j:Int) ≤ 4))) = true := by native_decide

/-! ## Correctness: `Pre → Post` -/

theorem correctness_thm (c s : Int) (_h : Pre c s) : Post_prop c s :=
  ⟨ite_thm c s, le_client_thm c s, le_server_thm c s, glb_thm c s, comm_thm c s,
    idem_thm c s, bounded_thm c s, dichotomy_thm c s,
    fun c_att hc => mono_offer_thm c_att c s hc⟩

/-- The post-condition in fact holds on the *whole* Python `int` domain:
`unsafe_tls_downgrade` is total, and `Pre` only records which arguments are
meaningful protocol version codes. -/
theorem correctness_uncond_thm (c s : Int) : Post_prop c s :=
  ⟨ite_thm c s, le_client_thm c s, le_server_thm c s, glb_thm c s, comm_thm c s,
    idem_thm c s, bounded_thm c s, dichotomy_thm c s,
    fun c_att hc => mono_offer_thm c_att c s hc⟩

/-! ## Imperative implementation -/

/-- Imperative rendering of the server's version selection: a mutable
`negotiated` register is initialised from the client's (possibly tampered)
offer and then capped by the server's own maximum.  Nothing records what the
client actually offered, which is the vulnerability. -/
def unsafeTlsDowngradeImp (clientOfferedMax serverMax : Int) : Int :=
  Id.run do
    let mut negotiated : Int := clientOfferedMax
    let mut serverCap : Int := serverMax
    if serverCap < negotiated then
      negotiated := serverCap
    return negotiated

/-! ## Imperative tests -/

example : unsafeTlsDowngradeImp 4 4 = 4 := by native_decide
example : unsafeTlsDowngradeImp 1 4 = 1 := by native_decide
example : unsafeTlsDowngradeImp 4 2 = 2 := by native_decide
example : unsafeTlsDowngradeImp 3 3 = 3 := by native_decide
example : unsafeTlsDowngradeImp 4 0 = 0 := by native_decide
example : unsafeTlsDowngradeImp 2 4 >= unsafeTlsDowngradeImp 1 4 := by native_decide
example : check unsafeTlsDowngradeImp = true := by native_decide

example : (List.range 12).all (fun i => (List.range 12).all (fun j =>
    decide (unsafeTlsDowngradeImp ((i:Int) - 5) ((j:Int) - 5) =
      min ((i:Int) - 5) ((j:Int) - 5)))) = true := by native_decide

#eval Plausible.Testable.check (∀ c s : Int, unsafeTlsDowngradeImp c s = unsafe_tls_downgrade c s)

#eval unsafeTlsDowngradeImp 4 4
#eval unsafeTlsDowngradeImp 1 4
#eval unsafeTlsDowngradeImp 4 2
#eval check unsafeTlsDowngradeImp

/-! ## Equivalence: functional = imperative -/

theorem imp_ite (c s : Int) : unsafeTlsDowngradeImp c s = if s < c then s else c := by rfl

theorem imp_eq_functional (c s : Int) :
    unsafeTlsDowngradeImp c s = unsafe_tls_downgrade c s := by
  rw [imp_ite, unsafe_tls_downgrade]
  by_cases h : c ≤ s
  · rw [if_neg (Int.not_lt.mpr h), min_eq_left h]
  · have hlt : s < c := Int.not_le.mp h
    rw [if_pos hlt, min_eq_right (le_of_lt hlt)]

theorem imp_satisfies_post (c s : Int) (h : Pre c s) : Post_prop c s := by
  have := correctness_thm c s h
  simpa [imp_eq_functional] using this

/-! ## A second imperative implementation: scanning the version ladder -/

/-- Imperative variant that mirrors how a real server walks its supported
version list: scan the ladder from the strongest version downwards and remember
the first version that both the (visible) client offer and the server's own
maximum allow.  On admissible inputs this is exactly `min`. -/
def unsafeTlsDowngradeLadderImp (clientOfferedMax serverMax : Int) : Int :=
  Id.run do
    let mut found : Bool := false
    let mut result : Int := SSL30
    for v in [TLS13, TLS12, TLS11, TLS10, SSL30] do
      if !found && decide (v ≤ clientOfferedMax) && decide (v ≤ serverMax) then
        found := true
        result := v
    return result

/-! ### Imperative (ladder) tests -/

example : unsafeTlsDowngradeLadderImp 4 4 = 4 := by native_decide
example : unsafeTlsDowngradeLadderImp 1 4 = 1 := by native_decide
example : unsafeTlsDowngradeLadderImp 4 2 = 2 := by native_decide
example : unsafeTlsDowngradeLadderImp 3 3 = 3 := by native_decide
example : unsafeTlsDowngradeLadderImp 4 0 = 0 := by native_decide
example : unsafeTlsDowngradeLadderImp 2 4 >= unsafeTlsDowngradeLadderImp 1 4 := by native_decide
example : check unsafeTlsDowngradeLadderImp = true := by native_decide

example : (List.range 5).all (fun i => (List.range 5).all (fun j =>
    decide (unsafeTlsDowngradeLadderImp (i:Int) (j:Int) = min (i:Int) (j:Int)))) = true := by native_decide

#eval Plausible.Testable.check (∀ c s : Int,
  ¬(0 ≤ c ∧ c ≤ 4 ∧ 0 ≤ s ∧ s ≤ 4) ||
  unsafeTlsDowngradeLadderImp c s = unsafe_tls_downgrade c s)

#eval unsafeTlsDowngradeLadderImp 4 4
#eval unsafeTlsDowngradeLadderImp 1 4
#eval unsafeTlsDowngradeLadderImp 4 2
#eval check unsafeTlsDowngradeLadderImp

/-! ### Equivalence of the ladder scan with the functional implementation -/

theorem ladderImp_eq_functional (c s : Int) (h : Pre c s) :
    unsafeTlsDowngradeLadderImp c s = unsafe_tls_downgrade c s := by
  obtain ⟨hc0, hc4, hs0, hs4⟩ := h
  have hcl : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by omega
  have hsl : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 := by omega
  rcases hcl with (rfl|rfl|rfl|rfl|rfl) <;> rcases hsl with (rfl|rfl|rfl|rfl|rfl) <;> rfl

theorem ladderImp_eq_imp (c s : Int) (h : Pre c s) :
    unsafeTlsDowngradeLadderImp c s = unsafeTlsDowngradeImp c s := by
  rw [ladderImp_eq_functional c s h, imp_eq_functional]

end UnsafeTlsDowngrade
