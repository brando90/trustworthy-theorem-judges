import Mathlib
namespace Agent

/-!
# Safe clickjacking defence: X-Frame-Options DENY and SAMEORIGIN

Lean 4 translation of the Python program `63_unsafeClickjacking_safe.py`
(MIT 6.858 Lecture 12 — Web Security Model).

The function `safeClickjacking xfoPolicy isSameOrigin` decides whether a page
may be framed, honouring both X-Frame-Options (XFO) policies:

* `XFO_DENY` (1): block framing by any origin.
* `XFO_SAMEORIGIN` (2): block cross-origin frames; allow same-origin frames.
* any other policy value (`XFO_NONE` = 0, or an unknown value): permissive.

`xfoPolicy` models the Python `int` argument as `Int`; `isSameOrigin` is
`true` if the frame's origin matches the page's origin.  The result is
`true` iff framing is allowed.
-/

namespace «63_unsafeClickjacking_safe»

/-! ## Policy constants -/

/-- No X-Frame-Options policy. -/
def XFO_NONE : Int := 0
/-- X-Frame-Options: DENY. -/
def XFO_DENY : Int := 1
/-- X-Frame-Options: SAMEORIGIN. -/
def XFO_SAMEORIGIN : Int := 2

/-! ## Functional implementation -/

/-- Block framing for DENY (all origins) or SAMEORIGIN (cross-origin only);
return `true` iff framing is allowed. -/
def safeClickjacking (xfoPolicy : Int) (isSameOrigin : Bool) : Bool :=
  if xfoPolicy = XFO_DENY then
    false                       -- DENY: block all frames
  else if xfoPolicy = XFO_SAMEORIGIN then
    isSameOrigin                -- SAMEORIGIN: allow only same-origin
  else
    true                        -- No policy: permissive

/-! ## Unit tests (mirroring the Python `check` harness) -/

-- DENY: blocks all frames regardless of origin
example : safeClickjacking XFO_DENY false = false := by native_decide
example : safeClickjacking XFO_DENY true = false := by native_decide
-- SAMEORIGIN: blocks cross-origin (the key fix)
example : safeClickjacking XFO_SAMEORIGIN false = false := by native_decide
-- SAMEORIGIN: allows same-origin
example : safeClickjacking XFO_SAMEORIGIN true = true := by native_decide
-- No policy: permissive
example : safeClickjacking XFO_NONE false = true := by native_decide
example : safeClickjacking XFO_NONE true = true := by native_decide

/-- Executable version of the Python `check` harness. -/
def check (candidate : Int → Bool → Bool) : Bool :=
  candidate XFO_DENY false == false &&
  candidate XFO_DENY true == false &&
  candidate XFO_SAMEORIGIN false == false &&
  candidate XFO_SAMEORIGIN true == true &&
  candidate XFO_NONE false == true &&
  candidate XFO_NONE true == true

example : check safeClickjacking = true := by native_decide

/-- The Python `check` harness passes (kernel-checked). -/
theorem check_safeClickjacking : check safeClickjacking = true := by decide

#eval safeClickjacking XFO_DENY false        -- false
#eval safeClickjacking XFO_DENY true         -- false
#eval safeClickjacking XFO_SAMEORIGIN false  -- false
#eval safeClickjacking XFO_SAMEORIGIN true   -- true
#eval safeClickjacking XFO_NONE false        -- true
#eval safeClickjacking XFO_NONE true         -- true
#eval check safeClickjacking                 -- true

/-! ## Pre-condition -/

set_option linter.unusedVariables false in
/-- The Python function accepts any integer policy and any Boolean flag:
there is no precondition. -/
def Pre (xfoPolicy : Int) (isSameOrigin : Bool) : Prop := True

/-! ## Policy constants are pairwise distinct -/

theorem deny_ne_sameorigin : XFO_DENY ≠ XFO_SAMEORIGIN := by decide
theorem none_ne_deny : XFO_NONE ≠ XFO_DENY := by decide
theorem none_ne_sameorigin : XFO_NONE ≠ XFO_SAMEORIGIN := by decide

/-! ## Properties -/

/-- DENY blocks framing from every origin. -/
def deny_blocks_all_prop : Prop :=
  ∀ isSameOrigin : Bool, safeClickjacking XFO_DENY isSameOrigin = false

theorem deny_blocks_all_thm : deny_blocks_all_prop := by
  intro b
  cases b <;> decide

/-- SAMEORIGIN allows framing exactly when the frame is same-origin. -/
def sameorigin_iff_prop : Prop :=
  ∀ isSameOrigin : Bool, safeClickjacking XFO_SAMEORIGIN isSameOrigin = isSameOrigin

theorem sameorigin_iff_thm : sameorigin_iff_prop := by
  intro b
  cases b <;> decide

/-- SAMEORIGIN blocks cross-origin frames (the key fix over the unsafe model). -/
def sameorigin_blocks_cross_prop : Prop :=
  safeClickjacking XFO_SAMEORIGIN false = false

theorem sameorigin_blocks_cross_thm : sameorigin_blocks_cross_prop := by
  unfold sameorigin_blocks_cross_prop
  decide

/-- SAMEORIGIN allows same-origin frames. -/
def sameorigin_allows_same_prop : Prop :=
  safeClickjacking XFO_SAMEORIGIN true = true

theorem sameorigin_allows_same_thm : sameorigin_allows_same_prop := by
  unfold sameorigin_allows_same_prop
  decide

/-- `XFO_NONE` (no policy) is permissive for every origin. -/
def none_permissive_prop : Prop :=
  ∀ isSameOrigin : Bool, safeClickjacking XFO_NONE isSameOrigin = true

theorem none_permissive_thm : none_permissive_prop := by
  intro b
  cases b <;> decide

/-- Without a DENY or SAMEORIGIN policy, framing is always permitted,
whatever the (possibly unknown) policy value. -/
def no_policy_permissive_prop : Prop :=
  ∀ (xfoPolicy : Int) (isSameOrigin : Bool),
    xfoPolicy ≠ XFO_DENY → xfoPolicy ≠ XFO_SAMEORIGIN →
      safeClickjacking xfoPolicy isSameOrigin = true

theorem no_policy_permissive_thm : no_policy_permissive_prop := by
  intro p b h1 h2
  simp [safeClickjacking, h1, h2]

/-- Framing is allowed only if the policy is not DENY and, under SAMEORIGIN,
the frame is same-origin. -/
def allowed_only_if_prop : Prop :=
  ∀ (xfoPolicy : Int) (isSameOrigin : Bool),
    safeClickjacking xfoPolicy isSameOrigin = true →
      xfoPolicy ≠ XFO_DENY ∧ (xfoPolicy = XFO_SAMEORIGIN → isSameOrigin = true)

theorem allowed_only_if_thm : allowed_only_if_prop := by
  intro p b h
  unfold safeClickjacking at h
  -- `split_ifs` discharges the DENY branch (`false = true`) automatically.
  split_ifs at h with h1 h2
  · exact ⟨h1, fun _ => h⟩
  · exact ⟨h1, fun h3 => absurd h3 h2⟩

/-- Full characterisation: framing is allowed iff the policy is not DENY and
(the policy is not SAMEORIGIN or the frame is same-origin). -/
def allowed_iff_prop : Prop :=
  ∀ (xfoPolicy : Int) (isSameOrigin : Bool),
    safeClickjacking xfoPolicy isSameOrigin = true ↔
      (xfoPolicy ≠ XFO_DENY ∧ (xfoPolicy = XFO_SAMEORIGIN → isSameOrigin = true))

theorem allowed_iff_thm : allowed_iff_prop := by
  intro p b
  unfold safeClickjacking
  split_ifs with h1 h2
  · simp [h1]
  · subst h2
    simp [h1]
  · simp [h1, h2]

/-- A cross-origin frame is allowed exactly when no XFO protection applies. -/
def cross_origin_allowed_iff_prop : Prop :=
  ∀ xfoPolicy : Int,
    safeClickjacking xfoPolicy false = true ↔
      (xfoPolicy ≠ XFO_DENY ∧ xfoPolicy ≠ XFO_SAMEORIGIN)

theorem cross_origin_allowed_iff_thm : cross_origin_allowed_iff_prop := by
  intro p
  unfold safeClickjacking
  split_ifs with h1 h2
  · simp [h1]
  · simp [h2]
  · simp [h1, h2]

/-- Being same-origin never hurts: if a cross-origin frame is allowed under a
policy, a same-origin frame under the same policy is also allowed. -/
def same_origin_monotone_prop : Prop :=
  ∀ xfoPolicy : Int,
    safeClickjacking xfoPolicy false = true → safeClickjacking xfoPolicy true = true

theorem same_origin_monotone_thm : same_origin_monotone_prop := by
  intro p h
  by_cases h1 : p = XFO_DENY <;> by_cases h2 : p = XFO_SAMEORIGIN <;>
    simp_all [safeClickjacking]

/-! ## Post-condition -/

/-- Post-condition: the result honours DENY, SAMEORIGIN and the permissive
default, and is characterised exactly by `allowed_iff_prop`. -/
def Post_prop (xfoPolicy : Int) (isSameOrigin : Bool) (result : Bool) : Prop :=
  (xfoPolicy = XFO_DENY → result = false) ∧
  (xfoPolicy = XFO_SAMEORIGIN → result = isSameOrigin) ∧
  (xfoPolicy ≠ XFO_DENY → xfoPolicy ≠ XFO_SAMEORIGIN → result = true) ∧
  (result = true ↔ (xfoPolicy ≠ XFO_DENY ∧ (xfoPolicy = XFO_SAMEORIGIN → isSameOrigin = true)))

/-- Executable Boolean form of `Post_prop` (used by the property-based tests). -/
def postCheck (xfoPolicy : Int) (isSameOrigin : Bool) (result : Bool) : Bool :=
  (xfoPolicy != XFO_DENY || result == false) &&
  (xfoPolicy != XFO_SAMEORIGIN || result == isSameOrigin) &&
  (xfoPolicy == XFO_DENY || xfoPolicy == XFO_SAMEORIGIN || result == true) &&
  (result == (xfoPolicy != XFO_DENY && (xfoPolicy != XFO_SAMEORIGIN || isSameOrigin)))

/-! ## Property-based tests -/

-- deny_blocks_all_prop
#eval Plausible.Testable.check (∀ b : Bool, safeClickjacking XFO_DENY b = false)
-- sameorigin_iff_prop
#eval Plausible.Testable.check (∀ b : Bool, safeClickjacking XFO_SAMEORIGIN b = b)
-- sameorigin_blocks_cross_prop / sameorigin_allows_same_prop (closed facts)
example : safeClickjacking XFO_SAMEORIGIN false = false := by native_decide
example : safeClickjacking XFO_SAMEORIGIN true = true := by native_decide
-- none_permissive_prop
#eval Plausible.Testable.check (∀ b : Bool, safeClickjacking XFO_NONE b = true)
-- no_policy_permissive_prop (Boolean form: DENY ∨ SAMEORIGIN ∨ allowed)
#eval Plausible.Testable.check (∀ (p : Int) (b : Bool),
  (p == XFO_DENY || p == XFO_SAMEORIGIN || safeClickjacking p b) = true)
#eval Plausible.Testable.check (∀ (p : Int) (b : Bool),
  p ≠ XFO_DENY → p ≠ XFO_SAMEORIGIN → safeClickjacking p b = true)
-- allowed_only_if_prop (Boolean form)
#eval Plausible.Testable.check (∀ (p : Int) (b : Bool),
  (!safeClickjacking p b || (p != XFO_DENY && (p != XFO_SAMEORIGIN || b))) = true)
-- allowed_iff_prop (Boolean form)
#eval Plausible.Testable.check (∀ (p : Int) (b : Bool),
  safeClickjacking p b = (p != XFO_DENY && (p != XFO_SAMEORIGIN || b)))
-- cross_origin_allowed_iff_prop (Boolean form)
#eval Plausible.Testable.check (∀ p : Int,
  safeClickjacking p false = (p != XFO_DENY && p != XFO_SAMEORIGIN))
-- same_origin_monotone_prop (Boolean form)
#eval Plausible.Testable.check (∀ p : Int,
  (!safeClickjacking p false || safeClickjacking p true) = true)
-- Post_prop (executable form)
#eval Plausible.Testable.check (∀ (p : Int) (b : Bool),
  postCheck p b (safeClickjacking p b) = true)

-- Bounded / exhaustive PBTs over policies -5 .. 14 and both origins.
example : (List.range 20).all (fun n =>
    let p : Int := (n : Int) - 5
    postCheck p false (safeClickjacking p false) &&
    postCheck p true (safeClickjacking p true)) = true := by native_decide
example : (List.range 20).all (fun n =>
    let p : Int := (n : Int) - 5
    (p == XFO_DENY || p == XFO_SAMEORIGIN ||
      (safeClickjacking p false && safeClickjacking p true))) = true := by native_decide
example : (List.range 20).all (fun n =>
    let p : Int := (n : Int) - 5
    safeClickjacking p false == (p != XFO_DENY && p != XFO_SAMEORIGIN)) = true := by
  native_decide
example : (List.range 20).all (fun n =>
    let p : Int := (n : Int) - 5
    (!safeClickjacking p false || safeClickjacking p true)) = true := by native_decide

/-! ## Correctness theorem: Pre → Post -/

theorem safeClickjacking_correct (xfoPolicy : Int) (isSameOrigin : Bool)
    (_hpre : Pre xfoPolicy isSameOrigin) :
    Post_prop xfoPolicy isSameOrigin (safeClickjacking xfoPolicy isSameOrigin) := by
  unfold Post_prop
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    subst h
    cases isSameOrigin <;> decide
  · intro h
    subst h
    cases isSameOrigin <;> decide
  · intro h1 h2
    simp [safeClickjacking, h1, h2]
  · have h : allowed_iff_prop := allowed_iff_thm
    unfold allowed_iff_prop at h
    exact h xfoPolicy isSameOrigin

/-- `postCheck` is a faithful executable rendering of `Post_prop`. -/
theorem postCheck_iff (xfoPolicy : Int) (isSameOrigin : Bool) (result : Bool) :
    postCheck xfoPolicy isSameOrigin result = true ↔
      Post_prop xfoPolicy isSameOrigin result := by
  unfold postCheck Post_prop
  by_cases h1 : xfoPolicy = XFO_DENY <;> by_cases h2 : xfoPolicy = XFO_SAMEORIGIN <;>
    cases result <;> cases isSameOrigin <;> simp_all

/-! ## Imperative implementation -/

/-- Imperative version with a mutable `allowed` flag, mirroring the Python
control flow. -/
def safeClickjackingImp (xfoPolicy : Int) (isSameOrigin : Bool) : Bool := Id.run do
  let mut allowed : Bool := true          -- No policy: permissive by default
  if xfoPolicy = XFO_DENY then
    allowed := false                      -- DENY: block all frames
  else if xfoPolicy = XFO_SAMEORIGIN then
    allowed := isSameOrigin               -- SAMEORIGIN: allow only same-origin
  return allowed

/-! ## Imperative tests -/

example : safeClickjackingImp XFO_DENY false = false := by native_decide
example : safeClickjackingImp XFO_DENY true = false := by native_decide
example : safeClickjackingImp XFO_SAMEORIGIN false = false := by native_decide
example : safeClickjackingImp XFO_SAMEORIGIN true = true := by native_decide
example : safeClickjackingImp XFO_NONE false = true := by native_decide
example : safeClickjackingImp XFO_NONE true = true := by native_decide
example : check safeClickjackingImp = true := by native_decide

#eval safeClickjackingImp XFO_DENY false        -- false
#eval safeClickjackingImp XFO_SAMEORIGIN false  -- false
#eval safeClickjackingImp XFO_SAMEORIGIN true   -- true
#eval safeClickjackingImp XFO_NONE true         -- true
#eval check safeClickjackingImp                 -- true

#eval Plausible.Testable.check (∀ (p : Int) (b : Bool),
  safeClickjacking p b = safeClickjackingImp p b)

/-! ## Equivalence theorem: functional = imperative -/

theorem safeClickjacking_eq_imp (xfoPolicy : Int) (isSameOrigin : Bool) :
    safeClickjacking xfoPolicy isSameOrigin = safeClickjackingImp xfoPolicy isSameOrigin := by
  unfold safeClickjacking safeClickjackingImp
  split_ifs <;> rfl

/-- The imperative implementation therefore also satisfies the post-condition. -/
theorem safeClickjackingImp_correct (xfoPolicy : Int) (isSameOrigin : Bool)
    (hpre : Pre xfoPolicy isSameOrigin) :
    Post_prop xfoPolicy isSameOrigin (safeClickjackingImp xfoPolicy isSameOrigin) := by
  rw [← safeClickjacking_eq_imp]
  exact safeClickjacking_correct xfoPolicy isSameOrigin hpre

/-- The imperative implementation also passes the Python `check` harness. -/
theorem check_safeClickjackingImp : check safeClickjackingImp = true := by decide

end «63_unsafeClickjacking_safe»
end Agent
