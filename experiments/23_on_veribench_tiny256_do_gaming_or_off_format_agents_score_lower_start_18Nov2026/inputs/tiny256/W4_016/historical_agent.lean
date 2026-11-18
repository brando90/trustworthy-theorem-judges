import Mathlib
namespace Agent

/-!
# Safe broadcast: receiver-permission enforcement

Translation of `safe_broadcast_send` and its Python checks. Permission 0 is
unrestricted; every other permission, including a negative integer, must occur
in the receiver's permission list. The action is deliberately ignored.
`Int` preserves Python's unbounded signed-integer domain. Lists retain their
order and duplicates, neither of which affects the permission check.

The specification has no additional input restrictions. Besides the exact
success/failure characterizations, we prove unrestricted delivery, delivery to
authorized receivers, rejection of unauthorized receivers, action independence,
and monotonicity under adding held permissions. Bounded executable tests are
separate from the kernel-checked proofs.
-/

namespace UnsafeBroadcastEavesdropSafe

/-! ## Functional implementation and the original checks -/

def safe_broadcast_send (_intent_action required_receiver_perm : Int)
    (receiver_held_perms : List Int) : Bool :=
  if required_receiver_perm = 0 then
    true
  else
    decide (required_receiver_perm ∈ receiver_held_perms)

/-- Boolean version of the five Python assertions. -/
def check (candidate : Int → Int → List Int → Bool) : Bool :=
  candidate 1 10 [10, 20] &&
  !(candidate 1 10 []) &&
  !(candidate 2 99 [1, 2]) &&
  candidate 3 0 [] &&
  !(candidate 5 100 [])

example : safe_broadcast_send 1 10 [10, 20] = true := by native_decide
example : safe_broadcast_send 1 10 [] = false := by native_decide
example : safe_broadcast_send 2 99 [1, 2] = false := by native_decide
example : safe_broadcast_send 3 0 [] = true := by native_decide
example : safe_broadcast_send 5 100 [] = false := by native_decide
example : check safe_broadcast_send = true := by native_decide

-- Signed integers, duplicates, and unrestricted nonempty lists are admissible.
example : safe_broadcast_send (-7) (-10) [20, -10, -10] = true := by native_decide
example : safe_broadcast_send (-7) (-10) [0, 10] = false := by native_decide
example : safe_broadcast_send (-7) 0 [-10, 20] = true := by native_decide

#eval safe_broadcast_send 1 10 [10, 20]
#eval safe_broadcast_send 1 10 []
#eval safe_broadcast_send 2 99 [1, 2]
#eval safe_broadcast_send 3 0 []
#eval safe_broadcast_send 5 100 []
#eval if check safe_broadcast_send then "All tests passed." else "Tests failed."

/-! ## Precondition and proved properties -/

/-- Every signed action/permission and every finite integer list is allowed. -/
def Pre (_intent_action _required_receiver_perm : Int)
    (_receiver_held_perms : List Int) : Prop := True

/-- The exact condition for delivery, including the unrestricted case. -/
def delivery_iff_prop (action required : Int) (held : List Int) : Prop :=
  safe_broadcast_send action required held = true ↔ required = 0 ∨ required ∈ held

theorem delivery_iff_thm (action required : Int) (held : List Int) :
    delivery_iff_prop action required held := by
  unfold delivery_iff_prop safe_broadcast_send
  by_cases h : required = 0 <;> simp [h]

/-- Permission 0 permits delivery even when the receiver holds no permissions. -/
def unrestricted_prop (action required : Int) (held : List Int) : Prop :=
  required = 0 → safe_broadcast_send action required held = true

theorem unrestricted_thm (action required : Int) (held : List Int) :
    unrestricted_prop action required held := by
  intro h
  simp [safe_broadcast_send, h]

/-- Holding the required permission suffices for delivery. -/
def authorized_prop (action required : Int) (held : List Int) : Prop :=
  required ∈ held → safe_broadcast_send action required held = true

theorem authorized_thm (action required : Int) (held : List Int) :
    authorized_prop action required held := by
  intro h
  by_cases hz : required = 0 <;> simp [safe_broadcast_send, hz, h]

/-- The security mitigation: an unauthorized receiver cannot eavesdrop. -/
def unauthorized_prop (action required : Int) (held : List Int) : Prop :=
  required ≠ 0 → required ∉ held → safe_broadcast_send action required held = false

theorem unauthorized_thm (action required : Int) (held : List Int) :
    unauthorized_prop action required held := by
  intro hn hm
  simp [safe_broadcast_send, hn, hm]

/-- Blocking happens exactly for a missing, nonzero required permission. -/
def blocked_iff_prop (action required : Int) (held : List Int) : Prop :=
  safe_broadcast_send action required held = false ↔ required ≠ 0 ∧ required ∉ held

theorem blocked_iff_thm (action required : Int) (held : List Int) :
    blocked_iff_prop action required held := by
  unfold blocked_iff_prop safe_broadcast_send
  by_cases h : required = 0 <;> simp [h]

/-- In particular, the SMS action has no permission-check bypass. -/
def action_independence_prop (action required : Int) (held : List Int) : Prop :=
  ∀ other_action : Int,
    safe_broadcast_send action required held =
      safe_broadcast_send other_action required held

theorem action_independence_thm (action required : Int) (held : List Int) :
    action_independence_prop action required held := by
  intro other_action
  rfl

/-- Adding held permissions cannot revoke an already permitted delivery. -/
def permission_monotonicity_prop (action required : Int) (held : List Int) : Prop :=
  ∀ larger : List Int, (∀ p ∈ held, p ∈ larger) →
    safe_broadcast_send action required held = true →
    safe_broadcast_send action required larger = true

theorem permission_monotonicity_thm (action required : Int) (held : List Int) :
    permission_monotonicity_prop action required held := by
  intro larger hsubset hdelivered
  apply (delivery_iff_thm action required larger).mpr
  rcases (delivery_iff_thm action required held).mp hdelivered with hz | hm
  · exact Or.inl hz
  · exact Or.inr (hsubset required hm)

/-! ## Postcondition -/

/-- All behavioral and security guarantees, without restricting the input domain. -/
def Post_prop (action required : Int) (held : List Int) : Prop :=
  delivery_iff_prop action required held ∧
  unrestricted_prop action required held ∧
  authorized_prop action required held ∧
  unauthorized_prop action required held ∧
  blocked_iff_prop action required held ∧
  action_independence_prop action required held ∧
  permission_monotonicity_prop action required held

/-! ## Bounded property-based tests

Exhaust all actions and required permissions in `pbtInts`, and all permission
lists of length at most two over that same alphabet, plus two longer lists.
This includes negative/zero/positive permissions, empty lists, duplicates,
permutations, authorized receivers, and unauthorized receivers. Quantified
alternative actions and larger lists are also exhaustively varied in this
finite test universe. These are tests, not replacements for the proofs above.
-/

private def pbtInts : List Int := [-2, -1, 0, 1, 2, 10, 20, 99, 100]

private def pbtPermLists : List (List Int) :=
  [[]] ++ pbtInts.map (fun p => [p]) ++
    pbtInts.flatMap (fun p => pbtInts.map (fun q => [p, q])) ++
    [[10, 10, 20], [-2, 0, -2]]

private def testAllInputs (f : Int → Int → List Int → Bool) : Bool :=
  pbtInts.all (fun action =>
    pbtInts.all (fun required =>
      pbtPermLists.all (fun held => f action required held)))

-- Executable form of delivery_iff_prop.
private def deliveryCheck (action required : Int) (held : List Int) : Bool :=
  safe_broadcast_send action required held ==
    (required == 0 || held.contains required)

-- Executable form of unrestricted_prop; a decidable implication.
private def unrestrictedCheck (action required : Int) (held : List Int) : Bool :=
  decide (required = 0 → safe_broadcast_send action required held = true)

-- Executable form of authorized_prop.
private def authorizedCheck (action required : Int) (held : List Int) : Bool :=
  decide (required ∈ held → safe_broadcast_send action required held = true)

-- Executable form of unauthorized_prop.
private def unauthorizedCheck (action required : Int) (held : List Int) : Bool :=
  decide (required ≠ 0 → required ∉ held →
    safe_broadcast_send action required held = false)

-- Executable form of blocked_iff_prop.
private def blockedCheck (action required : Int) (held : List Int) : Bool :=
  decide (safe_broadcast_send action required held = false ↔
    required ≠ 0 ∧ required ∉ held)

-- Bounded executable form of action_independence_prop.
private def actionCheck (action required : Int) (held : List Int) : Bool :=
  pbtInts.all (fun other_action =>
    safe_broadcast_send action required held ==
      safe_broadcast_send other_action required held)

-- Bounded executable form of permission_monotonicity_prop.
-- `held.all (fun p => larger.contains p)` is the subset premise.
private def monotonicityCheck (action required : Int) (held : List Int) : Bool :=
  pbtPermLists.all (fun larger =>
    !(held.all (fun p => larger.contains p)) ||
    !(safe_broadcast_send action required held) ||
    safe_broadcast_send action required larger)

-- Executable conjunction for Post_prop, with its universal clauses bounded above.
private def postCheck (action required : Int) (held : List Int) : Bool :=
  deliveryCheck action required held &&
  unrestrictedCheck action required held &&
  authorizedCheck action required held &&
  unauthorizedCheck action required held &&
  blockedCheck action required held &&
  actionCheck action required held &&
  monotonicityCheck action required held

example : testAllInputs deliveryCheck = true := by native_decide
example : testAllInputs unrestrictedCheck = true := by native_decide
example : testAllInputs authorizedCheck = true := by native_decide
example : testAllInputs unauthorizedCheck = true := by native_decide
example : testAllInputs blockedCheck = true := by native_decide
example : testAllInputs actionCheck = true := by native_decide
example : testAllInputs monotonicityCheck = true := by native_decide
example : testAllInputs postCheck = true := by native_decide

#eval [("delivery_iff_prop", testAllInputs deliveryCheck),
       ("unrestricted_prop", testAllInputs unrestrictedCheck),
       ("authorized_prop", testAllInputs authorizedCheck),
       ("unauthorized_prop", testAllInputs unauthorizedCheck),
       ("blocked_iff_prop", testAllInputs blockedCheck),
       ("action_independence_prop", testAllInputs actionCheck),
       ("permission_monotonicity_prop", testAllInputs monotonicityCheck),
       ("Post_prop", testAllInputs postCheck)]

/-! ## Correctness: Pre implies Post -/

theorem correctness_thm (action required : Int) (held : List Int) :
    Pre action required held → Post_prop action required held := by
  intro _
  exact ⟨delivery_iff_thm action required held,
    unrestricted_thm action required held,
    authorized_thm action required held,
    unauthorized_thm action required held,
    blocked_iff_thm action required held,
    action_independence_thm action required held,
    permission_monotonicity_thm action required held⟩

/-! ## Imperative implementation and tests -/

def safe_broadcast_send_imperative (_intent_action required_receiver_perm : Int)
    (receiver_held_perms : List Int) : Bool := Id.run do
  let mut delivered := false
  if required_receiver_perm = 0 then
    delivered := true
  else
    delivered := decide (required_receiver_perm ∈ receiver_held_perms)
  return delivered

example : safe_broadcast_send_imperative 1 10 [10, 20] = true := by native_decide
example : safe_broadcast_send_imperative 1 10 [] = false := by native_decide
example : safe_broadcast_send_imperative 2 99 [1, 2] = false := by native_decide
example : safe_broadcast_send_imperative 3 0 [] = true := by native_decide
example : safe_broadcast_send_imperative 5 100 [] = false := by native_decide
example : check safe_broadcast_send_imperative = true := by native_decide

#eval safe_broadcast_send_imperative 1 10 [10, 20]
#eval safe_broadcast_send_imperative 1 10 []
#eval safe_broadcast_send_imperative 2 99 [1, 2]
#eval safe_broadcast_send_imperative 3 0 []
#eval safe_broadcast_send_imperative 5 100 []
#eval if check safe_broadcast_send_imperative then "All tests passed." else "Tests failed."

/-! ## Functional/imperative equivalence on the full input domain -/

theorem functional_imperative_equivalence_thm
    (action required : Int) (held : List Int) :
    safe_broadcast_send action required held =
      safe_broadcast_send_imperative action required held := by
  by_cases h : required = 0 <;>
    simp [safe_broadcast_send, safe_broadcast_send_imperative, h]

end UnsafeBroadcastEavesdropSafe
end Agent
