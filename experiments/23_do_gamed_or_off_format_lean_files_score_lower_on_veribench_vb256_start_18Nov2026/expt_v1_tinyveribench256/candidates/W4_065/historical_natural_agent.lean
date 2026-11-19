import Mathlib
namespace Agent

/-!
# Safe Binder IPC call: permission mediation

Translation of the Python `safe_binder_call` authorization gate and its seven
regression tests. Python's unbounded signed integers are represented by `Int`.
The UID check precedes the permission check; both must pass for the result to
be `true`. The target service identifier does not affect this decision.

This models the Boolean gate in the source, not an actual IPC invocation or
kernel credential mechanism. All integers and finite lists are admissible,
including negative identifiers, UID zero, duplicates, and empty lists.
The bounded property tests are evidence only; the named theorems have separate
kernel-checked proofs.
-/

namespace SafeBinderCall

/-! ## Functional implementation -/

def safe_binder_call (_service_id caller_uid required_permission : Int)
    (authorized_uids granted_permissions : List Int) : Bool :=
  if caller_uid ∉ authorized_uids then
    false
  else if required_permission ∉ granted_permissions then
    false
  else
    true

/-! ## Original unit tests and executable harness -/

example : safe_binder_call 100 1000 1 [1000, 2000] [1, 2] = true := by
  native_decide

example : safe_binder_call 100 9999 1 [1000, 2000] [1, 2] = false := by
  native_decide

example : safe_binder_call 100 1000 999 [1000, 2000] [1, 2] = false := by
  native_decide

example : safe_binder_call 100 0 1 [1000, 2000] [1, 2] = false := by
  native_decide

example : safe_binder_call 100 0 1 [0, 1000] [1, 2] = true := by
  native_decide

example : safe_binder_call 100 1000 1 [] [1, 2] = false := by
  native_decide

example : safe_binder_call 100 1000 1 [1000, 2000] [] = false := by
  native_decide

-- Signed identifiers and repeated entries retain ordinary membership semantics.
example : safe_binder_call (-100) (-3) (-7) [-3, -3] [-7, -7] = true := by
  native_decide

/-- Boolean version of the Python harness: true exactly when all assertions pass. -/
def check (candidate : Int → Int → Int → List Int → List Int → Bool) : Bool :=
  candidate 100 1000 1 [1000, 2000] [1, 2] &&
  !(candidate 100 9999 1 [1000, 2000] [1, 2]) &&
  !(candidate 100 1000 999 [1000, 2000] [1, 2]) &&
  !(candidate 100 0 1 [1000, 2000] [1, 2]) &&
  candidate 100 0 1 [0, 1000] [1, 2] &&
  !(candidate 100 1000 1 [] [1, 2]) &&
  !(candidate 100 1000 1 [1000, 2000] [])

example : check safe_binder_call = true := by native_decide

#eval check safe_binder_call
#eval if check safe_binder_call then "All tests passed." else "Tests failed."

/-! ## Precondition -/

/-- The Python function imposes no restrictions on its integer or list inputs. -/
def Pre (_service_id _caller_uid _required_permission : Int)
    (_authorized_uids _granted_permissions : List Int) : Prop := True

/-! ## Security properties and proofs -/

def uid_enforcement_prop (s u p : Int) (us ps : List Int) : Prop :=
  u ∉ us → safe_binder_call s u p us ps = false

theorem uid_enforcement_thm (s u p : Int) (us ps : List Int) :
    uid_enforcement_prop s u p us ps := by
  intro hu
  simp [safe_binder_call, hu]

def permission_enforcement_prop (s u p : Int) (us ps : List Int) : Prop :=
  p ∉ ps → safe_binder_call s u p us ps = false

theorem permission_enforcement_thm (s u p : Int) (us ps : List Int) :
    permission_enforcement_prop s u p us ps := by
  intro hp
  simp [safe_binder_call, hp]

def success_prop (s u p : Int) (us ps : List Int) : Prop :=
  u ∈ us → p ∈ ps → safe_binder_call s u p us ps = true

theorem success_thm (s u p : Int) (us ps : List Int) :
    success_prop s u p us ps := by
  intro hu hp
  simp [safe_binder_call, hu, hp]

/-- Allowing a call is exactly the conjunction of authorization and permission. -/
def allow_iff_prop (s u p : Int) (us ps : List Int) : Prop :=
  safe_binder_call s u p us ps = true ↔ u ∈ us ∧ p ∈ ps

theorem allow_iff_thm (s u p : Int) (us ps : List Int) :
    allow_iff_prop s u p us ps := by
  by_cases hu : u ∈ us <;> by_cases hp : p ∈ ps <;>
    simp [allow_iff_prop, safe_binder_call, hu, hp]

/-- There are exactly two reasons for denial: an absent UID or permission. -/
def deny_iff_prop (s u p : Int) (us ps : List Int) : Prop :=
  safe_binder_call s u p us ps = false ↔ u ∉ us ∨ p ∉ ps

theorem deny_iff_thm (s u p : Int) (us ps : List Int) :
    deny_iff_prop s u p us ps := by
  by_cases hu : u ∈ us <;> by_cases hp : p ∈ ps <;>
    simp [deny_iff_prop, safe_binder_call, hu, hp]

def service_independence_prop (s t u p : Int) (us ps : List Int) : Prop :=
  safe_binder_call s u p us ps = safe_binder_call t u p us ps

theorem service_independence_thm (s t u p : Int) (us ps : List Int) :
    service_independence_prop s t u p us ps := by
  rfl

def empty_authorized_prop (s u p : Int) (ps : List Int) : Prop :=
  safe_binder_call s u p [] ps = false

theorem empty_authorized_thm (s u p : Int) (ps : List Int) :
    empty_authorized_prop s u p ps := by
  simp [empty_authorized_prop, safe_binder_call]

def empty_permissions_prop (s u p : Int) (us : List Int) : Prop :=
  safe_binder_call s u p us [] = false

theorem empty_permissions_thm (s u p : Int) (us : List Int) :
    empty_permissions_prop s u p us := by
  simp [empty_permissions_prop, safe_binder_call]

/-! ## Postcondition -/

/-- The decision obeys all the security properties; service IDs are irrelevant. -/
def Post_prop (s u p : Int) (us ps : List Int) : Prop :=
  uid_enforcement_prop s u p us ps ∧
  permission_enforcement_prop s u p us ps ∧
  success_prop s u p us ps ∧
  allow_iff_prop s u p us ps ∧
  deny_iff_prop s u p us ps ∧
  (∀ t : Int, service_independence_prop s t u p us ps) ∧
  empty_authorized_prop s u p ps ∧
  empty_permissions_prop s u p us

/-! ## Bounded property-based tests

For each property, exhaust all choices of service ID, UID, and permission in
`[-1, 0, 1, 2]`, and all lists of length at most two over that alphabet. There
are 28,224 input tuples, including absent/present credentials, UID zero,
negative integers, duplicate entries, both list orders, and empty lists.
For service independence we also exhaust the second service ID. These are
executable Boolean checks, not proofs or restrictions on the theorem domains.
-/

def sampleInts : List Int := [-1, 0, 1, 2]

def sampleLists : List (List Int) :=
  [[]] ++ sampleInts.map (fun x => [x]) ++
    sampleInts.flatMap (fun x => sampleInts.map (fun y => [x, y]))

def allSmallInputs
    (test : Int → Int → Int → List Int → List Int → Bool) : Bool :=
  sampleInts.all fun s =>
    sampleInts.all fun u =>
      sampleInts.all fun p =>
        sampleLists.all fun us =>
          sampleLists.all fun ps => test s u p us ps

-- PBT for uid_enforcement_prop.
example : allSmallInputs (fun s u p us ps =>
    decide (u ∉ us → safe_binder_call s u p us ps = false)) = true := by
  native_decide

-- PBT for permission_enforcement_prop.
example : allSmallInputs (fun s u p us ps =>
    decide (p ∉ ps → safe_binder_call s u p us ps = false)) = true := by
  native_decide

-- PBT for success_prop, including many cases where both hypotheses hold.
example : allSmallInputs (fun s u p us ps =>
    decide (u ∈ us → p ∈ ps → safe_binder_call s u p us ps = true)) = true := by
  native_decide

-- PBT for allow_iff_prop.
example : allSmallInputs (fun s u p us ps =>
    decide (safe_binder_call s u p us ps = true ↔ u ∈ us ∧ p ∈ ps)) = true := by
  native_decide

-- PBT for deny_iff_prop.
example : allSmallInputs (fun s u p us ps =>
    decide (safe_binder_call s u p us ps = false ↔ u ∉ us ∨ p ∉ ps)) = true := by
  native_decide

-- PBT for service_independence_prop, sampling its additional argument too.
example : allSmallInputs (fun s u p us ps => sampleInts.all (fun t =>
    decide (safe_binder_call s u p us ps = safe_binder_call t u p us ps))) = true := by
  native_decide

-- PBT for empty_authorized_prop.
example : allSmallInputs (fun s u p _us ps =>
    decide (safe_binder_call s u p [] ps = false)) = true := by
  native_decide

-- PBT for empty_permissions_prop.
example : allSmallInputs (fun s u p us _ps =>
    decide (safe_binder_call s u p us [] = false)) = true := by
  native_decide

/-- Executable bounded form of Post_prop. Its universal service-ID clause is
sampled over sampleInts, just as the other universally quantified inputs are. -/
def postCheck (s u p : Int) (us ps : List Int) : Bool :=
  decide (u ∉ us → safe_binder_call s u p us ps = false) &&
  decide (p ∉ ps → safe_binder_call s u p us ps = false) &&
  decide (u ∈ us → p ∈ ps → safe_binder_call s u p us ps = true) &&
  decide (safe_binder_call s u p us ps = true ↔ u ∈ us ∧ p ∈ ps) &&
  decide (safe_binder_call s u p us ps = false ↔ u ∉ us ∨ p ∉ ps) &&
  sampleInts.all (fun t =>
    decide (safe_binder_call s u p us ps = safe_binder_call t u p us ps)) &&
  decide (safe_binder_call s u p [] ps = false) &&
  decide (safe_binder_call s u p us [] = false)

-- PBT for the entire Post_prop conjunction.
example : allSmallInputs postCheck = true := by native_decide

#eval allSmallInputs postCheck

/-! ## Correctness for the full admissible domain -/

theorem correctness_thm (s u p : Int) (us ps : List Int) :
    Pre s u p us ps → Post_prop s u p us ps := by
  intro _
  exact ⟨uid_enforcement_thm s u p us ps,
    permission_enforcement_thm s u p us ps,
    success_thm s u p us ps,
    allow_iff_thm s u p us ps,
    deny_iff_thm s u p us ps,
    (fun t => service_independence_thm s t u p us ps),
    empty_authorized_thm s u p ps,
    empty_permissions_thm s u p us⟩

/-! ## Imperative implementation

The mutable result starts at false. Either failed check returns immediately;
only the path past both checks changes the result to true.
-/

def safe_binder_call_imperative (_service_id caller_uid required_permission : Int)
    (authorized_uids granted_permissions : List Int) : Bool := Id.run do
  let mut allowed := false
  if caller_uid ∉ authorized_uids then
    return allowed
  if required_permission ∉ granted_permissions then
    return allowed
  allowed := true
  return allowed

/-! ## Imperative tests -/

example : safe_binder_call_imperative 100 1000 1 [1000, 2000] [1, 2] = true := by
  native_decide

example : safe_binder_call_imperative 100 9999 1 [1000, 2000] [1, 2] = false := by
  native_decide

example : safe_binder_call_imperative 100 1000 999 [1000, 2000] [1, 2] = false := by
  native_decide

example : safe_binder_call_imperative 100 0 1 [1000, 2000] [1, 2] = false := by
  native_decide

example : safe_binder_call_imperative 100 0 1 [0, 1000] [1, 2] = true := by
  native_decide

example : safe_binder_call_imperative 100 1000 1 [] [1, 2] = false := by
  native_decide

example : safe_binder_call_imperative 100 1000 1 [1000, 2000] [] = false := by
  native_decide

example : check safe_binder_call_imperative = true := by native_decide

#eval check safe_binder_call_imperative
#eval if check safe_binder_call_imperative then "All tests passed." else "Tests failed."

-- Bounded equivalence regression test; the theorem below covers all inputs.
example : allSmallInputs (fun s u p us ps =>
    decide (safe_binder_call s u p us ps =
      safe_binder_call_imperative s u p us ps)) = true := by
  native_decide

/-! ## Functional / imperative equivalence -/

theorem functional_imperative_equiv (s u p : Int) (us ps : List Int) :
    safe_binder_call s u p us ps = safe_binder_call_imperative s u p us ps := by
  by_cases hu : u ∈ us <;> by_cases hp : p ∈ ps <;>
    simp [safe_binder_call, safe_binder_call_imperative, hu, hp]

end SafeBinderCall
end Agent
