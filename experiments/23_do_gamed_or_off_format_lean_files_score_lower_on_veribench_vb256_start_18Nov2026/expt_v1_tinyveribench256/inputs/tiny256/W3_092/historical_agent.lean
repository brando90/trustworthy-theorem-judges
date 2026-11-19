import Mathlib
namespace Agent

/-!
# Safe onion-routed forwarding

Translation of `safe_onion_route` and its Python checks. Python's unbounded signed
integers are represented by `Int`. The destination observes the last relay and
the unchanged message, or the source and message for the direct fallback.

For a nonempty relay chain the observation is independent of the source and of
the destination parameter. This is an extensional observation model, not a model
of encryption or network traffic. A relay address may numerically equal the
source address: numerical source exclusion requires the source not to occur in
the relay chain. No such restriction is imposed on the implementation's domain.
-/

namespace SafeOnionRoute

/-- The last relay, with the source as the empty-chain fallback. -/
def safe_onion_route (src_ip _dst_ip msg : Int) (relays : List Int) : Int × Int :=
  (relays.getLastD src_ip, msg)

-- Fixed tests from the Python program.
example : safe_onion_route 192168001 8080 42 [10, 20, 30] = (30, 42) := by
  native_decide
example : (safe_onion_route 192168001 8080 42 [10, 20, 30]).1 ≠ 192168001 := by
  native_decide
example : safe_onion_route 111 8080 99 [5, 6, 7] =
    safe_onion_route 222 8080 99 [5, 6, 7] := by native_decide
example : safe_onion_route 1 2 77 [99] = (99, 77) := by native_decide
example : safe_onion_route 1 2 5 [] = (1, 5) := by native_decide
example : safe_onion_route (-10) (-2) (-77) [-5, -9] = (-9, -77) := by
  native_decide
example : safe_onion_route 9 2 77 [9] = (9, 77) := by native_decide

#eval safe_onion_route 192168001 8080 42 [10, 20, 30]
#eval (safe_onion_route 111 8080 99 [5, 6, 7] ==
  safe_onion_route 222 8080 99 [5, 6, 7])
#eval safe_onion_route 1 2 5 []

/-- Every tuple of signed integers and every finite relay list is admissible. -/
def Pre (_src_ip _dst_ip _msg : Int) (_relays : List Int) : Prop := True

/-- Forwarding never changes the payload. -/
def message_prop (src dst msg : Int) (relays : List Int) : Prop :=
  (safe_onion_route src dst msg relays).2 = msg

/-- With no relays the destination sees the source itself. -/
def fallback_prop (src dst msg : Int) (relays : List Int) : Prop :=
  relays = [] → safe_onion_route src dst msg relays = (src, msg)

/-- With relays the destination sees exactly the last one. -/
def last_relay_prop (src dst msg : Int) (relays : List Int) : Prop :=
  ∀ h : relays ≠ [], safe_onion_route src dst msg relays = (relays.getLast h, msg)

/-- A single relay is itself the observed sender. -/
def singleton_prop (src dst msg relay : Int) : Prop :=
  safe_onion_route src dst msg [relay] = (relay, msg)

/-- Any two sources have the same destination observation on a nonempty chain. -/
def anonymity_prop (src dst msg : Int) (relays : List Int) : Prop :=
  relays ≠ [] → ∀ other_src : Int,
    safe_onion_route src dst msg relays = safe_onion_route other_src dst msg relays

/-- The destination parameter is not part of the returned observation. -/
def destination_independent_prop (src dst msg : Int) (relays : List Int) : Prop :=
  ∀ other_dst : Int,
    safe_onion_route src dst msg relays = safe_onion_route src other_dst msg relays

/-- On a nonempty route, the observed sender is a member of the relay chain. -/
def relay_member_prop (src dst msg : Int) (relays : List Int) : Prop :=
  relays ≠ [] → (safe_onion_route src dst msg relays).1 ∈ relays

/-- Numerical source exclusion, provided the source is not itself a relay. -/
def source_hidden_prop (src dst msg : Int) (relays : List Int) : Prop :=
  relays ≠ [] → src ∉ relays → (safe_onion_route src dst msg relays).1 ≠ src

theorem message_thm (src dst msg : Int) (relays : List Int) :
    message_prop src dst msg relays := by
  rfl

theorem fallback_thm (src dst msg : Int) (relays : List Int) :
    fallback_prop src dst msg relays := by
  intro h
  subst relays
  rfl

theorem last_relay_thm (src dst msg : Int) (relays : List Int) :
    last_relay_prop src dst msg relays := by
  intro h
  unfold safe_onion_route
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast h]
  rfl

theorem singleton_thm (src dst msg relay : Int) :
    singleton_prop src dst msg relay := by
  rfl

theorem anonymity_thm (src dst msg : Int) (relays : List Int) :
    anonymity_prop src dst msg relays := by
  intro h other_src
  exact (last_relay_thm src dst msg relays h).trans
    (last_relay_thm other_src dst msg relays h).symm

theorem destination_independent_thm (src dst msg : Int) (relays : List Int) :
    destination_independent_prop src dst msg relays := by
  intro other_dst
  rfl

theorem relay_member_thm (src dst msg : Int) (relays : List Int) :
    relay_member_prop src dst msg relays := by
  intro h
  rw [last_relay_thm src dst msg relays h]
  exact List.getLast_mem h

theorem source_hidden_thm (src dst msg : Int) (relays : List Int) :
    source_hidden_prop src dst msg relays := by
  intro h hnot heq
  apply hnot
  have hm := relay_member_thm src dst msg relays h
  rw [heq] at hm
  exact hm

/-- All observable guarantees, without excluding empty or repeated relay lists. -/
def Post_prop (src dst msg : Int) (relays : List Int) : Prop :=
  message_prop src dst msg relays ∧
  fallback_prop src dst msg relays ∧
  last_relay_prop src dst msg relays ∧
  (∀ relay : Int, singleton_prop src dst msg relay) ∧
  anonymity_prop src dst msg relays ∧
  destination_independent_prop src dst msg relays ∧
  relay_member_prop src dst msg relays ∧
  source_hidden_prop src dst msg relays

/-!
## Bounded property-based tests

The sample domain contains every signed integer from -2 through 2 and every
relay list of length at most three over those integers (156 lists). Thus it
includes empty chains, repeated addresses, source/relay collisions, and negative
addresses/messages. Each route checker visits 19,500 input tuples. The universal
other-source, other-destination, and singleton clauses are sampled over the same
five integers. These are executable counterparts of the propositions above;
the bounds apply only to testing, not to any theorem or precondition.
-/

def testInts : List Int := (List.range 5).map (fun n => (n : Int) - 2)

def chainsOfLength : Nat → List (List Int)
  | 0 => [[]]
  | n + 1 => testInts.flatMap (fun relay => (chainsOfLength n).map (relay :: ·))

def testRelays : List (List Int) := (List.range 4).flatMap chainsOfLength

def checkRoutes (p : Int → Int → Int → List Int → Bool) : Bool :=
  testInts.all fun src => testInts.all fun dst => testInts.all fun msg =>
    testRelays.all (p src dst msg)

-- Boolean counterpart of message_prop.
def message_check (src dst msg : Int) (relays : List Int) : Bool :=
  (safe_onion_route src dst msg relays).2 == msg

-- Boolean counterpart of fallback_prop.
def fallback_check (src dst msg : Int) (relays : List Int) : Bool :=
  !relays.isEmpty || safe_onion_route src dst msg relays == (src, msg)

-- Boolean counterpart of last_relay_prop. Reverse/head provides an independent
-- executable description of the last element; the empty-chain clause is vacuous.
def last_relay_check (src dst msg : Int) (relays : List Int) : Bool :=
  match relays.reverse with
  | [] => true
  | last :: _ => safe_onion_route src dst msg relays == (last, msg)

-- Boolean counterpart of singleton_prop.
def singleton_check (src dst msg relay : Int) : Bool :=
  safe_onion_route src dst msg [relay] == (relay, msg)

-- Bounded Boolean counterpart of the other-source quantifier in anonymity_prop.
def anonymity_check (src dst msg : Int) (relays : List Int) : Bool :=
  relays.isEmpty || testInts.all (fun other_src =>
    safe_onion_route src dst msg relays == safe_onion_route other_src dst msg relays)

-- Bounded Boolean counterpart of destination_independent_prop.
def destination_independent_check (src dst msg : Int) (relays : List Int) : Bool :=
  testInts.all (fun other_dst =>
    safe_onion_route src dst msg relays == safe_onion_route src other_dst msg relays)

-- Boolean counterpart of relay_member_prop.
def relay_member_check (src dst msg : Int) (relays : List Int) : Bool :=
  relays.isEmpty || relays.contains (safe_onion_route src dst msg relays).1

-- Boolean counterpart of source_hidden_prop, including both hypotheses.
def source_hidden_check (src dst msg : Int) (relays : List Int) : Bool :=
  relays.isEmpty || relays.contains src ||
    !((safe_onion_route src dst msg relays).1 == src)

-- One PBT for every property, not merely the fixed examples above.
example : checkRoutes message_check = true := by native_decide
example : checkRoutes fallback_check = true := by native_decide
example : checkRoutes last_relay_check = true := by native_decide
example : (testInts.all fun src => testInts.all fun dst => testInts.all fun msg =>
    testInts.all (singleton_check src dst msg)) = true := by native_decide
example : checkRoutes anonymity_check = true := by native_decide
example : checkRoutes destination_independent_check = true := by native_decide
example : checkRoutes relay_member_check = true := by native_decide
example : checkRoutes source_hidden_check = true := by native_decide

/-- Bounded executable conjunction corresponding to every clause of Post_prop. -/
def post_check (src dst msg : Int) (relays : List Int) : Bool :=
  message_check src dst msg relays &&
  fallback_check src dst msg relays &&
  last_relay_check src dst msg relays &&
  testInts.all (singleton_check src dst msg) &&
  anonymity_check src dst msg relays &&
  destination_independent_check src dst msg relays &&
  relay_member_check src dst msg relays &&
  source_hidden_check src dst msg relays

-- PBT for the full postcondition.
example : checkRoutes post_check = true := by native_decide
#eval (testInts.length, testRelays.length, checkRoutes post_check)

/-- All admissible inputs satisfy the entire observable specification. -/
theorem correctness_thm (src dst msg : Int) (relays : List Int) :
    Pre src dst msg relays → Post_prop src dst msg relays := by
  intro _
  exact ⟨message_thm src dst msg relays,
    fallback_thm src dst msg relays,
    last_relay_thm src dst msg relays,
    fun relay => singleton_thm src dst msg relay,
    anonymity_thm src dst msg relays,
    destination_independent_thm src dst msg relays,
    relay_member_thm src dst msg relays,
    source_hidden_thm src dst msg relays⟩

/-- Imperative forwarding: each hop replaces the sender seen at the next hop.
Starting with the source makes the zero-iteration case the direct fallback. -/
def safe_onion_route_imperative (src_ip _dst_ip msg : Int)
    (relays : List Int) : Int × Int := Id.run do
  let mut sender := src_ip
  for relay in relays do
    sender := relay
  return (sender, msg)

-- Imperative tests reproduce every branch of the Python checks.
example : safe_onion_route_imperative 192168001 8080 42 [10, 20, 30] =
    (30, 42) := by native_decide
example : (safe_onion_route_imperative 192168001 8080 42 [10, 20, 30]).1 ≠
    192168001 := by native_decide
example : safe_onion_route_imperative 111 8080 99 [5, 6, 7] =
    safe_onion_route_imperative 222 8080 99 [5, 6, 7] := by native_decide
example : safe_onion_route_imperative 1 2 77 [99] = (99, 77) := by native_decide
example : safe_onion_route_imperative 1 2 5 [] = (1, 5) := by native_decide
example : safe_onion_route_imperative (-10) (-2) (-77) [-5, -9] =
    (-9, -77) := by native_decide
#eval safe_onion_route_imperative 192168001 8080 42 [10, 20, 30]
#eval safe_onion_route_imperative 1 2 5 []

-- An additional bounded differential test, not a substitute for equivalence.
example : checkRoutes (fun src dst msg relays =>
    safe_onion_route src dst msg relays ==
      safe_onion_route_imperative src dst msg relays) = true := by native_decide

/-- Kernel-checked equivalence for all integers and all finite relay chains. -/
theorem functional_imperative_equiv_thm (src dst msg : Int) (relays : List Int) :
    safe_onion_route src dst msg relays =
      safe_onion_route_imperative src dst msg relays := by
  induction relays generalizing src with
  | nil => rfl
  | cons relay rest ih =>
    simp only [safe_onion_route, List.getLastD_cons] at *
    simpa [safe_onion_route_imperative, List.forIn_cons] using ih relay

end SafeOnionRoute
end Agent
