import Mathlib
namespace Agent

/-!
# Unsafe database query whitelist check

Translation of the Python `unsafe_query_check` and its `check` routine.
Service and query identifiers are arbitrary integers; a whitelist is a list of
(service identifier, query type) pairs. The function always returns `true`.
In particular, this deliberately preserves the vulnerability: membership is
never checked, and requests absent from the whitelist are accepted.

The precondition imposes no restrictions, including on negative identifiers,
empty lists, or duplicate entries. The functional and mutable implementations
have the same behavior. Executable tests are kept separate from the universally
quantified, kernel-checked proofs.
-/

namespace UnsafeQueryWhitelist

abbrev Whitelist := List (Int × Int)

/-- The unsafe proxy ignores every argument, just as the Python function does. -/
def unsafe_query_check (_service_id _query_type : Int)
    (_whitelist : Whitelist) : Bool :=
  true

/-! ## Fixed unit tests and the Python check routine -/

example : unsafe_query_check 1 10 [(1, 10), (2, 20)] = true := by
  native_decide

example : unsafe_query_check 3 99 [(1, 10), (2, 20)] = true := by
  native_decide

example : unsafe_query_check 0 0 [] = true := by
  native_decide

-- Explicitly exhibit the unauthorized request in the original test.
example : (3, 99) ∉ ([(1, 10), (2, 20)] : Whitelist) ∧
    unsafe_query_check 3 99 [(1, 10), (2, 20)] = true := by
  native_decide

example : unsafe_query_check (-7) (-100) [(-7, 10), (-7, 10)] = true := by
  native_decide

#eval unsafe_query_check 1 10 [(1, 10), (2, 20)]
#eval unsafe_query_check 3 99 [(1, 10), (2, 20)]
#eval unsafe_query_check 0 0 []

/-- Execute the three Python assertions, retaining their failure messages. -/
def check : IO Unit := do
  let wl : Whitelist := [(1, 10), (2, 20)]
  unless unsafe_query_check 1 10 wl do
    throw (IO.userError "normal case failed")
  unless unsafe_query_check 3 99 wl do
    throw (IO.userError "vuln: unauthorized query accepted")
  unless unsafe_query_check 0 0 [] do
    throw (IO.userError "vuln: empty whitelist ignored")
  IO.println "All tests passed."

#eval check

/-! ## Preconditions and behavioral properties -/

/-- All integer identifiers and all whitelists are admissible. -/
def Pre (_service_id _query_type : Int) (_whitelist : Whitelist) : Prop :=
  True

/-- Every invocation returns the Boolean `true`. -/
def always_accepts_prop (service_id query_type : Int)
    (whitelist : Whitelist) : Prop :=
  unsafe_query_check service_id query_type whitelist = true

theorem always_accepts_thm (service_id query_type : Int)
    (whitelist : Whitelist) :
    always_accepts_prop service_id query_type whitelist := by
  rfl

/-- Whitelisted requests are accepted (the ordinary use case). -/
def authorized_accepts_prop (service_id query_type : Int)
    (whitelist : Whitelist) : Prop :=
  (service_id, query_type) ∈ whitelist →
    unsafe_query_check service_id query_type whitelist = true

theorem authorized_accepts_thm (service_id query_type : Int)
    (whitelist : Whitelist) :
    authorized_accepts_prop service_id query_type whitelist := by
  intro _membership
  rfl

/-- Non-whitelisted requests are also accepted: authorization is not enforced. -/
def unauthorized_accepts_prop (service_id query_type : Int)
    (whitelist : Whitelist) : Prop :=
  (service_id, query_type) ∉ whitelist →
    unsafe_query_check service_id query_type whitelist = true

theorem unauthorized_accepts_thm (service_id query_type : Int)
    (whitelist : Whitelist) :
    unauthorized_accepts_prop service_id query_type whitelist := by
  intro _nonmembership
  rfl

/-- An empty whitelist does not deny any request. -/
def empty_whitelist_ignored_prop (service_id query_type : Int) : Prop :=
  unsafe_query_check service_id query_type [] = true

theorem empty_whitelist_ignored_thm (service_id query_type : Int) :
    empty_whitelist_ignored_prop service_id query_type := by
  rfl

/-- Replacing the whitelist by any other list cannot affect the result. -/
def whitelist_independent_prop (service_id query_type : Int)
    (whitelist : Whitelist) : Prop :=
  ∀ other_whitelist : Whitelist,
    unsafe_query_check service_id query_type whitelist =
      unsafe_query_check service_id query_type other_whitelist

theorem whitelist_independent_thm (service_id query_type : Int)
    (whitelist : Whitelist) :
    whitelist_independent_prop service_id query_type whitelist := by
  intro _other_whitelist
  rfl

/-- Neither service identity nor query type has any influence on acceptance. -/
def request_independent_prop (service_id query_type : Int)
    (whitelist : Whitelist) : Prop :=
  ∀ other_service other_query : Int,
    unsafe_query_check service_id query_type whitelist =
      unsafe_query_check other_service other_query whitelist

theorem request_independent_thm (service_id query_type : Int)
    (whitelist : Whitelist) :
    request_independent_prop service_id query_type whitelist := by
  intro _other_service _other_query
  rfl

/-! ## Postcondition -/

def Post_prop (service_id query_type : Int) (whitelist : Whitelist) : Prop :=
  always_accepts_prop service_id query_type whitelist ∧
  authorized_accepts_prop service_id query_type whitelist ∧
  unauthorized_accepts_prop service_id query_type whitelist ∧
  empty_whitelist_ignored_prop service_id query_type ∧
  whitelist_independent_prop service_id query_type whitelist ∧
  request_independent_prop service_id query_type whitelist

/-! ## Property-based tests

The bounded tests below check executable Boolean forms, not proofs of the
property definitions. They cover positive, zero and negative identifiers,
empty, singleton and multi-entry whitelists, and duplicate entries. Every
sampled request also occurs as a singleton whitelist, so the authorized test
has non-vacuous cases; the empty whitelist supplies non-vacuous unauthorized
cases. The universal theorem domains remain unrestricted.
-/

def pbtIdentifiers : List Int := [-3, -1, 0, 1, 2, 3, 10, 20, 99]

def pbtRequests : List (Int × Int) :=
  pbtIdentifiers.flatMap fun service_id =>
    pbtIdentifiers.map fun query_type => (service_id, query_type)

def pbtWhitelists : List Whitelist :=
  [[], [(1, 10), (2, 20)], [(1, 10), (1, 10)], [(-3, -1), (0, 0)]] ++
    pbtRequests.map (fun request => [request])

-- PBT: always_accepts_prop.
example : pbtRequests.all (fun r =>
    pbtWhitelists.all (fun wl => unsafe_query_check r.1 r.2 wl == true)) = true := by
  native_decide

-- Randomized coverage of arbitrary integer inputs and lists of pairs as well.
#eval Plausible.Testable.check
  (∀ service_id query_type : Int, ∀ whitelist : List (Int × Int),
    unsafe_query_check service_id query_type whitelist = true)

-- PBT: authorized_accepts_prop; Boolean implication is (!premise || conclusion).
example : pbtRequests.all (fun r =>
    pbtWhitelists.all (fun wl =>
      (!(wl.contains r)) || (unsafe_query_check r.1 r.2 wl == true))) = true := by
  native_decide

-- PBT: unauthorized_accepts_prop; premise is nonmembership.
example : pbtRequests.all (fun r =>
    pbtWhitelists.all (fun wl =>
      wl.contains r || (unsafe_query_check r.1 r.2 wl == true))) = true := by
  native_decide

-- PBT: empty_whitelist_ignored_prop.
example : pbtRequests.all (fun r =>
    unsafe_query_check r.1 r.2 [] == true) = true := by
  native_decide

-- PBT: whitelist_independent_prop, comparing every pair of sampled whitelists.
example : pbtRequests.all (fun r =>
    pbtWhitelists.all (fun wl =>
      pbtWhitelists.all (fun other =>
        unsafe_query_check r.1 r.2 wl ==
          unsafe_query_check r.1 r.2 other))) = true := by
  native_decide

-- PBT: request_independent_prop, comparing every pair of sampled requests.
example : pbtRequests.all (fun r =>
    pbtWhitelists.all (fun wl =>
      pbtRequests.all (fun other =>
        unsafe_query_check r.1 r.2 wl ==
          unsafe_query_check other.1 other.2 wl))) = true := by
  native_decide

-- PBT: Post_prop, checking the conjunction of all six executable properties.
example : pbtRequests.all (fun r =>
    pbtWhitelists.all (fun wl =>
      let result := unsafe_query_check r.1 r.2 wl
      (result == true) &&
      (!(wl.contains r) || (result == true)) &&
      (wl.contains r || (result == true)) &&
      (unsafe_query_check r.1 r.2 [] == true) &&
      (pbtWhitelists.all (fun other =>
        result == unsafe_query_check r.1 r.2 other)) &&
      (pbtRequests.all (fun other =>
        result == unsafe_query_check other.1 other.2 wl)))) = true := by
  native_decide

/-! ## Correctness: the specification preserves the unsafe behavior -/

theorem correctness_thm (service_id query_type : Int) (whitelist : Whitelist) :
    Pre service_id query_type whitelist → Post_prop service_id query_type whitelist := by
  intro _pre
  exact ⟨always_accepts_thm service_id query_type whitelist,
    authorized_accepts_thm service_id query_type whitelist,
    unauthorized_accepts_thm service_id query_type whitelist,
    empty_whitelist_ignored_thm service_id query_type,
    whitelist_independent_thm service_id query_type whitelist,
    request_independent_thm service_id query_type whitelist⟩

/-! ## Imperative implementation and tests -/

/-- Mutable-state version, still performing no whitelist validation. -/
def unsafe_query_check_imperative (_service_id _query_type : Int)
    (_whitelist : Whitelist) : Bool := Id.run do
  let mut accepted := false
  accepted := true
  return accepted

example : unsafe_query_check_imperative 1 10 [(1, 10), (2, 20)] = true := by
  native_decide

example : unsafe_query_check_imperative 3 99 [(1, 10), (2, 20)] = true := by
  native_decide

example : unsafe_query_check_imperative 0 0 [] = true := by
  native_decide

#eval unsafe_query_check_imperative 1 10 [(1, 10), (2, 20)]
#eval unsafe_query_check_imperative 3 99 [(1, 10), (2, 20)]
#eval unsafe_query_check_imperative 0 0 []

/-! ## Functional / imperative equivalence -/

theorem functional_imperative_equivalence_thm (service_id query_type : Int)
    (whitelist : Whitelist) :
    unsafe_query_check service_id query_type whitelist =
      unsafe_query_check_imperative service_id query_type whitelist := by
  rfl

end UnsafeQueryWhitelist
end Agent
