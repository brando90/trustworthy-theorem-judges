import Mathlib
namespace Agent

/-!
# Unsafe scope of any trusted root CA

This file translates `unsafe_any_root_ca_scope` and the six assertions in its
Python `check`. Python integers are modelled by `Int`, including negative IDs.
Trust stores are lists: ordering and duplicate entries do not change membership.
There is no restriction on the requested domain, CA ID, or trust store.

The implementation deliberately reproduces the vulnerability, rather than
repairing it: membership in the trust store is the entire authorization test.
In particular, a trusted CA is accepted for *every* domain. This models the
weakest-CA problem from MIT 6.858 Lecture 15, not cryptographic verification.
The final implementation performs a mutable-state scan of the trust store.
-/

namespace UnsafeAnyRootCaScope

/-! ## Functional implementation and the Python unit tests -/

def unsafe_any_root_ca_scope (_requested_domain : Int) (ca_id : Int)
    (trusted_ca_ids : List Int) : Bool :=
  decide (ca_id ∈ trusted_ca_ids)

/-- Boolean counterpart of the Python test harness. -/
def check (candidate : Int → Int → List Int → Bool) : Bool :=
  candidate 1 99 [99] &&
  !(candidate 1 99 [1, 2]) &&
  candidate 1 5 [5] &&
  candidate 999 5 [5] &&
  candidate 0 0 [0] &&
  !(candidate 0 0 [])

example : unsafe_any_root_ca_scope 1 99 [99] = true := by native_decide
example : unsafe_any_root_ca_scope 1 99 [1, 2] = false := by native_decide
example : unsafe_any_root_ca_scope 1 5 [5] = true := by native_decide
example : unsafe_any_root_ca_scope 999 5 [5] = true := by native_decide
example : unsafe_any_root_ca_scope 0 0 [0] = true := by native_decide
example : unsafe_any_root_ca_scope 0 0 [] = false := by native_decide
example : check unsafe_any_root_ca_scope = true := by native_decide
-- Additional coverage for signed Python integers and duplicate trust entries.
example : unsafe_any_root_ca_scope (-999) (-5) [3, -5, -5] = true := by
  native_decide

#eval check unsafe_any_root_ca_scope
#eval if check unsafe_any_root_ca_scope then "All tests passed." else "Test failure."

/-! ## Preconditions, semantic properties, and kernel-checked proofs -/

/-- All well-typed Python inputs are admissible; no positivity or scope assumption. -/
def Pre (_requested_domain _ca_id : Int) (_trusted_ca_ids : List Int) : Prop :=
  True

/-- Acceptance is exactly membership in the list of trusted CAs. -/
def trusted_iff_prop (domain ca : Int) (trusted : List Int) : Prop :=
  unsafe_any_root_ca_scope domain ca trusted = true ↔ ca ∈ trusted

theorem trusted_iff_thm (domain ca : Int) (trusted : List Int) :
    trusted_iff_prop domain ca trusted := by
  simp [trusted_iff_prop, unsafe_any_root_ca_scope]

/-- Rejection is exactly absence from the list, independent of the domain. -/
def untrusted_iff_prop (domain ca : Int) (trusted : List Int) : Prop :=
  unsafe_any_root_ca_scope domain ca trusted = false ↔ ca ∉ trusted

theorem untrusted_iff_thm (domain ca : Int) (trusted : List Int) :
    untrusted_iff_prop domain ca trusted := by
  simp [untrusted_iff_prop, unsafe_any_root_ca_scope]

/-- Changing only the requested domain never changes the result. -/
def domain_irrelevance_prop (domain otherDomain ca : Int)
    (trusted : List Int) : Prop :=
  unsafe_any_root_ca_scope domain ca trusted =
    unsafe_any_root_ca_scope otherDomain ca trusted

theorem domain_irrelevance_thm (domain otherDomain ca : Int)
    (trusted : List Int) : domain_irrelevance_prop domain otherDomain ca trusted := by
  rfl

/-- With no trusted root, every request is rejected, including CA zero. -/
def empty_trust_prop (domain ca : Int) : Prop :=
  unsafe_any_root_ca_scope domain ca [] = false

theorem empty_trust_thm (domain ca : Int) : empty_trust_prop domain ca := by
  simp [empty_trust_prop, unsafe_any_root_ca_scope]

/-- A singleton store trusts exactly its one root, not a domain-specific root. -/
def singleton_trust_prop (domain ca root : Int) : Prop :=
  unsafe_any_root_ca_scope domain ca [root] = decide (ca = root)

theorem singleton_trust_thm (domain ca root : Int) :
    singleton_trust_prop domain ca root := by
  simp [singleton_trust_prop, unsafe_any_root_ca_scope]

/-- Either part of an enlarged trust store can authorize the CA. -/
def trust_extension_prop (domain ca : Int) (trusted extra : List Int) : Prop :=
  unsafe_any_root_ca_scope domain ca (trusted ++ extra) =
    (unsafe_any_root_ca_scope domain ca trusted ||
      unsafe_any_root_ca_scope domain ca extra)

theorem trust_extension_thm (domain ca : Int) (trusted extra : List Int) :
    trust_extension_prop domain ca trusted extra := by
  simp [trust_extension_prop, unsafe_any_root_ca_scope, List.mem_append]

/-- The vulnerability: one trusted CA can authorize every integer domain. -/
def trusted_ca_unrestricted_prop (ca : Int) (trusted : List Int) : Prop :=
  ca ∈ trusted → ∀ domain : Int, unsafe_any_root_ca_scope domain ca trusted = true

theorem trusted_ca_unrestricted_thm (ca : Int) (trusted : List Int) :
    trusted_ca_unrestricted_prop ca trusted := by
  intro h domain
  simp [unsafe_any_root_ca_scope, h]

/-! ## Postcondition -/

/-- The full behavioral specification, including all alternate domains/stores. -/
def Post_prop (domain ca : Int) (trusted : List Int) : Prop :=
  trusted_iff_prop domain ca trusted ∧
  untrusted_iff_prop domain ca trusted ∧
  (∀ otherDomain : Int, domain_irrelevance_prop domain otherDomain ca trusted) ∧
  empty_trust_prop domain ca ∧
  (∀ root : Int, singleton_trust_prop domain ca root) ∧
  (∀ extra : List Int, trust_extension_prop domain ca trusted extra) ∧
  trusted_ca_unrestricted_prop ca trusted

/-! ## Property-based tests

These are evidence over executable Boolean counterparts, not proofs of the
universal theorems. The bounded tests include negative IDs, the Python examples,
duplicates, empty lists, and all lists of length at most two over five small IDs.
For universal conjuncts of `Post_prop`, the bounded test checks each quantified
argument against the corresponding sample set; the theorem below is unbounded.
-/

private def sampleInts : List Int := [-2, -1, 0, 1, 2, 5, 99, 999]

private def sampleTrustStores : List (List Int) :=
  let ids : List Int := [-2, -1, 0, 1, 2]
  [[]] ++ ids.map (fun x => [x]) ++
    ids.flatMap (fun x => ids.map (fun y => [x, y])) ++
    [[99], [5], [5, 5], [99, 1, 99], [-5, 0, -5]]

-- PBT for trusted_iff_prop: Bool equality is the executable form of the iff.
example : sampleInts.all (fun domain => sampleInts.all (fun ca =>
    sampleTrustStores.all (fun trusted =>
      unsafe_any_root_ca_scope domain ca trusted == decide (ca ∈ trusted)))) =
    true := by native_decide

-- PBT for untrusted_iff_prop.
example : sampleInts.all (fun domain => sampleInts.all (fun ca =>
    sampleTrustStores.all (fun trusted =>
      (!unsafe_any_root_ca_scope domain ca trusted) == decide (ca ∉ trusted)))) =
    true := by native_decide

-- PBT for domain_irrelevance_prop.
example : sampleInts.all (fun domain => sampleInts.all (fun otherDomain =>
    sampleInts.all (fun ca => sampleTrustStores.all (fun trusted =>
      unsafe_any_root_ca_scope domain ca trusted ==
        unsafe_any_root_ca_scope otherDomain ca trusted)))) = true := by
  native_decide

-- PBT for empty_trust_prop.
example : sampleInts.all (fun domain => sampleInts.all (fun ca =>
    !unsafe_any_root_ca_scope domain ca [])) = true := by native_decide

-- PBT for singleton_trust_prop.
example : sampleInts.all (fun domain => sampleInts.all (fun ca =>
    sampleInts.all (fun root =>
      unsafe_any_root_ca_scope domain ca [root] == decide (ca = root)))) =
    true := by native_decide

-- PBT for trust_extension_prop (the complete truth table, not just monotonicity).
example : sampleInts.all (fun domain => sampleInts.all (fun ca =>
    sampleTrustStores.all (fun trusted => sampleTrustStores.all (fun extra =>
      unsafe_any_root_ca_scope domain ca (trusted ++ extra) ==
        (unsafe_any_root_ca_scope domain ca trusted ||
          unsafe_any_root_ca_scope domain ca extra))))) = true := by native_decide

-- PBT for trusted_ca_unrestricted_prop: implication as Boolean disjunction.
example : sampleInts.all (fun ca => sampleTrustStores.all (fun trusted =>
    !(decide (ca ∈ trusted)) || sampleInts.all (fun domain =>
      unsafe_any_root_ca_scope domain ca trusted))) = true := by native_decide

-- PBT for the full Post_prop conjunction, including its universal conjuncts.
example : sampleInts.all (fun domain => sampleInts.all (fun ca =>
    sampleTrustStores.all (fun trusted =>
      (unsafe_any_root_ca_scope domain ca trusted == decide (ca ∈ trusted)) &&
      ((!unsafe_any_root_ca_scope domain ca trusted) == decide (ca ∉ trusted)) &&
      sampleInts.all (fun otherDomain =>
        unsafe_any_root_ca_scope domain ca trusted ==
          unsafe_any_root_ca_scope otherDomain ca trusted) &&
      (!unsafe_any_root_ca_scope domain ca []) &&
      sampleInts.all (fun root =>
        unsafe_any_root_ca_scope domain ca [root] == decide (ca = root)) &&
      sampleTrustStores.all (fun extra =>
        unsafe_any_root_ca_scope domain ca (trusted ++ extra) ==
          (unsafe_any_root_ca_scope domain ca trusted ||
            unsafe_any_root_ca_scope domain ca extra)) &&
      (!(decide (ca ∈ trusted)) || sampleInts.all (fun otherDomain =>
        unsafe_any_root_ca_scope otherDomain ca trusted))))) = true := by
  native_decide

-- Additional randomized checks on arbitrary signed IDs and arbitrary lists.
#eval Plausible.Testable.check (∀ domain ca : Int, ∀ trusted : List Int,
  unsafe_any_root_ca_scope domain ca trusted = decide (ca ∈ trusted))

#eval Plausible.Testable.check (∀ domain otherDomain ca : Int,
  ∀ trusted : List Int, unsafe_any_root_ca_scope domain ca trusted =
    unsafe_any_root_ca_scope otherDomain ca trusted)

/-! ## Total functional correctness -/

theorem correctness_thm (domain ca : Int) (trusted : List Int) :
    Pre domain ca trusted → Post_prop domain ca trusted := by
  intro _
  exact ⟨trusted_iff_thm domain ca trusted,
    untrusted_iff_thm domain ca trusted,
    fun otherDomain => domain_irrelevance_thm domain otherDomain ca trusted,
    empty_trust_thm domain ca,
    fun root => singleton_trust_thm domain ca root,
    fun extra => trust_extension_thm domain ca trusted extra,
    trusted_ca_unrestricted_thm ca trusted⟩

/-! ## Imperative implementation -/

/-- Scan every entry, keeping a mutable flag once a matching CA is encountered. -/
def unsafe_any_root_ca_scope_imp (_requested_domain : Int) (ca_id : Int)
    (trusted_ca_ids : List Int) : Bool := Id.run do
  let mut accepted := false
  for root in trusted_ca_ids do
    accepted := accepted || decide (ca_id = root)
  return accepted

/-! ## Imperative tests -/

example : unsafe_any_root_ca_scope_imp 1 99 [99] = true := by native_decide
example : unsafe_any_root_ca_scope_imp 1 99 [1, 2] = false := by native_decide
example : unsafe_any_root_ca_scope_imp 1 5 [5] = true := by native_decide
example : unsafe_any_root_ca_scope_imp 999 5 [5] = true := by native_decide
example : unsafe_any_root_ca_scope_imp 0 0 [0] = true := by native_decide
example : unsafe_any_root_ca_scope_imp 0 0 [] = false := by native_decide
example : check unsafe_any_root_ca_scope_imp = true := by native_decide
example : unsafe_any_root_ca_scope_imp (-999) (-5) [3, -5, -5] = true := by
  native_decide

#eval check unsafe_any_root_ca_scope_imp

-- Bounded cross-check of both implementations, in addition to the proof below.
example : sampleInts.all (fun domain => sampleInts.all (fun ca =>
    sampleTrustStores.all (fun trusted =>
      unsafe_any_root_ca_scope domain ca trusted ==
        unsafe_any_root_ca_scope_imp domain ca trusted))) = true := by native_decide

/-! ## Functional-imperative equivalence -/

private theorem scan_invariant (ca : Int) (xs : List Int) (found : Bool) :
    xs.foldl (fun state root => state || decide (ca = root)) found =
      (found || decide (ca ∈ xs)) := by
  induction xs generalizing found with
  | nil => simp
  | cons root rest ih =>
    simp [List.foldl_cons, ih, List.mem_cons, Bool.or_assoc]

theorem functional_imperative_equivalence_thm (domain ca : Int)
    (trusted : List Int) :
    unsafe_any_root_ca_scope domain ca trusted =
      unsafe_any_root_ca_scope_imp domain ca trusted := by
  simp [unsafe_any_root_ca_scope, unsafe_any_root_ca_scope_imp,
    List.forIn_pure_yield_eq_foldl, scan_invariant]

end UnsafeAnyRootCaScope
end Agent
