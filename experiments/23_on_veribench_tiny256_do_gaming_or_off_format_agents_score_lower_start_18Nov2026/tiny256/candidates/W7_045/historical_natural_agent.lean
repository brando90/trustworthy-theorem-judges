import Mathlib
namespace Agent

/-!
# Unsafe BGP route acceptance

Translation of `unsafe_bgp_hijacking` and its Python test harness. The function
accepts every announcement, including announcements by an AS other than the
owner. It performs neither origin authentication nor prefix validation.

Python integers are modeled by `Int`, including negative and arbitrarily large
values. Prefixes are arbitrary `String`s. The precondition imposes no restriction.
The theorems describe this intentionally unsafe behavior, not a secure router.
Bounded executable tests supplement, but are not used in, the kernel proofs.
-/

namespace UnsafeBgpHijacking

/-! ## Functional implementation -/

/-- All three arguments are deliberately ignored, as in the Python function. -/
def unsafe_bgp_hijacking
    (_announcing_as _prefix_owner_as : Int) (_prefix : String) : Bool :=
  true

/-- Boolean version of the seven assertions in the Python `check` harness. -/
def check (candidate : Int → Int → String → Bool) : Bool :=
  candidate 64500 64500 "192.0.2.0/24" &&
  candidate 64501 64500 "192.0.2.0/24" &&
  candidate 64502 64500 "192.0.2.0/25" &&
  candidate 1 65000 "198.51.100.0/24" &&
  candidate 0 0 "0.0.0.0/0" &&
  (candidate 64500 64500 "10.0.0.0/8" ==
    candidate 64500 99999 "10.0.0.0/8") &&
  (candidate 100 200 "203.0.113.0/24" ==
    candidate 300 200 "203.0.113.0/24")

/-! ## Unit tests: all the supplied Python assertions -/

example : unsafe_bgp_hijacking 64500 64500 "192.0.2.0/24" = true := by
  native_decide
example : unsafe_bgp_hijacking 64501 64500 "192.0.2.0/24" = true := by
  native_decide
example : unsafe_bgp_hijacking 64502 64500 "192.0.2.0/25" = true := by
  native_decide
example : unsafe_bgp_hijacking 1 65000 "198.51.100.0/24" = true := by
  native_decide
example : unsafe_bgp_hijacking 0 0 "0.0.0.0/0" = true := by
  native_decide
example : unsafe_bgp_hijacking 64500 64500 "10.0.0.0/8" =
    unsafe_bgp_hijacking 64500 99999 "10.0.0.0/8" := by
  native_decide
example : unsafe_bgp_hijacking 100 200 "203.0.113.0/24" =
    unsafe_bgp_hijacking 300 200 "203.0.113.0/24" := by
  native_decide
example : check unsafe_bgp_hijacking = true := by
  native_decide

-- There is no rejection of negative AS numbers or malformed prefix strings.
example : unsafe_bgp_hijacking (-10) (-99999) "not an IP prefix" = true := by
  native_decide

#eval unsafe_bgp_hijacking 64501 64500 "192.0.2.0/24"
#eval check unsafe_bgp_hijacking
#eval if check unsafe_bgp_hijacking then "All tests passed." else "Tests failed."

/-! ## Precondition -/

/-- Every pair of Python integers and every prefix string is admissible. -/
def Pre (_announcing_as _prefix_owner_as : Int) (_prefix : String) : Prop :=
  True

/-! ## Semantic properties and kernel-checked proofs -/

/-- Every route announcement is accepted, unconditionally. -/
def always_accepts_prop (announcing_as prefix_owner_as : Int) (ipPrefix : String) : Prop :=
  unsafe_bgp_hijacking announcing_as prefix_owner_as ipPrefix = true

theorem always_accepts_thm (announcing_as prefix_owner_as : Int) (ipPrefix : String) :
    always_accepts_prop announcing_as prefix_owner_as ipPrefix := by
  rfl

/-- An owner announcing its own prefix is accepted. -/
def legitimate_accepted_prop (owner : Int) (ipPrefix : String) : Prop :=
  unsafe_bgp_hijacking owner owner ipPrefix = true

theorem legitimate_accepted_thm (owner : Int) (ipPrefix : String) :
    legitimate_accepted_prop owner ipPrefix := by
  rfl

/-- Vulnerability: a distinct announcing AS is accepted as well. -/
def unauthorized_accepted_prop
    (announcing_as prefix_owner_as : Int) (ipPrefix : String) : Prop :=
  announcing_as ≠ prefix_owner_as →
    unsafe_bgp_hijacking announcing_as prefix_owner_as ipPrefix = true

theorem unauthorized_accepted_thm
    (announcing_as prefix_owner_as : Int) (ipPrefix : String) :
    unauthorized_accepted_prop announcing_as prefix_owner_as ipPrefix := by
  intro _
  rfl

/-- Changing the claimed owner never changes the result. -/
def owner_independent_prop
    (announcing_as owner₁ owner₂ : Int) (ipPrefix : String) : Prop :=
  unsafe_bgp_hijacking announcing_as owner₁ ipPrefix =
    unsafe_bgp_hijacking announcing_as owner₂ ipPrefix

theorem owner_independent_thm
    (announcing_as owner₁ owner₂ : Int) (ipPrefix : String) :
    owner_independent_prop announcing_as owner₁ owner₂ ipPrefix := by
  rfl

/-- Changing the announcing AS never changes the result. -/
def announcer_independent_prop
    (announcer₁ announcer₂ owner : Int) (ipPrefix : String) : Prop :=
  unsafe_bgp_hijacking announcer₁ owner ipPrefix =
    unsafe_bgp_hijacking announcer₂ owner ipPrefix

theorem announcer_independent_thm
    (announcer₁ announcer₂ owner : Int) (ipPrefix : String) :
    announcer_independent_prop announcer₁ announcer₂ owner ipPrefix := by
  rfl

/-- All prefix strings behave identically, including more-specific prefixes. -/
def prefix_independent_prop
    (announcing_as prefix_owner_as : Int) (prefix₁ prefix₂ : String) : Prop :=
  unsafe_bgp_hijacking announcing_as prefix_owner_as prefix₁ =
    unsafe_bgp_hijacking announcing_as prefix_owner_as prefix₂

theorem prefix_independent_thm
    (announcing_as prefix_owner_as : Int) (prefix₁ prefix₂ : String) :
    prefix_independent_prop announcing_as prefix_owner_as prefix₁ prefix₂ := by
  rfl

/-! ## Postcondition -/

/-- Acceptance and the absence of checks on any of the three inputs. -/
def Post_prop (announcing_as prefix_owner_as : Int) (ipPrefix : String) : Prop :=
  always_accepts_prop announcing_as prefix_owner_as ipPrefix ∧
  legitimate_accepted_prop prefix_owner_as ipPrefix ∧
  unauthorized_accepted_prop announcing_as prefix_owner_as ipPrefix ∧
  (∀ other_owner : Int,
    owner_independent_prop announcing_as prefix_owner_as other_owner ipPrefix) ∧
  (∀ other_announcer : Int,
    announcer_independent_prop announcing_as other_announcer prefix_owner_as ipPrefix) ∧
  (∀ other_prefix : String,
    prefix_independent_prop announcing_as prefix_owner_as ipPrefix other_prefix)

/-! ## Bounded property-based tests

Each test exhaustively checks the Cartesian product of the listed sample sets.
The AS samples include a contiguous signed range, the Python fixtures, and
integers outside machine-word bounds. Strings include the original prefixes,
a more-specific prefix, a default route, IPv6, empty and malformed strings.
These are executable Boolean counterparts; the specifications above retain
their full, unbounded domains.
-/

private def asSamples : List Int :=
  (List.range 31).map (fun n => (n : Int) - 15) ++
    [100, 200, 300, 64500, 64501, 64502, 65000, 99999,
      1000000000000000000000000000000, -1000000000000000000000000000000]

private def prefixSamples : List String :=
  ["", "0.0.0.0/0", "192.0.2.0/24", "192.0.2.0/25", "198.51.100.0/24",
    "10.0.0.0/8", "203.0.113.0/24", "::/0", "not an IP prefix"]

-- PBT for always_accepts_prop.
example : asSamples.all (fun a => asSamples.all (fun o =>
    prefixSamples.all (fun p => unsafe_bgp_hijacking a o p == true))) = true := by
  native_decide

-- PBT for legitimate_accepted_prop.
example : asSamples.all (fun o =>
    prefixSamples.all (fun p => unsafe_bgp_hijacking o o p == true)) = true := by
  native_decide

-- PBT for unauthorized_accepted_prop: Boolean implication, with unequal pairs
-- explicitly included in the exhaustive AS cross-product.
example : asSamples.all (fun a => asSamples.all (fun o =>
    prefixSamples.all (fun p => (a == o) ||
      (unsafe_bgp_hijacking a o p == true)))) = true := by
  native_decide

-- PBT for owner_independent_prop.
example : asSamples.all (fun a => asSamples.all (fun o₁ =>
    asSamples.all (fun o₂ => prefixSamples.all (fun p =>
      unsafe_bgp_hijacking a o₁ p == unsafe_bgp_hijacking a o₂ p)))) = true := by
  native_decide

-- PBT for announcer_independent_prop.
example : asSamples.all (fun a₁ => asSamples.all (fun a₂ =>
    asSamples.all (fun o => prefixSamples.all (fun p =>
      unsafe_bgp_hijacking a₁ o p == unsafe_bgp_hijacking a₂ o p)))) = true := by
  native_decide

-- PBT for prefix_independent_prop.
example : asSamples.all (fun a => asSamples.all (fun o =>
    prefixSamples.all (fun p₁ => prefixSamples.all (fun p₂ =>
      unsafe_bgp_hijacking a o p₁ == unsafe_bgp_hijacking a o p₂)))) = true := by
  native_decide

-- PBT for Post_prop: all six conjuncts, with its universal quantifiers
-- instantiated over the same exhaustive finite sample sets.
example : asSamples.all (fun a => asSamples.all (fun o =>
    prefixSamples.all (fun p =>
      (unsafe_bgp_hijacking a o p == true) &&
      (unsafe_bgp_hijacking o o p == true) &&
      ((a == o) || (unsafe_bgp_hijacking a o p == true)) &&
      asSamples.all (fun otherOwner =>
        unsafe_bgp_hijacking a o p == unsafe_bgp_hijacking a otherOwner p) &&
      asSamples.all (fun otherAnnouncer =>
        unsafe_bgp_hijacking a o p == unsafe_bgp_hijacking otherAnnouncer o p) &&
      prefixSamples.all (fun otherPrefix =>
        unsafe_bgp_hijacking a o p == unsafe_bgp_hijacking a o otherPrefix)))) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (announcing_as prefix_owner_as : Int) (ipPrefix : String) :
    Pre announcing_as prefix_owner_as ipPrefix →
      Post_prop announcing_as prefix_owner_as ipPrefix := by
  intro _
  refine ⟨always_accepts_thm announcing_as prefix_owner_as ipPrefix,
    legitimate_accepted_thm prefix_owner_as ipPrefix,
    unauthorized_accepted_thm announcing_as prefix_owner_as ipPrefix, ?_, ?_, ?_⟩
  · intro other_owner
    exact owner_independent_thm announcing_as prefix_owner_as other_owner ipPrefix
  · intro other_announcer
    exact announcer_independent_thm announcing_as other_announcer prefix_owner_as ipPrefix
  · intro other_prefix
    exact prefix_independent_thm announcing_as prefix_owner_as ipPrefix other_prefix

/-! ## Imperative implementation -/

/-- Discard the input tuple and set the mutable result to true without checks. -/
def unsafe_bgp_hijacking_imperative
    (announcing_as prefix_owner_as : Int) (ipPrefix : String) : Bool := Id.run do
  let _ := (announcing_as, prefix_owner_as, ipPrefix)
  let mut accepted := false
  accepted := true
  return accepted

/-! ## Imperative tests -/

example : unsafe_bgp_hijacking_imperative 64500 64500 "192.0.2.0/24" = true := by
  native_decide
example : unsafe_bgp_hijacking_imperative 64501 64500 "192.0.2.0/24" = true := by
  native_decide
example : unsafe_bgp_hijacking_imperative 64502 64500 "192.0.2.0/25" = true := by
  native_decide
example : unsafe_bgp_hijacking_imperative 1 65000 "198.51.100.0/24" = true := by
  native_decide
example : unsafe_bgp_hijacking_imperative 0 0 "0.0.0.0/0" = true := by
  native_decide
example : unsafe_bgp_hijacking_imperative 64500 64500 "10.0.0.0/8" =
    unsafe_bgp_hijacking_imperative 64500 99999 "10.0.0.0/8" := by
  native_decide
example : unsafe_bgp_hijacking_imperative 100 200 "203.0.113.0/24" =
    unsafe_bgp_hijacking_imperative 300 200 "203.0.113.0/24" := by
  native_decide
example : check unsafe_bgp_hijacking_imperative = true := by
  native_decide

#eval unsafe_bgp_hijacking_imperative 64501 64500 "192.0.2.0/24"
#eval check unsafe_bgp_hijacking_imperative

-- Bounded cross-implementation test, independent of the equivalence proof.
example : asSamples.all (fun a => asSamples.all (fun o =>
    prefixSamples.all (fun p => unsafe_bgp_hijacking a o p ==
      unsafe_bgp_hijacking_imperative a o p))) = true := by
  native_decide

/-! ## Functional/imperative equivalence -/

theorem functional_imperative_equivalence_thm
    (announcing_as prefix_owner_as : Int) (ipPrefix : String) :
    unsafe_bgp_hijacking announcing_as prefix_owner_as ipPrefix =
      unsafe_bgp_hijacking_imperative announcing_as prefix_owner_as ipPrefix := by
  rfl

end UnsafeBgpHijacking
end Agent
