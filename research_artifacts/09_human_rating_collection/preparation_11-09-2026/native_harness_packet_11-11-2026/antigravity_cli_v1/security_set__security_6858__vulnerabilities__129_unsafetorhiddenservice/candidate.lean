import Mathlib

/-!
# Unsafe Tor Hidden-Service Rendezvous

Formalization of the Python function `unsafe_tor_rendezvous`, illustrating the MIT 6.858
Fall 2012 Quiz 2 vulnerability where a Tor hidden service fails to authenticate or vet
the rendezvous point and unconditionally returns `True` (`true`), even when the
rendezvous point is controlled by a malicious adversary.
-/

namespace «129_unsafeTorHiddenService»

/-! ## 4. Implementation (Functional Definition) -/

/-- Returns `true` regardless of whether the rendezvous point is controlled by an adversary.

Vulnerability: a malicious Tor OR can set up a rendezvous point on itself and send its
address to the introduction point of a hidden service. When the hidden service connects,
the malicious node records the incoming connection's origin, deanonymizing the service.
The hidden service does not authenticate or vet the rendezvous point. -/
def unsafe_tor_rendezvous
    (_rendezvous_addr : Int) (_is_malicious : Bool) (_hidden_service_connects : Bool) : Bool :=
  true

/-! ## 5. Unit Tests -/

-- Test 1: honest rendezvous accepted (0x0A000001, False, True)
example : unsafe_tor_rendezvous 0x0A000001 false true = true := by native_decide
#eval unsafe_tor_rendezvous 0x0A000001 false true

-- Test 2: vuln: malicious rendezvous accepted (0xDEADBEEF, True, True)
example : unsafe_tor_rendezvous 0xDEADBEEF true true = true := by native_decide
#eval unsafe_tor_rendezvous 0xDEADBEEF true true

-- Test 3: vuln: no-connect malicious accepted (0x00000000, True, False)
example : unsafe_tor_rendezvous 0x00000000 true false = true := by native_decide
#eval unsafe_tor_rendezvous 0x00000000 true false

-- Test 4: localhost honest accepted (0x7F000001, False, False)
example : unsafe_tor_rendezvous 0x7F000001 false false = true := by native_decide
#eval unsafe_tor_rendezvous 0x7F000001 false false

-- Combined check mirroring Python `check()`
def check : Bool :=
  unsafe_tor_rendezvous 0x0A000001 false true == true &&
  unsafe_tor_rendezvous 0xDEADBEEF true true == true &&
  unsafe_tor_rendezvous 0x00000000 true false == true &&
  unsafe_tor_rendezvous 0x7F000001 false false == true

example : check = true := by native_decide
#eval check

/-! ## 6. Pre-condition Predicate -/

/-- Pre-condition for `unsafe_tor_rendezvous`: all integer addresses and boolean flags are admissible. -/
def Pre (_rendezvous_addr : Int) (_is_malicious : Bool) (_hidden_service_connects : Bool) : Prop :=
  True

/-! ## 7. Property Propositions and Theorems -/

/-- Property 1: `unsafe_tor_rendezvous` unconditionally returns `true` for all inputs. -/
def always_true_prop
    (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) : Prop :=
  unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects = true

theorem always_true_thm
    (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) :
    always_true_prop rendezvous_addr is_malicious hidden_service_connects := by
  rfl

/-- Property 2: Honest rendezvous points (`is_malicious = false`) are accepted. -/
def honest_accepted_prop
    (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) : Prop :=
  is_malicious = false →
    unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects = true

theorem honest_accepted_thm
    (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) :
    honest_accepted_prop rendezvous_addr is_malicious hidden_service_connects := by
  intro _
  rfl

/-- Property 3: Malicious rendezvous points (`is_malicious = true`) are also accepted
(the core vulnerability: lack of authentication of the rendezvous point). -/
def malicious_accepted_prop
    (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) : Prop :=
  is_malicious = true →
    unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects = true

theorem malicious_accepted_thm
    (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) :
    malicious_accepted_prop rendezvous_addr is_malicious hidden_service_connects := by
  intro _
  rfl

/-- Property 4: When the rendezvous point is malicious (`is_malicious = true`) and the hidden
service connects (`hidden_service_connects = true`), the rendezvous still succeeds, allowing
the malicious node to observe the incoming connection and deanonymize the hidden service. -/
def deanonymization_vuln_prop
    (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) : Prop :=
  (is_malicious = true ∧ hidden_service_connects = true) →
    unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects = true

theorem deanonymization_vuln_thm
    (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) :
    deanonymization_vuln_prop rendezvous_addr is_malicious hidden_service_connects := by
  intro _
  rfl

/-- Property 5: The rendezvous procedure does not distinguish between malicious and honest
rendezvous points (`is_malicious = true` vs `is_malicious = false`). -/
def unauthenticated_rendezvous_prop
    (rendezvous_addr : Int) (_is_malicious : Bool) (hidden_service_connects : Bool) : Prop :=
  unsafe_tor_rendezvous rendezvous_addr true hidden_service_connects =
    unsafe_tor_rendezvous rendezvous_addr false hidden_service_connects

theorem unauthenticated_rendezvous_thm
    (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) :
    unauthenticated_rendezvous_prop rendezvous_addr is_malicious hidden_service_connects := by
  rfl

/-- Property 6: The result is independent of whether the hidden service connects
(`hidden_service_connects = true` vs `hidden_service_connects = false`). -/
def connect_independent_prop
    (rendezvous_addr : Int) (is_malicious : Bool) (_hidden_service_connects : Bool) : Prop :=
  unsafe_tor_rendezvous rendezvous_addr is_malicious true =
    unsafe_tor_rendezvous rendezvous_addr is_malicious false

theorem connect_independent_thm
    (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) :
    connect_independent_prop rendezvous_addr is_malicious hidden_service_connects := by
  rfl

/-- Property 7: The hidden service does not vet the rendezvous address; any two addresses
produce the same result. -/
def address_independent_prop
    (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) : Prop :=
  ∀ other_addr : Int,
    unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects =
      unsafe_tor_rendezvous other_addr is_malicious hidden_service_connects

theorem address_independent_thm
    (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) :
    address_independent_prop rendezvous_addr is_malicious hidden_service_connects := by
  intro _
  rfl

/-! ## 8. Post-condition -/

/-- Post-condition for `unsafe_tor_rendezvous` as the conjunction of all semantic properties. -/
def Post_prop
    (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) : Prop :=
  always_true_prop rendezvous_addr is_malicious hidden_service_connects ∧
  honest_accepted_prop rendezvous_addr is_malicious hidden_service_connects ∧
  malicious_accepted_prop rendezvous_addr is_malicious hidden_service_connects ∧
  deanonymization_vuln_prop rendezvous_addr is_malicious hidden_service_connects ∧
  unauthenticated_rendezvous_prop rendezvous_addr is_malicious hidden_service_connects ∧
  connect_independent_prop rendezvous_addr is_malicious hidden_service_connects ∧
  address_independent_prop rendezvous_addr is_malicious hidden_service_connects

/-! ## 9. Property-Based Tests (PBTs) -/

-- PBT for `always_true_prop`
#eval Plausible.Testable.check
  (∀ (addr : Int) (mal conn : Bool),
    unsafe_tor_rendezvous addr mal conn = true)

example :
    (List.range 50).all (fun n =>
      let addr : Int := Int.ofNat n - 25
      [false, true].all (fun mal =>
        [false, true].all (fun conn =>
          unsafe_tor_rendezvous addr mal conn == true))) = true := by native_decide

-- PBT for `honest_accepted_prop`
#eval Plausible.Testable.check
  (∀ (addr : Int) (mal conn : Bool),
    ((mal != false) || unsafe_tor_rendezvous addr mal conn == true) = true)

example :
    (List.range 50).all (fun n =>
      let addr : Int := Int.ofNat n - 25
      [false, true].all (fun mal =>
        [false, true].all (fun conn =>
          (mal != false) || unsafe_tor_rendezvous addr mal conn == true))) = true := by native_decide

-- PBT for `malicious_accepted_prop`
#eval Plausible.Testable.check
  (∀ (addr : Int) (mal conn : Bool),
    ((mal != true) || unsafe_tor_rendezvous addr mal conn == true) = true)

example :
    (List.range 50).all (fun n =>
      let addr : Int := Int.ofNat n - 25
      [false, true].all (fun mal =>
        [false, true].all (fun conn =>
          (mal != true) || unsafe_tor_rendezvous addr mal conn == true))) = true := by native_decide

-- PBT for `deanonymization_vuln_prop`
#eval Plausible.Testable.check
  (∀ (addr : Int) (mal conn : Bool),
    ((!(mal && conn)) || unsafe_tor_rendezvous addr mal conn == true) = true)

example :
    (List.range 50).all (fun n =>
      let addr : Int := Int.ofNat n - 25
      [false, true].all (fun mal =>
        [false, true].all (fun conn =>
          (!(mal && conn)) || unsafe_tor_rendezvous addr mal conn == true))) = true := by native_decide

-- PBT for `unauthenticated_rendezvous_prop`
#eval Plausible.Testable.check
  (∀ (addr : Int) (conn : Bool),
    unsafe_tor_rendezvous addr true conn = unsafe_tor_rendezvous addr false conn)

example :
    (List.range 50).all (fun n =>
      let addr : Int := Int.ofNat n - 25
      [false, true].all (fun conn =>
        unsafe_tor_rendezvous addr true conn == unsafe_tor_rendezvous addr false conn)) = true := by
  native_decide

-- PBT for `connect_independent_prop`
#eval Plausible.Testable.check
  (∀ (addr : Int) (mal : Bool),
    unsafe_tor_rendezvous addr mal true = unsafe_tor_rendezvous addr mal false)

example :
    (List.range 50).all (fun n =>
      let addr : Int := Int.ofNat n - 25
      [false, true].all (fun mal =>
        unsafe_tor_rendezvous addr mal true == unsafe_tor_rendezvous addr mal false)) = true := by
  native_decide

-- PBT for `address_independent_prop`
#eval Plausible.Testable.check
  (∀ (addr1 addr2 : Int) (mal conn : Bool),
    unsafe_tor_rendezvous addr1 mal conn = unsafe_tor_rendezvous addr2 mal conn)

example :
    (List.range 20).all (fun n1 =>
      (List.range 20).all (fun n2 =>
        let addr1 : Int := Int.ofNat n1 - 10
        let addr2 : Int := Int.ofNat n2 - 10
        [false, true].all (fun mal =>
          [false, true].all (fun conn =>
            unsafe_tor_rendezvous addr1 mal conn == unsafe_tor_rendezvous addr2 mal conn)))) = true := by
  native_decide

-- PBT for `Post_prop` (executable Boolean form of the full post-condition)
#eval Plausible.Testable.check
  (∀ (addr other_addr : Int) (mal conn : Bool),
    (unsafe_tor_rendezvous addr mal conn == true &&
     ((!mal) || unsafe_tor_rendezvous addr mal conn == true) &&
     (mal || unsafe_tor_rendezvous addr mal conn == true) &&
     ((!(mal && conn)) || unsafe_tor_rendezvous addr mal conn == true) &&
     (unsafe_tor_rendezvous addr true conn == unsafe_tor_rendezvous addr false conn) &&
     (unsafe_tor_rendezvous addr mal true == unsafe_tor_rendezvous addr mal false) &&
     (unsafe_tor_rendezvous addr mal conn == unsafe_tor_rendezvous other_addr mal conn)) = true)

example :
    (List.range 20).all (fun n1 =>
      (List.range 20).all (fun n2 =>
        let addr : Int := Int.ofNat n1 - 10
        let other_addr : Int := Int.ofNat n2 - 10
        [false, true].all (fun mal =>
          [false, true].all (fun conn =>
            (unsafe_tor_rendezvous addr mal conn == true) &&
            ((mal != false) || (unsafe_tor_rendezvous addr mal conn == true)) &&
            ((mal != true) || (unsafe_tor_rendezvous addr mal conn == true)) &&
            ((!(mal && conn)) || (unsafe_tor_rendezvous addr mal conn == true)) &&
            (unsafe_tor_rendezvous addr true conn == unsafe_tor_rendezvous addr false conn) &&
            (unsafe_tor_rendezvous addr mal true == unsafe_tor_rendezvous addr mal false) &&
            (unsafe_tor_rendezvous addr mal conn == unsafe_tor_rendezvous other_addr mal conn))))) = true := by
  native_decide

/-! ## 10. Correctness Theorem (`Pre → Post`) -/

/-- Correctness theorem: under the pre-condition `Pre`, the post-condition `Post_prop` holds
for all inputs. -/
theorem unsafe_tor_rendezvous_correct
    (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool)
    (_hpre : Pre rendezvous_addr is_malicious hidden_service_connects) :
    Post_prop rendezvous_addr is_malicious hidden_service_connects := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact always_true_thm rendezvous_addr is_malicious hidden_service_connects
  · exact honest_accepted_thm rendezvous_addr is_malicious hidden_service_connects
  · exact malicious_accepted_thm rendezvous_addr is_malicious hidden_service_connects
  · exact deanonymization_vuln_thm rendezvous_addr is_malicious hidden_service_connects
  · exact unauthenticated_rendezvous_thm rendezvous_addr is_malicious hidden_service_connects
  · exact connect_independent_thm rendezvous_addr is_malicious hidden_service_connects
  · exact address_independent_thm rendezvous_addr is_malicious hidden_service_connects

/-! ## 11. Imperative Implementation -/

/-- Imperative implementation of `unsafe_tor_rendezvous` using `Id.run do` and mutable state. -/
def unsafe_tor_rendezvous_imp
    (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) : Bool :=
  Id.run do
    let mut result : Bool := false
    let _ := rendezvous_addr
    let _ := is_malicious
    let _ := hidden_service_connects
    result := true
    return result

/-! ## 12. Imperative Tests -/

example : unsafe_tor_rendezvous_imp 0x0A000001 false true = true := by native_decide
#eval unsafe_tor_rendezvous_imp 0x0A000001 false true

example : unsafe_tor_rendezvous_imp 0xDEADBEEF true true = true := by native_decide
#eval unsafe_tor_rendezvous_imp 0xDEADBEEF true true

example : unsafe_tor_rendezvous_imp 0x00000000 true false = true := by native_decide
#eval unsafe_tor_rendezvous_imp 0x00000000 true false

example : unsafe_tor_rendezvous_imp 0x7F000001 false false = true := by native_decide
#eval unsafe_tor_rendezvous_imp 0x7F000001 false false

#eval Plausible.Testable.check
  (∀ (addr : Int) (mal conn : Bool),
    unsafe_tor_rendezvous_imp addr mal conn = unsafe_tor_rendezvous addr mal conn)

/-! ## 13. Equivalence Theorem (Functional = Imperative) -/

/-- Pointwise equivalence between the functional and imperative implementations. -/
theorem unsafe_tor_rendezvous_equiv
    (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) :
    unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects =
      unsafe_tor_rendezvous_imp rendezvous_addr is_malicious hidden_service_connects := by
  rfl

/-- Extensional equivalence between the functional and imperative implementations. -/
theorem unsafe_tor_rendezvous_eq_imp :
    unsafe_tor_rendezvous = unsafe_tor_rendezvous_imp := by
  funext rendezvous_addr is_malicious hidden_service_connects
  rfl

end «129_unsafeTorHiddenService»
