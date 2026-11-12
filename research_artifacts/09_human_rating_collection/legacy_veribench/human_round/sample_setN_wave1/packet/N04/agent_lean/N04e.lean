import Mathlib

/-!
# Unsafe Tor Hidden-Service Rendezvous

Formalization of `unsafe_tor_rendezvous`, modeling the MIT 6.858 Fall 2012 Quiz 2
vulnerability in which a Tor hidden service fails to authenticate or vet the
rendezvous point, returning `true` regardless of whether the rendezvous point
is controlled by an adversary.
-/

namespace «129_unsafeTorHiddenService»

set_option linter.unusedVariables false

/-! ## 1. Functional Implementation -/

/--
Returns `true` regardless of whether the rendezvous point is controlled by an adversary.

Vulnerability: a malicious Tor OR can set up a rendezvous point on itself and send its
address to the introduction point of a hidden service. When the hidden service connects,
the malicious node records the incoming connection's origin, deanonymizing the service.
The hidden service does not authenticate or vet the rendezvous point.

MIT 6.858 Fall 2012 Quiz 2: Tor hidden service deanonymized via malicious rendezvous point.
-/
def unsafe_tor_rendezvous (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) : Bool :=
  true

/-! ## 2. Unit Tests -/

-- Honest rendezvous accepted
example : unsafe_tor_rendezvous 0x0A000001 false true = true := by native_decide

-- Vulnerability: malicious rendezvous accepted when hidden service connects
example : unsafe_tor_rendezvous 0xDEADBEEF true true = true := by native_decide

-- Vulnerability: no-connect malicious rendezvous accepted
example : unsafe_tor_rendezvous 0x00000000 true false = true := by native_decide

-- Localhost honest rendezvous accepted
example : unsafe_tor_rendezvous 0x7F000001 false false = true := by native_decide

#eval unsafe_tor_rendezvous 0x0A000001 false true
#eval unsafe_tor_rendezvous 0xDEADBEEF true true
#eval unsafe_tor_rendezvous 0x00000000 true false
#eval unsafe_tor_rendezvous 0x7F000001 false false

/-! ## 3. Pre-condition -/

/-- Pre-condition for `unsafe_tor_rendezvous`: all integer addresses and boolean flags are admissible. -/
def Pre (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) : Prop :=
  True

/-! ## 4. Properties and Theorems -/

/-- Property 1: The function unconditionally returns `true` for any inputs. -/
def always_true_prop (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) : Prop :=
  unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects = true

theorem always_true_thm (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) :
    always_true_prop rendezvous_addr is_malicious hidden_service_connects := by
  rfl

/-- Property 2 (Vulnerability): Even when the rendezvous point is controlled by an adversary (`is_malicious = true`), it is accepted (`true`). -/
def accepts_malicious_prop (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) : Prop :=
  is_malicious = true → unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects = true

theorem accepts_malicious_thm (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) :
    accepts_malicious_prop rendezvous_addr is_malicious hidden_service_connects := by
  intro _
  rfl

/-- Property 3 (Deanonymization scenario): When a malicious OR sets up a rendezvous point and the hidden service connects, the rendezvous is accepted. -/
def deanonymization_vuln_prop (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) : Prop :=
  (is_malicious = true ∧ hidden_service_connects = true) →
    unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects = true

theorem deanonymization_vuln_thm (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) :
    deanonymization_vuln_prop rendezvous_addr is_malicious hidden_service_connects := by
  intro _
  rfl

/-- Property 4: Honest rendezvous points (`is_malicious = false`) are accepted. -/
def accepts_honest_prop (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) : Prop :=
  is_malicious = false → unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects = true

theorem accepts_honest_thm (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) :
    accepts_honest_prop rendezvous_addr is_malicious hidden_service_connects := by
  intro _
  rfl

/-- Property 5 (No authentication of adversary status): The result does not distinguish malicious from honest rendezvous points. -/
def unauthenticated_malicious_invariant_prop (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) : Prop :=
  unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects =
    unsafe_tor_rendezvous rendezvous_addr (!is_malicious) hidden_service_connects

theorem unauthenticated_malicious_invariant_thm (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) :
    unauthenticated_malicious_invariant_prop rendezvous_addr is_malicious hidden_service_connects := by
  rfl

/-- Property 6 (Connection flag ignored): The result is invariant under flipping `hidden_service_connects`. -/
def connection_flag_invariant_prop (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) : Prop :=
  unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects =
    unsafe_tor_rendezvous rendezvous_addr is_malicious (!hidden_service_connects)

theorem connection_flag_invariant_thm (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) :
    connection_flag_invariant_prop rendezvous_addr is_malicious hidden_service_connects := by
  rfl

/-- Property 7 (Address not vetted): The result is independent of `rendezvous_addr`. -/
def unvetted_address_invariant_prop (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) : Prop :=
  ∀ (other_addr : Int),
    unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects =
      unsafe_tor_rendezvous other_addr is_malicious hidden_service_connects

theorem unvetted_address_invariant_thm (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) :
    unvetted_address_invariant_prop rendezvous_addr is_malicious hidden_service_connects := by
  intro _
  rfl

/-! ## 5. Post-condition -/

/-- Post-condition conjunction of all specification properties. -/
def Post_prop (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) : Prop :=
  always_true_prop rendezvous_addr is_malicious hidden_service_connects ∧
  accepts_malicious_prop rendezvous_addr is_malicious hidden_service_connects ∧
  deanonymization_vuln_prop rendezvous_addr is_malicious hidden_service_connects ∧
  accepts_honest_prop rendezvous_addr is_malicious hidden_service_connects ∧
  unauthenticated_malicious_invariant_prop rendezvous_addr is_malicious hidden_service_connects ∧
  connection_flag_invariant_prop rendezvous_addr is_malicious hidden_service_connects ∧
  unvetted_address_invariant_prop rendezvous_addr is_malicious hidden_service_connects

/-! ## 6. Property-Based Tests -/

-- Randomized PBT for always_true_prop
#eval Plausible.Testable.check (∀ (addr : Int) (mal conn : Bool),
  unsafe_tor_rendezvous addr mal conn = true)

-- Randomized PBT for accepts_malicious_prop
#eval Plausible.Testable.check (∀ (addr : Int) (mal conn : Bool),
  (!mal || unsafe_tor_rendezvous addr mal conn) = true)
#eval Plausible.Testable.check (∀ (addr : Int) (conn : Bool),
  unsafe_tor_rendezvous addr true conn = true)

-- Randomized PBT for deanonymization_vuln_prop
#eval Plausible.Testable.check (∀ (addr : Int) (mal conn : Bool),
  (!(mal && conn) || unsafe_tor_rendezvous addr mal conn) = true)
#eval Plausible.Testable.check (∀ (addr : Int),
  unsafe_tor_rendezvous addr true true = true)

-- Randomized PBT for accepts_honest_prop
#eval Plausible.Testable.check (∀ (addr : Int) (mal conn : Bool),
  (mal || unsafe_tor_rendezvous addr mal conn) = true)
#eval Plausible.Testable.check (∀ (addr : Int) (conn : Bool),
  unsafe_tor_rendezvous addr false conn = true)

-- Randomized PBT for unauthenticated_malicious_invariant_prop
#eval Plausible.Testable.check (∀ (addr : Int) (mal conn : Bool),
  unsafe_tor_rendezvous addr mal conn = unsafe_tor_rendezvous addr (!mal) conn)

-- Randomized PBT for connection_flag_invariant_prop
#eval Plausible.Testable.check (∀ (addr : Int) (mal conn : Bool),
  unsafe_tor_rendezvous addr mal conn = unsafe_tor_rendezvous addr mal (!conn))

-- Randomized PBT for unvetted_address_invariant_prop
#eval Plausible.Testable.check (∀ (addr other_addr : Int) (mal conn : Bool),
  unsafe_tor_rendezvous addr mal conn = unsafe_tor_rendezvous other_addr mal conn)

-- Randomized PBT for Post_prop (executable Boolean form)
#eval Plausible.Testable.check (∀ (addr other_addr : Int) (mal conn : Bool),
  (unsafe_tor_rendezvous addr mal conn == true) &&
  (!mal || (unsafe_tor_rendezvous addr mal conn == true)) &&
  (!(mal && conn) || (unsafe_tor_rendezvous addr mal conn == true)) &&
  (mal || (unsafe_tor_rendezvous addr mal conn == true)) &&
  (unsafe_tor_rendezvous addr mal conn == unsafe_tor_rendezvous addr (!mal) conn) &&
  (unsafe_tor_rendezvous addr mal conn == unsafe_tor_rendezvous addr mal (!conn)) &&
  (unsafe_tor_rendezvous addr mal conn == unsafe_tor_rendezvous other_addr mal conn))

-- Bounded PBT across address ranges and all Boolean combinations
example : (List.range 50).all (fun n =>
  let addr : Int := Int.ofNat n - 25
  [true, false].all (fun mal =>
    [true, false].all (fun conn =>
      (unsafe_tor_rendezvous addr mal conn == true) &&
      (!mal || (unsafe_tor_rendezvous addr mal conn == true)) &&
      (!(mal && conn) || (unsafe_tor_rendezvous addr mal conn == true)) &&
      (mal || (unsafe_tor_rendezvous addr mal conn == true)) &&
      (unsafe_tor_rendezvous addr mal conn == unsafe_tor_rendezvous addr (!mal) conn) &&
      (unsafe_tor_rendezvous addr mal conn == unsafe_tor_rendezvous addr mal (!conn)) &&
      (unsafe_tor_rendezvous addr mal conn == unsafe_tor_rendezvous 0 mal conn)))) = true := by
  native_decide

/-! ## 7. Correctness Theorem (Pre -> Post) -/

theorem unsafe_tor_rendezvous_correct (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool)
    (hPre : Pre rendezvous_addr is_malicious hidden_service_connects) :
    Post_prop rendezvous_addr is_malicious hidden_service_connects := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact always_true_thm rendezvous_addr is_malicious hidden_service_connects
  · exact accepts_malicious_thm rendezvous_addr is_malicious hidden_service_connects
  · exact deanonymization_vuln_thm rendezvous_addr is_malicious hidden_service_connects
  · exact accepts_honest_thm rendezvous_addr is_malicious hidden_service_connects
  · exact unauthenticated_malicious_invariant_thm rendezvous_addr is_malicious hidden_service_connects
  · exact connection_flag_invariant_thm rendezvous_addr is_malicious hidden_service_connects
  · exact unvetted_address_invariant_thm rendezvous_addr is_malicious hidden_service_connects

/-! ## 8. Imperative Implementation -/

/-- Imperative implementation using `Id.run do` with mutable state. -/
def unsafe_tor_rendezvous_imp (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) : Bool := Id.run do
  let mut addr := rendezvous_addr
  let mut mal := is_malicious
  let mut conn := hidden_service_connects
  let mut accepted : Bool := false
  -- Vulnerable: rendezvous is never authenticated or vetted
  accepted := true
  return accepted

/-! ## 9. Imperative Tests -/

example : unsafe_tor_rendezvous_imp 0x0A000001 false true = true := by native_decide
example : unsafe_tor_rendezvous_imp 0xDEADBEEF true true = true := by native_decide
example : unsafe_tor_rendezvous_imp 0x00000000 true false = true := by native_decide
example : unsafe_tor_rendezvous_imp 0x7F000001 false false = true := by native_decide

#eval unsafe_tor_rendezvous_imp 0x0A000001 false true
#eval unsafe_tor_rendezvous_imp 0xDEADBEEF true true
#eval unsafe_tor_rendezvous_imp 0x00000000 true false
#eval unsafe_tor_rendezvous_imp 0x7F000001 false false

#eval Plausible.Testable.check (∀ (addr : Int) (mal conn : Bool),
  unsafe_tor_rendezvous_imp addr mal conn = unsafe_tor_rendezvous addr mal conn)

/-! ## 10. Equivalence Theorem (Functional = Imperative) -/

theorem unsafe_tor_rendezvous_equiv (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) :
    unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects =
      unsafe_tor_rendezvous_imp rendezvous_addr is_malicious hidden_service_connects := by
  rfl

end «129_unsafeTorHiddenService»
