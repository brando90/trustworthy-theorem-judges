import Mathlib

/-!
# 129_unsafeTorHiddenService

Formalisation of the Python program `unsafe_tor_rendezvous`: an *unsafe* Tor hidden-service
rendezvous that never authenticates the rendezvous point.

## The Python program

```python
def unsafe_tor_rendezvous(rendezvous_addr: int, is_malicious: bool,
                          hidden_service_connects: bool) -> bool:
    return True  # vulnerable: rendezvous never authenticated
```

The function is total and constant: it returns `True` for every triple
`(rendezvous_addr, is_malicious, hidden_service_connects)`.  The four assertions of the Python
`check()` function are reproduced as unit tests below.

## The vulnerability (MIT 6.858 Fall 2012 Quiz 2)

A malicious Tor onion router can set up a rendezvous point on itself and send its address to
the introduction point of a hidden service.  When the hidden service connects to that
rendezvous point, the malicious node records the origin of the incoming connection and thereby
deanonymizes the hidden service.  The hidden service neither authenticates nor vets the
rendezvous point, so the adversarial case is accepted exactly like the honest one.  This file
models that behaviour faithfully: the acceptance decision is the constant `true`, it is
independent of `rendezvous_addr`, of `is_malicious` and of `hidden_service_connects`, and the
`deanonymized` predicate therefore fires for every adversarial rendezvous point that the
hidden service connects to.

## Modelling notes

* `rendezvous_addr : Nat` models the Python `int` address of the rendezvous point.  IPv4 style
  addresses are non negative and `Nat` is unbounded, just like Python's `int`; moreover the
  proved properties show that the result never depends on the address, so the entire
  admissible domain is covered by the theorems.
* `is_malicious : Bool` says whether the rendezvous point is controlled by an adversary.
* `hidden_service_connects : Bool` says whether the hidden service actually connects to it.
* `authenticate_rendezvous` models the authentication step that the vulnerable code omits; it
  is constantly `false`, i.e. no rendezvous point is ever authenticated.
* `deanonymized` models the security consequence: the adversary learns the origin of the
  hidden service's connection.
* `secure_tor_rendezvous` is the secure specification (reject an adversary controlled
  rendezvous point).  It is *not* part of the Python program; it is only used to state
  precisely how the program is vulnerable.
* Every theorem is discharged by the kernel (`rfl`, `cases`, `decide`).  `native_decide` is
  used only inside `example` unit tests and property based tests, never inside a theorem.
-/

set_option linter.unusedVariables false

namespace «129_unsafeTorHiddenService»

/-! ## 1. Functional implementation -/

/-- The authentication step that the vulnerable hidden service *omits*.

A correct implementation would vet the rendezvous point before connecting to it.  The Python
program performs no such check, so this function is constantly `false`: no rendezvous point is
ever authenticated. -/
def authenticate_rendezvous (_rendezvous_addr : Nat) : Bool :=
  false

/-- `unsafe_tor_rendezvous` from the Python program.

Returns `true` regardless of whether the rendezvous point is controlled by an adversary
(Python: `return True  # vulnerable: rendezvous never authenticated`). -/
def unsafe_tor_rendezvous (rendezvous_addr : Nat) (is_malicious : Bool)
    (hidden_service_connects : Bool) : Bool :=
  true

/-- `true` when the adversary running the rendezvous point gets to record the origin of the
hidden service's incoming connection, i.e. when the hidden service is deanonymized.

This happens exactly when the rendezvous point is malicious, the hidden service connects to
it, and the (unconditional) acceptance check accepts it. -/
def deanonymized (rendezvous_addr : Nat) (is_malicious : Bool)
    (hidden_service_connects : Bool) : Bool :=
  is_malicious && hidden_service_connects &&
    unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects

/-- The *secure* specification the Python program fails to implement: an adversary controlled
rendezvous point must be rejected.  Used only to state precisely how the implementation is
vulnerable. -/
def secure_tor_rendezvous (_rendezvous_addr : Nat) (is_malicious : Bool)
    (_hidden_service_connects : Bool) : Bool :=
  !is_malicious

/-! ## 2. Unit tests (the assertions of the Python `check()` function) -/

-- assert unsafe_tor_rendezvous(0x0A000001, False, True) == True, "honest rendezvous rejected"
example : unsafe_tor_rendezvous 0x0A000001 false true = true := by native_decide
-- assert unsafe_tor_rendezvous(0xDEADBEEF, True, True) == True, "vuln: malicious accepted"
example : unsafe_tor_rendezvous 0xDEADBEEF true true = true := by native_decide
-- assert unsafe_tor_rendezvous(0x00000000, True, False) == True, "vuln: no-connect malicious"
example : unsafe_tor_rendezvous 0x00000000 true false = true := by native_decide
-- assert unsafe_tor_rendezvous(0x7F000001, False, False) == True, "localhost honest rejected"
example : unsafe_tor_rendezvous 0x7F000001 false false = true := by native_decide

#eval unsafe_tor_rendezvous 0x0A000001 false true
#eval unsafe_tor_rendezvous 0xDEADBEEF true true
#eval unsafe_tor_rendezvous 0x00000000 true false
#eval unsafe_tor_rendezvous 0x7F000001 false false

-- the security consequence of those very calls
example : deanonymized 0xDEADBEEF true true = true := by native_decide
example : deanonymized 0x00000000 true false = false := by native_decide
example : deanonymized 0x0A000001 false true = false := by native_decide
#eval deanonymized 0xDEADBEEF true true

/-! ## 3. Pre-condition -/

/-- The Python function is total: `unsafe_tor_rendezvous` is defined for every address and
every pair of flags and never raises, so the pre-condition is `True` (no input is excluded).
The address is modelled as a `Nat`, which is unbounded like Python's `int`, and the theorems
below are stated for *all* addresses, all `is_malicious` and all `hidden_service_connects`. -/
@[reducible] def Pre (rendezvous_addr : Nat) (is_malicious : Bool)
    (hidden_service_connects : Bool) : Prop :=
  True

/-! ## 4. Properties and their proofs -/

/-- The rendezvous point is always accepted (Python: `return True`). -/
@[reducible] def always_accepts_prop (rendezvous_addr : Nat) (is_malicious : Bool)
    (hidden_service_connects : Bool) : Prop :=
  unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects = true

theorem always_accepts_thm (rendezvous_addr : Nat) (is_malicious : Bool)
    (hidden_service_connects : Bool) :
    always_accepts_prop rendezvous_addr is_malicious hidden_service_connects :=
  rfl

/-- The honest case of the Python `check()`: an honest rendezvous point is accepted. -/
@[reducible] def honest_rendezvous_accepted_prop (rendezvous_addr : Nat)
    (hidden_service_connects : Bool) : Prop :=
  unsafe_tor_rendezvous rendezvous_addr false hidden_service_connects = true

theorem honest_rendezvous_accepted_thm (rendezvous_addr : Nat)
    (hidden_service_connects : Bool) :
    honest_rendezvous_accepted_prop rendezvous_addr hidden_service_connects :=
  rfl

/-- The vulnerability: an adversary controlled rendezvous point is accepted as well
(Python: "vuln: malicious rendezvous accepted"). -/
@[reducible] def malicious_rendezvous_accepted_prop (rendezvous_addr : Nat)
    (hidden_service_connects : Bool) : Prop :=
  unsafe_tor_rendezvous rendezvous_addr true hidden_service_connects = true

theorem malicious_rendezvous_accepted_thm (rendezvous_addr : Nat)
    (hidden_service_connects : Bool) :
    malicious_rendezvous_accepted_prop rendezvous_addr hidden_service_connects :=
  rfl

/-- The acceptance decision does not depend on whether the rendezvous point is malicious:
the adversary controlled case is treated exactly like the honest one. -/
@[reducible] def ignores_malice_prop (rendezvous_addr : Nat) (is_malicious : Bool)
    (hidden_service_connects : Bool) : Prop :=
  unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects =
    unsafe_tor_rendezvous rendezvous_addr (!is_malicious) hidden_service_connects

theorem ignores_malice_thm (rendezvous_addr : Nat) (is_malicious : Bool)
    (hidden_service_connects : Bool) :
    ignores_malice_prop rendezvous_addr is_malicious hidden_service_connects :=
  rfl

/-- The acceptance decision does not depend on the rendezvous address: any address an
adversary may advertise is accepted. -/
@[reducible] def ignores_address_prop (addr₁ addr₂ : Nat) (is_malicious : Bool)
    (hidden_service_connects : Bool) : Prop :=
  unsafe_tor_rendezvous addr₁ is_malicious hidden_service_connects =
    unsafe_tor_rendezvous addr₂ is_malicious hidden_service_connects

theorem ignores_address_thm (addr₁ addr₂ : Nat) (is_malicious : Bool)
    (hidden_service_connects : Bool) :
    ignores_address_prop addr₁ addr₂ is_malicious hidden_service_connects :=
  rfl

/-- The acceptance decision does not depend on whether the hidden service connects. -/
@[reducible] def ignores_connect_prop (rendezvous_addr : Nat) (is_malicious : Bool)
    (connects₁ connects₂ : Bool) : Prop :=
  unsafe_tor_rendezvous rendezvous_addr is_malicious connects₁ =
    unsafe_tor_rendezvous rendezvous_addr is_malicious connects₂

theorem ignores_connect_thm (rendezvous_addr : Nat) (is_malicious : Bool)
    (connects₁ connects₂ : Bool) :
    ignores_connect_prop rendezvous_addr is_malicious connects₁ connects₂ :=
  rfl

/-- The rendezvous point is never authenticated: the missing security check. -/
@[reducible] def no_authentication_prop (rendezvous_addr : Nat) : Prop :=
  authenticate_rendezvous rendezvous_addr = false

theorem no_authentication_thm (rendezvous_addr : Nat) :
    no_authentication_prop rendezvous_addr :=
  rfl

/-- Deanonymization: because the rendezvous point is accepted unconditionally, the hidden
service is deanonymized exactly when the rendezvous point is malicious and the service
connects to it. -/
@[reducible] def deanonymization_prop (rendezvous_addr : Nat) (is_malicious : Bool)
    (hidden_service_connects : Bool) : Prop :=
  deanonymized rendezvous_addr is_malicious hidden_service_connects =
    (is_malicious && hidden_service_connects)

theorem deanonymization_thm (rendezvous_addr : Nat) (is_malicious : Bool)
    (hidden_service_connects : Bool) :
    deanonymization_prop rendezvous_addr is_malicious hidden_service_connects := by
  cases is_malicious <;> cases hidden_service_connects <;> rfl

/-- The implementation deviates from the secure specification: it accepts a malicious
rendezvous point that the secure specification rejects. -/
@[reducible] def insecure_vs_secure_prop (rendezvous_addr : Nat)
    (hidden_service_connects : Bool) : Prop :=
  unsafe_tor_rendezvous rendezvous_addr true hidden_service_connects = true ∧
    secure_tor_rendezvous rendezvous_addr true hidden_service_connects = false

theorem insecure_vs_secure_thm (rendezvous_addr : Nat) (hidden_service_connects : Bool) :
    insecure_vs_secure_prop rendezvous_addr hidden_service_connects :=
  ⟨rfl, rfl⟩

/-- Concrete witness of the vulnerability: some admissible input on which the unsafe program
and the secure specification disagree. -/
theorem vulnerability_witness_thm :
    ∃ (rendezvous_addr : Nat) (is_malicious : Bool) (hidden_service_connects : Bool),
      unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects ≠
        secure_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects :=
  ⟨0xDEADBEEF, true, true, by decide⟩

/-- The four assertions of the Python `check()` function, as a single closed proposition. -/
@[reducible] def check_prop : Prop :=
  unsafe_tor_rendezvous 0x0A000001 false true = true ∧
    unsafe_tor_rendezvous 0xDEADBEEF true true = true ∧
    unsafe_tor_rendezvous 0x00000000 true false = true ∧
    unsafe_tor_rendezvous 0x7F000001 false false = true

theorem check_thm : check_prop :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## 5. Post-condition -/

/-- The post-condition: conjunction of all the properties above, at the given input. -/
@[reducible] def Post_prop (rendezvous_addr : Nat) (is_malicious : Bool)
    (hidden_service_connects : Bool) : Prop :=
  always_accepts_prop rendezvous_addr is_malicious hidden_service_connects ∧
    honest_rendezvous_accepted_prop rendezvous_addr hidden_service_connects ∧
    malicious_rendezvous_accepted_prop rendezvous_addr hidden_service_connects ∧
    ignores_malice_prop rendezvous_addr is_malicious hidden_service_connects ∧
    ignores_address_prop rendezvous_addr 0xDEADBEEF is_malicious hidden_service_connects ∧
    ignores_connect_prop rendezvous_addr is_malicious hidden_service_connects
      (!hidden_service_connects) ∧
    no_authentication_prop rendezvous_addr ∧
    deanonymization_prop rendezvous_addr is_malicious hidden_service_connects ∧
    insecure_vs_secure_prop rendezvous_addr hidden_service_connects

/-! ## 6. Property-based tests

Every executable property stated above (each `_prop` and the post-condition) is tested on many
inputs: once randomly with Plausible and once exhaustively on a bounded range of addresses and
on all Boolean flag combinations.  A PBT is evidence, not a proof; the proofs are the theorems
of section 4 and the correctness theorem of section 7. -/

-- PBT: always_accepts_prop
#eval Plausible.Testable.check (∀ (a : Nat) (m c : Bool), always_accepts_prop a m c)
example : (List.range 64).all (fun n => [true, false].all (fun m => [true, false].all (fun c =>
    decide (always_accepts_prop n m c)))) = true := by native_decide

-- PBT: honest_rendezvous_accepted_prop
#eval Plausible.Testable.check (∀ (a : Nat) (c : Bool), honest_rendezvous_accepted_prop a c)
example : (List.range 64).all (fun n => [true, false].all (fun c =>
    decide (honest_rendezvous_accepted_prop n c))) = true := by native_decide

-- PBT: malicious_rendezvous_accepted_prop
#eval Plausible.Testable.check (∀ (a : Nat) (c : Bool), malicious_rendezvous_accepted_prop a c)
example : (List.range 64).all (fun n => [true, false].all (fun c =>
    decide (malicious_rendezvous_accepted_prop n c))) = true := by native_decide

-- PBT: ignores_malice_prop
#eval Plausible.Testable.check (∀ (a : Nat) (m c : Bool), ignores_malice_prop a m c)
example : (List.range 64).all (fun n => [true, false].all (fun m => [true, false].all (fun c =>
    decide (ignores_malice_prop n m c)))) = true := by native_decide

-- PBT: ignores_address_prop
#eval Plausible.Testable.check (∀ (a b : Nat) (m c : Bool), ignores_address_prop a b m c)
example : (List.range 32).all (fun n => (List.range 32).all (fun k =>
    [true, false].all (fun m => [true, false].all (fun c =>
      decide (ignores_address_prop n k m c))))) = true := by native_decide

-- PBT: ignores_connect_prop
#eval Plausible.Testable.check
  (∀ (a : Nat) (m c d : Bool), ignores_connect_prop a m c d)
example : (List.range 32).all (fun n => [true, false].all (fun m =>
    [true, false].all (fun c => [true, false].all (fun d =>
      decide (ignores_connect_prop n m c d))))) = true := by native_decide

-- PBT: no_authentication_prop
#eval Plausible.Testable.check (∀ a : Nat, no_authentication_prop a)
example : (List.range 64).all (fun n => decide (no_authentication_prop n)) = true :=
  by native_decide

-- PBT: deanonymization_prop
#eval Plausible.Testable.check (∀ (a : Nat) (m c : Bool), deanonymization_prop a m c)
example : (List.range 64).all (fun n => [true, false].all (fun m => [true, false].all (fun c =>
    decide (deanonymization_prop n m c)))) = true := by native_decide

-- PBT: insecure_vs_secure_prop
#eval Plausible.Testable.check (∀ (a : Nat) (c : Bool), insecure_vs_secure_prop a c)
example : (List.range 64).all (fun n => [true, false].all (fun c =>
    decide (insecure_vs_secure_prop n c))) = true := by native_decide

-- PBT: check_prop (closed proposition: the four Python assertions)
example : decide check_prop = true := by native_decide

-- PBT: vulnerability_witness_thm (existential; the bounded search exhibits a witness)
example : (List.range 8).any (fun n =>
    decide (unsafe_tor_rendezvous n true true ≠ secure_tor_rendezvous n true true)) = true :=
  by native_decide

-- PBT: Post_prop
#eval Plausible.Testable.check (∀ (a : Nat) (m c : Bool), Post_prop a m c)
example : (List.range 32).all (fun n => [true, false].all (fun m => [true, false].all (fun c =>
    decide (Post_prop n m c)))) = true := by native_decide

/-! ## 7. Correctness theorem -/

/-- The program is correct with respect to `Pre` and `Post_prop`: for every admissible input
(and every input is admissible, the Python function is total) the acceptance decision is the
constant `true`, it ignores the address, the malice flag and the connection flag, the
rendezvous point is never authenticated, an adversary controlled rendezvous point that the
hidden service connects to deanonymizes it, and the behaviour deviates from the secure
specification. -/
theorem correctness (rendezvous_addr : Nat) (is_malicious : Bool)
    (hidden_service_connects : Bool)
    (h : Pre rendezvous_addr is_malicious hidden_service_connects) :
    Post_prop rendezvous_addr is_malicious hidden_service_connects :=
  ⟨always_accepts_thm _ _ _,
   honest_rendezvous_accepted_thm _ _,
   malicious_rendezvous_accepted_thm _ _,
   ignores_malice_thm _ _ _,
   ignores_address_thm _ _ _ _,
   ignores_connect_thm _ _ _ _,
   no_authentication_thm _,
   deanonymization_thm _ _ _,
   insecure_vs_secure_thm _ _⟩

/-! ## 8. Imperative implementation (mutable state in the `Id` monad) -/

/-- Imperative rendition of `unsafe_tor_rendezvous`, mirroring the control flow of a hidden
service that handles a rendezvous request with mutable state. -/
def unsafe_tor_rendezvous_imp (rendezvous_addr : Nat) (is_malicious : Bool)
    (hidden_service_connects : Bool) : Bool :=
  Id.run do
    -- mutable state: was the rendezvous point authenticated?
    let mut authenticated : Bool := false
    -- mutable state: the acceptance decision
    let mut accepted : Bool := false
    -- Step 1. The introduction point hands over the rendezvous address.  The vulnerable code
    -- never vets it, so `authenticated` stays `false` for every address.
    authenticated := authenticate_rendezvous rendezvous_addr
    -- Step 2. The rendezvous point is accepted unconditionally: neither `is_malicious` nor
    -- `hidden_service_connects` can veto the decision (`true || _` is `true`).
    accepted := true || (is_malicious && hidden_service_connects)
    -- Step 3. The authentication result is never used to veto the acceptance, so this guard
    -- is dead code (`authenticated` is always `false`).  That is exactly the bug: a malicious
    -- rendezvous point is accepted just like an honest one.
    if authenticated && is_malicious && hidden_service_connects then
      accepted := false
    -- Step 4. The hidden service connects to the (possibly adversarial) rendezvous point,
    -- which lets the adversary record the origin of the incoming connection.
    return accepted

/-- Imperative rendition of `deanonymized`. -/
def deanonymized_imp (rendezvous_addr : Nat) (is_malicious : Bool)
    (hidden_service_connects : Bool) : Bool :=
  Id.run do
    let mut accepted : Bool := unsafe_tor_rendezvous_imp rendezvous_addr is_malicious
      hidden_service_connects
    let mut deanonymized_flag : Bool := false
    deanonymized_flag := is_malicious && hidden_service_connects && accepted
    return deanonymized_flag

/-! ## 9. Imperative tests -/

example : unsafe_tor_rendezvous_imp 0x0A000001 false true = true := by native_decide
example : unsafe_tor_rendezvous_imp 0xDEADBEEF true true = true := by native_decide
example : unsafe_tor_rendezvous_imp 0x00000000 true false = true := by native_decide
example : unsafe_tor_rendezvous_imp 0x7F000001 false false = true := by native_decide

#eval unsafe_tor_rendezvous_imp 0x0A000001 false true
#eval unsafe_tor_rendezvous_imp 0xDEADBEEF true true
#eval unsafe_tor_rendezvous_imp 0x00000000 true false
#eval unsafe_tor_rendezvous_imp 0x7F000001 false false

example : deanonymized_imp 0xDEADBEEF true true = true := by native_decide
example : deanonymized_imp 0x0A000001 false true = false := by native_decide
#eval deanonymized_imp 0xDEADBEEF true true

-- bounded property-based tests over the imperative implementation
example : (List.range 32).all (fun n => [true, false].all (fun m => [true, false].all (fun c =>
    (unsafe_tor_rendezvous_imp n m c == true)))) = true := by native_decide
example : (List.range 32).all (fun n => [true, false].all (fun m => [true, false].all (fun c =>
    (deanonymized_imp n m c == (m && c))))) = true := by native_decide
#eval Plausible.Testable.check
  (∀ (a : Nat) (m c : Bool), unsafe_tor_rendezvous_imp a m c = true)

/-! ## 10. Equivalence of the functional and the imperative implementation -/

theorem imperative_always_accepts (rendezvous_addr : Nat) (is_malicious : Bool)
    (hidden_service_connects : Bool) :
    unsafe_tor_rendezvous_imp rendezvous_addr is_malicious hidden_service_connects = true :=
  rfl

theorem functional_imperative_equiv (rendezvous_addr : Nat) (is_malicious : Bool)
    (hidden_service_connects : Bool) :
    unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects =
      unsafe_tor_rendezvous_imp rendezvous_addr is_malicious hidden_service_connects :=
  rfl

theorem deanonymized_functional_imperative_equiv (rendezvous_addr : Nat) (is_malicious : Bool)
    (hidden_service_connects : Bool) :
    deanonymized rendezvous_addr is_malicious hidden_service_connects =
      deanonymized_imp rendezvous_addr is_malicious hidden_service_connects := by
  cases is_malicious <;> cases hidden_service_connects <;> rfl

/-- The post-condition restated over the imperative implementation. -/
@[reducible] def Post_prop_imp (rendezvous_addr : Nat) (is_malicious : Bool)
    (hidden_service_connects : Bool) : Prop :=
  unsafe_tor_rendezvous_imp rendezvous_addr is_malicious hidden_service_connects = true ∧
    deanonymized_imp rendezvous_addr is_malicious hidden_service_connects =
      (is_malicious && hidden_service_connects) ∧
    authenticate_rendezvous rendezvous_addr = false

/-- The imperative implementation discharges the same obligations as the functional one: the
first component is `always_accepts_thm` transported along `functional_imperative_equiv`. -/
theorem correctness_imp (rendezvous_addr : Nat) (is_malicious : Bool)
    (hidden_service_connects : Bool)
    (h : Pre rendezvous_addr is_malicious hidden_service_connects) :
    Post_prop_imp rendezvous_addr is_malicious hidden_service_connects := by
  have e := functional_imperative_equiv rendezvous_addr is_malicious hidden_service_connects
  refine ⟨?_, ?_, no_authentication_thm rendezvous_addr⟩
  · rw [← e]
    exact always_accepts_thm rendezvous_addr is_malicious hidden_service_connects
  · cases is_malicious <;> cases hidden_service_connects <;> rfl

-- PBT: Post_prop_imp
#eval Plausible.Testable.check (∀ (a : Nat) (m c : Bool), Post_prop_imp a m c)
example : (List.range 32).all (fun n => [true, false].all (fun m => [true, false].all (fun c =>
    decide (Post_prop_imp n m c)))) = true := by native_decide

end «129_unsafeTorHiddenService»
