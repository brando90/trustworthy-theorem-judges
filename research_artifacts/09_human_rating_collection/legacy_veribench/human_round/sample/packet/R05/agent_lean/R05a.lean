import Mathlib

/-!
# Unsafe Tor hidden-service rendezvous (MIT 6.858 Fall 2012, Quiz 2)

Translation of a Python program modelling a Tor hidden service that accepts a
rendezvous point **without authenticating it**.

A malicious Tor OR can set up a rendezvous point on itself and hand its address to the
introduction point of a hidden service.  When the hidden service dutifully connects to
that rendezvous point, the malicious node observes the origin of the incoming connection
and thereby deanonymizes the hidden service.

The Python function

```python
def unsafe_tor_rendezvous(rendezvous_addr: int, is_malicious: bool,
                          hidden_service_connects: bool) -> bool:
    return True  # vulnerable: rendezvous never authenticated
```

is a constant `True`: the decision to use the rendezvous point does not depend on the
rendezvous address, on whether the rendezvous point is adversary-controlled, nor on
whether the hidden service actually connects.  That *constancy* is precisely the bug, and
it is what the specifications below pin down:

* the function always accepts (`always_accepts_prop`);
* it never rejects, in particular it never rejects a malicious rendezvous point
  (`accepts_malicious_prop`, `never_rejects_prop`);
* it ignores all of its inputs (`ignores_inputs_prop`, `independent_of_maliciousness_prop`).

The file also gives an imperative (`Id.run do`) rendering and proves it equivalent to the
functional one.
-/

namespace UnsafeTorHiddenService

/-! ## Implementation -/

/-- A rendezvous-point address (e.g. `0x0A000001`), modelled as a natural number. -/
abbrev Addr := Nat

/--
The vulnerable hidden-service logic: the rendezvous point is *always* used, whatever its
address, whether or not it is malicious, and whether or not the service connects.
-/
def unsafeTorRendezvous (_rendezvousAddr : Addr) (_isMalicious : Bool)
    (_hiddenServiceConnects : Bool) : Bool :=
  true -- vulnerable: rendezvous never authenticated

/-! ## Unit tests (mirroring Python's `check`) -/

-- honest rendezvous rejected
example : unsafeTorRendezvous 0x0A000001 false true = true := by native_decide
-- vuln: malicious rendezvous accepted
example : unsafeTorRendezvous 0xDEADBEEF true true = true := by native_decide
-- vuln: no-connect malicious accepted
example : unsafeTorRendezvous 0x00000000 true false = true := by native_decide
-- localhost honest rejected
example : unsafeTorRendezvous 0x7F000001 false false = true := by native_decide

#eval unsafeTorRendezvous 0x0A000001 false true
#eval unsafeTorRendezvous 0xDEADBEEF true true
#eval unsafeTorRendezvous 0x00000000 true false
#eval unsafeTorRendezvous 0x7F000001 false false

/-! ## Pre-condition -/

/-- The Python function has no restriction on its inputs: every triple is admissible. -/
def Pre (_rendezvousAddr : Addr) (_isMalicious : Bool) (_hiddenServiceConnects : Bool) : Prop :=
  True

/-! ## Properties -/

/-- The hidden service always accepts the proposed rendezvous point. -/
def always_accepts_prop (a : Addr) (m c : Bool) : Prop :=
  unsafeTorRendezvous a m c = true

theorem always_accepts_thm (a : Addr) (m c : Bool) : always_accepts_prop a m c := by
  rfl

/-- **The vulnerability**: a rendezvous point known to be adversary-controlled is accepted. -/
def accepts_malicious_prop (a : Addr) (c : Bool) : Prop :=
  unsafeTorRendezvous a true c = true

theorem accepts_malicious_thm (a : Addr) (c : Bool) : accepts_malicious_prop a c := by
  rfl

/-- The result is never `false`: there is no input at all that gets rejected. -/
def never_rejects_prop : Prop :=
  ¬ ∃ (a : Addr) (m c : Bool), unsafeTorRendezvous a m c = false

theorem never_rejects_thm : never_rejects_prop := by
  rintro ⟨a, m, c, h⟩
  exact Bool.noConfusion h

/-- The decision ignores every input: it is a constant function. -/
def ignores_inputs_prop (a₁ a₂ : Addr) (m₁ m₂ c₁ c₂ : Bool) : Prop :=
  unsafeTorRendezvous a₁ m₁ c₁ = unsafeTorRendezvous a₂ m₂ c₂

theorem ignores_inputs_thm (a₁ a₂ : Addr) (m₁ m₂ c₁ c₂ : Bool) :
    ignores_inputs_prop a₁ a₂ m₁ m₂ c₁ c₂ := by
  rfl

/--
No authentication happens: flipping the `isMalicious` bit — the only information that
could distinguish an honest rendezvous point from an adversarial one — does not change
the outcome.
-/
def independent_of_maliciousness_prop (a : Addr) (c : Bool) : Prop :=
  unsafeTorRendezvous a true c = unsafeTorRendezvous a false c

theorem independent_of_maliciousness_thm (a : Addr) (c : Bool) :
    independent_of_maliciousness_prop a c := by
  rfl

/--
A secure implementation would reject at least one malicious rendezvous point; this one
provably does not, so it cannot be refined into a safe one by any choice of address.
-/
def not_secure_prop : Prop :=
  ¬ ∃ (a : Addr) (c : Bool), unsafeTorRendezvous a true c = false

theorem not_secure_thm : not_secure_prop := by
  rintro ⟨a, c, h⟩
  exact Bool.noConfusion h

/-- The four concrete assertions of the Python `check` function. -/
def check_prop : Prop :=
  unsafeTorRendezvous 0x0A000001 false true = true ∧
  unsafeTorRendezvous 0xDEADBEEF true true = true ∧
  unsafeTorRendezvous 0x00000000 true false = true ∧
  unsafeTorRendezvous 0x7F000001 false false = true

theorem check_thm : check_prop := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-! ## Post-condition and correctness -/

/-- Full post-condition: the conjunction of all specified properties. -/
def Post_prop (a : Addr) (m c : Bool) : Prop :=
  always_accepts_prop a m c ∧
  accepts_malicious_prop a c ∧
  independent_of_maliciousness_prop a c ∧
  (∀ a' : Addr, ∀ m' c' : Bool, ignores_inputs_prop a a' m m' c c') ∧
  never_rejects_prop ∧
  not_secure_prop ∧
  check_prop

/-- Correctness: the pre-condition implies the full post-condition. -/
theorem correctness_thm (a : Addr) (m c : Bool) (_h : Pre a m c) : Post_prop a m c :=
  ⟨always_accepts_thm a m c, accepts_malicious_thm a c, independent_of_maliciousness_thm a c,
    fun a' m' c' => ignores_inputs_thm a a' m m' c c', never_rejects_thm, not_secure_thm,
    check_thm⟩

/-! ## Imperative implementation -/

/--
Imperative rendering: a mutable `accepted` flag that starts out `true` and is never
cleared, because no authentication step is ever performed on the rendezvous point.
-/
def unsafeTorRendezvousImp (rendezvousAddr : Addr) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) : Bool := Id.run do
  let mut accepted : Bool := true
  -- The address is recorded but never vetted.
  let mut _seenAddr : Addr := rendezvousAddr
  -- A secure implementation would authenticate here, e.g.
  --   `if isMalicious then accepted := false`.
  -- The vulnerable one inspects nothing.
  if isMalicious && hiddenServiceConnects then
    accepted := accepted -- deanonymization happens, yet the service still connects
  return accepted

/-! ## Imperative tests -/

example : unsafeTorRendezvousImp 0x0A000001 false true = true := by native_decide
example : unsafeTorRendezvousImp 0xDEADBEEF true true = true := by native_decide
example : unsafeTorRendezvousImp 0x00000000 true false = true := by native_decide
example : unsafeTorRendezvousImp 0x7F000001 false false = true := by native_decide

#eval unsafeTorRendezvousImp 0xDEADBEEF true true

/-! ## Equivalence -/

/-- The functional and imperative implementations agree on all inputs. -/
def equiv_prop : Prop :=
  ∀ (a : Addr) (m c : Bool), unsafeTorRendezvous a m c = unsafeTorRendezvousImp a m c

theorem equiv_thm : equiv_prop := by
  intro a m c
  cases m <;> cases c <;> rfl

end UnsafeTorHiddenService
