import Mathlib
namespace Agent

/-!
# Safe constant-time RSA exponentiation: one-bit timing model

This formalizes the Python `safe_rsa_bit` and its assertion-based checker.
Every integer input returns `(None, 60)`: the modeled square-and-multiply
cost is independent of the secret bit. `Int` preserves the full Python
integer domain (including inputs other than 0 and 1); `Option Unit.none`
represents Python's `None`.

The result models the reported cycle count, not wall-clock execution time
of Lean code or the arithmetic of a full RSA implementation. The mutable
implementation performs the same unconditional assignment as the model.
-/

namespace UnsafeRsaExponentiationSafe

/-! ## Functional implementation and Python checker -/

def safe_rsa_bit (_bit : Int) : Option Unit × Int :=
  (none, 60)

/-- Boolean counterpart of all assertions in the Python `check` function. -/
def check (candidate : Int → Option Unit × Int) : Bool :=
  ((candidate 1).2 == 60) &&
  ((candidate 0).2 == 60) &&
  ((candidate 1).2 == (candidate 0).2) &&
  ([0, 1, 7, 255] : List Int).all (fun bit => (candidate bit).2 == 60)

/-! ## Unit tests -/

example : safe_rsa_bit 1 = (none, 60) := by native_decide
example : safe_rsa_bit 0 = (none, 60) := by native_decide
example : (safe_rsa_bit 1).2 = (safe_rsa_bit 0).2 := by native_decide
example : ([0, 1, 7, 255] : List Int).all
    (fun bit => (safe_rsa_bit bit).2 == 60) = true := by native_decide
example : safe_rsa_bit (-12345) = (none, 60) := by native_decide
example : check safe_rsa_bit = true := by native_decide

#eval ([0, 1, 7, 255, -12345] : List Int).map safe_rsa_bit
#eval check safe_rsa_bit

/-! ## Precondition and proved properties -/

/-- There is no restriction to binary inputs: every integer is admissible. -/
def Pre (_bit : Int) : Prop := True

/-- The second tuple component is always exactly 60 cycles. -/
def cycles_prop (bit : Int) : Prop :=
  (safe_rsa_bit bit).2 = 60

theorem cycles_thm (bit : Int) : cycles_prop bit := by
  rfl

/-- The first tuple component is Python's `None`. -/
def none_prop (bit : Int) : Prop :=
  (safe_rsa_bit bit).1 = none

theorem none_thm (bit : Int) : none_prop bit := by
  rfl

/-- Any two inputs have identical reported timing, not merely 0 and 1. -/
def timing_prop (bit₁ bit₂ : Int) : Prop :=
  (safe_rsa_bit bit₁).2 = (safe_rsa_bit bit₂).2

theorem timing_thm (bit₁ bit₂ : Int) : timing_prop bit₁ bit₂ := by
  rfl

/-- The implementation satisfies every assertion in the original checker. -/
theorem check_thm : check safe_rsa_bit = true := by
  decide

/-! ## Postcondition -/

def Post_prop (bit : Int) : Prop :=
  none_prop bit ∧
  cycles_prop bit ∧
  (∀ other : Int, timing_prop bit other) ∧
  check safe_rsa_bit = true

/-! ## Property-based tests

These executable checks are evidence only; none is used in a theorem proof.
The universally quantified theorems above cover all integers, independently
of the sample sizes used here.
-/

-- PBT for cycles_prop.
#eval Plausible.Testable.check
  (∀ bit : Int, (safe_rsa_bit bit).2 = 60)

-- PBT for none_prop.
#eval Plausible.Testable.check
  (∀ bit : Int, (safe_rsa_bit bit).1 = (none : Option Unit))

-- PBT for timing_prop, independently sampling both inputs.
#eval Plausible.Testable.check
  (∀ bit other : Int, (safe_rsa_bit bit).2 = (safe_rsa_bit other).2)

-- PBT for Post_prop, including the original checker. Moving its universally
-- quantified comparison input to the front gives an executable sampled form.
#eval Plausible.Testable.check
  (∀ bit other : Int,
    (safe_rsa_bit bit).1 = (none : Option Unit) ∧
    (safe_rsa_bit bit).2 = 60 ∧
    (safe_rsa_bit bit).2 = (safe_rsa_bit other).2 ∧
    check safe_rsa_bit = true)

/-- Exhaustive signed test inputs, including 0, 1, 7, and 255. -/
private def pbtInputs : List Int :=
  (List.range 513).map (fun n => (n : Int) - 256)

-- Bounded PBTs supplement sampling with every input from -256 through 256.
example : pbtInputs.all
    (fun bit => (safe_rsa_bit bit).2 == 60) = true := by
  native_decide

example : pbtInputs.all
    (fun bit => (safe_rsa_bit bit).1 == (none : Option Unit)) = true := by
  native_decide

example : pbtInputs.all (fun bit => pbtInputs.all (fun other =>
    (safe_rsa_bit bit).2 == (safe_rsa_bit other).2)) = true := by
  native_decide

-- Bounded executable form of the whole postcondition, over all input pairs.
example : pbtInputs.all (fun bit => pbtInputs.all (fun other =>
    ((safe_rsa_bit bit).1 == (none : Option Unit)) &&
    ((safe_rsa_bit bit).2 == 60) &&
    ((safe_rsa_bit bit).2 == (safe_rsa_bit other).2) &&
    check safe_rsa_bit)) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (bit : Int) : Pre bit → Post_prop bit := by
  intro _
  exact ⟨none_thm bit, cycles_thm bit,
    (fun other => timing_thm bit other), check_thm⟩

/-! ## Imperative implementation -/

def safe_rsa_bit_imp (_bit : Int) : Option Unit × Int := Id.run do
  let mut cycles : Int := 0
  cycles := 60
  return (none, cycles)

/-! ## Imperative tests -/

example : safe_rsa_bit_imp 1 = (none, 60) := by native_decide
example : safe_rsa_bit_imp 0 = (none, 60) := by native_decide
example : (safe_rsa_bit_imp 1).2 = (safe_rsa_bit_imp 0).2 := by native_decide
example : ([0, 1, 7, 255, -12345] : List Int).all
    (fun bit => safe_rsa_bit_imp bit == (none, 60)) = true := by
  native_decide
example : check safe_rsa_bit_imp = true := by native_decide

#eval ([0, 1, 7, 255, -12345] : List Int).map safe_rsa_bit_imp
#eval check safe_rsa_bit_imp

-- Additional PBT for functional/imperative agreement.
#eval Plausible.Testable.check
  (∀ bit : Int, safe_rsa_bit bit = safe_rsa_bit_imp bit)

/-! ## Functional/imperative equivalence -/

theorem functional_imperative_equiv (bit : Int) :
    safe_rsa_bit bit = safe_rsa_bit_imp bit := by
  rfl

end UnsafeRsaExponentiationSafe
end Agent
