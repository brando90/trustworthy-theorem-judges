import Mathlib

/-!
# Natural-number exponentiation with checked integer inputs

`power` is the functional multiplication algorithm. `prog` models the Python
entry point: nonnegative integer inputs return a natural number, and negative
inputs return an `Except.error` carrying the ValueError message. Lean's `Int`
input type enforces the source's integer type check statically; `Pre` records
the remaining nonnegativity checks. Naturals and integers have unbounded size.
In particular, zero to the zeroth power is one.

The imperative version uses a mutable accumulator and one multiplication for
each element of `List.range exponent`. Bounded executable tests complement,
but are not used in, the kernel-checked proofs.
-/

namespace MyPower

-- Computable equality for both successful results and error messages.
deriving instance DecidableEq for Except

/-! ## Functional implementation -/

def power (base : Nat) : Nat → Nat
  | 0 => 1
  | exponent + 1 => power base exponent * base

def valueError (base exponent : Int) : String :=
  s!"Require base,exponent ∈ ℕ (got base={base}, exponent={exponent})"

def prog (base exponent : Int) : Except String Nat :=
  if 0 ≤ base ∧ 0 ≤ exponent then
    .ok (power base.toNat exponent.toNat)
  else
    .error (valueError base exponent)

/-! ## Unit tests -/

example : power 2 3 = 8 := by native_decide
example : power 0 0 = 1 := by native_decide
example : power 0 7 = 0 := by native_decide
example : power 5 0 = 1 := by native_decide
example : prog 2 3 = .ok 8 := by native_decide
example : prog 0 0 = .ok 1 := by native_decide
example : prog (-1) 2 = .error (valueError (-1) 2) := by native_decide
example : prog 2 (-1) = .error (valueError 2 (-1)) := by native_decide

#eval prog 2 3
#eval prog 0 0
#eval prog (-1) 2
#eval prog 2 (-1)

/-! ## Precondition -/

def Pre (base exponent : Int) : Prop := 0 ≤ base ∧ 0 ≤ exponent

/-! ## Properties and their proofs -/

def power_spec_prop (base exponent : Nat) : Prop :=
  power base exponent = base ^ exponent

theorem power_spec_thm (base exponent : Nat) : power_spec_prop base exponent := by
  unfold power_spec_prop
  induction exponent with
  | zero => rfl
  | succ exponent ih => simp [power, pow_succ, ih]

def zero_exponent_prop (base : Nat) : Prop := power base 0 = 1

theorem zero_exponent_thm (base : Nat) : zero_exponent_prop base := by
  rfl

def zero_base_prop (exponent : Nat) : Prop :=
  0 < exponent → power 0 exponent = 0

theorem zero_base_thm (exponent : Nat) : zero_base_prop exponent := by
  unfold zero_base_prop
  intro h
  cases exponent with
  | zero => omega
  | succ exponent => simp [power]

def successor_prop (base exponent : Nat) : Prop :=
  power base (exponent + 1) = power base exponent * base

theorem successor_thm (base exponent : Nat) : successor_prop base exponent := by
  rfl

def valid_result_prop (base exponent : Int) : Prop :=
  prog base exponent = .ok (base.toNat ^ exponent.toNat)

theorem valid_result_thm (base exponent : Int) (h : Pre base exponent) :
    valid_result_prop base exponent := by
  have h' : 0 ≤ base ∧ 0 ≤ exponent := h
  simp only [valid_result_prop, prog, if_pos h', Except.ok.injEq]
  exact power_spec_thm base.toNat exponent.toNat

def rejection_prop (base exponent : Int) : Prop :=
  ¬ Pre base exponent → prog base exponent = .error (valueError base exponent)

theorem rejection_thm (base exponent : Int) : rejection_prop base exponent := by
  unfold rejection_prop
  intro h
  have h' : ¬ (0 ≤ base ∧ 0 ≤ exponent) := h
  simp [prog, h']

/-! ## Postcondition -/

/-- The returned value is the mathematical power, with both boundary cases explicit. -/
def Post_prop (base exponent : Int) : Prop :=
  valid_result_prop base exponent ∧
  (exponent = 0 → prog base exponent = .ok 1) ∧
  (base = 0 ∧ 0 < exponent → prog base exponent = .ok 0)

/-! ## Property-based tests

Each test enumerates a domain rather than checking one fixed input. The signed
input tests include negative bases, negative exponents, and all boundary cases.
Their predicates below are executable forms of the corresponding properties.
-/

-- PBT: power_spec_prop.
example : (List.range 13).all (fun b => (List.range 13).all
    (fun e => decide (power b e = b ^ e))) = true := by native_decide

-- PBT: zero_exponent_prop.
example : (List.range 101).all (fun b => decide (power b 0 = 1)) = true := by
  native_decide

-- PBT: zero_base_prop, including the vacuous zero-exponent case.
example : (List.range 101).all
    (fun e => decide (0 < e → power 0 e = 0)) = true := by native_decide

-- PBT: successor_prop.
example : (List.range 13).all (fun b => (List.range 13).all
    (fun e => decide (power b (e + 1) = power b e * b))) = true := by native_decide

-- Integer samples from -3 through 12.
def signedSamples : List Int := (List.range 16).map (fun n => (n : Int) - 3)

-- PBT: valid_result_prop under precisely its precondition.
example : signedSamples.all (fun b => signedSamples.all (fun e =>
    decide ((0 ≤ b ∧ 0 ≤ e) → prog b e = .ok (b.toNat ^ e.toNat)))) = true := by
  native_decide

-- PBT: rejection_prop, checking all invalid pairs in the sampled domain.
example : signedSamples.all (fun b => signedSamples.all (fun e =>
    decide (¬ (0 ≤ b ∧ 0 ≤ e) → prog b e = .error (valueError b e)))) = true := by
  native_decide

-- PBT: the full Post_prop under Pre, not merely its main equality.
example : signedSamples.all (fun b => signedSamples.all (fun e =>
    decide ((0 ≤ b ∧ 0 ≤ e) →
      prog b e = .ok (b.toNat ^ e.toNat) ∧
      (e = 0 → prog b e = .ok 1) ∧
      (b = 0 ∧ 0 < e → prog b e = .ok 0)))) = true := by native_decide

#eval (List.range 13).all (fun b => (List.range 13).all
  (fun e => decide (power b e = b ^ e)))

/-! ## Correctness -/

theorem correctness (base exponent : Int) : Pre base exponent → Post_prop base exponent := by
  intro h
  refine ⟨valid_result_thm base exponent h, ?_, ?_⟩
  · intro he
    subst exponent
    simpa [valid_result_prop] using valid_result_thm base 0 h
  · rintro ⟨hb, he⟩
    subst base
    have hn : exponent.toNat ≠ 0 := by omega
    simpa [valid_result_prop, zero_pow hn] using valid_result_thm 0 exponent h

/-! ## Imperative implementation -/

def powerImperative (base exponent : Nat) : Nat := Id.run do
  if exponent == 0 then
    return 1
  let mut result := 1
  for _ in List.range exponent do
    result := result * base
  return result

def progImperative (base exponent : Int) : Except String Nat :=
  if 0 ≤ base ∧ 0 ≤ exponent then
    .ok (powerImperative base.toNat exponent.toNat)
  else
    .error (valueError base exponent)

/-! ## Imperative tests -/

example : powerImperative 2 3 = 8 := by native_decide
example : powerImperative 0 0 = 1 := by native_decide
example : powerImperative 0 9 = 0 := by native_decide
example : progImperative (-1) 2 = .error (valueError (-1) 2) := by native_decide
example : progImperative 2 (-1) = .error (valueError 2 (-1)) := by native_decide
example : signedSamples.all (fun b => signedSamples.all
    (fun e => decide (prog b e = progImperative b e))) = true := by native_decide

#eval progImperative 2 3
#eval progImperative 0 0
#eval progImperative (-1) 2
#eval progImperative 2 (-1)

/-! ## Equivalence -/

/-- After processing a list of iterations, the accumulator has been multiplied
by the base once per list element. The iteration indices are irrelevant. -/
theorem foldl_power (base : Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl (fun result _ => result * base) acc = acc * power base xs.length := by
  induction xs generalizing acc with
  | nil => simp [power]
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_cons, power]
    ac_rfl

theorem power_equivalence (base exponent : Nat) :
    power base exponent = powerImperative base exponent := by
  by_cases he : exponent = 0
  · subst exponent
    rfl
  · simp [powerImperative, he, foldl_power]

theorem prog_equivalence (base exponent : Int) :
    prog base exponent = progImperative base exponent := by
  simp only [prog, progImperative, power_equivalence]

end MyPower
