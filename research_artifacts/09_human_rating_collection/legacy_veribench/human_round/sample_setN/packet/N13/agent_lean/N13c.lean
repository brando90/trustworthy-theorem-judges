import Mathlib

/-!
# MyFactorial: Python factorial with checked inputs

`factorial` is the exact, unbounded natural-number computation. `prog` retains
Python's input check: integers must be nonnegative, and floats (even integral
ones) and all other non-integer objects are rejected. Python booleans are
integer instances, so they are interpreted as 0 and 1. `other` represents any
remaining non-integer object, labelled by a description.

A returned `Nat` represents the nonnegative Python integer result. `Except`
records the observable ValueError exception class; diagnostic message text is
not part of this interface. No floating-point arithmetic is used to compute a
factorial. The imperative version multiplies 1, ..., n in ascending order.
-/

namespace MyFactorial

/-! ## Functional implementation -/

inductive Input where
  | int (value : Int)
  | float (value : Float)
  | bool (value : Bool)
  | other (description : String)
  deriving Repr

def Input.asInt : Input → Option Int
  | .int z => some z
  | .bool b => some (if b then 1 else 0)
  | .float _ => none
  | .other _ => none

inductive Error where
  | valueError
  deriving Repr, DecidableEq, BEq

deriving instance DecidableEq for Except

abbrev Result := Except Error Nat

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => factorial n * (n + 1)

/-- Executable translation of Python's `pre`. -/
def pre (x : Input) : Bool :=
  match x.asInt with
  | none => false
  | some z => decide (0 ≤ z)

def prog (x : Input) : Result :=
  match x.asInt with
  | none => .error .valueError
  | some z => if 0 ≤ z then .ok (factorial z.toNat) else .error .valueError

/-! ## Unit tests -/

example : prog (.int 3) = .ok 6 := by native_decide
example : prog (.int 0) = .ok 1 := by native_decide
example : prog (.int 1) = .ok 1 := by native_decide
example : prog (.int 10) = .ok 3628800 := by native_decide
example : prog (.int (-1)) = .error .valueError := by native_decide
example : prog (.float 3.14) = .error .valueError := by native_decide
example : prog (.float 3.0) = .error .valueError := by native_decide
example : prog (.bool false) = .ok 1 := by native_decide
example : prog (.bool true) = .ok 1 := by native_decide
example : prog (.other "None") = .error .valueError := by native_decide

#eval prog (.int 3)
#eval prog (.int 0)
#eval prog (.int (-1))
#eval prog (.float 3.14)

/-! ## Precondition -/

/-- Exactly the integer-instance/nonnegative test, with no bound on magnitude. -/
def Pre (x : Input) : Prop :=
  match x.asInt with
  | none => False
  | some z => 0 ≤ z

instance (x : Input) : Decidable (Pre x) := by
  unfold Pre
  cases x.asInt <;> infer_instance

/-! ## Properties and kernel-checked proofs -/

def pre_prop (x : Input) : Prop := pre x = true ↔ Pre x

theorem pre_thm (x : Input) : pre_prop x := by
  unfold pre_prop pre Pre
  cases x.asInt <;> simp

/-- Independent specification in terms of Mathlib's factorial. -/
def factorial_spec_prop (n : Nat) : Prop := factorial n = Nat.factorial n

theorem factorial_spec_thm (n : Nat) : factorial_spec_prop n := by
  change factorial n = Nat.factorial n
  induction n with
  | zero => rfl
  | succ n ih => simp [factorial, Nat.factorial_succ, ih, Nat.mul_comm]

def factorial_step_prop (n : Nat) : Prop :=
  factorial (n + 1) = (n + 1) * factorial n

theorem factorial_step_thm (n : Nat) : factorial_step_prop n := by
  simp [factorial_step_prop, factorial, Nat.mul_comm]

def factorial_positive_prop (n : Nat) : Prop := 0 < factorial n

theorem factorial_positive_thm (n : Nat) : factorial_positive_prop n := by
  change 0 < factorial n
  rw [show factorial n = Nat.factorial n from factorial_spec_thm n]
  exact Nat.factorial_pos n

/-- Every admissible input returns exactly its factorial. -/
def value_prop (x : Input) (out : Result) : Prop :=
  ∀ z : Int, x.asInt = some z → 0 ≤ z → out = .ok (Nat.factorial z.toNat)

theorem value_thm (x : Input) : value_prop x (prog x) := by
  intro z hx hz
  simp only [prog, hx, if_pos hz]
  exact congrArg Except.ok (factorial_spec_thm z.toNat)

/-- Every precondition violation raises ValueError, not an arbitrary result. -/
def error_prop (x : Input) (out : Result) : Prop :=
  ¬ Pre x → out = .error .valueError

theorem error_thm (x : Input) : error_prop x (prog x) := by
  intro h
  cases hx : x.asInt with
  | none => simp [prog, hx]
  | some z =>
    have hz : ¬ 0 ≤ z := by simpa [Pre, hx] using h
    simp [prog, hx, hz]

/-- Any successful result is strictly positive (in particular nonnegative). -/
def positive_prop (out : Result) : Prop :=
  ∀ r : Nat, out = .ok r → 0 < r

theorem positive_thm (x : Input) : positive_prop (prog x) := by
  intro r hr
  cases hx : x.asInt with
  | none => simp [prog, hx] at hr
  | some z =>
    by_cases hz : 0 ≤ z
    · have heq : factorial z.toNat = r := by simpa [prog, hx, hz] using hr
      rw [← heq]
      exact factorial_positive_thm z.toNat
    · simp [prog, hx, hz] at hr

theorem zero_thm : prog (.int 0) = .ok 1 := by rfl

theorem one_thm : prog (.int 1) = .ok 1 := by rfl

/-! ## Postcondition -/

/-- A total contract: exact value on valid inputs, error on invalid inputs,
and positivity of every successful result. -/
def Post_prop (x : Input) (out : Result) : Prop :=
  value_prop x out ∧ error_prop x out ∧ positive_prop out

/-! ## Property-based tests

The tagged input type has no automatic sampler. These bounded tests include
all integers from -10 through 30 and representatives of every non-integer tag.
Checks of quantified output properties use their equivalent executable forms:
`asInt` has at most one value, and `out` has at most one successful result.
-/

def testInputs : List Input :=
  (List.range 41).map (fun n => .int ((n : Int) - 10)) ++
    [.float 3.14, .float 3.0, .float (-2.5), .float 0.0,
     .bool false, .bool true, .other "None", .other "string"]

def valueCheck (x : Input) (out : Result) : Bool :=
  match x.asInt with
  | none => true
  | some z => if 0 ≤ z then decide (out = .ok (Nat.factorial z.toNat)) else true

def errorCheck (x : Input) (out : Result) : Bool :=
  if Pre x then true else decide (out = .error .valueError)

def positiveCheck (out : Result) : Bool :=
  match out with
  | .ok r => decide (0 < r)
  | .error _ => true

-- PBT for pre_prop.
example : testInputs.all (fun x => decide (pre x = true ↔ Pre x)) = true := by
  native_decide
-- PBT for factorial_spec_prop.
example : (List.range 31).all (fun n => decide (factorial n = Nat.factorial n)) = true := by
  native_decide
-- PBT for factorial_step_prop.
example : (List.range 31).all
    (fun n => decide (factorial (n + 1) = (n + 1) * factorial n)) = true := by
  native_decide
-- PBT for factorial_positive_prop.
example : (List.range 31).all (fun n => decide (0 < factorial n)) = true := by
  native_decide
-- PBT for value_prop.
example : testInputs.all (fun x => valueCheck x (prog x)) = true := by native_decide
-- PBT for error_prop.
example : testInputs.all (fun x => errorCheck x (prog x)) = true := by native_decide
-- PBT for positive_prop.
example : testInputs.all (fun x => positiveCheck (prog x)) = true := by native_decide
-- PBT for the entire Post_prop conjunction.
example : testInputs.all (fun x =>
    valueCheck x (prog x) && errorCheck x (prog x) && positiveCheck (prog x)) = true := by
  native_decide

#eval testInputs.all (fun x =>
  valueCheck x (prog x) && errorCheck x (prog x) && positiveCheck (prog x))

/-! ## Correctness -/

theorem correctness_thm (x : Input) : Pre x → Post_prop x (prog x) := by
  intro _
  exact ⟨value_thm x, error_thm x, positive_thm x⟩

/-- The contract also covers rejected inputs, without assuming Pre. -/
theorem total_correctness_thm (x : Input) : Post_prop x (prog x) := by
  exact ⟨value_thm x, error_thm x, positive_thm x⟩

/-! ## Imperative implementation -/

/-- Python's multiplication loop; `List.range' 1 n` is `[1, ..., n]`. -/
def factorialImperative (n : Nat) : Nat := Id.run do
  if n == 0 then
    return 1
  let mut result := 1
  for i in List.range' 1 n do
    result := result * i
  return result

def progImperative (x : Input) : Result := Id.run do
  match x.asInt with
  | none => return .error .valueError
  | some z =>
    if z < 0 then
      return .error .valueError
    return .ok (factorialImperative z.toNat)

/-! ## Imperative tests -/

example : progImperative (.int 3) = .ok 6 := by native_decide
example : progImperative (.int 0) = .ok 1 := by native_decide
example : progImperative (.int 1) = .ok 1 := by native_decide
example : progImperative (.int 10) = .ok 3628800 := by native_decide
example : progImperative (.int (-1)) = .error .valueError := by native_decide
example : progImperative (.float 3.14) = .error .valueError := by native_decide
example : testInputs.all (fun x => decide (prog x = progImperative x)) = true := by
  native_decide

#eval progImperative (.int 3)
#eval progImperative (.int 0)
#eval progImperative (.int (-1))
#eval progImperative (.float 3.14)

/-! ## Functional–imperative equivalence -/

/-- After multiplying the first n positive integers, the accumulator is n!. -/
theorem fold_range_factorial (n : Nat) :
    (List.range' 1 n).foldl (fun acc i => acc * i) 1 = factorial n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [List.range'_concat, List.foldl_append, ih, factorial, Nat.add_comm]

/-- The actual mutable ascending loop computes the recursive function. -/
theorem factorial_equivalence_thm (n : Nat) :
    factorial n = factorialImperative n := by
  by_cases hn : n = 0
  · subst n
    rfl
  · simp [factorialImperative, hn, List.forIn_pure_yield_eq_foldl,
      fold_range_factorial]

/-- Total equivalence, including negative integers and all non-integer inputs. -/
theorem equivalence_thm (x : Input) : prog x = progImperative x := by
  cases hx : x.asInt with
  | none => simp [prog, progImperative, hx]
  | some z =>
    by_cases hz : 0 ≤ z
    · have hn : ¬ z < 0 := not_lt.mpr hz
      simp [prog, progImperative, hx, hz, hn, factorial_equivalence_thm]
    · have hn : z < 0 := lt_of_not_ge hz
      simp [prog, progImperative, hx, hz, hn]

/-- The same total specification therefore holds for the imperative program. -/
theorem imperative_correctness_thm (x : Input) :
    Post_prop x (progImperative x) := by
  rw [← equivalence_thm x]
  exact total_correctness_thm x

end MyFactorial
