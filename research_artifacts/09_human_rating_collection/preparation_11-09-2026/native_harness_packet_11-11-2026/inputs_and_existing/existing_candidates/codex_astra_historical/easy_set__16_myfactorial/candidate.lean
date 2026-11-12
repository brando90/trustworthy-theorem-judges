import Mathlib

/-!
# Factorial with Python-style input validation

`factorial` computes the exact natural-number factorial by recursion. `prog`
models the Python entry point, returning `Except.error ValueError.invalidInput`
on a negative integer or a non-integer. The exception class is preserved; its
diagnostic string is abstracted away. `Input` distinguishes integers, floats,
booleans, and all remaining Python values (represented by a descriptive label).
Booleans count as integers, as they do for Python's `isinstance(n, int)`.

All arithmetic on accepted inputs is unbounded and exact. Floats are retained
only as rejected inputs, so no floating-point arithmetic model is needed.
The final implementation uses a mutable accumulator over `1, ..., n`, with a
proof of equivalence for every input, including precondition violations.
-/

namespace MyFactorial

/-! ## Functional implementation -/

inductive Input where
  | integer (value : Int)
  | floating (value : Float)
  | boolean (value : Bool)
  | other (description : String)
  deriving Repr

inductive ValueError where
  | invalidInput
  deriving DecidableEq, Repr

abbrev Result := Except ValueError Nat

deriving instance DecidableEq for Except

/-- The integer value used by Python's precondition, including `bool` values. -/
def asInt : Input → Option Int
  | .integer n => some n
  | .boolean false => some 0
  | .boolean true => some 1
  | .floating _ | .other _ => none

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => factorial n * (n + 1)

def prog (input : Input) : Result :=
  match asInt input with
  | none => .error .invalidInput
  | some n =>
      if 0 ≤ n then .ok (factorial n.toNat) else .error .invalidInput

/-! ## Unit tests -/

example : prog (.integer 3) = .ok 6 := by native_decide
example : prog (.integer 0) = .ok 1 := by native_decide
example : prog (.integer 1) = .ok 1 := by native_decide
example : prog (.integer 10) = .ok 3628800 := by native_decide
example : prog (.integer (-1)) = .error .invalidInput := by native_decide
example : prog (.floating 3.14) = .error .invalidInput := by native_decide
example : prog (.floating 3.0) = .error .invalidInput := by native_decide
example : prog (.boolean false) = .ok 1 := by native_decide
example : prog (.boolean true) = .ok 1 := by native_decide
example : prog (.other "None") = .error .invalidInput := by native_decide

#eval prog (.integer 3)
#eval prog (.integer 0)
#eval prog (.integer (-1))
#eval prog (.floating 3.14)

/-! ## Precondition -/

/-- Exactly the Python predicate `isinstance(n, int) and n >= 0`. -/
def Pre (input : Input) : Prop :=
  match asInt input with
  | some n => 0 ≤ n
  | none => False

/-! ## Properties and proofs -/

def factorial_prop (n : Nat) : Prop := factorial n = Nat.factorial n

theorem factorial_thm (n : Nat) : factorial_prop n := by
  unfold factorial_prop
  induction n with
  | zero => rfl
  | succ n ih => simp [factorial, Nat.factorial_succ, ih, Nat.mul_comm]

def recurrence_prop (n : Nat) : Prop :=
  factorial (n + 1) = (n + 1) * factorial n

theorem recurrence_thm (n : Nat) : recurrence_prop n := by
  simp [recurrence_prop, factorial, Nat.mul_comm]

def positive_prop (n : Nat) : Prop := 0 < factorial n

theorem positive_thm (n : Nat) : positive_prop n := by
  unfold positive_prop
  rw [factorial_thm n]
  exact Nat.factorial_pos n

/-- Every accepted input returns its mathematical factorial. -/
def accepted_prop (input : Input) : Prop :=
  match asInt input with
  | none => True
  | some n => 0 ≤ n → prog input = .ok (Nat.factorial n.toNat)

theorem accepted_thm (input : Input) : accepted_prop input := by
  unfold accepted_prop
  cases h : asInt input with
  | none => trivial
  | some n =>
      intro hn
      simp only [prog, h, if_pos hn]
      exact congrArg Except.ok (factorial_thm n.toNat)

/-- A ValueError occurs exactly when the Python precondition fails. -/
def rejected_prop (input : Input) : Prop :=
  prog input = .error .invalidInput ↔ ¬ Pre input

theorem rejected_thm (input : Input) : rejected_prop input := by
  unfold rejected_prop
  cases h : asInt input with
  | none => simp [prog, Pre, h]
  | some n =>
      by_cases hn : 0 ≤ n <;> simp [prog, Pre, h, hn]

def zero_prop (input : Input) : Prop :=
  asInt input = some 0 → prog input = .ok 1

theorem zero_thm (input : Input) : zero_prop input := by
  intro h
  simp [prog, h, factorial]

def one_prop (input : Input) : Prop :=
  asInt input = some 1 → prog input = .ok 1

theorem one_thm (input : Input) : one_prop input := by
  intro h
  simp [prog, h, factorial]

/-! ## Postcondition -/

def Post_prop (input : Input) : Prop :=
  accepted_prop input ∧ rejected_prop input ∧ zero_prop input ∧ one_prop input ∧
    match asInt input with
    | none => True
    | some n => 0 ≤ n →
        factorial_prop n.toNat ∧ recurrence_prop n.toNat ∧ positive_prop n.toNat

/-! ## Property-based tests

These are exhaustive bounded checks of the executable forms of the properties.
The mixed-input sample includes every integer from -32 through 64, both booleans,
many floats (including integral floats), and representatives of other types.
The zero and one properties are tested for both their integer and boolean
encodings. All seven properties and the entire postcondition are checked.
-/

def testInputs : List Input :=
  (List.range 97).map (fun n => .integer (Int.ofNat n - 32)) ++
  [.boolean false, .boolean true] ++
  (List.range 33).map (fun n => .floating (Float.ofNat n)) ++
  [.floating 3.14, .floating (-1.5), .other "None", .other "str", .other "list"]

-- PBT: factorial_prop.
example : (List.range 65).all
    (fun n => decide (factorial n = Nat.factorial n)) = true := by native_decide

-- PBT: recurrence_prop.
example : (List.range 65).all
    (fun n => decide (factorial (n + 1) = (n + 1) * factorial n)) = true := by
  native_decide

-- PBT: positive_prop.
example : (List.range 65).all
    (fun n => decide (0 < factorial n)) = true := by native_decide

def acceptedCheck (input : Input) : Bool :=
  match asInt input with
  | none => true
  | some n => decide (0 ≤ n → prog input = .ok (Nat.factorial n.toNat))

def rejectedCheck (input : Input) : Bool :=
  match asInt input with
  | none => decide (prog input = .error .invalidInput)
  | some n => decide ((prog input = .error .invalidInput) ↔ ¬ 0 ≤ n)

def zeroCheck (input : Input) : Bool :=
  decide (asInt input = some 0 → prog input = .ok 1)

def oneCheck (input : Input) : Bool :=
  decide (asInt input = some 1 → prog input = .ok 1)

-- PBT: accepted_prop.
example : testInputs.all acceptedCheck = true := by native_decide
-- PBT: rejected_prop.
example : testInputs.all rejectedCheck = true := by native_decide
-- PBT: zero_prop.
example : testInputs.all zeroCheck = true := by native_decide
-- PBT: one_prop.
example : testInputs.all oneCheck = true := by native_decide

def postCheck (input : Input) : Bool :=
  acceptedCheck input && rejectedCheck input && zeroCheck input && oneCheck input &&
    match asInt input with
    | none => true
    | some n => decide (0 ≤ n →
        factorial n.toNat = Nat.factorial n.toNat ∧
        factorial (n.toNat + 1) = (n.toNat + 1) * factorial n.toNat ∧
        0 < factorial n.toNat)

-- PBT: Post_prop, checking the complete conjunction for every sampled input.
example : testInputs.all postCheck = true := by native_decide
#eval testInputs.all postCheck

/-! ## Correctness -/

theorem correctness_thm (input : Input) : Pre input → Post_prop input := by
  intro _
  refine ⟨accepted_thm input, rejected_thm input, zero_thm input, one_thm input, ?_⟩
  cases h : asInt input with
  | none => trivial
  | some n =>
      intro _
      exact ⟨factorial_thm n.toNat, recurrence_thm n.toNat, positive_thm n.toNat⟩

/-! ## Imperative implementation -/

/-- `List.range' 1 n` is Python's `range(1, n + 1)`. -/
def factorialImperative (n : Nat) : Nat := Id.run do
  if n == 0 then
    return 1
  let mut result := 1
  for i in List.range' 1 n do
    result := result * i
  return result

def progImperative (input : Input) : Result := Id.run do
  match asInt input with
  | none => return .error .invalidInput
  | some n =>
      if n < 0 then
        return .error .invalidInput
      return .ok (factorialImperative n.toNat)

/-! ## Imperative tests -/

example : progImperative (.integer 3) = .ok 6 := by native_decide
example : progImperative (.integer 0) = .ok 1 := by native_decide
example : progImperative (.integer 1) = .ok 1 := by native_decide
example : progImperative (.integer (-1)) = .error .invalidInput := by native_decide
example : progImperative (.floating 3.14) = .error .invalidInput := by native_decide
example : progImperative (.boolean true) = .ok 1 := by native_decide

#eval progImperative (.integer 3)
#eval progImperative (.integer 0)
#eval progImperative (.floating 3.14)

example : (List.range 65).all
    (fun n => decide (factorial n = factorialImperative n)) = true := by native_decide
example : testInputs.all
    (fun input => decide (prog input = progImperative input)) = true := by native_decide

/-! ## Equivalence proofs -/

private theorem range_product (n : Nat) : (List.range' 1 n).prod = factorial n := by
  induction n with
  | zero => simp [factorial]
  | succ n ih => simp [List.range'_concat, factorial, ih, Nat.add_comm]

theorem factorial_equivalence_thm (n : Nat) : factorial n = factorialImperative n := by
  cases n with
  | zero => rfl
  | succ n =>
      simpa [factorialImperative, ← List.prod_eq_foldl] using (range_product (n + 1)).symm

theorem equivalence_thm (input : Input) : prog input = progImperative input := by
  cases h : asInt input with
  | none => simp [prog, progImperative, h]
  | some n =>
      by_cases hn : 0 ≤ n
      · simp [prog, progImperative, h, hn, Int.not_lt.mpr hn, factorial_equivalence_thm]
      · have hneg : n < 0 := Int.lt_of_not_ge hn
        simp [prog, progImperative, h, hn, hneg]

end MyFactorial
