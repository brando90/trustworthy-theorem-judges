import Mathlib

/-!
# 16_MyFactorial — factorial of a natural number (VeriBench translation)

The Python source program is

```python
def pre(n):
    return isinstance(n, int) and n >= 0

def prog(n):
    if not pre(n):
        raise ValueError(f"Input must be a non-negative integer (got n={n})")
    if n == 0:
        return 1
    result = 1
    for i in range(1, n + 1):
        result *= i
    return result
```

## Modelling decisions

* `Nat` is the natural home of a factorial.  The Python argument is an `int`, so the functional
  implementation `prog` takes an `Int`, guards on `0 ≤ n` and returns `fact n.toNat`.
* `ValueError` is modelled by the constructor `Outcome.valueError`, which carries exactly the
  message the Python program builds (`errMsg`).  `Outcome.raised` is `true` precisely when the
  run raised, i.e. when the precondition was violated.
* Python is dynamically typed and the reference test-suite feeds the float `3.14` to `prog`.
  The inductive type `PyVal` models the two argument shapes that occur (`int` and `float`);
  `PreVal` / `progVal` reproduce the `isinstance(n, int)` half of the precondition, so every
  `flt` argument is rejected, exactly as in Python.
* `factImp` / `progImp` are the imperative counterparts written with `Id.run do` and a mutable
  accumulator, mirroring `result = 1; for i in range(1, n+1): result *= i`.  `loopProd` exposes
  that accumulation loop as a function of the index list so it can be analysed by induction.
* `fact n` is proved equal to Mathlib's `Nat.factorial n`, which ties the executable model to
  the mathematical factorial.
-/

namespace «16_MyFactorial»

/-! ## 1. Implementation (functional definition) -/

/-- Result of running `prog`: either the returned value, or a raised `ValueError` together with
its message. -/
inductive Outcome where
  | ok : Nat → Outcome
  | valueError : String → Outcome
  deriving DecidableEq, Repr

/-- `true` iff the evaluation raised (i.e. produced a `ValueError`). -/
def Outcome.raised : Outcome → Bool
  | .ok _ => false
  | .valueError _ => true

/-- A Python-level argument value: the reference test-suite feeds `prog` both `int`s and a
`float` (`3.14`), and `pre` distinguishes them with `isinstance`. -/
inductive PyVal where
  | int : Int → PyVal
  | flt : Float → PyVal
  deriving Repr

/-- The message of the `ValueError` raised by the Python program. -/
def errMsg (n : Int) : String := s!"Input must be a non-negative integer (got n={n})"

/-- The same message for a non-`int` (float) argument. -/
def errMsgFlt (x : Float) : String := s!"Input must be a non-negative integer (got n={x})"

/-- `n!`, defined by the recursion that the Python loop computes:
`fact 0 = 1` and `fact (n+1) = (n+1) * fact n`. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- The functional implementation of `prog` on an `int` argument: guard, then return `n!`. -/
def prog (n : Int) : Outcome :=
  if 0 ≤ n then .ok (fact n.toNat) else .valueError (errMsg n)

/-- The functional implementation of `prog` on an arbitrary Python-level argument: a `float`
violates `isinstance(n, int)` and therefore always raises. -/
def progVal : PyVal → Outcome
  | .int n => prog n
  | .flt x => .valueError (errMsgFlt x)

/-! ## 2. Unit tests -/

-- Basic unit test (Python: `candidate(3) == 6`)
example : prog 3 = .ok 6 := by native_decide
example : progVal (.int 3) = .ok 6 := by native_decide
example : fact 3 = 6 := by native_decide

-- Edge unit test (Python: `candidate(0) == 1`)
example : prog 0 = .ok 1 := by native_decide
example : fact 0 = 1 := by native_decide
example : fact 1 = 1 := by native_decide

-- More values
example : prog 5 = .ok 120 := by native_decide
example : prog 10 = .ok 3628800 := by native_decide

-- Negative tests: pre-violations must raise `ValueError`
example : (prog (-1)).raised = true := by native_decide
example : prog (-1) = .valueError (errMsg (-1)) := by native_decide
example : (progVal (.flt 3.14)).raised = true := by native_decide
example : (progVal (.flt (-1.0))).raised = true := by native_decide

#eval prog 6
#eval prog (-2)
#eval progVal (.int 7)
#eval progVal (.flt 3.14)
#eval fact 12

/-! ## 3. Pre-condition -/

/-- `pre(n)`: the input is a (non-negative) integer.  On the `Int` layer the `isinstance` part
is discharged by the type, leaving `n ≥ 0`. -/
def Pre (n : Int) : Prop := 0 ≤ n

instance (n : Int) : Decidable (Pre n) := decidable_of_iff (0 ≤ n) (by simp [Pre])

/-- Executable (Boolean) form of the guard used by `prog`. -/
def preGuard (n : Int) : Bool := decide (Pre n)

/-- `pre` on an arbitrary Python-level value: `isinstance(n, int) and n >= 0`.  A `float` never
satisfies it. -/
def PreVal : PyVal → Prop
  | .int n => Pre n
  | .flt _ => False

instance : DecidablePred PreVal
  | .int n => inferInstanceAs (Decidable (0 ≤ n))
  | .flt _ => isFalse (fun h => h)

/-! ## 4. Properties and their proofs -/

def fact_zero_prop : Prop := fact 0 = 1

def fact_one_prop : Prop := fact 1 = 1

def fact_succ_prop : Prop := ∀ n : Nat, fact (n + 1) = (n + 1) * fact n

def fact_pos_prop : Prop := ∀ n : Nat, 0 < fact n

def fact_mono_prop : Prop := ∀ n m : Nat, n ≤ m → fact n ≤ fact m

def fact_eq_factorial_prop : Prop := ∀ n : Nat, fact n = Nat.factorial n

def pre_iff_prop : Prop := ∀ n : Int, Pre n ↔ 0 ≤ n

def preGuard_sound_prop : Prop := ∀ n : Int, preGuard n = true ↔ Pre n

def preVal_flt_prop : Prop := ∀ x : Float, ¬ PreVal (.flt x)

def prog_ok_prop : Prop := ∀ n : Int, Pre n → prog n = .ok (fact n.toNat)

def prog_error_prop : Prop := ∀ n : Int, ¬ Pre n → prog n = .valueError (errMsg n)

def prog_no_raise_prop : Prop := ∀ n : Int, Pre n → (prog n).raised = false

def prog_value_prop : Prop :=
  ∀ n : Int, Pre n → ∀ v : Nat, prog n = .ok v → v = Nat.factorial n.toNat

def prog_nat_prop : Prop := ∀ n : Nat, prog (n : Int) = .ok (Nat.factorial n)

def progVal_int_prop : Prop := ∀ n : Int, progVal (.int n) = prog n

def progVal_flt_prop : Prop := ∀ x : Float, (progVal (.flt x)).raised = true

theorem fact_zero_thm : fact_zero_prop := rfl

theorem fact_one_thm : fact_one_prop := rfl

theorem fact_succ_thm : fact_succ_prop := fun _ => rfl

theorem fact_pos_thm : fact_pos_prop := by
  intro n
  induction n with
  | zero => exact Nat.one_pos
  | succ n ih =>
      have e : fact (n + 1) = (n + 1) * fact n := rfl
      rw [e]
      exact Nat.mul_pos (Nat.succ_pos n) ih

theorem fact_le_add_thm (n k : Nat) : fact n ≤ fact (n + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have e : n + (k + 1) = (n + k) + 1 := by omega
      rw [e]
      have e2 : fact ((n + k) + 1) = ((n + k) + 1) * fact (n + k) := rfl
      rw [e2]
      exact Nat.le_trans ih (Nat.le_mul_of_pos_left (fact (n + k)) (Nat.succ_pos (n + k)))

theorem fact_mono_thm : fact_mono_prop := by
  intro n m h
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
  rw [hk]
  exact fact_le_add_thm n k

theorem fact_eq_factorial_thm : fact_eq_factorial_prop := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      have e1 : fact (n + 1) = (n + 1) * fact n := rfl
      have e2 : Nat.factorial (n + 1) = (n + 1) * Nat.factorial n := Nat.factorial_succ n
      rw [e1, e2, ih]

theorem pre_iff_thm : pre_iff_prop := fun _ => Iff.rfl

theorem preGuard_sound_thm : preGuard_sound_prop := by
  intro n
  rw [preGuard, decide_eq_true_iff]

theorem preVal_flt_thm : preVal_flt_prop := by
  intro x
  simp [PreVal]

theorem prog_ok_thm : prog_ok_prop := by
  intro n h
  have h' : 0 ≤ n := h
  simp [prog, h']

theorem prog_error_thm : prog_error_prop := by
  intro n h
  have h' : ¬ (0 ≤ n) := h
  simp [prog, h']

theorem prog_no_raise_thm : prog_no_raise_prop := by
  intro n h
  rw [prog_ok_thm n h]
  rfl

theorem prog_value_thm : prog_value_prop := by
  intro n h v hv
  rw [prog_ok_thm n h] at hv
  have hinj : fact n.toNat = v := Outcome.ok.inj hv
  rw [← hinj, fact_eq_factorial_thm]

theorem prog_nat_thm : prog_nat_prop := by
  intro n
  have h : Pre (n : Int) := by simp [Pre]
  have h1 : prog (n : Int) = .ok (fact (n : Int).toNat) := prog_ok_thm (n : Int) h
  have h2 : (n : Int).toNat = n := by simp
  rw [h1, h2, fact_eq_factorial_thm]

theorem progVal_int_thm : progVal_int_prop := fun _ => rfl

theorem progVal_flt_thm : progVal_flt_prop := fun _ => rfl

/-! ## 5. Post-condition -/

/-- The post-condition of `prog`: under the precondition the result is `ok` and carries exactly
`n.toNat !` (a positive number); when the precondition is violated the run raised a
`ValueError`. -/
def Post_prop (n : Int) (out : Outcome) : Prop :=
  (Pre n → ∃ v : Nat, out = .ok v ∧ v = Nat.factorial n.toNat ∧ 0 < v) ∧
  (¬ Pre n → out.raised = true)

/-- The post-condition on the Python-value layer (it also covers the `isinstance` violation). -/
def PostVal_prop (v : PyVal) (out : Outcome) : Prop :=
  (PreVal v → ∃ n : Int, v = .int n ∧ out = .ok (Nat.factorial n.toNat)) ∧
  (¬ PreVal v → out.raised = true)

/-- Executable (Boolean) form of `Post_prop`; used by the property-based tests below. -/
def postBool (n : Int) (out : Outcome) : Bool :=
  if Pre n then
    match out with
    | .ok v => v == Nat.factorial n.toNat && decide (0 < v)
    | .valueError _ => false
  else
    out.raised

/-- Executable (Boolean) form of `PostVal_prop`. -/
def postValBool (v : PyVal) (out : Outcome) : Bool :=
  match v with
  | .int n => postBool n out
  | .flt _ => out.raised

/-- Executable (Boolean) form of `prog_value_prop`. -/
def valueBool (n : Int) : Bool :=
  match prog n with
  | .ok v => v == Nat.factorial n.toNat
  | .valueError _ => ! decide (Pre n)

/-! ## 6. Property-based tests -/

/-- Sample inputs for the bounded property-based tests. -/
def testNats : List Nat := List.range 40

def testInts : List Int := (List.range 41).map (fun i => (i : Int) - 20)

def testFloats : List Float := [-3.14, -1.0, -0.5, 0.0, 0.5, 1.0, 2.0, 3.14, 1e10, -1e10]

def testVals : List PyVal := testInts.map PyVal.int ++ testFloats.map PyVal.flt

-- PBT for `fact_zero_prop` and `fact_one_prop` (closed cases: exhaustive)
example : decide (fact 0 = 1) = true := by native_decide
example : decide (fact 1 = 1) = true := by native_decide
#eval Plausible.Testable.check (fact 0 = 1 ∧ fact 1 = 1)

-- PBT for `fact_succ_prop`
#eval Plausible.Testable.check (∀ n : Nat, fact (n + 1) = (n + 1) * fact n)
example : testNats.all (fun n => decide (fact (n + 1) = (n + 1) * fact n)) = true := by native_decide

-- PBT for `fact_pos_prop`
#eval Plausible.Testable.check (∀ n : Nat, 0 < fact n)
example : testNats.all (fun n => decide (0 < fact n)) = true := by native_decide

-- PBT for `fact_mono_prop`
#eval Plausible.Testable.check (∀ a b : Nat, a ≤ b → fact a ≤ fact b)
example : (List.range 25).all
    (fun i => (List.range 25).all (fun j => decide (i ≤ j → fact i ≤ fact j))) = true := by
  native_decide

-- PBT for `fact_eq_factorial_prop`
#eval Plausible.Testable.check (∀ n : Nat, fact n = Nat.factorial n)
example : testNats.all (fun n => decide (fact n = Nat.factorial n)) = true := by native_decide

-- PBT for `pre_iff_prop`
#eval Plausible.Testable.check (∀ n : Int, Pre n ↔ 0 ≤ n)
example : testInts.all (fun n => decide (Pre n ↔ 0 ≤ n)) = true := by native_decide

-- PBT for `preGuard_sound_prop`
#eval Plausible.Testable.check (∀ n : Int, preGuard n = true ↔ Pre n)
example : testInts.all (fun n => preGuard n == decide (Pre n)) = true := by native_decide

-- PBT for `preVal_flt_prop`
-- (Plausible has no `Sampler Float`, so this property is tested exhaustively on a bounded list)
example : testFloats.all (fun x => decide (¬ PreVal (.flt x))) = true := by native_decide
example : testInts.all (fun i => decide (PreVal (.int i) ↔ 0 ≤ i)) = true := by native_decide
example : testVals.all (fun v => decide (PreVal v) == match v with
    | .int n => decide (0 ≤ n)
    | .flt _ => false) = true := by native_decide

-- PBT for `prog_ok_prop`
#eval Plausible.Testable.check (∀ n : Nat, (prog (n : Int)).raised = false)
example : testInts.all (fun n => decide (Pre n → prog n = .ok (fact n.toNat))) = true := by
  native_decide

-- PBT for `prog_error_prop`
#eval Plausible.Testable.check (∀ n : Nat, (prog (-(n : Int) - 1)).raised = true)
example : testInts.all (fun n => decide (¬ Pre n → prog n = .valueError (errMsg n))) = true := by
  native_decide

-- PBT for `prog_no_raise_prop`
example : testInts.all (fun n => decide (Pre n → (prog n).raised = false)) = true := by
  native_decide

-- PBT for `prog_value_prop`
#eval Plausible.Testable.check (∀ n : Int, valueBool n = true)
example : testInts.all valueBool = true := by native_decide

-- PBT for `prog_nat_prop`
#eval Plausible.Testable.check (∀ n : Nat, prog (n : Int) = .ok (Nat.factorial n))
example : testNats.all (fun n => decide (prog (n : Int) = .ok (Nat.factorial n))) = true := by
  native_decide

-- PBT for `progVal_int_prop`
#eval Plausible.Testable.check (∀ n : Int, progVal (.int n) = prog n)
example : testInts.all (fun n => decide (progVal (.int n) = prog n)) = true := by native_decide

-- PBT for `progVal_flt_prop` (bounded: no `Sampler Float`)
example : testFloats.all (fun x => (progVal (.flt x)).raised) = true := by native_decide

-- PBT for `Post_prop`
#eval Plausible.Testable.check (∀ n : Int, postBool n (prog n) = true)
example : testInts.all (fun n => postBool n (prog n)) = true := by native_decide
example : (List.range 60).all (fun i => postBool ((i : Int) - 30) (prog ((i : Int) - 30))) = true :=
  by native_decide

-- PBT for `PostVal_prop`
example : testVals.all (fun v => postValBool v (progVal v)) = true := by native_decide

/-! ## 7. Correctness theorem (`Pre -> Post`) -/

/-- Full specification of `prog`: both the success and the raising branch. -/
theorem prog_spec_thm (n : Int) : Post_prop n (prog n) := by
  refine ⟨?_, ?_⟩
  · intro h
    rw [prog_ok_thm n h]
    exact ⟨fact n.toNat, rfl, fact_eq_factorial_thm n.toNat, fact_pos_thm n.toNat⟩
  · intro h
    rw [prog_error_thm n h]
    rfl

/-- Correctness: the precondition implies the post-condition. -/
theorem correctness_thm (n : Int) (h : Pre n) : Post_prop n (prog n) := by
  have spec := prog_spec_thm n
  exact ⟨fun _ => spec.1 h, spec.2⟩

/-- The complementary half of the specification: a pre-violation raises. -/
theorem correctness_error_thm (n : Int) (h : ¬ Pre n) : (prog n).raised = true :=
  (prog_spec_thm n).2 h

/-- Full specification of `prog` on the Python-value layer. -/
theorem progVal_spec_thm (v : PyVal) : PostVal_prop v (progVal v) := by
  cases v with
  | int n =>
      have e : progVal (.int n) = prog n := rfl
      rw [e]
      refine ⟨fun h => ⟨n, rfl, ?_⟩, ?_⟩
      · rw [prog_ok_thm n h, fact_eq_factorial_thm]
      · intro h
        rw [prog_error_thm n h]
        rfl
  | flt x =>
      refine ⟨fun h => absurd h (preVal_flt_thm x), fun _ => rfl⟩

theorem correctnessVal_thm (v : PyVal) (h : PreVal v) : PostVal_prop v (progVal v) := by
  have spec := progVal_spec_thm v
  exact ⟨fun _ => spec.1 h, spec.2⟩

/-! ## 8. Imperative implementation (`Id.run do` with mutable state) -/

/-- The accumulation loop of the Python program, exposed as a function of the index list so that
it can be analysed by induction: `result` is the mutable accumulator. -/
def loopProd (xs : List Nat) (acc : Nat) : Nat := Id.run do
  let mut result := acc
  for i in xs do
    result := result * (i + 1)
  return result

/-- Imperative factorial, a direct transcription of
`result = 1; for i in range(1, n + 1): result *= i`.
`List.range n` enumerates `0, …, n-1`, hence `i + 1` enumerates Python's `range(1, n+1)`. -/
def factImp (n : Nat) : Nat := Id.run do
  let mut result := 1
  for i in List.range n do
    result := result * (i + 1)
  return result

/-- Imperative `prog`: guard on the precondition, then run the mutable accumulation loop. -/
def progImp (n : Int) : Outcome := Id.run do
  if Pre n then
    return .ok (factImp n.toNat)
  else
    return .valueError (errMsg n)

/-- Imperative `prog` on the Python-value layer. -/
def progValImp : PyVal → Outcome
  | .int n => progImp n
  | .flt x => .valueError (errMsgFlt x)

/-! ## 9. Imperative tests -/

example : loopProd [] 1 = 1 := by native_decide
example : loopProd [0, 1, 2] 1 = 6 := by native_decide
example : factImp 0 = 1 := by native_decide
example : factImp 1 = 1 := by native_decide
example : factImp 3 = 6 := by native_decide
example : factImp 5 = 120 := by native_decide
example : factImp 10 = 3628800 := by native_decide
example : progImp 0 = .ok 1 := by native_decide
example : progImp 3 = .ok 6 := by native_decide
example : (progImp (-1)).raised = true := by native_decide
example : (progValImp (.flt 3.14)).raised = true := by native_decide
example : progValImp (.int 4) = .ok 24 := by native_decide

#eval factImp 8
#eval progImp 6
#eval progImp (-3)
#eval loopProd (List.range 6) 1

/-! ## 10. Equivalence: functional = imperative -/

theorem loopProd_nil_thm (acc : Nat) : loopProd [] acc = acc := rfl

theorem loopProd_cons_thm (x : Nat) (xs : List Nat) (acc : Nat) :
    loopProd (x :: xs) acc = loopProd xs (acc * (x + 1)) := by simp [loopProd]

theorem factImp_eq_loop_thm (n : Nat) : factImp n = loopProd (List.range n) 1 := rfl

/-- The imperative loop computes `acc` times the product of the shifted index list. -/
theorem loopProd_eq_thm (xs : List Nat) (acc : Nat) :
    loopProd xs acc = acc * (List.map (fun i => i + 1) xs).prod := by
  induction xs generalizing acc with
  | nil => simp [loopProd_nil_thm]
  | cons y ys ih =>
      rw [loopProd_cons_thm, ih (acc * (y + 1)), List.map_cons, List.prod_cons]
      ring

/-- The shifted index list `[1, …, n]` has product `n!`. -/
theorem prod_map_range_thm : ∀ n : Nat,
    (List.map (fun i => i + 1) (List.range n)).prod = fact n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      have h1 : List.map (fun i => i + 1) (List.range (n + 1))
          = List.map (fun i => i + 1) (List.range n) ++ [n + 1] := by
        rw [List.range_succ, List.map_append]
        rfl
      rw [h1, List.prod_append, List.prod_singleton, ih]
      have e : fact (n + 1) = (n + 1) * fact n := rfl
      rw [e]
      ring

def factImp_eq_prop : Prop := ∀ n : Nat, factImp n = fact n

theorem factImp_eq_thm : factImp_eq_prop := by
  intro n
  rw [factImp_eq_loop_thm, loopProd_eq_thm, prod_map_range_thm]
  simp

def progImp_eq_prop : Prop := ∀ n : Int, progImp n = prog n

theorem progImp_eq_thm : progImp_eq_prop := by
  intro n
  simp only [progImp, prog, Pre, factImp_eq_thm n.toNat]
  exact rfl

def progValImp_eq_prop : Prop := ∀ v : PyVal, progValImp v = progVal v

theorem progValImp_eq_thm : progValImp_eq_prop := by
  intro v
  cases v with
  | int n => simp only [progValImp, progVal, progImp_eq_thm n]
  | flt _ => rfl

/-- The imperative implementation satisfies the same post-condition. -/
theorem progImp_spec_thm (n : Int) : Post_prop n (progImp n) := by
  rw [progImp_eq_thm n]
  exact prog_spec_thm n

theorem correctnessImp_thm (n : Int) (h : Pre n) : Post_prop n (progImp n) := by
  have spec := progImp_spec_thm n
  exact ⟨fun _ => spec.1 h, spec.2⟩

-- PBT for `factImp_eq_prop`
#eval Plausible.Testable.check (∀ n : Nat, factImp n = fact n)
example : testNats.all (fun n => decide (factImp n = fact n)) = true := by native_decide

-- PBT for `progImp_eq_prop`
#eval Plausible.Testable.check (∀ n : Int, progImp n = prog n)
example : testInts.all (fun n => decide (progImp n = prog n)) = true := by native_decide

-- PBT for `progValImp_eq_prop` (bounded: no `Sampler Float`)
example : testVals.all (fun v => decide (progValImp v = progVal v)) = true := by native_decide

-- PBT for the imperative post-condition (`Post_prop` over `progImp`)
#eval Plausible.Testable.check (∀ n : Int, postBool n (progImp n) = true)
example : testInts.all (fun n => postBool n (progImp n)) = true := by native_decide

end «16_MyFactorial»
