import Mathlib

/-!
# 19_MyPower: natural-number exponentiation by repeated multiplication

Lean 4 formalization of the Python program `power(base, exponent)`:

* `prog base exponent` returns `base ^ exponent` for non-negative integers `base`, `exponent`,
  computed by repeated multiplication exactly like the Python `for` loop
  (`power(n, 0) = 1`, `power(0, n) = 0` for `n > 0`, `power(0, 0) = 1`);
* the Python `ValueError` raised when an input is negative is modelled by `Except.error`
  carrying the same message text, so the result type is `Except String Int`;
* `Pre` is the Python `pre`, each `_prop`/`_thm` pair states and proves one property of the
  result, `Post_prop` is their conjunction, `correctness_thm` proves `Pre → Post`;
* `progImp` is an imperative `Id.run do` implementation with a mutable accumulator and a
  `for` loop over `[0:exponent]`, proved equal to `prog` in `prog_eq_progImp_thm`.
-/

namespace «19_MyPower»

-- Some property definitions deliberately take all of `base`, `exponent`, `result` for a
-- uniform `Post_prop`, even when a property mentions only some of them.
set_option linter.unusedVariables false

-- Lean core ships no `DecidableEq` instance for `Except`; derive one so that results can be
-- compared in unit tests and property-based tests.
deriving instance DecidableEq for Except

/-! ## Implementation (functional) -/

/-- Text of the Python `ValueError` raised on a precondition violation. -/
def errorMsg (base exponent : Int) : String :=
  s!"Require base,exponent ∈ ℕ (got base={base}, exponent={exponent})"

/-- The Python `pre(base, exponent)`: both inputs are non-negative integers
(the `isinstance(_, int)` checks are enforced by the Lean types). -/
def pre (base exponent : Int) : Bool :=
  0 ≤ base && 0 ≤ exponent

/-- `result = 1; for _ in range(n): result *= base` as a structural recursion on `n`. -/
def powerLoop (base : Int) : Nat → Int
  | 0 => 1
  | n + 1 => powerLoop base n * base

/-- The Python `prog(base, exponent)`: `Except.error` models the raised `ValueError`,
`Except.ok` the returned integer. -/
def prog (base exponent : Int) : Except String Int :=
  if pre base exponent then
    if exponent = 0 then .ok 1
    else .ok (powerLoop base exponent.toNat)
  else .error (errorMsg base exponent)

/-- The Python test harness `check(candidate)`. -/
def check (candidate : Int → Int → Except String Int) : Bool :=
  candidate 2 3 = .ok 8 &&
  candidate 0 0 = .ok 1 &&
  [((-1 : Int), (2 : Int)), (2, -1)].all fun p =>
    match candidate p.1 p.2 with
    | .error _ => true
    | .ok _ => false

/-! ## Unit tests -/

example : prog 2 3 = .ok 8 := by native_decide
example : prog 0 0 = .ok 1 := by native_decide
example : prog (-1) 2 = .error "Require base,exponent ∈ ℕ (got base=-1, exponent=2)" := by
  native_decide
example : prog 2 (-1) = .error "Require base,exponent ∈ ℕ (got base=2, exponent=-1)" := by
  native_decide
example : prog 0 5 = .ok 0 := by native_decide
example : prog 7 0 = .ok 1 := by native_decide
example : prog 5 1 = .ok 5 := by native_decide
example : prog 3 4 = .ok 81 := by native_decide
example : prog 2 10 = .ok 1024 := by native_decide
example : check prog = true := by native_decide

#eval prog 2 3
#eval prog 0 0
#eval prog (-1) 2
#eval prog 2 (-1)
#eval check prog

/-! ## Pre-condition -/

/-- Pre-condition: both inputs are natural numbers (the Python `pre`). -/
def Pre (base exponent : Int) : Prop :=
  0 ≤ base ∧ 0 ≤ exponent

instance (base exponent : Int) : Decidable (Pre base exponent) :=
  inferInstanceAs (Decidable (0 ≤ base ∧ 0 ≤ exponent))

/-- The Boolean `pre` decides the proposition `Pre`. -/
theorem pre_iff_Pre_thm (base exponent : Int) : pre base exponent = true ↔ Pre base exponent := by
  simp [pre, Pre]

/-! ## Properties -/

/-- The hand-rolled multiplication loop computes the mathematical power. -/
theorem powerLoop_eq_pow_thm (base : Int) (n : Nat) : powerLoop base n = base ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [powerLoop, ih, pow_succ]

/-- Property: on admissible inputs the program returns (no exception) exactly
`base ^ exponent`. -/
def pow_prop (base exponent : Int) (result : Except String Int) : Prop :=
  result = .ok (base ^ exponent.toNat)

theorem pow_thm (base exponent : Int) (h : Pre base exponent) :
    pow_prop base exponent (prog base exponent) := by
  have hp : pre base exponent = true := (pre_iff_Pre_thm base exponent).2 h
  unfold pow_prop prog
  rw [if_pos hp]
  split_ifs with h0
  · subst h0
    simp
  · rw [powerLoop_eq_pow_thm]

/-- Property (edge case): `power(n, 0) = 1` for any `n`. -/
def exp_zero_prop (base exponent : Int) (result : Except String Int) : Prop :=
  exponent = 0 → result = .ok 1

theorem exp_zero_thm (base exponent : Int) (h : Pre base exponent) :
    exp_zero_prop base exponent (prog base exponent) := by
  intro h0
  rw [pow_thm base exponent h]
  subst h0
  simp

/-- Property (edge case): `power(0, n) = 0` for `n > 0`. -/
def base_zero_prop (base exponent : Int) (result : Except String Int) : Prop :=
  base = 0 → 0 < exponent → result = .ok 0

theorem base_zero_thm (base exponent : Int) (h : Pre base exponent) :
    base_zero_prop base exponent (prog base exponent) := by
  intro hb he
  rw [pow_thm base exponent h]
  subst hb
  have hne : exponent.toNat ≠ 0 := by omega
  rw [zero_pow hne]

/-- Property (edge case): `power(0, 0) = 1` by convention. -/
def zero_zero_prop (base exponent : Int) (result : Except String Int) : Prop :=
  base = 0 → exponent = 0 → result = .ok 1

theorem zero_zero_thm (base exponent : Int) (h : Pre base exponent) :
    zero_zero_prop base exponent (prog base exponent) := by
  intro _ he
  exact exp_zero_thm base exponent h he

/-- Property: `power(n, 1) = n`. -/
def exp_one_prop (base exponent : Int) (result : Except String Int) : Prop :=
  exponent = 1 → result = .ok base

theorem exp_one_thm (base exponent : Int) (h : Pre base exponent) :
    exp_one_prop base exponent (prog base exponent) := by
  intro h1
  rw [pow_thm base exponent h]
  subst h1
  simp

/-- Property: on admissible inputs the program returns normally and the result is again a
natural number (non-negative). -/
def nonneg_prop (base exponent : Int) (result : Except String Int) : Prop :=
  ∃ r : Int, result = .ok r ∧ 0 ≤ r

theorem nonneg_thm (base exponent : Int) (h : Pre base exponent) :
    nonneg_prop base exponent (prog base exponent) := by
  refine ⟨base ^ exponent.toNat, pow_thm base exponent h, ?_⟩
  exact pow_nonneg h.1 _

/-- Property: a positive base yields a positive power. -/
def pos_prop (base exponent : Int) (result : Except String Int) : Prop :=
  0 < base → ∃ r : Int, result = .ok r ∧ 0 < r

theorem pos_thm (base exponent : Int) (h : Pre base exponent) :
    pos_prop base exponent (prog base exponent) := by
  intro hb
  exact ⟨base ^ exponent.toNat, pow_thm base exponent h, pow_pos hb _⟩

/-- Property: the recurrence behind the loop, `power(b, e + 1) = power(b, e) * b`. -/
def succ_prop (base exponent : Int) : Prop :=
  prog base (exponent + 1) = (prog base exponent).map (· * base)

theorem succ_thm (base exponent : Int) (h : Pre base exponent) : succ_prop base exponent := by
  have he : 0 ≤ exponent := h.2
  have h' : Pre base (exponent + 1) := ⟨h.1, by omega⟩
  unfold succ_prop
  rw [pow_thm base exponent h, pow_thm base (exponent + 1) h']
  have ht : (exponent + 1).toNat = exponent.toNat + 1 := by omega
  rw [ht, pow_succ]
  rfl

/-- Property: outside the precondition the program raises `ValueError` with the Python
message (and returns nothing). -/
def error_prop (base exponent : Int) (result : Except String Int) : Prop :=
  result = .error (errorMsg base exponent)

theorem error_thm (base exponent : Int) (h : ¬ Pre base exponent) :
    error_prop base exponent (prog base exponent) := by
  have hp : ¬ pre base exponent = true := fun hc => h ((pre_iff_Pre_thm base exponent).1 hc)
  unfold error_prop prog
  rw [if_neg hp]

/-- Property: the program returns normally exactly when the precondition holds. -/
def ok_iff_prop (base exponent : Int) : Prop :=
  (∃ r : Int, prog base exponent = .ok r) ↔ Pre base exponent

theorem ok_iff_thm (base exponent : Int) : ok_iff_prop base exponent := by
  unfold ok_iff_prop
  constructor
  · rintro ⟨r, hr⟩
    by_contra hn
    rw [error_thm base exponent hn] at hr
    cases hr
  · intro h
    exact ⟨base ^ exponent.toNat, pow_thm base exponent h⟩

/-! ## Post-condition -/

/-- Post-condition on the result of `prog base exponent` under `Pre`: conjunction of the
properties above. -/
def Post_prop (base exponent : Int) (result : Except String Int) : Prop :=
  pow_prop base exponent result ∧
  exp_zero_prop base exponent result ∧
  base_zero_prop base exponent result ∧
  zero_zero_prop base exponent result ∧
  exp_one_prop base exponent result ∧
  nonneg_prop base exponent result ∧
  pos_prop base exponent result

/-! ## Property-based tests -/

/-- Executable form of `nonneg_prop`. -/
def okNonneg : Except String Int → Bool
  | .ok r => decide (0 ≤ r)
  | .error _ => false

/-- Executable form of `pos_prop` (conclusion). -/
def okPos : Except String Int → Bool
  | .ok r => decide (0 < r)
  | .error _ => false

/-- Executable form of `Post_prop base exponent (prog base exponent)`. -/
def postCheck (base exponent : Int) : Bool :=
  let result := prog base exponent
  result = .ok (base ^ exponent.toNat) &&
  (exponent == 0 → result = .ok 1) &&
  (base == 0 → 0 < exponent → result = .ok 0) &&
  (base == 0 → exponent == 0 → result = .ok 1) &&
  (exponent == 1 → result = .ok base) &&
  okNonneg result &&
  (0 < base → okPos result)

-- pow_prop (admissible inputs are exactly the naturals, so sample `Nat` and cast)
#eval Plausible.Testable.check
  (∀ base exponent : Nat, prog (base : Int) (exponent : Int) = .ok ((base : Int) ^ exponent))
#eval Plausible.Testable.check
  (∀ base exponent : Int, 0 ≤ base → 0 ≤ exponent → prog base exponent = .ok (base ^ exponent.toNat))
example : ((List.range 13).all fun b => (List.range 13).all fun e =>
    prog (b : Int) (e : Int) = .ok ((b : Int) ^ e)) = true := by native_decide

-- exp_zero_prop
#eval Plausible.Testable.check (∀ base : Nat, prog (base : Int) 0 = .ok 1)
example : ((List.range 50).all fun b => prog (b : Int) 0 = .ok 1) = true := by native_decide

-- base_zero_prop
#eval Plausible.Testable.check (∀ exponent : Nat, prog 0 ((exponent : Int) + 1) = .ok 0)
example : ((List.range 50).all fun e => prog 0 ((e : Int) + 1) = .ok 0) = true := by native_decide

-- zero_zero_prop
example : prog 0 0 = .ok 1 := by native_decide

-- exp_one_prop
#eval Plausible.Testable.check (∀ base : Nat, prog (base : Int) 1 = .ok (base : Int))
example : ((List.range 50).all fun b => prog (b : Int) 1 = .ok (b : Int)) = true := by native_decide

-- nonneg_prop
#eval Plausible.Testable.check
  (∀ base exponent : Nat, okNonneg (prog (base : Int) (exponent : Int)) = true)
example : ((List.range 13).all fun b => (List.range 13).all fun e =>
    okNonneg (prog (b : Int) (e : Int))) = true := by native_decide

-- pos_prop
#eval Plausible.Testable.check
  (∀ base exponent : Nat, okPos (prog ((base : Int) + 1) (exponent : Int)) = true)
example : ((List.range 13).all fun b => (List.range 13).all fun e =>
    okPos (prog ((b : Int) + 1) (e : Int))) = true := by native_decide

-- succ_prop
#eval Plausible.Testable.check
  (∀ base exponent : Nat,
    prog (base : Int) ((exponent : Int) + 1) = (prog (base : Int) (exponent : Int)).map (· * (base : Int)))
example : ((List.range 13).all fun b => (List.range 13).all fun e =>
    prog (b : Int) ((e : Int) + 1) = (prog (b : Int) (e : Int)).map (· * (b : Int))) = true := by
  native_decide

-- error_prop
#eval Plausible.Testable.check
  (∀ base exponent : Int, ¬ (0 ≤ base ∧ 0 ≤ exponent) →
    prog base exponent = .error (errorMsg base exponent))
example : ((List.range 13).all fun b => (List.range 13).all fun e =>
    prog (-(b : Int) - 1) (e : Int) = .error (errorMsg (-(b : Int) - 1) (e : Int)) &&
    prog (b : Int) (-(e : Int) - 1) = .error (errorMsg (b : Int) (-(e : Int) - 1)) &&
    prog (-(b : Int) - 1) (-(e : Int) - 1) =
      .error (errorMsg (-(b : Int) - 1) (-(e : Int) - 1))) = true := by native_decide

-- ok_iff_prop
#eval Plausible.Testable.check
  (∀ base exponent : Int, (prog base exponent).isOk = (0 ≤ base && 0 ≤ exponent))
example : ((List.range 25).all fun b => (List.range 25).all fun e =>
    (prog ((b : Int) - 12) ((e : Int) - 12)).isOk ==
      (0 ≤ (b : Int) - 12 && 0 ≤ (e : Int) - 12)) = true := by native_decide

-- Post_prop
#eval Plausible.Testable.check
  (∀ base exponent : Nat, postCheck (base : Int) (exponent : Int) = true)
#eval Plausible.Testable.check
  (∀ base exponent : Int, 0 ≤ base → 0 ≤ exponent → postCheck base exponent = true)
example : ((List.range 13).all fun b => (List.range 13).all fun e =>
    postCheck (b : Int) (e : Int)) = true := by native_decide

/-! ## Correctness: `Pre → Post` -/

theorem correctness_thm (base exponent : Int) (h : Pre base exponent) :
    Post_prop base exponent (prog base exponent) :=
  ⟨pow_thm base exponent h, exp_zero_thm base exponent h, base_zero_thm base exponent h,
    zero_zero_thm base exponent h, exp_one_thm base exponent h, nonneg_thm base exponent h,
    pos_thm base exponent h⟩

/-! ## Imperative implementation -/

/-- Imperative transcription of the Python `prog`: early `return` on the precondition check
and on `exponent == 0`, then a mutable accumulator multiplied `exponent` times. -/
def progImp (base exponent : Int) : Except String Int := Id.run do
  if !pre base exponent then
    return .error (errorMsg base exponent)
  if exponent = 0 then
    return .ok 1
  let mut result : Int := 1
  for _ in [0:exponent.toNat] do
    result := result * base
  return .ok result

/-! ## Imperative tests -/

example : progImp 2 3 = .ok 8 := by native_decide
example : progImp 0 0 = .ok 1 := by native_decide
example : progImp (-1) 2 = .error "Require base,exponent ∈ ℕ (got base=-1, exponent=2)" := by
  native_decide
example : progImp 2 (-1) = .error "Require base,exponent ∈ ℕ (got base=2, exponent=-1)" := by
  native_decide
example : progImp 0 5 = .ok 0 := by native_decide
example : progImp 3 4 = .ok 81 := by native_decide
example : check progImp = true := by native_decide
example : ((List.range 13).all fun b => (List.range 13).all fun e =>
    progImp (b : Int) (e : Int) = prog (b : Int) (e : Int)) = true := by native_decide

#eval progImp 2 3
#eval progImp 0 0
#eval progImp (-1) 2
#eval check progImp
#eval Plausible.Testable.check (∀ base exponent : Int, progImp base exponent = prog base exponent)

/-! ## Equivalence: functional = imperative -/

/-- Folding `· * base` over any `List.range'` of length `n` multiplies by `base` `n` times. -/
theorem foldl_mul_range'_thm (base init : Int) (s n step : Nat) :
    List.foldl (fun (b : Int) (_ : Nat) => b * base) init (List.range' s n step) =
      init * powerLoop base n := by
  induction n generalizing s init with
  | zero => simp [powerLoop]
  | succ n ih =>
    rw [List.range'_succ, List.foldl_cons, ih, powerLoop]
    ring

/-- The `for _ in [0:n]` accumulator loop in the `Id` monad computes `init * powerLoop base n`. -/
theorem forIn_range_mul_thm (base init : Int) (n : Nat) :
    (forIn (m := Id) [0:n] init fun _ r => pure (ForInStep.yield (r * base))) =
      pure (init * powerLoop base n) := by
  rw [Std.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl]
  have hsize : ([0:n] : Std.Range).size = n := by simp [Std.Range.size]
  simp only [hsize]
  rw [foldl_mul_range'_thm]

theorem prog_eq_progImp_thm (base exponent : Int) : prog base exponent = progImp base exponent := by
  unfold prog progImp
  simp only [Id.run, pure_bind, forIn_range_mul_thm, one_mul]
  split_ifs <;> simp_all <;> rfl

end «19_MyPower»
