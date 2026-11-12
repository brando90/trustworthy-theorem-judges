import Mathlib

/-!
# Factorial of a natural number

Lean 4 formalization of the Python program `16_MyFactorial`:

```python
def pre(n: int) -> bool:
    return isinstance(n, int) and n >= 0

def prog(n: int) -> int:
    if not pre(n):
        raise ValueError(f"Input must be a non-negative integer (got n={n})")
    if n == 0:
        return 1
    result = 1
    for i in range(1, n + 1):
        result *= i
    return result
```

The Python function is total on the (mathematical) integers: it either returns
`n!` when `n ≥ 0`, or raises `ValueError`.  We model the raising behaviour with
`Except String Int`, so `prog : Int → Except String Int` is a total Lean function
whose `Except.error` case exactly mirrors the Python `raise`.

The file contains:

* `factCore` — the functional (structurally recursive) kernel;
* `prog` — the functional model of the Python function, including error handling;
* unit tests mirroring the Python `check` function (including the two
  pre-violating inputs `-1` and `3.14`, the latter being representable only as a
  non-integer and therefore witnessed by the absence of an integer equal to it);
* the precondition `Pre`, the individual property propositions with proofs, the
  post-condition `Post_prop` and the correctness theorem `Pre → Post`;
* an imperative implementation `progImp` using `Id.run do` with a mutable
  accumulator and a `for` loop over `range(1, n + 1)`, plus the equivalence
  theorem `progImp = prog`.
-/

namespace MyFactorial

/-! ## Implementation (functional) -/

/-- The factorial kernel, defined by structural recursion on a natural number. -/
def factCore : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factCore n

/-- The error message raised by the Python program on a pre-condition violation. -/
def errMsg (n : Int) : String :=
  s!"Input must be a non-negative integer (got n={n})"

/-- Functional model of the Python `prog`.

`Except.error` corresponds to Python raising `ValueError`. -/
def prog (n : Int) : Except String Int :=
  if 0 ≤ n then Except.ok (factCore n.toNat) else Except.error (errMsg n)

instance : DecidableEq (Except String Int) := fun a b => by
  cases a <;> cases b <;> simp <;> infer_instance

/-! ## Unit tests (functional) -/

#eval prog 3
#eval prog 0
#eval prog (-1)

-- Basic unit test: `candidate(3) == 6`.
example : prog 3 = Except.ok 6 := by native_decide

-- Edge unit test: `candidate(0) == 1`.
example : prog 0 = Except.ok 1 := by native_decide

example : prog 1 = Except.ok 1 := by native_decide
example : prog 5 = Except.ok 120 := by native_decide
example : prog 10 = Except.ok 3628800 := by native_decide

-- Negative test: `-1` violates the pre-condition, so a `ValueError` is raised.
example : prog (-1) = Except.error (errMsg (-1)) := by native_decide
example : (prog (-1)).toOption = none := by native_decide

-- Negative test: `3.14` is not an integer.  In Lean the input type is `Int`, so
-- non-integrality is witnessed by the fact that no integer equals `3.14`;
-- consequently `3.14` is outside the domain of `prog` altogether.
example : ¬ ∃ n : Int, (n : ℚ) = 3.14 := by
  rintro ⟨n, hn⟩
  have h2 : ((n * 100 : Int) : ℚ) = ((314 : Int) : ℚ) := by push_cast; rw [hn]; norm_num
  have h3 : n * 100 = 314 := by exact_mod_cast h2
  omega

/-! ## Pre-condition -/

/-- `Pre n` holds iff `n` is a non-negative integer — the Python `pre`. -/
def Pre (n : Int) : Prop := 0 ≤ n

instance (n : Int) : Decidable (Pre n) := by unfold Pre; infer_instance

example : Pre 3 := by decide
example : Pre 0 := by decide
example : ¬ Pre (-1) := by decide

/-! ## Properties -/

/-- The kernel agrees with `Nat.factorial`. -/
def factCore_spec_prop : Prop := ∀ n : Nat, factCore n = Nat.factorial n

theorem factCore_spec_thm : factCore_spec_prop := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih => simp [factCore, Nat.factorial, ih]

/-- `factorial(0) = 1` by definition. -/
def base_prop : Prop := prog 0 = Except.ok 1

theorem base_thm : base_prop := by
  simp [base_prop, prog, factCore]

/-- `factorial(1) = 1`. -/
def one_prop : Prop := prog 1 = Except.ok 1

theorem one_thm : one_prop := by
  simp [one_prop, prog, factCore]

/-- On a valid input `prog` succeeds and returns `n !`. -/
def factorial_prop (n : Int) : Prop :=
  prog n = Except.ok (Nat.factorial n.toNat : Int)

theorem factorial_thm (n : Int) (h : Pre n) : factorial_prop n := by
  have h' : (0 : Int) ≤ n := h
  simp [factorial_prop, prog, h', factCore_spec_thm n.toNat]

/-- `prog` returns exactly the product accumulated by the Python loop
`result = 1; for i in range(1, n + 1): result *= i`. -/
def prod_prop (n : Int) : Prop :=
  prog n = Except.ok (∏ i ∈ Finset.Icc 1 n.toNat, (i : Int))

theorem prod_Icc_id (m : Nat) : (∏ i ∈ Finset.Icc 1 m, i) = Nat.factorial m := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_id_eq_factorial]

theorem prod_thm (n : Int) (h : Pre n) : prod_prop n := by
  have h' : (0 : Int) ≤ n := h
  have hprod : (∏ i ∈ Finset.Icc 1 n.toNat, (i : Int))
      = ((∏ i ∈ Finset.Icc 1 n.toNat, i : Nat) : Int) := by
    push_cast
    rfl
  show prog n = _
  rw [prog, if_pos h', hprod, prod_Icc_id, factCore_spec_thm]

/-- The factorial recurrence `(n+1)! = (n+1) * n!` at the level of `prog`. -/
def rec_prop (n : Int) : Prop :=
  prog (n + 1) = Except.ok ((n + 1) * (factCore n.toNat : Int))

theorem rec_thm (n : Int) (h : Pre n) : rec_prop n := by
  have h' : (0 : Int) ≤ n := h
  have h1 : (0 : Int) ≤ n + 1 := by omega
  have h2 : (n + 1).toNat = n.toNat + 1 := by omega
  show prog (n + 1) = _
  simp only [prog, if_pos h1, h2, factCore, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Except.ok.injEq]
  have h3 : ((n.toNat : Int) + 1) = n + 1 := by omega
  rw [h3]

/-- Whenever `prog` succeeds, the returned value is a positive integer. -/
def pos_prop (n : Int) : Prop := ∀ v : Int, prog n = Except.ok v → 1 ≤ v

theorem pos_thm (n : Int) : pos_prop n := by
  intro v hv
  rw [prog] at hv
  split at hv
  · have hcore : 0 < factCore n.toNat := by
      rw [factCore_spec_thm]; exact Nat.factorial_pos _
    simp only [Except.ok.injEq] at hv
    omega
  · simp at hv

/-- A pre-condition violation raises `ValueError`: `prog` returns an error. -/
def raises_prop (n : Int) : Prop := ¬ Pre n → prog n = Except.error (errMsg n)

theorem raises_thm (n : Int) : raises_prop n := by
  intro hn
  have hn' : ¬ (0 : Int) ≤ n := hn
  rw [prog, if_neg hn']

/-- `prog` succeeds *exactly* on the inputs satisfying `Pre`. -/
def ok_iff_pre_prop (n : Int) : Prop := (∃ v, prog n = Except.ok v) ↔ Pre n

theorem ok_iff_pre_thm (n : Int) : ok_iff_pre_prop n := by
  constructor
  · rintro ⟨v, hv⟩
    rw [prog] at hv
    split at hv
    · assumption
    · simp at hv
  · intro hn
    have hn' : (0 : Int) ≤ n := hn
    exact ⟨_, by rw [prog, if_pos hn']⟩

/-! ## Post-condition -/

/-- The post-condition: on a valid input the call succeeds and returns `n!`,
equal to the product `1 * 2 * ⋯ * n` computed by the Python loop; the result is
positive, and it satisfies the factorial recurrence together with the base
cases `0! = 1` and `1! = 1`. -/
def Post_prop (n : Int) : Prop :=
  factorial_prop n ∧ prod_prop n ∧ rec_prop n ∧ pos_prop n ∧ base_prop ∧ one_prop

/-- **Correctness**: the pre-condition implies the post-condition. -/
theorem correctness_thm (n : Int) (h : Pre n) : Post_prop n :=
  ⟨factorial_thm n h, prod_thm n h, rec_thm n h, pos_thm n, base_thm, one_thm⟩

/-! ## Implementation (imperative) -/

/-- Imperative model of the Python program: a mutable accumulator `result`
updated by a `for` loop over `range(1, n + 1)`. -/
def progImp (n : Int) : Except String Int := Id.run do
  if n < 0 then
    return Except.error (errMsg n)
  if n = 0 then
    return Except.ok 1
  let mut result : Nat := 1
  for i in [1 : n.toNat + 1] do
    result := result * i
  return Except.ok (result : Int)

/-! ## Unit tests (imperative) -/

#eval progImp 3
#eval progImp 0
#eval progImp (-1)

example : progImp 3 = Except.ok 6 := by native_decide
example : progImp 0 = Except.ok 1 := by native_decide
example : progImp 1 = Except.ok 1 := by native_decide
example : progImp 5 = Except.ok 120 := by native_decide
example : progImp 10 = Except.ok 3628800 := by native_decide
example : progImp (-1) = Except.error (errMsg (-1)) := by native_decide

/-! ## Equivalence of the functional and imperative implementations -/

/-- The loop body accumulates the factorial. -/
theorem foldl_range'_mul (m : Nat) :
    ∀ acc : Nat, (List.range' 1 m 1).foldl (fun b a => b * a) acc = acc * factCore m := by
  induction m with
  | zero => intro acc; simp [factCore]
  | succ k ih =>
    intro acc
    rw [List.range'_concat, List.foldl_append, ih acc]
    simp [factCore]
    ring

set_option linter.deprecated false in
/-- Running the `for` loop of `progImp` over `range(1, m + 1)` yields `factCore m`. -/
theorem forIn_range_factCore (m : Nat) :
    (forIn (m := Id) [1 : m + 1] (1 : Nat) (fun i r => ForInStep.yield (r * i)))
      = factCore m := by
  rw [Std.Range.forIn_eq_forIn_range']
  have hsize : (Std.Range.mk 1 (m + 1) 1 (by omega)).size = m := by
    simp [Std.Range.size]
  rw [hsize, List.forIn_yield_eq_foldl, foldl_range'_mul m 1]
  simp

/-- **Equivalence**: the imperative implementation agrees with the functional one. -/
theorem prog_eq_progImp_thm (n : Int) : progImp n = prog n := by
  by_cases hneg : n < 0
  · have h1 : ¬ (0 : Int) ≤ n := by omega
    simp only [progImp, prog, Id.run, if_pos hneg, if_neg h1]
    rfl
  · have hn : (0 : Int) ≤ n := by omega
    by_cases hz : n = 0
    · subst hz
      simp only [progImp, prog, Id.run, if_neg hneg, if_pos hn]
      rfl
    · simp only [progImp, prog, Id.run, if_neg hneg, if_neg hz, if_pos hn]
      exact congrArg (fun k : Nat => Except.ok (k : Int)) (forIn_range_factCore n.toNat)

/-- Consequently the imperative version also satisfies the post-condition. -/
theorem correctness_imp_thm (n : Int) (h : Pre n) :
    progImp n = Except.ok (Nat.factorial n.toNat : Int) := by
  rw [prog_eq_progImp_thm n]
  exact factorial_thm n h

end MyFactorial
