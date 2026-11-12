import Mathlib

/-!
# VeriBench 20 - `MySumDigits`: sum of the decimal digits of a non-negative integer

## Python source (abridged)

```python
def pre(n):  return isinstance(n, int) and n >= 0

def prog(n):
    if not pre(n): raise ValueError(...)
    if n == 0: return 0
    total = 0
    while n > 0:
        total += n % 10
        n //= 10
    return total
```

## Modelling decisions

* `sumDigits : Nat -> Nat` is the functional translation of the loop
  `total += n % 10; n //= 10`.  It is defined by recursion on `n` itself, which is
  exactly the loop's termination measure (`n / 10 < n` for `0 < n`).  The equation
  `sumDigits 0 = 0` is Python's early return `if n == 0: return 0`.
* `Pre (n : Int) := 0 <= n` translates `pre` on the integer layer, and
  `prog : Int -> Except String Nat` translates `prog`: the `.error valueErrorMsg`
  branch is Python's `raise ValueError`.
* Python's `pre` also rejects *non-integers* such as `3.14`.  Lean is statically
  typed, so the dynamically typed Python argument is modelled in `RatLayer` by a
  `Rat`: `PreRat q := q.den = 1 /\ 0 <= q.num` holds exactly for the non-negative
  integers, hence `progRat (-1)` and `progRat (314/100)` both take the `ValueError`
  branch, exactly as the Python `check` harness requires.
* `sumDigitsImp` is the imperative translation: `Id.run do` with a mutable state.
  The mutable state `s` is the pair `(m, total)` of the two Python loop variables,
  and one pass of the loop is `impStep`, i.e. `total += m % 10; m //= 10` under the
  guard `0 < m`.  Lean's `while` desugars to `Lean.Loop.forIn`, which is a
  `partial def` and hence opaque to the kernel (nothing can be proved about it), so
  the loop is written as a `for` loop over `List.range (n + 1)`: `n + 1` is an upper
  bound for the number of passes of the Python `while` loop (each pass with `0 < m`
  replaces `m` by `m / 10 < m`), and the surplus passes are no-ops thanks to the
  guard.  This keeps the imperative shape and makes the equivalence theorem
  kernel-checkable.

Every theorem below is proved.  `native_decide` is used only inside `example`
tests, never inside a theorem proof.
-/

namespace «20_MySumDigits»

/-! ## 4. Implementation (functional definition) -/

/-- The message of the `ValueError` that the Python program raises when `pre` fails. -/
def valueErrorMsg : String := "ValueError: Require non-negative integer"

/-- `true` iff the result is the error branch, i.e. iff Python raised. -/
def isErr {ε α : Type} (e : Except ε α) : Bool :=
  match e with
  | .error _ => true
  | .ok _ => false

/-- The value carried by a result, `none` on the error branch. -/
def okVal {ε α : Type} (e : Except ε α) : Option α :=
  match e with
  | .ok a => some a
  | .error _ => none

/-- `sumDigits n` is the sum of the decimal digits of `n`.

Functional translation of
```
total = 0
while n > 0:
    total += n % 10
    n //= 10
return total
```
-/
def sumDigits : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) % 10 + sumDigits ((n + 1) / 10)
termination_by n => n
decreasing_by simp_wf; omega

set_option linter.unusedSimpArgs false in
@[simp] theorem sumDigits_zero : sumDigits 0 = 0 := by simp [sumDigits]

/-- The defining equation, in a form that rewrites an arbitrary expression. -/
theorem sumDigits_eq (n : Nat) :
    sumDigits n = if n = 0 then 0 else n % 10 + sumDigits (n / 10) := by
  cases n <;> simp [sumDigits]

/-- Induction principle matching the recursion of `sumDigits` (and of the Python loop). -/
theorem sumDigits_induction {P : Nat → Prop} (h0 : P 0)
    (hs : ∀ n, 0 < n → P (n / 10) → P n) : ∀ n, P n := by
  have key : ∀ n, (∀ m, m < n → P m) → P n := by
    intro n ih
    by_cases hn : n = 0
    · subst hn
      exact h0
    · exact hs n (Nat.pos_of_ne_zero hn)
        (ih (n / 10) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)))
  intro n
  exact Nat.strong_induction_on n key

theorem prod_fst_mk (a b : Nat) : (a, b).1 = a := rfl
theorem prod_snd_mk (a b : Nat) : (a, b).2 = b := rfl

/-! ## 5. Unit tests -/

example : sumDigits 123 = 6 := by native_decide
example : sumDigits 0 = 0 := by simp
example : sumDigits 7 = 7 := by native_decide
example : sumDigits 9999 = 36 := by native_decide
example : sumDigits 1000000 = 1 := by native_decide
example : sumDigits 987654321 = 45 := by native_decide

#eval sumDigits 123 -- 6
#eval sumDigits 0 -- 0
#eval sumDigits 987654321 -- 45

/-! ## 6. Pre-condition predicate -/

/-- Translation of the Python `pre`: the argument has to be a non-negative integer. -/
def Pre (n : Int) : Prop := 0 ≤ n

instance (n : Int) : Decidable (Pre n) := inferInstanceAs (Decidable (0 ≤ n))

/-- Translation of the Python `prog`.  The `.error` branch models `raise ValueError`. -/
def prog (n : Int) : Except String Nat :=
  if Pre n then .ok (sumDigits n.toNat) else .error valueErrorMsg

example : okVal (prog 123) = some 6 := by native_decide
example : okVal (prog 0) = some 0 := by native_decide
example : isErr (prog (-1)) = true := by native_decide
example : isErr (prog 123) = false := by native_decide

#eval prog 123
#eval prog (-1)

/-! ## 7. Properties -/

/-- Edge case of the Python docstring: the sum of digits of `0` is `0`. -/
def zero_prop : Prop := sumDigits 0 = 0

theorem zero_thm : zero_prop := sumDigits_zero

/-- Edge case of the Python docstring: single digit numbers return themselves. -/
def singleDigit_prop : Prop := ∀ d : Nat, d < 10 → sumDigits d = d

theorem singleDigit_thm : singleDigit_prop := by
  intro d hd
  rw [sumDigits_eq]
  by_cases h : d = 0
  · simp [h]
  · rw [if_neg h, Nat.mod_eq_of_lt hd, Nat.div_eq_of_lt hd, sumDigits_zero]
    omega

/-- One pass of the loop peels off the last decimal digit. -/
def recursion_prop : Prop :=
  ∀ k d : Nat, d < 10 → sumDigits (10 * k + d) = d + sumDigits k

theorem recursion_thm : recursion_prop := by
  intro k d hd
  rw [sumDigits_eq]
  rcases k with _ | k
  · have h0 : 10 * 0 + d = d := by omega
    rw [h0, sumDigits_zero]
    by_cases h : d = 0
    · simp [h]
    · rw [if_neg h, Nat.mod_eq_of_lt hd, Nat.div_eq_of_lt hd, sumDigits_zero]
  · have hne : 10 * (k + 1) + d ≠ 0 := by omega
    rw [if_neg hne]
    have h1 : (10 * (k + 1) + d) % 10 = d := by omega
    have h2 : (10 * (k + 1) + d) / 10 = k + 1 := by omega
    rw [h1, h2]

/-- Casting out nines: the digit sum is congruent to `n` modulo 9. -/
def mod9_prop : Prop := ∀ n : Nat, sumDigits n % 9 = n % 9

theorem mod9_thm : mod9_prop := by
  apply sumDigits_induction
  · simp
  · intro n hn ih
    rw [sumDigits_eq, if_neg (Nat.ne_of_gt hn)]
    omega

/-- The digit sum never exceeds the number itself. -/
def leSelf_prop : Prop := ∀ n : Nat, sumDigits n ≤ n

theorem leSelf_thm : leSelf_prop := by
  apply sumDigits_induction
  · simp
  · intro n hn ih
    rw [sumDigits_eq, if_neg (Nat.ne_of_gt hn)]
    omega

/-- A positive input yields a positive digit sum: the loop only stops at `n = 0`,
    and `prog` returns `0` exactly for the input `0`. -/
def pos_prop : Prop := ∀ n : Nat, 0 < n → 0 < sumDigits n

theorem pos_thm : pos_prop := by
  apply sumDigits_induction
  · intro h
    omega
  · intro n hn ih
    rw [sumDigits_eq, if_neg (Nat.ne_of_gt hn)]
    intro _
    by_cases h : n / 10 = 0
    · omega
    · have hpos := ih (Nat.pos_of_ne_zero h)
      omega

/-- Appending a trailing zero does not change the digit sum. -/
def mulTen_prop : Prop := ∀ n : Nat, sumDigits (10 * n) = sumDigits n

theorem mulTen_thm : mulTen_prop := by
  intro n
  have h := recursion_thm n 0 (by decide)
  simp only [Nat.add_zero, Nat.zero_add] at h
  exact h

/-- `sumDigits` agrees with Mathlib's little-endian decimal digit list. -/
def digits_prop : Prop := ∀ n : Nat, sumDigits n = (Nat.digits 10 n).sum

theorem digits_thm : digits_prop := by
  apply sumDigits_induction
  · simp
  · intro n hn ih
    rw [sumDigits_eq, if_neg (Nat.ne_of_gt hn),
      Nat.digits_of_two_le_of_pos (by decide) hn, List.sum_cons]
    omega

/-- Pre-violations raise: `prog` produces the `ValueError` branch. -/
def raises_prop : Prop := ∀ n : Int, ¬ Pre n → prog n = .error valueErrorMsg

theorem raises_thm : raises_prop := by
  intro n hn
  simp [prog, if_neg hn]

/-- On admissible input `prog` returns the digit sum of `n`. -/
def okValue_prop : Prop := ∀ n : Int, Pre n → prog n = .ok (sumDigits n.toNat)

theorem okValue_thm : okValue_prop := by
  intro n hn
  simp [prog, if_pos hn]

/-! ## 8. Post-condition -/

/-- Post-condition of `prog`, as a conjunction of the properties proved above:

* on admissible input the result is `.ok` and carries the digit sum of `n`;
* on inadmissible input the result is the `ValueError` branch (Python's `raise`);
* whenever a value `s` is returned, `s` is the digit sum of `n`, `s` is congruent
  to `n` modulo 9, and `s` does not exceed `n`.
-/
def Post_prop (n : Int) (res : Except String Nat) : Prop :=
  (Pre n → res = .ok (sumDigits n.toNat)) ∧
    (¬ Pre n → res = .error valueErrorMsg) ∧
    (∀ s : Nat, res = .ok s → (s = sumDigits n.toNat ∧ s % 9 = n.toNat % 9 ∧ s ≤ n.toNat))

/-! ## 9. Property-based tests -/

/-- Executable (Boolean) counterpart of `Post_prop`, which is a `Prop` and hence has
    no `Decidable` instance; the property-based tests below check this function. -/
def postCheck (n : Int) : Bool :=
  (isErr (prog n) == decide (¬ Pre n)) &&
    match prog n with
    | .ok s => s == sumDigits n.toNat && s % 9 == n.toNat % 9 && decide (s ≤ n.toNat)
    | .error _ => true

-- Randomized PBTs (Plausible).  A counterexample makes the file fail to compile.
-- Preconditions are avoided in the sampled statements; the literal preconditioned
-- statements are covered by the bounded PBTs below.
#eval Plausible.Testable.check (sumDigits 0 = 0)
#eval Plausible.Testable.check (∀ n : Nat, sumDigits n % 9 = n % 9)
#eval Plausible.Testable.check (∀ n : Nat, sumDigits n ≤ n)
#eval Plausible.Testable.check (∀ n : Nat, 0 < sumDigits (n + 1))
#eval Plausible.Testable.check (∀ n : Nat, sumDigits n = (Nat.digits 10 n).sum)
#eval Plausible.Testable.check (∀ d : Nat, sumDigits (d % 10) = d % 10)
#eval Plausible.Testable.check
  (∀ k d : Nat, sumDigits (10 * k + d % 10) = d % 10 + sumDigits k)
#eval Plausible.Testable.check (∀ n : Nat, sumDigits (10 * n) = sumDigits n)
#eval Plausible.Testable.check (∀ m : Nat, isErr (prog (m : Int)) = false)
#eval Plausible.Testable.check (∀ m : Nat, isErr (prog (-(m : Int) - 1)) = true)
#eval Plausible.Testable.check (∀ n : Int, postCheck n = true)

-- Bounded PBTs: exhaustive small cases, including the preconditioned statements.
example : (sumDigits 0 == 0) = true := by native_decide
example : (List.range 10).all (fun d => sumDigits d == d) = true := by native_decide
example : (List.range 300).all (fun n => sumDigits n % 9 == n % 9) = true := by native_decide
example : (List.range 300).all (fun n => decide (sumDigits n ≤ n)) = true := by native_decide
example : (List.range 300).all (fun n => decide (0 < n → 0 < sumDigits n)) = true := by native_decide
example : (List.range 300).all (fun n => sumDigits n == (Nat.digits 10 n).sum) = true := by native_decide
example : (List.range 60).all (fun k =>
    (List.range 10).all (fun d => sumDigits (10 * k + d) == d + sumDigits k)) = true := by native_decide
example : (List.range 120).all (fun n => sumDigits (10 * n) == sumDigits n) = true := by native_decide
example : (List.range 121).all (fun i => postCheck ((i : Int) - 60)) = true := by native_decide
example : (List.range 41).all (fun i =>
    isErr (prog ((i : Int) - 20)) == decide (((i : Int) - 20) < 0)) = true := by native_decide

/-! ## 10. Correctness theorem -/

theorem post_thm : ∀ n : Int, Post_prop n (prog n) := by
  intro n
  by_cases h : Pre n
  · have hprog : prog n = .ok (sumDigits n.toNat) := by simp [prog, if_pos h]
    refine ⟨fun _ => hprog, fun hn => absurd h hn, ?_⟩
    intro s hs
    rw [hprog] at hs
    simp at hs
    subst hs
    exact ⟨rfl, mod9_thm _, leSelf_thm _⟩
  · have hprog : prog n = .error valueErrorMsg := by simp [prog, if_neg h]
    refine ⟨fun hn => absurd hn h, fun _ => hprog, ?_⟩
    intro s hs
    rw [hprog] at hs
    cases hs

/-- Correctness of the translation: the precondition implies the postcondition. -/
theorem correctness_thm : ∀ n : Int, Pre n → Post_prop n (prog n) := by
  intro n _hn
  exact post_thm n

/-! ## 11. Imperative implementation (`Id.run do` with mutable state) -/

/-- One pass of the loop body over the mutable state `s = (m, total)`:
    `total += m % 10; m //= 10`, guarded by the loop condition `0 < m`. -/
def impStep (s : Nat × Nat) : Nat × Nat :=
  if 0 < s.1 then (s.1 / 10, s.2 + s.1 % 10) else s

/-- Imperative translation of the Python loop, in `Id.run do` with mutable state.

The mutable state `s` is the pair `(m, total)` of the two Python loop variables:
`m` is the running quotient (initially `n`) and `total` the running digit sum
(initially `0`).  Each pass of the loop executes `impStep`, i.e. the Python body
`total += m % 10; m //= 10` under the loop guard `0 < m`, and the loop stops as
soon as the guard fails.

The Python `while n > 0` loop performs at most `n + 1` passes (every pass with
`0 < m` replaces `m` by `m / 10 < m`), so the bounded `for` loop below visits the
same states; once `m = 0` the guard makes the remaining passes no-ops. -/
def sumDigitsImp (n : Nat) : Nat := Id.run do
  let mut s : Nat × Nat := (n, 0) -- the mutable pair (m, total)
  for _ in List.range (n + 1) do
    s := impStep s
  return s.2

/-- Imperative translation of `prog`: precondition check, then the loop, else `ValueError`. -/
def progImp (n : Int) : Except String Nat := Id.run do
  let mut res : Except String Nat := .error valueErrorMsg
  if Pre n then
    res := .ok (sumDigitsImp n.toNat)
  return res

/-! ## 12. Imperative tests -/

example : sumDigitsImp 123 = 6 := by native_decide
example : sumDigitsImp 0 = 0 := by native_decide
example : sumDigitsImp 7 = 7 := by native_decide
example : sumDigitsImp 9999 = 36 := by native_decide
example : okVal (progImp 123) = some 6 := by native_decide
example : isErr (progImp (-1)) = true := by native_decide
example : (List.range 150).all (fun n => sumDigitsImp n == sumDigits n) = true := by native_decide

#eval sumDigitsImp 123 -- 6
#eval sumDigitsImp 9999 -- 36
#eval progImp 123
#eval progImp (-1)

/-! ## 13. Equivalence: functional = imperative -/

/-- The `do` block is the fold of `impStep` over the loop's iteration list. -/
theorem imp_fold (n : Nat) :
    sumDigitsImp n = (List.foldl (fun s _ => impStep s) (n, 0) (List.range (n + 1))).2 := by
  simp [sumDigitsImp]

/-- One loop pass preserves the invariant `total + sumDigits m`. -/
theorem impStep_inv (s : Nat × Nat) :
    (impStep s).2 + sumDigits (impStep s).1 = s.2 + sumDigits s.1 := by
  rcases s with ⟨m, t⟩
  by_cases h : 0 < m
  · have h1 : impStep (m, t) = (m / 10, t + m % 10) := by simp [impStep, h]
    have hsum : sumDigits m = m % 10 + sumDigits (m / 10) := by
      rw [sumDigits_eq, if_neg (Nat.ne_of_gt h)]
    rw [h1]
    simp
    omega
  · have h1 : impStep (m, t) = (m, t) := by simp [impStep, h]
    rw [h1]

/-- The loop invariant, for any number of passes. -/
theorem impFold_inv {α : Type} (l : List α) : ∀ s : Nat × Nat,
    (List.foldl (fun p _ => impStep p) s l).2 +
        sumDigits (List.foldl (fun p _ => impStep p) s l).1 =
      s.2 + sumDigits s.1 := by
  induction l with
  | nil => intro s; simp
  | cons a l ih =>
    intro s
    have h1 := ih (impStep s)
    have h2 := impStep_inv s
    simp only [List.foldl_cons]
    omega

/-- `l.length` passes drive the mutable `m` down to `0` whenever `l.length ≥ m`
    (in particular `n + 1` passes suffice for the input `n`). -/
theorem impFold_zero {α : Type} (l : List α) : ∀ s : Nat × Nat, l.length ≥ s.1 →
    (List.foldl (fun p _ => impStep p) s l).1 = 0 := by
  induction l with
  | nil =>
    intro s h
    simp at h ⊢
    omega
  | cons a l ih =>
    intro s h
    simp only [List.length_cons, List.foldl_cons] at h ⊢
    by_cases hpos : 0 < s.1
    · have hstep : impStep s = (s.1 / 10, s.2 + s.1 % 10) := by
        rcases s with ⟨m, t⟩
        simp [impStep, hpos]
      have hlen : l.length ≥ s.1 / 10 := by omega
      have hres := ih (s.1 / 10, s.2 + s.1 % 10) hlen
      rw [← hstep] at hres
      exact hres
    · have hstep : impStep s = s := by simp [impStep, hpos]
      rw [hstep]
      exact ih s (by omega)

/-- The imperative loop computes the same value as the functional definition. -/
theorem equiv_thm : ∀ n : Nat, sumDigits n = sumDigitsImp n := by
  intro n
  rw [imp_fold]
  have h1 := impFold_inv (List.range (n + 1)) (n, 0)
  have hlen : (List.range (n + 1)).length ≥ n := by simp [List.length_range]
  have h2 := impFold_zero (List.range (n + 1)) (n, 0) hlen
  simp only [h2, sumDigits_zero, add_zero, zero_add] at h1
  omega

/-- The imperative program is equivalent to the functional one on the whole input
    domain (both the `.ok` and the `ValueError` branch). -/
theorem equiv_prog_thm : ∀ n : Int, prog n = progImp n := by
  intro n
  by_cases h : Pre n
  · have h1 : prog n = .ok (sumDigits n.toNat) := by simp [prog, if_pos h]
    have h2 : progImp n = .ok (sumDigitsImp n.toNat) := by simp [progImp, if_pos h]
    rw [h1, h2, equiv_thm]
  · have h1 : prog n = .error valueErrorMsg := by simp [prog, if_neg h]
    have h2 : progImp n = .error valueErrorMsg := by simp [progImp, if_neg h]
    rw [h1, h2]

/-! ## Extra numeric layer: `RatLayer`

Python's `pre` is `isinstance(n, int) and n >= 0`, so it rejects *non-integer*
arguments such as `3.14` as well as negative ones.  Lean is statically typed, so
the dynamically typed Python argument is modelled here by a `Rat`: `PreRat q`
holds exactly when `q` is a non-negative integer.
-/

namespace RatLayer

/-- Translation of `pre` for a Python argument modelled as a `Rat`:
    `isinstance(n, int) and n >= 0` becomes "`q` has denominator `1` and a
    non-negative numerator". -/
def PreRat (q : Rat) : Prop := q.den = 1 ∧ 0 ≤ q.num

instance (q : Rat) : Decidable (PreRat q) :=
  inferInstanceAs (Decidable (q.den = 1 ∧ 0 ≤ q.num))

/-- Translation of `prog` at the rational layer; `.error` models `raise ValueError`. -/
def progRat (q : Rat) : Except String Nat :=
  if PreRat q then .ok (sumDigits q.num.natAbs) else .error valueErrorMsg

theorem preRat_natCast (m : Nat) : PreRat (m : Rat) := by
  simp [PreRat]

/-- Python: `pre(-1)` is `False`, so `prog(-1)` raises `ValueError`. -/
theorem not_preRat_neg_one : ¬ PreRat (-1 : Rat) := by decide

/-- Python: `pre(3.14)` is `False` (`isinstance(3.14, int)` fails), so `prog(3.14)`
    raises `ValueError`. -/
theorem not_preRat_314 : ¬ PreRat (314 / 100 : Rat) := by
  intro h
  obtain ⟨h1, _⟩ := h
  have hden : (314 / 100 : Rat).den = 50 := by norm_num
  rw [hden] at h1
  exact absurd h1 (by decide)

theorem progRat_natCast (m : Nat) : progRat (m : Rat) = .ok (sumDigits m) := by
  simp [progRat, if_pos (preRat_natCast m)]

theorem progRat_error : ∀ q : Rat, ¬ PreRat q → progRat q = .error valueErrorMsg := by
  intro q hq
  simp [progRat, if_neg hq]

/-- The rational layer agrees with the integer layer on integer arguments. -/
theorem progRat_comp_prog : ∀ m : Nat, progRat (m : Rat) = prog (m : Int) := by
  intro m
  have hpre : Pre (m : Int) := Int.natCast_nonneg m
  rw [progRat_natCast, okValue_thm (m : Int) hpre]
  rfl

example : okVal (progRat (123 : Rat)) = some 6 := by native_decide
example : okVal (progRat (0 : Rat)) = some 0 := by native_decide
example : okVal (progRat (7 : Rat)) = some 7 := by native_decide
example : isErr (progRat (-1 : Rat)) = true := by native_decide
example : isErr (progRat (314 / 100 : Rat)) = true := by native_decide
example : isErr (progRat (12 : Rat)) = false := by native_decide

#eval progRat (123 : Rat)
#eval progRat (-1 : Rat)
#eval progRat (314 / 100 : Rat)

-- Bounded PBTs for the rational layer (`Rat` has no Plausible sampler): the
-- admissible/inadmissible split is checked exhaustively on small samples.
example : (List.range 41).all (fun i =>
    let q : Rat := ((i : Int) - 20) / 3
    isErr (progRat q) == decide (¬ PreRat q)) = true := by native_decide
example : (List.range 41).all (fun i => isErr (progRat (i : Rat)) = false) = true := by native_decide
example : (List.range 20).all (fun i =>
    okVal (progRat (i : Rat)) == some (sumDigits i)) = true := by native_decide
example : (List.range 20).all (fun i =>
    okVal (progRat (i : Rat)) == okVal (prog (i : Int))) = true := by native_decide

end RatLayer

end «20_MySumDigits»
