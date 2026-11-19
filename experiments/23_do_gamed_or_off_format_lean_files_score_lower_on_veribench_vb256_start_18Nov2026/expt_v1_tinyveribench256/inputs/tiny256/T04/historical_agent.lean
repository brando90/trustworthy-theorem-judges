import Mathlib
namespace Agent

/-!
# HumanEval/44 — `change_base`

Translation of the Python program

```python
def change_base(x: int, base: int):
    ret = ""
    while x > 0:
        ret = str(x % base) + ret
        x //= base
    return ret
```

which renders the natural number `x` in positional notation with radix `base`
(the problem statement guarantees `base < 10`, so every digit `str(x % base)` is a
single character).  Note that `change_base 0 base = ""`, exactly as in Python.

This file provides

* a functional implementation `changeBase`,
* a digit-string evaluator `evalBase` used to state correctness,
* the pre-condition `Pre`, the individual properties, the post-condition `Post_prop`
  and the correctness theorem `Pre → Post`,
* an imperative implementation `changeBaseImp` written with `Id.run do` and mutable
  state, together with a proof that it agrees with `changeBase`.
-/

namespace humaneval_44_change_base

/-! ## Functional implementation -/

/-- `changeBase x base` is the base-`base` representation of `x`.
The `1 < base` guard makes the recursion terminate; for `base ≤ 1` (outside the
pre-condition) it returns `""`. -/
def changeBase (x base : Nat) : String :=
  if h : 1 < base ∧ 0 < x then
    changeBase (x / base) base ++ toString (x % base)
  else
    ""
termination_by x
decreasing_by exact Nat.div_lt_self h.2 h.1

/-- Value of a digit character. -/
def digitVal (c : Char) : Nat := c.toNat - 48

/-- Interpret a string of digits as a number written in base `base`. -/
def evalBase (s : String) (base : Nat) : Nat :=
  s.data.foldl (fun acc c => acc * base + digitVal c) 0

/-! ## Unit tests (mirroring the Python `check` function) -/

example : changeBase 8 3 = "22" := by native_decide
example : changeBase 9 3 = "100" := by native_decide
example : changeBase 234 2 = "11101010" := by native_decide
example : changeBase 16 2 = "10000" := by native_decide
example : changeBase 8 2 = "1000" := by native_decide
example : changeBase 7 2 = "111" := by native_decide
example : ∀ x ∈ [2, 3, 4, 5, 6, 7], changeBase x (x + 1) = toString x := by native_decide
example : changeBase 0 5 = "" := by native_decide

#eval changeBase 8 3
#eval changeBase 234 2

/-! ## Basic equations -/

theorem changeBase_of_pos {x base : Nat} (hb : 1 < base) (hx : 0 < x) :
    changeBase x base = changeBase (x / base) base ++ toString (x % base) := by
  rw [changeBase]
  simp [hb, hx]

theorem changeBase_zero (base : Nat) : changeBase 0 base = "" := by
  rw [changeBase]; simp

/-- For `d < 10` the decimal string of `d` is the single character `'0' + d`. -/
theorem data_toString_of_lt_ten {d : Nat} (h : d < 10) :
    (toString d).data = [Char.ofNat (d + 48)] := by
  interval_cases d <;> rfl

theorem digitVal_ofNat {d : Nat} (h : d < 10) : digitVal (Char.ofNat (d + 48)) = d := by
  interval_cases d <;> rfl

/-! ## Pre-condition

The Python docstring states that base numbers are less than 10; a positional
system additionally needs at least two digits. -/

def Pre (x base : Nat) : Prop := 2 ≤ base ∧ base < 10

/-! ## Properties -/

/-- **Correctness**: reading the produced string back in base `base` returns `x`. -/
def roundtrip_prop (x base : Nat) : Prop := evalBase (changeBase x base) base = x

theorem roundtrip_thm (x base : Nat) (h : Pre x base) : roundtrip_prop x base := by
  obtain ⟨hb2, hb10⟩ := h
  have hb : 1 < base := hb2
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rcases Nat.eq_zero_or_pos x with hx | hx
    · subst hx; simp [roundtrip_prop, changeBase_zero, evalBase]
    · have hlt : x / base < x := Nat.div_lt_self hx hb
      have hmod : x % base < 10 := lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega)
      have ih' : evalBase (changeBase (x / base) base) base = x / base := ih _ hlt
      have key : evalBase (changeBase x base) base
          = evalBase (changeBase (x / base) base) base * base + x % base := by
        rw [changeBase_of_pos hb hx]
        simp only [evalBase, String.data_append, List.foldl_append,
          data_toString_of_lt_ten hmod, List.foldl_cons, List.foldl_nil,
          digitVal_ofNat hmod]
      rw [roundtrip_prop, key, ih', Nat.div_add_mod']

/-- The result is empty exactly for `x = 0` (Python returns `""` for `x = 0`). -/
def empty_iff_prop (x base : Nat) : Prop := changeBase x base = "" ↔ x = 0

theorem empty_iff_thm (x base : Nat) (h : Pre x base) : empty_iff_prop x base := by
  obtain ⟨hb2, hb10⟩ := h
  have hb : 1 < base := hb2
  constructor
  · intro he
    have := roundtrip_thm x base ⟨hb2, hb10⟩
    rw [roundtrip_prop, he] at this
    simpa [evalBase] using this.symm
  · intro hx; subst hx; exact changeBase_zero base

/-- Every character of the output is a digit smaller than `base`
(this is what makes `evalBase` the right inverse). -/
def digits_prop (x base : Nat) : Prop :=
  ∀ c ∈ (changeBase x base).data, ∃ d, d < base ∧ c = Char.ofNat (d + 48)

theorem digits_thm (x base : Nat) (h : Pre x base) : digits_prop x base := by
  obtain ⟨hb2, hb10⟩ := h
  have hb : 1 < base := hb2
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rcases Nat.eq_zero_or_pos x with hx | hx
    · subst hx; simp [digits_prop, changeBase_zero]
    · have hlt : x / base < x := Nat.div_lt_self hx hb
      have hmodb : x % base < base := Nat.mod_lt _ (by omega)
      have hmod : x % base < 10 := by omega
      intro c hc
      rw [changeBase_of_pos hb hx, String.data_append, List.mem_append,
        data_toString_of_lt_ten hmod] at hc
      rcases hc with hc | hc
      · exact ih _ hlt c hc
      · simp only [List.mem_singleton] at hc
        exact ⟨x % base, hmodb, hc⟩

/-- A number below the base is rendered by its own decimal digit;
this is the Python test `candidate(x, x + 1) == str(x)`. -/
def single_digit_prop (x base : Nat) : Prop := 0 < x → x < base → changeBase x base = toString x

theorem single_digit_thm (x base : Nat) (h : Pre x base) : single_digit_prop x base := by
  obtain ⟨hb2, hb10⟩ := h
  intro hx hxb
  rw [changeBase_of_pos hb2 hx, Nat.div_eq_of_lt hxb, Nat.mod_eq_of_lt hxb,
    changeBase_zero]
  simp

/-- The output has no leading zero, so the representation is the canonical one. -/
def no_leading_zero_prop (x base : Nat) : Prop :=
  0 < x → (changeBase x base).data.head? ≠ some (Char.ofNat 48)

theorem no_leading_zero_thm (x base : Nat) (h : Pre x base) : no_leading_zero_prop x base := by
  obtain ⟨hb2, hb10⟩ := h
  have hb : 1 < base := hb2
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hx
    have hlt : x / base < x := Nat.div_lt_self hx hb
    have hmodb : x % base < base := Nat.mod_lt _ (by omega)
    have hmod : x % base < 10 := by omega
    rw [changeBase_of_pos hb hx, String.data_append]
    rcases Nat.eq_zero_or_pos (x / base) with hq | hq
    · -- single digit: `x < base` and `0 < x`
      have hxb : x < base := by
        by_contra hcon
        exact absurd (Nat.div_pos (not_lt.mp hcon) (by omega)) (by omega)
      rw [hq, changeBase_zero, Nat.mod_eq_of_lt hxb, data_toString_of_lt_ten (by omega)]
      simp only [List.nil_append, List.head?_cons, ne_eq, Option.some.injEq]
      intro hcon
      have h1 : Char.toNat (Char.ofNat (x + 48)) = Char.toNat (Char.ofNat 48) := by
        rw [hcon]
      simp [Char.toNat, Char.ofNat, Char.ofNatAux,
        Nat.isValidChar, show x + 48 < 55296 by omega] at h1
      omega
    · have hIH := ih _ hlt hq
      have hne : (changeBase (x / base) base).data ≠ [] := by
        intro hcon
        have hemp : changeBase (x / base) base = "" := by
          apply String.ext; simpa using hcon
        have := (empty_iff_thm (x / base) base ⟨hb2, hb10⟩).mp hemp
        omega
      obtain ⟨a, l, hal⟩ := List.exists_cons_of_ne_nil hne
      rw [hal] at hIH ⊢
      simpa using hIH

/-! ## Post-condition and correctness -/

def Post_prop (x base : Nat) : Prop :=
  roundtrip_prop x base ∧ empty_iff_prop x base ∧ digits_prop x base ∧
    single_digit_prop x base ∧ no_leading_zero_prop x base

theorem correctness (x base : Nat) (h : Pre x base) : Post_prop x base :=
  ⟨roundtrip_thm x base h, empty_iff_thm x base h, digits_thm x base h,
    single_digit_thm x base h, no_leading_zero_thm x base h⟩

/-! ## Imperative implementation

A direct transcription of the Python `while` loop.  The loop is bounded by `x`
iterations, which is always enough because each iteration divides `x` by
`base ≥ 2`; once `n` reaches `0` the remaining iterations do nothing, mirroring
the `while x > 0` test. -/

def changeBaseImp (x base : Nat) : String := Id.run do
  let mut ret : String := ""
  let mut n : Nat := x
  for _ in List.replicate x () do
    if 0 < n ∧ 1 < base then
      ret := toString (n % base) ++ ret
      n := n / base
  return ret

/-! ## Imperative tests -/

example : changeBaseImp 8 3 = "22" := by native_decide
example : changeBaseImp 9 3 = "100" := by native_decide
example : changeBaseImp 234 2 = "11101010" := by native_decide
example : changeBaseImp 16 2 = "10000" := by native_decide
example : changeBaseImp 8 2 = "1000" := by native_decide
example : changeBaseImp 7 2 = "111" := by native_decide
example : ∀ x ∈ [2, 3, 4, 5, 6, 7], changeBaseImp x (x + 1) = toString x := by native_decide
example : changeBaseImp 0 5 = "" := by native_decide

#eval changeBaseImp 234 2

/-! ## Equivalence -/

/-- The body of the `for` loop, as an explicit function on the loop state
`⟨n, ret⟩`. -/
def loopBody (base : Nat) : Unit → MProd Nat String → Id (ForInStep (MProd Nat String)) :=
  fun _ r =>
    if 0 < r.fst ∧ 1 < base then
      pure (ForInStep.yield ⟨r.fst / base, toString (r.fst % base) ++ r.snd⟩)
    else
      pure (ForInStep.yield r)

theorem changeBaseImp_eq (x base : Nat) :
    changeBaseImp x base =
      (Id.run (forIn (List.replicate x ()) (⟨x, ""⟩ : MProd Nat String) (loopBody base))).snd :=
  rfl

/-- Running the loop for `k ≥ n` iterations starting from `⟨n, ret⟩` consumes all of
`n` and prepends its digits to `ret`. -/
theorem loop_eq (base : Nat) (hb : 1 < base) :
    ∀ (k n : Nat) (ret : String), n ≤ k →
      Id.run (forIn (List.replicate k ()) (⟨n, ret⟩ : MProd Nat String) (loopBody base))
        = (⟨0, changeBase n base ++ ret⟩ : MProd Nat String) := by
  intro k
  induction k with
  | zero =>
    intro n ret hn
    have : n = 0 := by omega
    subst this
    simp only [List.replicate_zero, List.forIn_nil, changeBase_zero, String.empty_append]
    rfl
  | succ k ih =>
    intro n ret hn
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · subst hn0
      simp only [List.replicate_succ, List.forIn_cons, loopBody]
      simp only [lt_self_iff_false, false_and, if_false]
      simpa [changeBase_zero] using ih 0 ret (by omega)
    · have hdiv : n / base ≤ k := by
        have : n / base < n := Nat.div_lt_self hn0 hb
        omega
      simp only [List.replicate_succ, List.forIn_cons, loopBody]
      simp only [hn0, hb, and_self, if_true]
      rw [show (pure (ForInStep.yield
            (⟨n / base, toString (n % base) ++ ret⟩ : MProd Nat String)) :
              Id (ForInStep (MProd Nat String))) >>= _
          = Id.run (forIn (List.replicate k ())
              (⟨n / base, toString (n % base) ++ ret⟩ : MProd Nat String) (loopBody base))
        from rfl]
      rw [ih _ _ hdiv, changeBase_of_pos hb hn0, String.append_assoc]
      rfl

/-- **Equivalence**: the imperative `while`-loop version computes the same string as
the functional version. -/
theorem changeBase_eq_changeBaseImp (x base : Nat) (h : Pre x base) :
    changeBase x base = changeBaseImp x base := by
  obtain ⟨hb2, hb10⟩ := h
  rw [changeBaseImp_eq, loop_eq base hb2 x x "" (le_refl x)]
  simp

end humaneval_44_change_base
end Agent
