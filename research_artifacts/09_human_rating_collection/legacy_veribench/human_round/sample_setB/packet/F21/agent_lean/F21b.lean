import Mathlib

/-!
# 19_MyPower — natural-number exponentiation (VeriBench translation)

Formalization of the Python program

    def pre(base, exponent):
        return isinstance(base, int) and isinstance(exponent, int) and base >= 0 and exponent >= 0

    def prog(base, exponent):
        if not pre(base, exponent):
            raise ValueError("Require base,exponent in N (got base=..., exponent=...)")
        if exponent == 0:
            return 1
        result = 1
        for _ in range(exponent):
            result *= base
        return result

## Modelling decisions

* Python `int` arguments are modelled by Lean `Int`.  The dynamic `isinstance(·, int)` tests are
  enforced statically by the type, so the precondition `Pre` keeps the two non-negativity
  obligations `0 ≤ base` and `0 ≤ exponent`; `pre_nat_thm` proves that `Pre b e` holds exactly
  when both arguments are natural numbers.
* `raise ValueError(msg)` is modelled by the constructor `Result.valueError msg`, where
  `msg = errMsg base exponent` is exactly the message the Python program formats; a normal
  `return v` is modelled by `Result.ok v`.
* The loop `result = 1; for _ in range(exponent): result *= base` is modelled by the structural
  recursion `powerNat` (functional implementation) and by the mutable-state loop `impLoop`,
  executed with `Id.run do` (imperative implementation).  `impLoop_spec` proves the two agree,
  and `equivalence_thm` proves `progImp = prog` on every input, admissible or not.
* `Int.toNat exponent` converts the (proved non-negative) exponent into the `Nat` the loop needs.
* The edge cases `power(n,0) = 1`, `power(0,n) = 0` for `n > 0` and `power(0,0) = 1` are stated
  and proved separately (`exp_zero_thm`, `zero_base_thm`, `zero_zero_thm`), and the
  pre-violations `(-1, 2)`, `(2, -1)` of the Python test harness are covered by `neg_thm`,
  `error_thm` and `error_msg_thm`.
* The task is purely discrete, so everything is stated over `Int`/`Nat`; `pow_eq_thm` connects
  the implementation with Mathlib's mathematical power `^`.
-/

namespace «19_MyPower»

/-! ## Result type: a returned value or a raised `ValueError` -/

/-- The observable outcome of the Python function: either the returned integer or the
raised `ValueError` together with its message. -/
inductive Result where
  | ok : Int → Result
  | valueError : String → Result
  deriving DecidableEq, BEq, Repr

/-- Map the returned value, propagating an exception (models `f(prog(b, e))`). -/
def Result.map (f : Int → Int) : Result → Result
  | .ok v => .ok (f v)
  | .valueError m => .valueError m

/-- Monadic bind, propagating an exception (models using two calls together). -/
def Result.bind (f : Int → Result) : Result → Result
  | .ok v => f v
  | .valueError m => .valueError m

/-- `true` iff the call raised. -/
def Result.isError : Result → Bool
  | .ok _ => false
  | .valueError _ => true

/-! ## Implementation (functional definition) -/

/-- The message of the `ValueError` raised by the Python program. -/
def errMsg (base exponent : Int) : String :=
  s!"Require base,exponent ∈ ℕ (got base={base}, exponent={exponent})"

/-- Executable counterpart of the Python predicate `pre`: `true` iff both inputs are
non-negative integers (the `isinstance` tests are guaranteed by the `Int` type). -/
def preBool (base exponent : Int) : Bool := decide (0 ≤ base ∧ 0 ≤ exponent)

/-- `powerNat b n` is `b ^ n`, computed by iterated multiplication exactly as the Python loop
`result = 1; for _ in range(exponent): result *= base` does.  The clause `powerNat b 0 = 1`
covers both the Python early return `if exponent == 0: return 1` and `power(0,0) = 1`. -/
def powerNat : Int → Nat → Int
  | _, 0 => 1
  | b, n + 1 => powerNat b n * b

/-- Functional implementation of the Python function `prog`. -/
def prog (base exponent : Int) : Result :=
  match preBool base exponent with
  | true => .ok (powerNat base (Int.toNat exponent))
  | false => .valueError (errMsg base exponent)

/-- Lean mirror of the Python `check` test harness. -/
def check (candidate : Int → Int → Result) : Bool :=
  (candidate 2 3 == .ok 8) && (candidate 0 0 == .ok 1) &&
    (candidate (-1) 2).isError && (candidate 2 (-1)).isError

/-! ## Unit tests -/

example : prog 2 3 = .ok 8 := by native_decide
#eval prog 2 3
example : prog 3 4 = .ok 81 := by native_decide
example : prog 2 10 = .ok 1024 := by native_decide
example : prog 10 5 = .ok 100000 := by native_decide
#eval prog 10 5

-- edge cases listed in the Python docstring
example : prog 5 0 = .ok 1 := by native_decide
example : prog 0 0 = .ok 1 := by native_decide
example : prog 0 7 = .ok 0 := by native_decide
#eval prog 0 0

-- precondition violations raise `ValueError`
example : prog (-1) 2 = .valueError (errMsg (-1) 2) := by native_decide
example : prog 2 (-1) = .valueError (errMsg 2 (-1)) := by native_decide
example : (prog (-1) 2).isError = true := by native_decide
example : (prog 2 (-1)).isError = true := by native_decide
#eval prog (-1) 2

-- the whole Python test harness passes
example : check prog = true := by native_decide

/-- The Python test harness passes for the functional implementation (kernel-checked). -/
theorem check_thm : check prog = true := by decide

/-! ## Precondition -/

/-- Precondition of the Python program `pre`: both arguments are natural numbers,
 i.e. integers `≥ 0` (integrality itself is enforced by the `Int` type). -/
def Pre (base exponent : Int) : Prop := 0 ≤ base ∧ 0 ≤ exponent

instance (base exponent : Int) : Decidable (Pre base exponent) :=
  show Decidable (0 ≤ base ∧ 0 ≤ exponent) from inferInstance

/-- `preBool` decides `Pre`. -/
theorem preBool_iff (base exponent : Int) : preBool base exponent = true ↔ Pre base exponent := by
  simp only [preBool, Pre, decide_eq_true_iff]

theorem preBool_true (base exponent : Int) (h : Pre base exponent) :
    preBool base exponent = true := by
  simp only [preBool, decide_eq_true_iff]
  exact h

theorem preBool_false (base exponent : Int) (h : ¬ Pre base exponent) :
    preBool base exponent = false := by
  simp only [preBool, decide_eq_false_iff_not]
  exact h

/-- Executable counterpart of the negated precondition. -/
def notPreBool (base exponent : Int) : Bool := decide (¬ Pre base exponent)

theorem notPreBool_true (base exponent : Int) (h : ¬ Pre base exponent) :
    notPreBool base exponent = true := by
  simp only [notPreBool, decide_eq_true_iff]
  exact h

theorem notPreBool_false (base exponent : Int) (h : Pre base exponent) :
    notPreBool base exponent = false := by
  simp only [notPreBool, decide_eq_false_iff_not]
  exact fun hh => hh h

/-! ## Basic reduction lemmas -/

/-- On admissible inputs `prog` returns the iterated product. -/
theorem prog_of_Pre (base exponent : Int) (h : Pre base exponent) :
    prog base exponent = .ok (powerNat base (Int.toNat exponent)) := by
  simp only [prog, preBool_true base exponent h]

/-- On inadmissible inputs `prog` raises `ValueError` with the documented message. -/
theorem prog_of_notPre (base exponent : Int) (h : ¬ Pre base exponent) :
    prog base exponent = .valueError (errMsg base exponent) := by
  simp only [prog, preBool_false base exponent h]

/-- The iterated product is Mathlib's power. -/
theorem powerNat_eq_pow (b : Int) : ∀ n : Nat, powerNat b n = b ^ n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [powerNat, ih, pow_succ]

/-- Every non-negative integer is a natural number. -/
lemma eq_natCast_of_nonneg {a : Int} (h : 0 ≤ a) : ∃ n : Nat, a = (n : Int) :=
  ⟨a.toNat, (Int.toNat_of_nonneg h).symm⟩

/-- The specification specialised to a `Nat` exponent. -/
lemma prog_natCast (b : Int) (n : Nat) (hb : 0 ≤ b) : prog b (n : Int) = .ok (b ^ n) := by
  rw [prog_of_Pre b (n : Int) ⟨hb, Int.ofNat_zero_le n⟩, powerNat_eq_pow, Int.toNat_natCast]

/-- Monotonicity of the mathematical power for bases `≥ 1`. -/
lemma pow_le_pow_add (b : Int) (hb : 1 ≤ b) : ∀ n k : Nat, b ^ n ≤ b ^ (n + k) := by
  intro n k
  induction k with
  | zero => simp
  | succ k ih =>
      have hpos : 0 ≤ b ^ (n + k) := pow_nonneg (by linarith) (n + k)
      have hstep : b ^ (n + (k + 1)) = b ^ (n + k) * b := by
        rw [← Nat.add_assoc, pow_add, pow_one]
      rw [hstep]
      have hmul : b ^ (n + k) * 1 ≤ b ^ (n + k) * b := mul_le_mul_of_nonneg_left hb hpos
      linarith

/-! ## Properties -/

/-- `power(n, 0) = 1` for any admissible `n` (Python: `if exponent == 0: return 1`). -/
def exp_zero_prop : Prop := ∀ b : Int, Pre b 0 → prog b 0 = .ok 1

theorem exp_zero_thm : exp_zero_prop := by
  intro b hb
  have h1 : prog b 0 = .ok (powerNat b (Int.toNat 0)) := prog_of_Pre b 0 hb
  have h2 : powerNat b (Int.toNat 0) = (1 : Int) := rfl
  rw [h1, h2]

/-- `power(0, n) = 0` for `n > 0`. -/
def zero_base_prop : Prop := ∀ e : Int, 0 < e → prog 0 e = .ok 0

theorem zero_base_thm : zero_base_prop := by
  intro e he
  obtain ⟨n, rfl⟩ := eq_natCast_of_nonneg (le_of_lt he)
  cases n with
  | zero => exact absurd he (by decide)
  | succ k => rw [prog_natCast 0 (k + 1) (le_refl (0 : Int)), zero_pow (by omega)]

/-- `power(0, 0) = 1` by convention. -/
def zero_zero_prop : Prop := prog 0 0 = .ok 1

theorem zero_zero_thm : zero_zero_prop := exp_zero_thm 0 (by decide)

/-- A violated precondition raises an exception (`raise ValueError`). -/
def error_prop : Prop :=
  ∀ b e : Int, ¬ Pre b e → ∃ msg : String, prog b e = .valueError msg

theorem error_thm : error_prop := fun b e h => ⟨errMsg b e, prog_of_notPre b e h⟩

/-- The raised exception carries exactly the message the Python program formats. -/
def error_msg_prop : Prop :=
  ∀ b e : Int, ¬ Pre b e → prog b e = .valueError (errMsg b e)

theorem error_msg_thm : error_msg_prop := fun b e h => prog_of_notPre b e h

/-- The Python `bad_inputs` `(-1, 2)` and `(2, -1)`: a negative argument is rejected. -/
def neg_prop : Prop :=
  ∀ b e : Int, b < 0 ∨ e < 0 → ∃ msg : String, prog b e = .valueError msg

theorem neg_thm : neg_prop := by
  intro b e h
  refine error_thm b e ?_
  intro hpre
  cases h with
  | inl hb => exact absurd hb (not_lt_of_ge hpre.1)
  | inr he => exact absurd he (not_lt_of_ge hpre.2)

/-- Main specification: an admissible call returns `base ^ exponent`. -/
def spec_prop : Prop := ∀ b e : Int, Pre b e → prog b e = .ok (b ^ e.toNat)

theorem spec_thm : spec_prop := by
  intro b e h
  rw [prog_of_Pre b e h, powerNat_eq_pow]

/-- `Pre b e` holds exactly when both arguments are natural numbers
(the Python test `isinstance(·, int) and · >= 0`). -/
def pre_nat_prop : Prop :=
  ∀ b e : Int, Pre b e ↔ ∃ m n : Nat, b = (m : Int) ∧ e = (n : Int)

theorem pre_nat_thm : pre_nat_prop := by
  intro b e
  constructor
  · intro h
    exact ⟨b.toNat, e.toNat, (Int.toNat_of_nonneg h.1).symm, (Int.toNat_of_nonneg h.2).symm⟩
  · rintro ⟨m, n, rfl, rfl⟩
    exact ⟨Int.ofNat_zero_le m, Int.ofNat_zero_le n⟩

/-- The recursion performed by the Python loop: `power(b, e + 1) = power(b, e) * b`. -/
def step_prop : Prop :=
  ∀ b e : Int, Pre b e → prog b (e + 1) = (prog b e).map (fun v => v * b)

theorem step_thm : step_prop := by
  intro b e h
  obtain ⟨n, rfl⟩ := eq_natCast_of_nonneg h.2
  rw [← Int.natCast_succ, prog_natCast b (n + 1) h.1, prog_natCast b n h.1, pow_succ]
  rfl

/-- `power(b, e1 + e2) = power(b, e1) * power(b, e2)`. -/
def add_prop : Prop :=
  ∀ b e1 e2 : Int, Pre b e1 → Pre b e2 →
    prog b (e1 + e2) = (prog b e1).bind (fun v1 => (prog b e2).map (fun v2 => v1 * v2))

theorem add_thm : add_prop := by
  intro b e1 e2 h1 h2
  obtain ⟨n1, rfl⟩ := eq_natCast_of_nonneg h1.2
  obtain ⟨n2, rfl⟩ := eq_natCast_of_nonneg h2.2
  rw [← Int.natCast_add, prog_natCast b (n1 + n2) h1.1, prog_natCast b n1 h1.1,
    prog_natCast b n2 h1.1, pow_add]
  rfl

/-- `power(b1 * b2, e) = power(b1, e) * power(b2, e)`. -/
def mul_prop : Prop :=
  ∀ b1 b2 e : Int, Pre b1 e → Pre b2 e →
    prog (b1 * b2) e = (prog b1 e).bind (fun v1 => (prog b2 e).map (fun v2 => v1 * v2))

theorem mul_thm : mul_prop := by
  intro b1 b2 e h1 h2
  obtain ⟨n, rfl⟩ := eq_natCast_of_nonneg h1.2
  rw [prog_natCast (b1 * b2) n (mul_nonneg h1.1 h2.1), prog_natCast b1 n h1.1,
    prog_natCast b2 n h2.1, mul_pow]
  rfl

/-- `power(1, e) = 1`. -/
def one_prop : Prop := ∀ e : Int, Pre 1 e → prog 1 e = .ok 1

theorem one_thm : one_prop := by
  intro e h
  obtain ⟨n, rfl⟩ := eq_natCast_of_nonneg h.2
  rw [prog_natCast 1 n (by decide : 0 ≤ (1 : Int)), one_pow]

/-- The iterated product computed by the loop equals the mathematical power. -/
def pow_eq_prop : Prop := ∀ b : Int, ∀ n : Nat, powerNat b n = b ^ n

theorem pow_eq_thm : pow_eq_prop := fun b n => powerNat_eq_pow b n

/-- Monotone in the exponent for bases `≥ 1`. -/
def monotone_prop : Prop :=
  ∀ b e1 e2 : Int, Pre b e1 → Pre b e2 → 1 ≤ b → e1 ≤ e2 →
    ∀ v1 v2 : Int, prog b e1 = .ok v1 → prog b e2 = .ok v2 → v1 ≤ v2

theorem monotone_thm : monotone_prop := by
  intro b e1 e2 h1 h2 hb hle v1 v2 hv1 hv2
  obtain ⟨n1, rfl⟩ := eq_natCast_of_nonneg h1.2
  obtain ⟨n2, rfl⟩ := eq_natCast_of_nonneg h2.2
  rw [prog_natCast b n1 h1.1] at hv1
  rw [prog_natCast b n2 h1.1] at hv2
  simp only [Result.ok.injEq] at hv1 hv2
  subst hv1
  subst hv2
  have hnm : n1 ≤ n2 := by exact_mod_cast hle
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hnm
  rw [hk]
  exact pow_le_pow_add b hb n1 k

/-- Positive for base `≥ 1` and exponent `≥ 1`. -/
def pos_prop : Prop :=
  ∀ b e : Int, Pre b e → 1 ≤ b → 1 ≤ e → ∀ v : Int, prog b e = .ok v → 1 ≤ v

theorem pos_thm : pos_prop := by
  intro b e h hb he v hv
  obtain ⟨n, rfl⟩ := eq_natCast_of_nonneg h.2
  rw [prog_natCast b n h.1] at hv
  simp only [Result.ok.injEq] at hv
  subst hv
  have h1 : b ^ 0 ≤ b ^ (0 + n) := pow_le_pow_add b hb 0 n
  simpa using h1

/-- The returned value is never negative. -/
def nonneg_prop : Prop :=
  ∀ b e : Int, Pre b e → ∀ v : Int, prog b e = .ok v → 0 ≤ v

theorem nonneg_thm : nonneg_prop := by
  intro b e h v hv
  obtain ⟨n, rfl⟩ := eq_natCast_of_nonneg h.2
  rw [prog_natCast b n h.1] at hv
  simp only [Result.ok.injEq] at hv
  subst hv
  exact pow_nonneg h.1 n

/-- The call raises exactly when the precondition fails (Python: `if not pre(...): raise`). -/
def error_iff_prop : Prop :=
  ∀ b e : Int, ((prog b e).isError = true ↔ ¬ Pre b e)

theorem error_iff_thm : error_iff_prop := by
  intro b e
  by_cases h : Pre b e
  · have h1 : (prog b e).isError = false := by
      rw [prog_of_Pre b e h]
      rfl
    rw [h1]
    refine ⟨?_, ?_⟩
    · intro hh
      cases hh
    · intro hn
      exact False.elim (absurd h hn)
  · have h1 : (prog b e).isError = true := by
      rw [prog_of_notPre b e h]
      rfl
    rw [h1]
    exact ⟨fun _ => h, fun _ => rfl⟩

/-! ## Postcondition -/

/-- Postcondition of the Python program: an admissible call returns exactly `base ^ exponent`
(a non-negative integer), and an inadmissible call raises `ValueError` with the documented
message. -/
def Post_prop (base exponent : Int) (r : Result) : Prop :=
  (Pre base exponent → ∃ v : Int, r = .ok v ∧ v = base ^ exponent.toNat ∧ 0 ≤ v) ∧
  (¬ Pre base exponent → r = .valueError (errMsg base exponent))

/-- Executable Boolean form of `Post_prop`; `postCheck_iff` proves the correspondence. -/
def postCheck (base exponent : Int) (r : Result) : Bool :=
  match r with
  | .ok v => preBool base exponent && decide (v = base ^ exponent.toNat ∧ 0 ≤ v)
  | .valueError msg => notPreBool base exponent && decide (msg = errMsg base exponent)

theorem postCheck_iff (base exponent : Int) (r : Result) :
    postCheck base exponent r = true ↔ Post_prop base exponent r := by
  by_cases h : Pre base exponent
  · cases r with
    | ok v =>
        simp [postCheck, preBool_true base exponent h]
        constructor
        · intro hv
          exact ⟨fun _ => ⟨v, rfl, hv.1, hv.2⟩, fun hn => absurd h hn⟩
        · rintro ⟨h1, _⟩
          obtain ⟨w, hw, hval, hnn⟩ := h1 h
          simp only [Result.ok.injEq] at hw
          subst hw
          exact ⟨hval, hnn⟩
    | valueError msg =>
        simp [postCheck, notPreBool_false base exponent h]
        intro hpost
        obtain ⟨w, hw, _, _⟩ := hpost.1 h
        cases hw
  · cases r with
    | ok v =>
        simp [postCheck, preBool_false base exponent h]
        intro hpost
        cases hpost.2 h
    | valueError msg =>
        simp [postCheck, notPreBool_true base exponent h]
        constructor
        · intro hm
          exact ⟨fun hp => absurd hp h, fun _ => by rw [hm]⟩
        · rintro ⟨_, h2⟩
          have ht := h2 h
          simp only [Result.valueError.injEq] at ht
          exact ht

/-! ## Property-based tests

Each executable property stated above is checked on many inputs: exhaustively on a bounded grid
(`native_decide`, which is only ever used inside `example` tests) and randomly with `Plausible`.
The randomized checks are phrased over `Nat` samplers, or over explicitly negative integers, so
that every generated sample is admissible and no sample is discarded.  `postCheck_iff` connects
the Boolean post-condition test `postCheck` with `Post_prop`.
-/

-- PBT for `exp_zero_prop`: power(n, 0) = 1
example : (List.range 30).all (fun n => decide (prog (n : Int) 0 = .ok 1)) = true := by
  native_decide
#eval Plausible.Testable.check (∀ b : Nat, prog (b : Int) 0 = .ok 1)

-- PBT for `zero_base_prop`: power(0, n) = 0 for n > 0
example : (List.range 30).all (fun n => decide (prog 0 ((n : Int) + 1) = .ok 0)) = true := by
  native_decide
#eval Plausible.Testable.check (∀ e : Nat, prog 0 ((e : Int) + 1) = .ok 0)

-- PBT for `zero_zero_prop`: power(0, 0) = 1
example : decide (prog 0 0 = .ok 1) = true := by native_decide

-- PBT for `error_prop`, `error_msg_prop` and `neg_prop`: pre-violations raise `ValueError`
example : (List.range 20).all (fun n =>
    (prog (-1 - (n : Int)) 2).isError && (prog 2 (-1 - (n : Int))).isError) = true := by
  native_decide
example : (List.range 20).all (fun n =>
    decide (prog (-1 - (n : Int)) 2 = .valueError (errMsg (-1 - (n : Int)) 2)) &&
    decide (prog 2 (-1 - (n : Int)) = .valueError (errMsg 2 (-1 - (n : Int))))) = true := by
  native_decide
#eval Plausible.Testable.check (∀ b e : Nat,
  ((prog (-1 - (b : Int)) (e : Int)).isError && (prog (b : Int) (-1 - (e : Int))).isError) = true)
#eval Plausible.Testable.check (∀ b e : Nat,
  prog (-1 - (b : Int)) (e : Int) = .valueError (errMsg (-1 - (b : Int)) (e : Int)))
#eval Plausible.Testable.check (∀ b : Int, ∀ e : Nat,
  prog b (-1 - (e : Int)) = .valueError (errMsg b (-1 - (e : Int))))

-- PBT for `spec_prop`: admissible calls return base ^ exponent
example : (List.range 12).all (fun n => (List.range 12).all (fun m =>
    decide (prog (n : Int) (m : Int) = .ok ((n : Int) ^ m)))) = true := by native_decide
#eval Plausible.Testable.check (∀ b e : Nat, prog (b : Int) (e : Int) = .ok ((b : Int) ^ e))

-- PBT for `pre_nat_prop`: `Pre` is exactly "both arguments are natural numbers"
example : (List.range 20).all (fun n => (List.range 20).all (fun m =>
    decide (Pre (n : Int) (m : Int)) &&
    decide (¬ Pre (-1 - (n : Int)) (m : Int)) &&
    decide (¬ Pre (n : Int) (-1 - (m : Int))))) = true := by native_decide
#eval Plausible.Testable.check (∀ b e : Nat, Pre (b : Int) (e : Int))
#eval Plausible.Testable.check (∀ b : Int, ∀ e : Nat, ¬ Pre b (-1 - (e : Int)))

-- PBT for `step_prop`: power(b, e + 1) = power(b, e) * b
example : (List.range 10).all (fun n => (List.range 10).all (fun m =>
    decide (prog (n : Int) ((m : Int) + 1) =
      (prog (n : Int) (m : Int)).map (fun v => v * (n : Int))))) = true := by native_decide
#eval Plausible.Testable.check (∀ b e : Nat,
  prog (b : Int) ((e : Int) + 1) = (prog (b : Int) (e : Int)).map (fun v => v * (b : Int)))

-- PBT for `add_prop`: power(b, e1 + e2) = power(b, e1) * power(b, e2)
example : (List.range 8).all (fun n => (List.range 8).all (fun m => (List.range 6).all (fun b =>
    decide (prog (b : Int) ((n : Int) + (m : Int)) =
      (prog (b : Int) (n : Int)).bind
        (fun v1 => (prog (b : Int) (m : Int)).map (fun v2 => v1 * v2)))))) = true := by
  native_decide
#eval Plausible.Testable.check (∀ b e1 e2 : Nat,
  prog (b : Int) ((e1 : Int) + (e2 : Int)) =
    (prog (b : Int) (e1 : Int)).bind
      (fun v1 => (prog (b : Int) (e2 : Int)).map (fun v2 => v1 * v2)))

-- PBT for `mul_prop`: power(b1 * b2, e) = power(b1, e) * power(b2, e)
example : (List.range 6).all (fun n => (List.range 6).all (fun m => (List.range 6).all (fun b =>
    decide (prog ((b : Int) * (m : Int)) (n : Int) =
      (prog (b : Int) (n : Int)).bind
        (fun v1 => (prog (m : Int) (n : Int)).map (fun v2 => v1 * v2)))))) = true := by
  native_decide
#eval Plausible.Testable.check (∀ b1 b2 e : Nat,
  prog ((b1 : Int) * (b2 : Int)) (e : Int) =
    (prog (b1 : Int) (e : Int)).bind
      (fun v1 => (prog (b2 : Int) (e : Int)).map (fun v2 => v1 * v2)))

-- PBT for `one_prop`: power(1, e) = 1
example : (List.range 25).all (fun n => decide (prog 1 (n : Int) = .ok 1)) = true := by
  native_decide
#eval Plausible.Testable.check (∀ e : Nat, prog 1 (e : Int) = .ok 1)

-- PBT for `pow_eq_prop`: the loop computes Mathlib's power
example : (List.range 20).all (fun n => (List.range 12).all (fun m =>
    decide (powerNat (n : Int) m = (n : Int) ^ m))) = true := by native_decide
#eval Plausible.Testable.check (∀ b : Int, ∀ n : Nat, powerNat b n = b ^ n)

-- PBT for `monotone_prop`: monotone in the exponent for bases >= 1
example : (List.range 12).all (fun n => (List.range 12).all (fun m => (List.range 4).all (fun b =>
    decide (n ≤ m → powerNat ((b : Int) + 1) n ≤ powerNat ((b : Int) + 1) m)))) = true := by
  native_decide
#eval Plausible.Testable.check (∀ b n k : Nat,
  powerNat ((b : Int) + 1) n ≤ powerNat ((b : Int) + 1) (n + k))

-- PBT for `pos_prop`: positive for base >= 1 and exponent >= 1
example : (List.range 8).all (fun n => (List.range 8).all (fun m =>
    decide (1 ≤ powerNat ((n : Int) + 1) (m + 1)))) = true := by native_decide
#eval Plausible.Testable.check (∀ b e : Nat, 1 ≤ powerNat ((b : Int) + 1) (e + 1))

-- PBT for `nonneg_prop`: the result is never negative
example : (List.range 15).all (fun n => (List.range 15).all (fun m =>
    decide (0 ≤ powerNat (n : Int) m))) = true := by native_decide
#eval Plausible.Testable.check (∀ b e : Nat, 0 ≤ powerNat (b : Int) e)

-- PBT for `error_iff_prop`: raises iff the precondition fails
example : (List.range 15).all (fun n => (List.range 15).all (fun m =>
    decide ((prog (n : Int) (m : Int)).isError = false) &&
    decide ((prog (-1 - (n : Int)) (m : Int)).isError = true))) = true := by native_decide
#eval Plausible.Testable.check (∀ b e : Nat, (prog (b : Int) (e : Int)).isError = false)
#eval Plausible.Testable.check (∀ b : Int, ∀ e : Nat, (prog b (-1 - (e : Int))).isError = true)

-- PBT for `Post_prop`, via its executable form `postCheck` (see `postCheck_iff`)
example : (List.range 12).all (fun n => (List.range 12).all (fun m =>
    postCheck (n : Int) (m : Int) (prog (n : Int) (m : Int)) &&
    postCheck (-1 - (n : Int)) (m : Int) (prog (-1 - (n : Int)) (m : Int)) &&
    postCheck (n : Int) (-1 - (m : Int)) (prog (n : Int) (-1 - (m : Int))))) = true := by
  native_decide
#eval Plausible.Testable.check (∀ b e : Int, postCheck b e (prog b e) = true)


/-! ## Correctness -/

/-- `prog` satisfies the postcondition on every input. -/
theorem prog_post (base exponent : Int) : Post_prop base exponent (prog base exponent) := by
  refine ⟨?_, ?_⟩
  · intro h
    refine ⟨base ^ exponent.toNat, ?_, rfl, pow_nonneg h.1 exponent.toNat⟩
    rw [prog_of_Pre base exponent h, powerNat_eq_pow]
  · intro h
    exact prog_of_notPre base exponent h

/-- Correctness of the implementation: the precondition implies the postcondition. -/
theorem correctness_thm (base exponent : Int) (h : Pre base exponent) :
    Post_prop base exponent (prog base exponent) := by
  have hall := prog_post base exponent
  exact ⟨fun _ => hall.1 h, fun hn => absurd h hn⟩

/-! ## Imperative implementation (mutable state, `Id.run do`) -/

/-- Imperative accumulation loop: `result` is a mutable variable updated inside an `Id.run do`
block, exactly as the Python loop `result = 1; for _ in range(exponent): result *= base`. -/
def impLoop (base : Int) (exponent : Nat) : Int :=
  Id.run do
    let mut result : Int := 1
    for _ in List.range exponent do
      result := result * base
    pure result

/-- Imperative implementation of the Python function `prog`. -/
def progImp (base exponent : Int) : Result :=
  match preBool base exponent with
  | true => .ok (impLoop base (Int.toNat exponent))
  | false => .valueError (errMsg base exponent)

/-- The mutable loop is the left fold over `List.range exponent`. -/
theorem foldl_range (b : Int) : ∀ n : Nat,
    List.foldl (fun acc _ => acc * b) 1 (List.range n) = powerNat b n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, ih]
      simp only [List.foldl_cons, List.foldl_nil, powerNat]

/-- The imperative loop computes `powerNat`. -/
theorem impLoop_spec (b : Int) (n : Nat) : impLoop b n = powerNat b n := by
  simp only [impLoop, bind_pure_comp, map_pure, List.forIn_pure_yield_eq_foldl, bind_pure,
    Id.run_pure]
  exact foldl_range b n

theorem progImp_of_Pre (base exponent : Int) (h : Pre base exponent) :
    progImp base exponent = .ok (impLoop base (Int.toNat exponent)) := by
  simp only [progImp, preBool_true base exponent h]

theorem progImp_of_notPre (base exponent : Int) (h : ¬ Pre base exponent) :
    progImp base exponent = .valueError (errMsg base exponent) := by
  simp only [progImp, preBool_false base exponent h]

/-! ## Imperative tests -/

example : progImp 2 3 = .ok 8 := by native_decide
#eval progImp 2 3
example : progImp 3 4 = .ok 81 := by native_decide
example : progImp 2 10 = .ok 1024 := by native_decide
#eval progImp 2 10
example : progImp 5 0 = .ok 1 := by native_decide
example : progImp 0 0 = .ok 1 := by native_decide
example : progImp 0 7 = .ok 0 := by native_decide
example : progImp (-1) 2 = .valueError (errMsg (-1) 2) := by native_decide
example : progImp 2 (-1) = .valueError (errMsg 2 (-1)) := by native_decide
example : impLoop 3 5 = 243 := by native_decide
#eval impLoop 3 5

-- the Python test harness also passes for the imperative implementation
example : check progImp = true := by native_decide

/-- The Python test harness passes for the imperative implementation (kernel-checked). -/
theorem check_imp_thm : check progImp = true := by decide

-- property-based test: the imperative version agrees with the functional one everywhere
example : (List.range 12).all (fun n => (List.range 12).all (fun m =>
    decide (progImp (n : Int) (m : Int) = prog (n : Int) (m : Int)) &&
    decide (progImp (-1 - (n : Int)) (m : Int) = prog (-1 - (n : Int)) (m : Int)))) = true := by
  native_decide
#eval Plausible.Testable.check (∀ b e : Int, progImp b e = prog b e)

/-! ## Equivalence of the functional and the imperative implementations -/

/-- The imperative implementation is extensionally equal to the functional one, on admissible
and on inadmissible inputs alike. -/
theorem equivalence_thm : ∀ base exponent : Int, progImp base exponent = prog base exponent := by
  intro b e
  by_cases h : Pre b e
  · rw [progImp_of_Pre b e h, impLoop_spec b (Int.toNat e), prog_of_Pre b e h]
  · rw [progImp_of_notPre b e h, prog_of_notPre b e h]

end «19_MyPower»
