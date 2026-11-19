import Mathlib
namespace Agent

/-!
# HumanEval 32: polynomial evaluation and a zero by bisection

Coefficients are in increasing order of degree. `FloatLayer` executes the
Python summation, doubling search and left-endpoint bisection (including its
strict product comparison). The mathematical model uses real arithmetic:
its guarantee is distance at most `1e-10` from a zero, not exact equality of
the returned endpoint with a zero, and not a coefficient-independent bound
on the residual. IEEE overflow/NaN and rounding are not real arithmetic.
-/

namespace humaneval_32_poly

namespace FloatLayer

def poly (xs : List Float) (x : Float) : Float :=
  (xs.zipIdx).foldl (fun s ci => s + ci.1 * x.pow ci.2.toFloat) 0

partial def expand (xs : List Float) (a b : Float) : Float × Float :=
  if poly xs a * poly xs b > 0 then expand xs (a * 2) (b * 2)
  else (a, b)

partial def bisect (xs : List Float) (a b : Float) : Float :=
  if b - a > 0.0000000001 then
    let c := (a + b) / 2
    if poly xs c * poly xs a > 0 then bisect xs c b
    else bisect xs a c
  else a

def find_zero (xs : List Float) : Float :=
  let ab := expand xs (-1) 1
  bisect xs ab.1 ab.2

end FloatLayer

/-- A finite execution prefix, shared by the mathematical loop models. -/
def runN {α : Type} (step : α → α) : Nat → α → α
  | 0, s => s
  | n + 1, s => step (runN step n s)

namespace RealLayer

/-- Horner evaluation, proved below to equal the enumerated power sum. -/
def poly : List ℝ → ℝ → ℝ
  | [], _ => 0
  | a :: xs, x => a + x * poly xs x

def powerSum : List ℝ → ℝ → Nat → ℝ
  | [], _, _ => 0
  | a :: xs, x, i => a * x ^ i + powerSum xs x (i + 1)

noncomputable def polynomial : List ℝ → Polynomial ℝ
  | [] => 0
  | a :: xs => Polynomial.C a + Polynomial.X * polynomial xs

noncomputable def tolerance : ℝ := 1 / 10000000000

def enumeratedSum (xs : List ℝ) (x : ℝ) : ℝ :=
  xs.zipIdx.foldl (fun s ci => s + ci.1 * x ^ ci.2) 0

def double (s : ℝ × ℝ) : ℝ × ℝ := (s.1 * 2, s.2 * 2)

/-- Bounds for |p| and its Lipschitz constant on [-R,R]. -/
noncomputable def normBounds : List ℝ → ℝ → ℝ × ℝ
  | [], _ => (0, 0)
  | a :: xs, R =>
    let b := normBounds xs R
    (|a| + R * b.1, b.1 + R * b.2)

def radius (n : Nat) : ℝ := 2 ^ n

def initial (n : Nat) : ℝ × ℝ := (-radius n, radius n)

noncomputable def step (xs : List ℝ) (s : ℝ × ℝ) : ℝ × ℝ := by
  classical
  exact if poly xs ((s.1 + s.2) / 2) * poly xs s.1 > 0
    then ((s.1 + s.2) / 2, s.2) else (s.1, (s.1 + s.2) / 2)

def expansionOK (xs : List ℝ) (n : Nat) : Prop :=
  poly xs (initial n).1 * poly xs (initial n).2 ≤ 0

/-- First successful doubling; the fallback is irrelevant on `Pre`. -/
noncomputable def expansionCount (xs : List ℝ) : Nat := by
  classical
  exact if h : ∃ n, expansionOK xs n then Nat.find h else 0

/-- First iteration at which the interval is no wider than the tolerance. -/
noncomputable def refinementCount (s : ℝ × ℝ) : Nat := by
  classical
  exact if h : ∃ n : Nat, (s.2 - s.1) / 2 ^ n ≤ tolerance then Nat.find h else 0

noncomputable def bracket (xs : List ℝ) : ℝ × ℝ := initial (expansionCount xs)

noncomputable def resultInterval (xs : List ℝ) : ℝ × ℝ :=
  runN (step xs) (refinementCount (bracket xs)) (bracket xs)

noncomputable def find_zero (xs : List ℝ) : ℝ := (resultInterval xs).1

end RealLayer

example : (FloatLayer.poly [1, 2] 3 == 7) = true := by native_decide
example : (FloatLayer.poly [-6, 11, -6, 1] 1 == 0) = true := by native_decide
example : (FloatLayer.find_zero [1, 2] + 0.5).abs < 0.0000000001 := by native_decide
example : (FloatLayer.find_zero [-6, 11, -6, 1] - 1).abs < 0.0000000001 := by native_decide
#eval FloatLayer.find_zero [1, 2]
#eval FloatLayer.find_zero [-6, 11, -6, 1]



/-- Exactly the documented domain: an even, nonzero number of coefficients,
with the last coefficient nonzero. The other coefficients may be zero. -/
def Pre (xs : List ℝ) : Prop :=
  ∃ ys a, xs = ys ++ [a] ∧ a ≠ 0 ∧ Odd ys.length


open RealLayer

/-- Finite big-step semantics of a while loop: the guard is true for each
update and false at precisely the final state. No iteration cap is built in. -/
inductive WhileExec {α : Type} (guard : α → Prop) (update : α → α) : α → α → Prop
  | stop (s : α) (h : ¬guard s) : WhileExec guard update s s
  | next {s t : α} (h : guard s) (rest : WhileExec guard update (update s) t) :
      WhileExec guard update s t

lemma runN_shift {α : Type} (f : α → α) (n : Nat) (s : α) :
    runN f n (f s) = runN f (n + 1) s := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [runN] using congrArg f ih

lemma while_of_first_exit {α : Type} (guard : α → Prop) (f : α → α)
    (n : Nat) (s : α)
    (hbefore : ∀ k < n, guard (runN f k s))
    (hstop : ¬guard (runN f n s)) : WhileExec guard f s (runN f n s) := by
  induction n generalizing s with
  | zero => exact .stop s hstop
  | succ n ih =>
    have hnext : WhileExec guard f (f s) (runN f n (f s)) := by
      apply ih
      · intro k hk
        rw [runN_shift]
        exact hbefore (k + 1) (by omega)
      · rw [runN_shift]
        exact hstop
    have hfirst : guard s := hbefore 0 (by omega)
    simpa only [runN_shift] using WhileExec.next hfirst hnext

lemma while_deterministic {α : Type} {guard : α → Prop} {f : α → α} {s t u : α}
    (ht : WhileExec guard f s t) (hu : WhileExec guard f s u) : t = u := by
  induction ht generalizing u with
  | stop s hn =>
    cases hu with
    | stop => rfl
    | next hg _ => exact (hn hg).elim
  | next hg rest ih =>
    cases hu with
    | stop _ hn => exact (hn hg).elim
    | next _ rest' => exact ih rest'

/-- The first loop really visits (-2^n,2^n), not arbitrary brackets. -/
lemma doubling_state (n : Nat) : runN double n (-1, 1) = initial n := by
  induction n with
  | zero => norm_num [runN, initial, radius]
  | succ n ih =>
    rw [runN, ih]
    ext <;> simp [double, initial, radius, pow_succ]


lemma eval_polynomial (xs : List ℝ) (x : ℝ) :
    (polynomial xs).eval x = poly xs x := by
  induction xs with
  | nil => simp [polynomial, poly]
  | cons a xs ih => simp [polynomial, poly, ih]

lemma powerSum_factor (xs : List ℝ) (x : ℝ) (i : Nat) :
    powerSum xs x i = x ^ i * poly xs x := by
  induction xs generalizing i with
  | nil => simp [powerSum, poly]
  | cons a xs ih => rw [powerSum, ih, poly, pow_succ]; ring

lemma enumeratedSum_aux (xs : List ℝ) (x : ℝ) (i : Nat) (s : ℝ) :
    (xs.zipIdx i).foldl (fun acc ci => acc + ci.1 * x ^ ci.2) s = s + powerSum xs x i := by
  induction xs generalizing i s with
  | nil => simp [powerSum]
  | cons a xs ih =>
    rw [List.zipIdx_cons, List.foldl_cons, ih, powerSum]
    ring

lemma enumeratedSum_eq (xs : List ℝ) (x : ℝ) : enumeratedSum xs x = poly xs x := by
  rw [enumeratedSum, enumeratedSum_aux, powerSum_factor]
  simp

def poly_prop (xs : List ℝ) : Prop :=
  ∀ x, poly xs x = powerSum xs x 0 ∧ poly xs x = (polynomial xs).eval x ∧
    poly xs x = enumeratedSum xs x

theorem poly_thm (xs : List ℝ) : poly_prop xs := by
  intro x
  constructor
  · simpa using (powerSum_factor xs x 0).symm
  · exact ⟨(eval_polynomial xs x).symm, (enumeratedSum_eq xs x).symm⟩

lemma polynomial_degree (ys : List ℝ) (a : ℝ) (ha : a ≠ 0) :
    polynomial (ys ++ [a]) ≠ 0 ∧ (polynomial (ys ++ [a])).natDegree = ys.length := by
  induction ys with
  | nil => simpa [polynomial] using ha
  | cons b ys ih =>
    have hd : (polynomial ((b :: ys) ++ [a])).natDegree = ys.length + 1 := by
      simpa only [List.cons_append, polynomial, Polynomial.natDegree_C_add,
        Polynomial.natDegree_X_mul ih.1] using congrArg (· + 1) ih.2
    refine ⟨?_, hd⟩
    intro hz
    have hzdeg : (polynomial ((b :: ys) ++ [a])).natDegree = 0 := by
      rw [hz, Polynomial.natDegree_zero]
    omega

lemma odd_degree (xs : List ℝ) (h : Pre xs) :
    polynomial xs ≠ 0 ∧ Odd (polynomial xs).natDegree := by
  obtain ⟨ys, a, rfl, ha, ho⟩ := h
  obtain ⟨hp, hd⟩ := polynomial_degree ys a ha
  exact ⟨hp, hd ▸ ho⟩

/-- Opposite signs are eventually reached by the unbounded doubling search. -/
lemma expansion_exists (xs : List ℝ) (h : Pre xs) : ∃ n, expansionOK xs n := by
  obtain ⟨hp, ho⟩ := odd_degree xs h
  let p := polynomial xs
  have hp' : p ≠ 0 := hp
  have hn : 0 < p.natDegree := by
    obtain ⟨k, hk⟩ := ho
    dsimp [p]
    omega
  have hc : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp'
  have hcomp : p.comp (-Polynomial.X) ≠ 0 := by
    intro he
    have he' := congrArg Polynomial.natDegree he
    simp only [Polynomial.natDegree_comp, Polynomial.natDegree_neg,
      Polynomial.natDegree_X, mul_one, Polynomial.natDegree_zero] at he'
    omega
  have hl : (p.comp (-Polynomial.X)).leadingCoeff = -p.leadingCoeff := by
    rw [Polynomial.leadingCoeff_comp (by simp), Polynomial.leadingCoeff_neg,
      Polynomial.leadingCoeff_X, ho.neg_pow, one_pow]
    ring
  let q := p.comp (-Polynomial.X) * p
  have hqd : 0 < q.degree := by
    apply Polynomial.natDegree_pos_iff_degree_pos.mp
    dsimp [q]
    rw [Polynomial.natDegree_mul hcomp hp', Polynomial.natDegree_comp]
    simp only [Polynomial.natDegree_neg, Polynomial.natDegree_X, mul_one]
    omega
  have hql : q.leadingCoeff ≤ 0 := by
    dsimp [q]
    rw [Polynomial.leadingCoeff_mul, hl]
    nlinarith [sq_nonneg p.leadingCoeff]
  have ht := (q.tendsto_atBot_of_leadingCoeff_nonpos hqd hql).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  obtain ⟨n, hn⟩ := (ht.eventually (Filter.eventually_le_atBot (0 : ℝ))).exists
  refine ⟨n, ?_⟩
  simpa [q, p, Polynomial.eval_mul, Polynomial.eval_comp, eval_polynomial,
    expansionOK, initial, radius] using hn

def expansion_prop (xs : List ℝ) : Prop :=
  expansionOK xs (expansionCount xs) ∧
  ∀ n < expansionCount xs, 0 < poly xs (initial n).1 * poly xs (initial n).2

theorem expansion_thm (xs : List ℝ) (h : Pre xs) : expansion_prop xs := by
  classical
  have he := expansion_exists xs h
  simp only [expansion_prop, expansionCount, dif_pos he]
  refine ⟨Nat.find_spec he, ?_⟩
  intro n hn
  exact lt_of_not_ge (Nat.find_min he hn)

lemma tolerance_pos : 0 < tolerance := by norm_num [tolerance]

lemma refinement_exists (s : ℝ × ℝ) :
    ∃ n : Nat, (s.2 - s.1) / 2 ^ n ≤ tolerance := by
  obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt
    (by norm_num : (1 : ℝ) < 2)).eventually
      (Filter.eventually_gt_atTop ((s.2 - s.1) / tolerance))).exists
  refine ⟨n, (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).mpr ?_⟩
  have hh := (div_lt_iff₀ tolerance_pos).mp hn
  nlinarith

lemma refinement_spec (s : ℝ × ℝ) :
    (s.2 - s.1) / 2 ^ refinementCount s ≤ tolerance ∧
    ∀ n < refinementCount s, tolerance < (s.2 - s.1) / 2 ^ n := by
  classical
  have he := refinement_exists s
  simp only [refinementCount, dif_pos he]
  exact ⟨Nat.find_spec he, fun n hn => lt_of_not_ge (Nat.find_min he hn)⟩

lemma replace_left_sign {a b c : ℝ} (hab : a * b ≤ 0) (hca : 0 < c * a) :
    c * b ≤ 0 := by
  rcases mul_pos_iff.mp hca with ⟨hc, ha⟩ | ⟨hc, ha⟩
  · have hb : b ≤ 0 := by nlinarith
    exact mul_nonpos_of_nonneg_of_nonpos hc.le hb
  · have hb : 0 ≤ b := by nlinarith
    exact mul_nonpos_of_nonpos_of_nonneg hc.le hb

lemma step_width (xs : List ℝ) (s : ℝ × ℝ) :
    (step xs s).2 - (step xs s).1 = (s.2 - s.1) / 2 := by
  classical
  unfold step
  split_ifs <;> dsimp <;> ring

lemma step_invariant (xs : List ℝ) (s : ℝ × ℝ)
    (hs : s.1 ≤ s.2 ∧ poly xs s.1 * poly xs s.2 ≤ 0) :
    (step xs s).1 ≤ (step xs s).2 ∧
    poly xs (step xs s).1 * poly xs (step xs s).2 ≤ 0 := by
  classical
  unfold step
  split_ifs with hc
  · exact ⟨by dsimp; linarith [hs.1], replace_left_sign hs.2 hc⟩
  · refine ⟨by dsimp; linarith [hs.1], ?_⟩
    dsimp
    simpa [mul_comm] using le_of_not_gt hc

lemma step_nested (xs : List ℝ) (s : ℝ × ℝ) (hs : s.1 ≤ s.2) :
    s.1 ≤ (step xs s).1 ∧ (step xs s).2 ≤ s.2 := by
  classical
  unfold step
  split_ifs <;> dsimp <;> constructor <;> linarith

lemma runN_width (xs : List ℝ) (n : Nat) (s : ℝ × ℝ) :
    (runN (step xs) n s).2 - (runN (step xs) n s).1 = (s.2 - s.1) / 2 ^ n := by
  induction n with
  | zero => simp [runN]
  | succ n ih => rw [runN, step_width, ih, pow_succ]; ring

lemma runN_invariant (xs : List ℝ) (n : Nat) (s : ℝ × ℝ)
    (hs : s.1 ≤ s.2 ∧ poly xs s.1 * poly xs s.2 ≤ 0) :
    (runN (step xs) n s).1 ≤ (runN (step xs) n s).2 ∧
    poly xs (runN (step xs) n s).1 * poly xs (runN (step xs) n s).2 ≤ 0 := by
  induction n with
  | zero => exact hs
  | succ n ih => exact step_invariant xs _ ih

lemma runN_nested (xs : List ℝ) (n : Nat) (s : ℝ × ℝ) (hs : s.1 ≤ s.2) :
    s.1 ≤ (runN (step xs) n s).1 ∧ (runN (step xs) n s).2 ≤ s.2 := by
  induction n with
  | zero => exact ⟨le_rfl, le_rfl⟩
  | succ n ih =>
    have hw : (runN (step xs) n s).1 ≤ (runN (step xs) n s).2 := by
      have hd := runN_width xs n s
      have hn : 0 ≤ (s.2 - s.1) / 2 ^ n := div_nonneg (sub_nonneg.mpr hs) (by positivity)
      linarith
    have hn := step_nested xs (runN (step xs) n s) hw
    exact ⟨ih.1.trans hn.1, hn.2.trans ih.2⟩

lemma bracket_invariant (xs : List ℝ) (h : Pre xs) :
    (bracket xs).1 ≤ (bracket xs).2 ∧
    poly xs (bracket xs).1 * poly xs (bracket xs).2 ≤ 0 := by
  refine ⟨?_, (expansion_thm xs h).1⟩
  dsimp [bracket, initial, radius]
  have : (0 : ℝ) ≤ 2 ^ expansionCount xs := by positivity
  linarith

def bisection_prop (xs : List ℝ) : Prop :=
  let s := resultInterval xs
  s.1 ≤ s.2 ∧ poly xs s.1 * poly xs s.2 ≤ 0 ∧
  s.2 - s.1 ≤ tolerance ∧
  (bracket xs).1 ≤ s.1 ∧ s.2 ≤ (bracket xs).2 ∧
  ∀ n < refinementCount (bracket xs),
    tolerance < (runN (step xs) n (bracket xs)).2 - (runN (step xs) n (bracket xs)).1

theorem bisection_thm (xs : List ℝ) (h : Pre xs) : bisection_prop xs := by
  have hb := bracket_invariant xs h
  have hi := runN_invariant xs (refinementCount (bracket xs)) (bracket xs) hb
  have hn := runN_nested xs (refinementCount (bracket xs)) (bracket xs) hb.1
  refine ⟨hi.1, hi.2, ?_, hn.1, hn.2, ?_⟩
  · rw [resultInterval, runN_width]
    exact (refinement_spec _).1
  · intro n hn
    rw [runN_width]
    exact (refinement_spec _).2 n hn

/-- Adequacy of the mathematical model for the original two while loops.
Together with `while_deterministic`, this identifies their unique final
interval; the count selection is not an alternative root-selection rule. -/
theorem loop_semantics_thm (xs : List ℝ) (h : Pre xs) :
    WhileExec (fun s => 0 < poly xs s.1 * poly xs s.2) double (-1, 1) (bracket xs) ∧
    WhileExec (fun s => tolerance < s.2 - s.1) (step xs) (bracket xs) (resultInterval xs) := by
  constructor
  · have he := expansion_thm xs h
    have hex := while_of_first_exit
      (fun s : ℝ × ℝ => 0 < poly xs s.1 * poly xs s.2)
      double (expansionCount xs) (-1, 1)
      (by intro k hk; rw [doubling_state]; exact he.2 k hk)
      (by rw [doubling_state]; exact not_lt.mpr he.1)
    simpa only [doubling_state, bracket] using hex
  · apply while_of_first_exit
    · intro k hk
      rw [runN_width]
      exact (refinement_spec (bracket xs)).2 k hk
    · rw [runN_width]
      exact not_lt.mpr (refinement_spec (bracket xs)).1

lemma root_in_interval (xs : List ℝ) (s : ℝ × ℝ)
    (hs : s.1 ≤ s.2 ∧ poly xs s.1 * poly xs s.2 ≤ 0) :
    ∃ z, z ∈ Set.Icc s.1 s.2 ∧ poly xs z = 0 := by
  have hc : Continuous (poly xs) := by
    simpa only [eval_polynomial] using (polynomial xs).continuous
  rcases mul_nonpos_iff.mp hs.2 with hsign | hsign
  · exact intermediate_value_Icc' hs.1 hc.continuousOn ⟨hsign.2, hsign.1⟩
  · exact intermediate_value_Icc hs.1 hc.continuousOn ⟨hsign.1, hsign.2⟩

def zero_prop (xs : List ℝ) : Prop :=
  ∃ z, poly xs z = 0 ∧ find_zero xs ≤ z ∧
    z ≤ (resultInterval xs).2 ∧ |find_zero xs - z| ≤ tolerance

theorem zero_thm (xs : List ℝ) (h : Pre xs) : zero_prop xs := by
  have hb := bisection_thm xs h
  obtain ⟨z, hz, he⟩ := root_in_interval xs (resultInterval xs) ⟨hb.1, hb.2.1⟩
  refine ⟨z, he, hz.1, hz.2, ?_⟩
  dsimp [find_zero]
  rw [abs_of_nonpos (sub_nonpos.mpr hz.1)]
  linarith [hb.2.2.1, hz.2]

lemma normBounds_nonneg (xs : List ℝ) (R : ℝ) (hR : 0 ≤ R) :
    0 ≤ (normBounds xs R).1 ∧ 0 ≤ (normBounds xs R).2 := by
  induction xs with
  | nil => exact ⟨le_rfl, le_rfl⟩
  | cons a xs ih =>
    exact ⟨add_nonneg (abs_nonneg a) (mul_nonneg hR ih.1),
      add_nonneg ih.1 (mul_nonneg hR ih.2)⟩

lemma poly_abs_bound (xs : List ℝ) (R x : ℝ) (hR : 0 ≤ R) (hx : |x| ≤ R) :
    |poly xs x| ≤ (normBounds xs R).1 := by
  induction xs with
  | nil => simp [poly, normBounds]
  | cons a xs ih =>
    change |a + x * poly xs x| ≤ |a| + R * (normBounds xs R).1
    calc
      _ ≤ |a| + |x * poly xs x| := abs_add _ _
      _ = |a| + |x| * |poly xs x| := by rw [abs_mul]
      _ ≤ _ := by gcongr

lemma poly_lipschitz (xs : List ℝ) (R x y : ℝ) (hR : 0 ≤ R)
    (hx : |x| ≤ R) (hy : |y| ≤ R) :
    |poly xs x - poly xs y| ≤ (normBounds xs R).2 * |x - y| := by
  induction xs with
  | nil => simp [poly, normBounds]
  | cons a xs ih =>
    change |(a + x * poly xs x) - (a + y * poly xs y)| ≤
      ((normBounds xs R).1 + R * (normBounds xs R).2) * |x - y|
    calc
      _ = |(x - y) * poly xs x + y * (poly xs x - poly xs y)| := by congr 1; ring
      _ ≤ |(x - y) * poly xs x| + |y * (poly xs x - poly xs y)| := abs_add _ _
      _ = |x - y| * |poly xs x| + |y| * |poly xs x - poly xs y| := by
        rw [abs_mul, abs_mul]
      _ ≤ |x - y| * (normBounds xs R).1 + R * ((normBounds xs R).2 * |x - y|) := by
        gcongr
        exact poly_abs_bound xs R x hR hx
      _ = _ := by ring

/-- Quantitative residual guarantee on the full domain. The coefficient-
dependent factor cannot in general be replaced by a universal constant. -/
def residual_prop (xs : List ℝ) : Prop :=
  |poly xs (find_zero xs)| ≤ (normBounds xs (radius (expansionCount xs))).2 * tolerance

theorem residual_thm (xs : List ℝ) (h : Pre xs) : residual_prop xs := by
  obtain ⟨z, hz, hlo, hhi, herr⟩ := zero_thm xs h
  have hb := bisection_thm xs h
  let R := radius (expansionCount xs)
  have hR : 0 ≤ R := by dsimp [R, radius]; positivity
  have hleft : -R ≤ find_zero xs := hb.2.2.2.1
  have hright : (resultInterval xs).2 ≤ R := hb.2.2.2.2.1
  have hx : |find_zero xs| ≤ R := abs_le.mpr ⟨hleft, hb.1.trans hright⟩
  have hzR : |z| ≤ R := abs_le.mpr ⟨hleft.trans hlo, hhi.trans hright⟩
  have hl := poly_lipschitz xs R (find_zero xs) z hR hx hzR
  calc
    |poly xs (find_zero xs)| ≤ (normBounds xs R).2 * |find_zero xs - z| := by
      simpa only [hz, sub_zero] using hl
    _ ≤ (normBounds xs R).2 * tolerance :=
      mul_le_mul_of_nonneg_left herr (normBounds_nonneg xs R hR).2

/-- Evaluation, both loop exits, and a certified nearby mathematical zero. -/
def Post_prop (xs : List ℝ) : Prop :=
  poly_prop xs ∧ expansion_prop xs ∧ bisection_prop xs ∧ zero_prop xs ∧ residual_prop xs


/-! ## Property-based tests

The propositions above quantify over `Real`, whose comparisons are not
executable. These bounded tests exercise their exact-integer evaluation
counterpart and the executable Float loop counterparts. They do not assert
that IEEE arithmetic and real arithmetic are identical. The known-root
families also test the existential witness in `zero_prop` and `Post_prop`.
-/

namespace Tests

def intPoly (xs : List Int) (x : Int) : Int :=
  xs.foldr (fun a r => a + x * r) 0

def intSum (xs : List Int) (x : Int) : Int :=
  xs.zipIdx.foldl (fun s ci => s + ci.1 * x ^ ci.2) 0

/- The 100 coefficient lists generated by the public Python check with
`random.Random(42)`, in order; zeros have been replaced by ones. -/
set_option maxHeartbeats 1000000 in
def publicInputs : List (List Int) :=
  [ [-10, -2],
    [-3, -6, -7, 7],
    [8, 3],
    [-10, -8],
    [-3, 6, 9, -10],
    [10, 7, 3, -3],
    [8, -2, -10, -5, 3, 1, -2, -6],
    [1, -7, -8, 2],
    [1, 1],
    [-9, 4, 7, -7, 2, -8],
    [10, 9, 1, 8, -4, -8],
    [-3, -1],
    [-3, -7],
    [-2, 4, 10, 1, -5, 1, 1, -4],
    [10, -8, 9, 10, -5, 7],
    [-5, 4, 2, -2],
    [1, -9, -3, -9],
    [2, -2, -8, -4, 8, 1],
    [10, 5, 2, 10],
    [-6, -2, -6, -3, 7, 7, -2, 8],
    [8, 2, 1, -3, -6, 6, 5, -8],
    [-7, -6],
    [3, 9, -8, 2],
    [9, 4, 6, -2, 7, -10, -7, 7],
    [10, 1, -7, -1, 3, -5],
    [-10, -2, 6, -5, 6, -7, 10, -1],
    [-6, 1, -5, 7],
    [9, 1],
    [-10, -7, 1, -1, -3, -9, -3, 8],
    [-8, 5],
    [7, -6],
    [5, 7, -5, -2],
    [-4, 7, -4, -1, 2, 10, 1, 4],
    [-7, -3, -3, -8, 1, -10, 8, 7],
    [8, -3, -10, -8],
    [-3, -8],
    [1, -8],
    [-2, 5, -4, 7],
    [8, 8, 5, -3],
    [3, -4, -7, -7, 3, 1, 3, 3],
    [-9, 10, 10, -7, -9, 2, 1, -7],
    [-4, -4, 7, 4],
    [3, -5, -2, 4],
    [-8, 4, 7, -7],
    [10, 7],
    [-8, -3],
    [3, 5, 5, -4],
    [-9, -5, 2, -10, 2, -2, 4, -1],
    [7, 5, -6, -4, -1, -4, -9, 8],
    [1, -9],
    [8, 5],
    [-9, 6, -8, -5],
    [9, -8],
    [2, -7, 8, -3],
    [9, -8],
    [8, 8, 6, 1, -2, -4, 1, -3],
    [2, -6, 10, -1, 4, 1],
    [-10, 4],
    [-8, 7],
    [6, -2, -6, 1],
    [-3, 1],
    [-5, 4, 7, -1, 9, 10],
    [7, -1],
    [-6, -2],
    [-7, 7],
    [-2, -1, 9, -4],
    [-4, 10, -2, 6, 5, -2],
    [-8, 10],
    [-2, -9, -10, 1, -6, 10, -2, -5],
    [7, 3, 7, -10, -7, -8, -6, 7],
    [1, 8],
    [3, -6, -9, -1],
    [-9, 1, -4, -3, -7, 1],
    [9, -6, -3, -5, -5, 3, -10, -5],
    [3, -3, -2, -5, -7, 2],
    [5, -3],
    [4, 1, -1, -3],
    [-10, -4, 2, 1],
    [-8, -2, 1, 10, 6, 2],
    [-10, -7, -2, -5, 8, -2],
    [-7, 9],
    [1, 1, 3, 9, 6, -7, 2, 8],
    [-2, -9, 3, -10],
    [1, 3, -8, 1],
    [-7, -1, 6, -1, 3, 1],
    [-1, 7, -6, -4, 3, 2, -5, 9],
    [2, 7, -10, -1, -1, -4],
    [8, 9, 10, 1, 4, 4, 4, -4],
    [-5, -8, -1, 6, 10, 9, 1, -8],
    [-1, -3, -4, -6],
    [-9, -3],
    [9, -8, 4, 3, 10, 8, -4, 2],
    [2, -3, -6, 10, -10, -7, 3, -3],
    [6, 4, -9, 7],
    [-7, 4, -6, 4],
    [4, 9, 6, 3, 7, 4],
    [5, 4, -2, -3],
    [6, 5, 10, -3, -2, 4],
    [-1, -3],
    [1, 1, 7, -8, -6, -6] ]

def intToFloat (z : Int) : Float :=
  if z < 0 then -z.natAbs.toFloat else z.natAbs.toFloat

def toFloats (xs : List Int) : List Float := xs.map intToFloat

def fstep (xs : List Float) (s : Float × Float) : Float × Float :=
  let c := (s.1 + s.2) / 2
  if FloatLayer.poly xs c * FloatLayer.poly xs s.1 > 0 then (c, s.2) else (s.1, c)

partial def expansionTrace (xs : List Float) (a b : Float) : (Float × Float) × Nat :=
  if FloatLayer.poly xs a * FloatLayer.poly xs b > 0 then
    let r := expansionTrace xs (a * 2) (b * 2)
    (r.1, r.2 + 1)
  else ((a, b), 0)

partial def bisectionTrace (xs : List Float) (s : Float × Float) : (Float × Float) × Nat :=
  if s.2 - s.1 > 0.0000000001 then
    let r := bisectionTrace xs (fstep xs s)
    (r.1, r.2 + 1)
  else (s, 0)

def evaluationCheck (xs : List Int) : Bool :=
  (List.range 7).all fun n =>
    let x := (n : Int) - 3
    intPoly xs x == intSum xs x

def expansionCheck (xs : List Float) : Bool :=
  let t := expansionTrace xs (-1) 1
  let s := FloatLayer.expand xs (-1) 1
  (s.1 == t.1.1) && (s.2 == t.1.2) &&
  decide (s.1 ≤ s.2) && decide (FloatLayer.poly xs s.1 * FloatLayer.poly xs s.2 ≤ 0) &&
  (List.range t.2).all (fun n =>
    let r := (2 : Float).pow n.toFloat
    decide (FloatLayer.poly xs (-r) * FloatLayer.poly xs r > 0))

def bisectionCheck (xs : List Float) : Bool :=
  let s := FloatLayer.expand xs (-1) 1
  let t := bisectionTrace xs s
  (FloatLayer.find_zero xs == t.1.1) &&
  decide (t.1.1 ≤ t.1.2) &&
  decide (FloatLayer.poly xs t.1.1 * FloatLayer.poly xs t.1.2 ≤ 0) &&
  decide (t.1.2 - t.1.1 ≤ 0.0000000001) &&
  decide (s.1 ≤ t.1.1) && decide (t.1.2 ≤ s.2) &&
  (List.range t.2).all (fun n =>
    let u := runN (fstep xs) n s
    decide (0.0000000001 < u.2 - u.1))

/-- (x-r)(x²+a), with a positive: r is its unique real zero. -/
def knownRootCoeffs (r a : Int) : List Int := [-r * a, a, -r, 1]

def rootCheck (r a : Int) : Bool :=
  let xs := toFloats (knownRootCoeffs r a)
  let z := intToFloat r
  let t := bisectionTrace xs (FloatLayer.expand xs (-1) 1)
  let y := FloatLayer.find_zero xs
  (FloatLayer.poly xs z == 0) && decide (y ≤ z) && decide (z ≤ t.1.2) &&
  decide ((y - z).abs ≤ 0.0000000001)

def floatNormBounds : List Float → Float → Float × Float
  | [], _ => (0, 0)
  | a :: xs, R =>
    let b := floatNormBounds xs R
    (a.abs + R * b.1, b.1 + R * b.2)

def residualCheck (xs : List Float) : Bool :=
  let R := (FloatLayer.expand xs (-1) 1).2
  decide ((FloatLayer.poly xs (FloatLayer.find_zero xs)).abs ≤
    (floatNormBounds xs R).2 * 0.0000000001)

def postCheck (r a : Int) : Bool :=
  let cs := knownRootCoeffs r a
  let xs := toFloats cs
  evaluationCheck cs && expansionCheck xs && bisectionCheck xs && rootCheck r a && residualCheck xs

-- PBT for poly_prop: 700 exact integer evaluations, including all public inputs.
example : publicInputs.all evaluationCheck = true := by native_decide
-- PBT for expansion_prop: final sign and every preceding doubling guard.
example : publicInputs.all (fun xs => expansionCheck (toFloats xs)) = true := by native_decide
-- PBT for bisection_prop: sign, nesting, width, and all preceding width guards.
example : publicInputs.all (fun xs => bisectionCheck (toFloats xs)) = true := by native_decide
-- PBT for zero_prop: 85 admissible cubics with independently known roots.
example : (List.range 17).all (fun r => (List.range 5).all (fun a =>
    rootCheck ((r : Int) - 8) ((a : Int) + 1))) = true := by native_decide
-- PBT for residual_prop: coefficient-dependent error bounds.
example : publicInputs.all (fun cs => residualCheck (toFloats cs)) = true := by native_decide
-- PBT for the full Post_prop, on the same 85 known-root inputs.
example : (List.range 17).all (fun r => (List.range 5).all (fun a =>
    postCheck ((r : Int) - 8) ((a : Int) + 1))) = true := by native_decide
-- The Python public check's residual criterion, on its actual 100 inputs.
example : publicInputs.all (fun cs =>
    let xs := toFloats cs
    decide ((FloatLayer.poly xs (FloatLayer.find_zero xs)).abs < 0.0001)) = true := by
  native_decide
#eval publicInputs.length
#eval publicInputs.all (fun cs =>
  let xs := toFloats cs
  decide ((FloatLayer.poly xs (FloatLayer.find_zero xs)).abs < 0.0001))

end Tests

/-- Correctness on the complete documented coefficient domain, in exact real
arithmetic. This is not a claim about Float overflow or rounding. -/
theorem correctness_thm (xs : List ℝ) : Pre xs → Post_prop xs := by
  intro h
  exact ⟨poly_thm xs, expansion_thm xs h, bisection_thm xs h, zero_thm xs h, residual_thm xs h⟩

/-! ## Imperative implementations -/

namespace FloatLayer

def polyImperative (xs : List Float) (x : Float) : Float := Id.run do
  let mut sum := 0
  for ci in xs.zipIdx do
    sum := sum + ci.1 * x.pow ci.2.toFloat
  return sum

/-- A literal mutable-state translation of the two Python while loops. -/
partial def find_zeroImperative (xs : List Float) : Float := Id.run do
  let mut begin := -1.0
  let mut finish := 1.0
  while poly xs begin * poly xs finish > 0 do
    begin := begin * 2.0
    finish := finish * 2.0
  while finish - begin > 0.0000000001 do
    let center := (begin + finish) / 2.0
    if poly xs center * poly xs begin > 0 then
      begin := center
    else
      finish := center
  return begin

end FloatLayer

/-- Mutable-state execution of an exact finite loop count. -/
def runNImperative {α : Type} (f : α → α) (n : Nat) (s : α) : α := Id.run do
  let mut state := s
  for _ in List.range n do
    state := f state
  return state

namespace RealLayer

/-- The real-arithmetic imperative model. The bounds are the *first* exit
counts proved above, not externally supplied fuel or iteration cutoffs. -/
noncomputable def find_zeroImperative (xs : List ℝ) : ℝ := Id.run do
  let mut state : ℝ × ℝ := (-1, 1)
  state := runNImperative double (expansionCount xs) state
  state := runNImperative (step xs) (refinementCount state) state
  return state.1

end RealLayer

example : (FloatLayer.polyImperative [1, 2] 3 == 7) = true := by native_decide
example : (FloatLayer.find_zeroImperative [1, 2] + 0.5).abs < 0.0000000001 := by
  native_decide
example : (FloatLayer.find_zeroImperative [-6, 11, -6, 1] - 1).abs < 0.0000000001 := by
  native_decide
example : Tests.publicInputs.all (fun cs =>
    let xs := Tests.toFloats cs
    FloatLayer.find_zero xs == FloatLayer.find_zeroImperative xs) = true := by native_decide
#eval FloatLayer.find_zeroImperative [1, 2]
#eval FloatLayer.find_zeroImperative [-6, 11, -6, 1]

/-- This structural equivalence is valid even for primitive Float: it asserts
identical operations and order, not any opaque Float arithmetic law. -/
theorem poly_float_equivalence_thm (xs : List Float) (x : Float) :
    FloatLayer.poly xs x = FloatLayer.polyImperative xs x := by
  simp [FloatLayer.poly, FloatLayer.polyImperative]

theorem runN_equivalence_thm {α : Type} (f : α → α) (n : Nat) (s : α) :
    runNImperative f n s = runN f n s := by
  induction n with
  | zero => simp [runNImperative, runN]
  | succ n ih => simpa [runNImperative, runN, List.range_succ] using congrArg f ih

/-- Full functional/imperative equivalence in the mathematical model. It
holds even off the documented domain (where both use the same fallback). -/
theorem equivalence_thm (xs : List ℝ) :
    RealLayer.find_zero xs = RealLayer.find_zeroImperative xs := by
  simp [RealLayer.find_zeroImperative, runN_equivalence_thm, doubling_state,
    RealLayer.find_zero, resultInterval, bracket]

end humaneval_32_poly
end Agent
