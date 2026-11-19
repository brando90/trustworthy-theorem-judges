import Mathlib
namespace Agent

/-!
# Polynomial root approximation by bisection

The executable layer uses `Float`, in the Python evaluation order. A signed
integer fuel and `Except` preserve invalid-input errors (Lean's list and numeric
types already enforce the Python type checks). The mathematical layer uses ℝ,
not an assumption of exact IEEE arithmetic. Both layers instantiate the same
accumulator evaluator and bisection control flow. The real guarantees below
are explicitly about that exact-arithmetic model, not a claim that Float
arithmetic is exact. In particular, early stopping guarantees a small residual,
not necessarily a small distance to a root.
-/

namespace humaneval_32_findZero

/-- The Python loop, including its order of additions and multiplications. -/
def evalAux {α : Type} [Add α] [Mul α] : List α → α → α → α → α
  | [], _, acc, _ => acc
  | c :: cs, x, acc, p => evalAux cs x (acc + c * p) (p * x)

def poly {α : Type} [Add α] [Mul α] [OfNat α 0] [OfNat α 1]
    (xs : List α) (x : α) : α := evalAux xs x 0 1

/-- Arithmetic is a parameter, so no unproved Float arithmetic laws are used. -/
def bisectCore {α : Type} (mid : α → α → α) (small : α → Bool)
    (opposite : α → α → Bool) (f : α → α) : Nat → α → α → α
  | 0, a, b => mid a b
  | n + 1, a, b =>
      let m := mid a b
      if small (f m) then m
      else if opposite (f a) (f m) then
        bisectCore mid small opposite f n a m
      else bisectCore mid small opposite f n m b

namespace FloatLayer

def midpoint (a b : Float) : Float := (a + b) / 2.0

def valid (xs : List Float) (a b : Float) (fuel : Int) : Bool :=
  !xs.isEmpty && decide (0 ≤ fuel) && (a < b) && (poly xs a * poly xs b ≤ 0.0)

def bisect (xs : List Float) (a b : Float) (fuel : Nat) : Float :=
  bisectCore midpoint (fun v => v.abs < 1e-10)
    (fun u v => u * v ≤ 0.0) (poly xs) fuel a b

def findZero (xs : List Float) (a b : Float) (fuel : Int) : Except String Float :=
  if valid xs a b fuel then .ok (bisect xs a b fuel.toNat)
  else .error "Invalid inputs or bracket does not contain a root"

def near (out : Except String Float) (expected : Float) : Bool :=
  match out with
  | .ok r => (r - expected).abs < 1e-2
  | .error _ => false

def rejected (out : Except String Float) : Bool :=
  match out with
  | .ok _ => false
  | .error _ => true

example : near (findZero [1.0, 2.0] (-1.0) 0.0 100) (-0.5) = true := by native_decide
example : near (findZero [-6.0, 11.0, -6.0, 1.0] 0.0 2.0 100) 1.0 = true := by native_decide
example : near (findZero [0.0, 1.0] (-1.0) 1.0 100) 0.0 = true := by native_decide
example : near (findZero [-4.0, 0.0, 1.0] 1.0 3.0 100) 2.0 = true := by native_decide
example : rejected (findZero [] (-1.0) 1.0 10) = true := by native_decide
example : rejected (findZero [1.0] 0.0 1.0 (-1)) = true := by native_decide
example : rejected (findZero [1.0] 1.0 0.0 10) = true := by native_decide
example : rejected (findZero [1.0] 0.0 1.0 10) = true := by native_decide
example : near (findZero [0.0, 1.0] (-2.0) 1.0 0) (-0.5) = true := by native_decide
#eval findZero [1.0, 2.0] (-1.0) 0.0 100
#eval findZero [] (-1.0) 1.0 10

end FloatLayer

namespace RealLayer

noncomputable def midpoint (a b : ℝ) : ℝ := (a + b) / 2

noncomputable def tolerance : ℝ := 1 / 10 ^ 10

noncomputable def bisect (xs : List ℝ) (a b : ℝ) (fuel : Nat) : ℝ :=
  bisectCore midpoint (fun v => decide (|v| < tolerance))
    (fun u v => decide (u * v ≤ 0)) (poly xs) fuel a b

/-- No restriction on coefficients or endpoints beyond the source precondition. -/
def Pre (xs : List ℝ) (a b : ℝ) (fuel : Int) : Prop :=
  xs ≠ [] ∧ a < b ∧ 0 ≤ fuel ∧ poly xs a * poly xs b ≤ 0

noncomputable def findZero (xs : List ℝ) (a b : ℝ) (fuel : Int) : Except String ℝ :=
  by
    classical
    exact if Pre xs a b fuel then .ok (bisect xs a b fuel.toNat)
      else .error "Invalid inputs or bracket does not contain a root"


/-- Relate the accumulator evaluation to the usual coefficient expansion. -/
theorem evalAux_horner_thm (xs : List ℝ) (x acc p : ℝ) :
    evalAux xs x acc p = acc + p * xs.foldr (fun c v => c + x * v) 0 := by
  induction xs generalizing acc p with
  | nil => simp [evalAux]
  | cons c cs ih =>
      simp only [evalAux, List.foldr_cons, ih]
      ring

def poly_recursion_prop (xs : List ℝ) (c x : ℝ) : Prop :=
  poly (c :: xs) x = c + x * poly xs x

theorem poly_recursion_thm (xs : List ℝ) (c x : ℝ) : poly_recursion_prop xs c x := by
  simp [poly_recursion_prop, poly, evalAux_horner_thm]

theorem continuous_evalAux (xs : List ℝ) (a p : ℝ → ℝ)
    (ha : Continuous a) (hp : Continuous p) :
    Continuous (fun x => evalAux xs x (a x) (p x)) := by
  induction xs generalizing a p with
  | nil => exact ha
  | cons c cs ih =>
      exact ih (fun x => a x + c * p x) (fun x => p x * x)
        (ha.add (continuous_const.mul hp)) (hp.mul continuous_id)

theorem continuous_poly (xs : List ℝ) : Continuous (poly xs) :=
  continuous_evalAux xs _ _ continuous_const continuous_const

/-- The sign test really supplies a root; endpoints and the zero polynomial
are included. No uniqueness or simple-root assumption is imposed. -/
def bracket_prop (xs : List ℝ) (a b : ℝ) : Prop :=
  ∃ z, a ≤ z ∧ z ≤ b ∧ poly xs z = 0

theorem bracket_thm (xs : List ℝ) (a b : ℝ)
    (hab : a ≤ b) (hs : poly xs a * poly xs b ≤ 0) : bracket_prop xs a b := by
  have hc : ContinuousOn (poly xs) (Set.Icc a b) := (continuous_poly xs).continuousOn
  rcases mul_nonpos_iff.mp hs with h | h
  · obtain ⟨z, hz, he⟩ := intermediate_value_Icc' hab hc ⟨h.2, h.1⟩
    exact ⟨z, hz.1, hz.2, he⟩
  · obtain ⟨z, hz, he⟩ := intermediate_value_Icc hab hc ⟨h.1, h.2⟩
    exact ⟨z, hz.1, hz.2, he⟩

theorem midpoint_mem (a b : ℝ) (hab : a ≤ b) :
    a ≤ midpoint a b ∧ midpoint a b ≤ b := by
  dsimp [midpoint]
  constructor <;> linarith

/-- If the left half does not bracket a root, the right half does. -/
theorem right_sign (u v w : ℝ) (huv : u * v ≤ 0) (huw : ¬ u * w ≤ 0) :
    w * v ≤ 0 := by
  have hpos : 0 < u * w := lt_of_not_ge huw
  rcases lt_trichotomy u 0 with h | h | h
  · have hw : w < 0 := by nlinarith
    have hv : 0 ≤ v := by nlinarith
    exact mul_nonpos_of_nonpos_of_nonneg hw.le hv
  · simp [h] at hpos
  · have hw : 0 < w := by nlinarith
    have hv : v ≤ 0 := by nlinarith
    exact mul_nonpos_of_nonneg_of_nonpos hw.le hv

theorem bisect_zero (xs : List ℝ) (a b : ℝ) :
    bisect xs a b 0 = midpoint a b := rfl

theorem bisect_step (xs : List ℝ) (a b : ℝ) (n : Nat) :
    bisect xs a b (n + 1) =
      if |poly xs (midpoint a b)| < tolerance then midpoint a b
      else if poly xs a * poly xs (midpoint a b) ≤ 0 then
        bisect xs a (midpoint a b) n
      else bisect xs (midpoint a b) b n := by
  simp [bisect, bisectCore]

/-- Either a residual exit occurred or all iterations produced an exact-width
sign-changing subinterval. This also records the final midpoint, not just bounds. -/
def Certificate (xs : List ℝ) (a b : ℝ) (n : Nat) (r : ℝ) : Prop :=
  a ≤ r ∧ r ≤ b ∧
    (|poly xs r| < tolerance ∨
      ∃ l u, a ≤ l ∧ l ≤ u ∧ u ≤ b ∧ poly xs l * poly xs u ≤ 0 ∧
        r = midpoint l u ∧ u - l = (b - a) / 2 ^ n)

theorem certificate_thm (xs : List ℝ) (n : Nat) (a b : ℝ)
    (hab : a ≤ b) (hs : poly xs a * poly xs b ≤ 0) :
    Certificate xs a b n (bisect xs a b n) := by
  induction n generalizing a b with
  | zero =>
      rw [bisect_zero]
      refine ⟨(midpoint_mem a b hab).1, (midpoint_mem a b hab).2, Or.inr ?_⟩
      exact ⟨a, b, le_rfl, hab, le_rfl, hs, rfl, by simp⟩
  | succ n ih =>
      rw [bisect_step]
      have hm := midpoint_mem a b hab
      split_ifs with he hs'
      · exact ⟨hm.1, hm.2, Or.inl he⟩
      · obtain ⟨hrl, hru, hr⟩ := ih a (midpoint a b) hm.1 hs'
        refine ⟨hrl, hru.trans hm.2, ?_⟩
        rcases hr with hr | ⟨l, u, hal, hlu, hum, hsign, hr, hw⟩
        · exact Or.inl hr
        · refine Or.inr ⟨l, u, hal, hlu, hum.trans hm.2, hsign, hr, ?_⟩
          rw [hw, pow_succ, div_mul_eq_div_div]
          dsimp [midpoint]
          ring
      · obtain ⟨hrl, hru, hr⟩ := ih (midpoint a b) b hm.2
          (right_sign _ _ _ hs hs')
        refine ⟨hm.1.trans hrl, hru, ?_⟩
        rcases hr with hr | ⟨l, u, hml, hlu, hub, hsign, hr, hw⟩
        · exact Or.inl hr
        · refine Or.inr ⟨l, u, hm.1.trans hml, hlu, hub, hsign, hr, ?_⟩
          rw [hw, pow_succ, div_mul_eq_div_div]
          dsimp [midpoint]
          ring

def range_prop (xs : List ℝ) (a b : ℝ) (n : Nat) : Prop :=
  a ≤ bisect xs a b n ∧ bisect xs a b n ≤ b

theorem range_thm (xs : List ℝ) (a b : ℝ) (n : Nat)
    (hab : a ≤ b) (hs : poly xs a * poly xs b ≤ 0) : range_prop xs a b n := by
  have h := certificate_thm xs n a b hab hs
  exact ⟨h.1, h.2.1⟩

/-- The sound accuracy alternative: small residual OR distance to some root
bounded by half the final bracket width. Early stopping cannot in general
promise the latter bound. -/
def accuracy_prop (xs : List ℝ) (a b : ℝ) (n : Nat) : Prop :=
  |poly xs (bisect xs a b n)| < tolerance ∨
    ∃ z, a ≤ z ∧ z ≤ b ∧ poly xs z = 0 ∧
      |bisect xs a b n - z| ≤ (b - a) / 2 ^ (n + 1)

theorem accuracy_thm (xs : List ℝ) (a b : ℝ) (n : Nat)
    (hab : a ≤ b) (hs : poly xs a * poly xs b ≤ 0) : accuracy_prop xs a b n := by
  obtain ⟨_, _, h⟩ := certificate_thm xs n a b hab hs
  rcases h with h | ⟨l, u, hal, hlu, hub, hs', hr, hw⟩
  · exact Or.inl h
  · obtain ⟨z, hlz, hzu, hz⟩ := bracket_thm xs l u hlu hs'
    refine Or.inr ⟨z, hal.trans hlz, hzu.trans hub, hz, ?_⟩
    have hwidth : (b - a) / 2 ^ (n + 1) = (u - l) / 2 := by
      rw [hw, pow_succ, div_mul_eq_div_div]
    rw [hr, hwidth, abs_le]
    dsimp [midpoint]
    constructor <;> linarith

def rejection_prop (xs : List ℝ) (a b : ℝ) (fuel : Int) : Prop :=
  ¬ Pre xs a b fuel → findZero xs a b fuel =
    .error "Invalid inputs or bracket does not contain a root"

theorem rejection_thm (xs : List ℝ) (a b : ℝ) (fuel : Int) :
    rejection_prop xs a b fuel := by
  intro h
  simp [findZero, h]

/-- A successful result is the algorithm's actual output, lies in the original
bracket, and satisfies the residual-or-root-distance guarantee. -/
def Post_prop (xs : List ℝ) (a b : ℝ) (fuel : Int) (out : Except String ℝ) : Prop :=
  out = .ok (bisect xs a b fuel.toNat) ∧
  bracket_prop xs a b ∧ range_prop xs a b fuel.toNat ∧ accuracy_prop xs a b fuel.toNat


/-! ## Property-based tests

Real comparison and existential quantification over real roots are not
executable. These bounded tests use exact rational arithmetic with the same
control-flow kernel, proved below to commute with casting to ℝ. They are test
evidence, not a rational restriction of any
theorem above, nor a proof of correspondence with rounded Float arithmetic.
For `bracket_prop`, `accuracy_prop` and `Post_prop`, known-root families supply
explicit executable witnesses. Arbitrary real existential root search itself
has no decidable executable check. `Certificate` likewise quantifies over real
endpoints; its consequences are tested here via range and accuracy.
-/
namespace PBT

def eps : ℚ := 1 / 10 ^ 10

def run (xs : List ℚ) (a b : ℚ) (n : Nat) : ℚ :=
  bisectCore (fun l r => (l + r) / 2) (fun v => decide (|v| < eps))
    (fun u v => decide (u * v ≤ 0)) (poly xs) n a b

def valid (xs : List ℚ) (a b : ℚ) (fuel : Int) : Bool :=
  !xs.isEmpty && decide (a < b ∧ 0 ≤ fuel ∧ poly xs a * poly xs b ≤ 0)

def checked (xs : List ℚ) (a b : ℚ) (fuel : Int) : Except String ℚ :=
  if valid xs a b fuel then .ok (run xs a b fuel.toNat)
  else .error "Invalid inputs or bracket does not contain a root"

def numbers : List ℚ := (List.range 5).map (fun i => (i : ℚ) - 2)
def points : List ℚ := (List.range 7).map (fun i => (i : ℚ) - 3)
def polynomials : List (List ℚ) :=
  [[]] ++ numbers.map (fun c => [c]) ++
  numbers.flatMap (fun c => numbers.map (fun d => [c, d])) ++
  numbers.flatMap (fun c => numbers.flatMap (fun d => numbers.map (fun e => [c, d, e])))

-- PBT for poly_recursion_prop: all small coefficients, including the empty tail.
example : polynomials.all (fun xs => numbers.all (fun c => points.all (fun x =>
    decide (poly (c :: xs) x = c + x * poly xs x)))) = true := by native_decide

-- PBT for range_prop: general (not just linear) sign-changing brackets.
example : polynomials.all (fun xs => points.all (fun a => points.all (fun b =>
    (List.range 7).all (fun n => !valid xs a b n ||
      decide (a ≤ run xs a b n ∧ run xs a b n ≤ b))))) = true := by native_decide

-- PBT for rejection_prop: includes negative fuel, empty lists, reversed
-- brackets, equal endpoints, and brackets with no sign change.
example : polynomials.all (fun xs => points.all (fun a => points.all (fun b =>
    (List.range 5).all (fun k =>
      let fuel : Int := (k : Int) - 2
      valid xs a b fuel || (match checked xs a b fuel with
        | .error msg => msg == "Invalid inputs or bracket does not contain a root"
        | .ok _ => false))))) = true := by native_decide

structure RootCase where
  xs : List ℚ
  a : ℚ
  b : ℚ
  z : ℚ
  n : Nat

/-- Linear, cubic with exactly one real root, and identically zero families;
also includes roots at either endpoint, asymmetric brackets, and zero fuel. -/
def rootCases : List RootCase :=
  (List.range 9).flatMap fun k =>
    let z : ℚ := ((k : ℚ) - 4) / 3
    [[-z, 1], [-z, 1, -z, 1], [0]].flatMap fun xs =>
      (List.range 4).flatMap fun lo =>
        (List.range 4).flatMap fun hi =>
          (List.range 11).map fun n => ⟨xs, z - lo, z + hi, z, n⟩

def bracketOK (c : RootCase) : Bool :=
  decide (c.a ≤ c.z ∧ c.z ≤ c.b ∧ poly c.xs c.z = 0)

def rangeOK (c : RootCase) : Bool :=
  decide (c.a ≤ run c.xs c.a c.b c.n ∧ run c.xs c.a c.b c.n ≤ c.b)

def accuracyOK (c : RootCase) : Bool :=
  let r := run c.xs c.a c.b c.n
  decide (|poly c.xs r| < eps ∨ |r - c.z| ≤ (c.b - c.a) / 2 ^ (c.n + 1))

def postOK (c : RootCase) : Bool :=
  (match checked c.xs c.a c.b c.n with
    | .ok r => decide (r = run c.xs c.a c.b c.n)
    | .error _ => false) &&
    bracketOK c && rangeOK c && accuracyOK c

-- PBT for bracket_prop, with explicit root witnesses rather than a decision
-- procedure for quantification over ℝ.
example : rootCases.all (fun c => !valid c.xs c.a c.b c.n || bracketOK c) = true := by
  native_decide
-- PBT for accuracy_prop, with the same residual-or-distance alternative.
example : rootCases.all (fun c => !valid c.xs c.a c.b c.n ||
    (bracketOK c && accuracyOK c)) = true := by native_decide
-- PBT for the whole Post_prop, including successful wrapper return.
example : rootCases.all (fun c => !valid c.xs c.a c.b c.n || postOK c) = true := by
  native_decide
#eval (rootCases.length, rootCases.all (fun c => !valid c.xs c.a c.b c.n || postOK c))

end PBT

/-! The exact rational testing layer is formally connected to the real model.
These are correspondence proofs, not a claim that rounded Float arithmetic
commutes with casting. Their real-valued equalities are not executable PBTs. -/

theorem evalAux_rat_cast (xs : List ℚ) (x acc p : ℚ) :
    evalAux (xs.map (fun q : ℚ => (q : ℝ))) (x : ℝ) (acc : ℝ) (p : ℝ) =
      (evalAux xs x acc p : ℚ) := by
  induction xs generalizing acc p with
  | nil => rfl
  | cons c cs ih =>
      simpa only [List.map_cons, evalAux, Rat.cast_add, Rat.cast_mul] using
        ih (acc + c * p) (p * x)

theorem poly_rat_cast (xs : List ℚ) (x : ℚ) :
    poly (xs.map (fun q : ℚ => (q : ℝ))) (x : ℝ) = (poly xs x : ℚ) := by
  simpa [poly] using evalAux_rat_cast xs x 0 1

theorem midpoint_rat_cast (a b : ℚ) :
    midpoint (a : ℝ) (b : ℝ) = (((a + b) / 2 : ℚ) : ℝ) := by
  simp [midpoint]

theorem run_rat_cast (xs : List ℚ) (a b : ℚ) (n : Nat) :
    ((PBT.run xs a b n : ℚ) : ℝ) =
      bisect (xs.map (fun q : ℚ => (q : ℝ))) (a : ℝ) (b : ℝ) n := by
  have heps : (PBT.eps : ℝ) = tolerance := by norm_num [PBT.eps, tolerance]
  induction n generalizing a b with
  | zero => simp [PBT.run, bisect_zero, bisectCore, midpoint]
  | succ n ih =>
      have step : PBT.run xs a b (n + 1) =
          if |poly xs ((a + b) / 2)| < PBT.eps then (a + b) / 2
          else if poly xs a * poly xs ((a + b) / 2) ≤ 0 then
            PBT.run xs a ((a + b) / 2) n
          else PBT.run xs ((a + b) / 2) b n := by simp [PBT.run, bisectCore]
      rw [step, bisect_step, midpoint_rat_cast]
      simp only [poly_rat_cast, ← Rat.cast_abs, ← heps, Rat.cast_lt,
        ← Rat.cast_mul, Rat.cast_nonpos]
      split_ifs <;> simp_all

theorem pre_rat_cast (xs : List ℚ) (a b : ℚ) (fuel : Int) :
    PBT.valid xs a b fuel = true ↔
      Pre (xs.map (fun q : ℚ => (q : ℝ))) (a : ℝ) (b : ℝ) fuel := by
  simp [PBT.valid, Pre, poly_rat_cast, ← Rat.cast_mul]

theorem checked_rat_cast (xs : List ℚ) (a b : ℚ) (fuel : Int) :
    (PBT.checked xs a b fuel).map (fun q : ℚ => (q : ℝ)) =
      findZero (xs.map (fun q : ℚ => (q : ℝ))) (a : ℝ) (b : ℝ) fuel := by
  classical
  by_cases h : PBT.valid xs a b fuel = true
  · have hp := (pre_rat_cast xs a b fuel).mp h
    simp [PBT.checked, findZero, h, hp, run_rat_cast, Except.map]
  · have hp := (pre_rat_cast xs a b fuel).not.mp h
    simp [PBT.checked, findZero, h, hp, Except.map]

/-- Mathematical correctness on the full real-valued source precondition. -/
theorem correctness_thm (xs : List ℝ) (a b : ℝ) (fuel : Int)
    (h : Pre xs a b fuel) : Post_prop xs a b fuel (findZero xs a b fuel) := by
  refine ⟨?_, bracket_thm xs a b h.2.1.le h.2.2.2,
    range_thm xs a b fuel.toNat h.2.1.le h.2.2.2,
    accuracy_thm xs a b fuel.toNat h.2.1.le h.2.2.2⟩
  simp [findZero, h]

end RealLayer

/-! ## Imperative implementation
The list of unit values is the iteration schedule: its length is exactly fuel.
The `for` loop uses mutable endpoints and actually returns early, as in Python.
-/

def evalAuxImperative {α : Type} [Add α] [Mul α]
    (xs : List α) (x acc p : α) : α := Id.run do
  let mut acc := acc
  let mut power := p
  for c in xs do
    acc := acc + c * power
    power := power * x
  return acc

def polyImperative {α : Type} [Add α] [Mul α] [OfNat α 0] [OfNat α 1]
    (xs : List α) (x : α) : α := evalAuxImperative xs x 0 1

def bisectImperativeLoop {α : Type} (mid : α → α → α) (small : α → Bool)
    (opposite : α → α → Bool) (f : α → α) (iters : List Unit) (a b : α) : α := Id.run do
  let mut left := a
  let mut right := b
  for _ in iters do
    let m := mid left right
    let fm := f m
    if small fm then return m
    if opposite (f left) fm then
      right := m
    else
      left := m
  return mid left right

def bisectImperativeCore {α : Type} (mid : α → α → α) (small : α → Bool)
    (opposite : α → α → Bool) (f : α → α) (fuel : Nat) (a b : α) : α :=
  bisectImperativeLoop mid small opposite f (List.replicate fuel ()) a b

namespace FloatLayer

def validImperative (xs : List Float) (a b : Float) (fuel : Int) : Bool :=
  !xs.isEmpty && decide (0 ≤ fuel) && (a < b) &&
    (polyImperative xs a * polyImperative xs b ≤ 0.0)

def findZeroImperative (xs : List Float) (a b : Float) (fuel : Int) : Except String Float :=
  Id.run do
    if validImperative xs a b fuel then
      let r := bisectImperativeCore midpoint (fun v => v.abs < 1e-10)
        (fun u v => u * v ≤ 0.0) (polyImperative xs) fuel.toNat a b
      return .ok r
    else
      return .error "Invalid inputs or bracket does not contain a root"

example : near (findZeroImperative [1.0, 2.0] (-1.0) 0.0 100) (-0.5) = true := by native_decide
example : near (findZeroImperative [-6.0, 11.0, -6.0, 1.0] 0.0 2.0 100) 1.0 = true := by native_decide
example : near (findZeroImperative [0.0, 1.0] (-1.0) 1.0 100) 0.0 = true := by native_decide
example : near (findZeroImperative [-4.0, 0.0, 1.0] 1.0 3.0 100) 2.0 = true := by native_decide
example : rejected (findZeroImperative [] (-1.0) 1.0 10) = true := by native_decide
example : rejected (findZeroImperative [1.0] 0.0 1.0 (-1)) = true := by native_decide
example : rejected (findZeroImperative [1.0] 1.0 0.0 10) = true := by native_decide
example : rejected (findZeroImperative [1.0] 0.0 1.0 10) = true := by native_decide
example : near (findZeroImperative [0.0, 1.0] (-2.0) 1.0 0) (-0.5) = true := by native_decide
#eval findZeroImperative [-4.0, 0.0, 1.0] 1.0 3.0 100

def sameResult (u v : Except String Float) : Bool :=
  match u, v with
  | .ok x, .ok y => x == y
  | .error x, .error y => x == y
  | _, _ => false

-- Bounded Float PBT: independent implementations, varying roots, asymmetric
-- brackets, budgets, empty inputs and non-bracketing constant polynomials.
example : (List.range 21).all (fun k => (List.range 12).all (fun n =>
    let z := k.toFloat - 10.0
    [[-z, 1.0], [-z, 1.0, -z, 1.0], [], [1.0]].all (fun xs =>
      sameResult (findZero xs (z - 2.0) (z + 3.0) n)
        (findZeroImperative xs (z - 2.0) (z + 3.0) n)))) = true := by native_decide

-- Executable Float validation property, including negative fuel.
example : (List.range 21).all (fun k => (List.range 6).all (fun n =>
    let z := k.toFloat - 10.0
    let fuel : Int := (n : Int) - 2
    [[-z, 1.0], [], [1.0]].all (fun xs =>
      rejected (findZero xs (z - 2.0) (z + 3.0) fuel) ==
        !valid xs (z - 2.0) (z + 3.0) fuel))) = true := by native_decide

/-- An operational theorem for actual Float execution, without finiteness or
arithmetic assumptions. The exact real bounds are deliberately not asserted
for overflow, NaNs, or rounded arithmetic. -/
theorem validation_thm (xs : List Float) (a b : Float) (fuel : Int) :
    (findZero xs a b fuel = .error "Invalid inputs or bracket does not contain a root" ↔
      valid xs a b fuel = false) ∧
    (valid xs a b fuel = true → findZero xs a b fuel = .ok (bisect xs a b fuel.toNat)) := by
  cases h : valid xs a b fuel <;> simp [findZero, h]

end FloatLayer

namespace RealLayer

noncomputable def findZeroImperative (xs : List ℝ) (a b : ℝ) (fuel : Int) : Except String ℝ := by
  classical
  exact Id.run do
    if Pre xs a b fuel then
      let r := bisectImperativeCore midpoint (fun v => decide (|v| < tolerance))
        (fun u v => decide (u * v ≤ 0)) (polyImperative xs) fuel.toNat a b
      return .ok r
    else
      return .error "Invalid inputs or bracket does not contain a root"

end RealLayer

/-- The polynomial loop preserves the exact accumulator operation order,
including for Float: this proof uses no algebraic laws at all. -/
theorem evalAux_equivalence_thm {α : Type} [Add α] [Mul α]
    (xs : List α) (x acc p : α) : evalAuxImperative xs x acc p = evalAux xs x acc p := by
  induction xs generalizing acc p with
  | nil => rfl
  | cons c cs ih =>
      simp only [evalAuxImperative, List.forIn_cons, Id.run, bind, pure, evalAux] at *
      exact ih (acc + c * p) (p * x)

theorem poly_equivalence_thm {α : Type} [Add α] [Mul α] [OfNat α 0] [OfNat α 1]
    (xs : List α) : polyImperative xs = poly xs := by
  funext x
  exact evalAux_equivalence_thm xs x 0 1

theorem imperative_cons {α : Type} (mid : α → α → α) (small : α → Bool)
    (opposite : α → α → Bool) (f : α → α) (iters : List Unit) (a b : α) :
    bisectImperativeLoop mid small opposite f (() :: iters) a b =
      if small (f (mid a b)) then mid a b
      else if opposite (f a) (f (mid a b)) then
        bisectImperativeLoop mid small opposite f iters a (mid a b)
      else bisectImperativeLoop mid small opposite f iters (mid a b) b := by
  cases hs : small (f (mid a b)) <;>
    cases ho : opposite (f a) (f (mid a b)) <;>
      simp [bisectImperativeLoop, List.forIn_cons, hs, ho]

theorem imperative_loop_equivalence {α : Type} (mid : α → α → α) (small : α → Bool)
    (opposite : α → α → Bool) (f : α → α) (iters : List Unit) (a b : α) :
    bisectImperativeLoop mid small opposite f iters a b =
      bisectCore mid small opposite f iters.length a b := by
  induction iters generalizing a b with
  | nil => rfl
  | cons u us ih =>
      cases u
      rw [imperative_cons]
      simp only [List.length_cons, bisectCore, ih]

theorem bisect_equivalence_thm {α : Type} (mid : α → α → α) (small : α → Bool)
    (opposite : α → α → Bool) (f : α → α) (fuel : Nat) (a b : α) :
    bisectImperativeCore mid small opposite f fuel a b =
      bisectCore mid small opposite f fuel a b := by
  simp [bisectImperativeCore, imperative_loop_equivalence]

/-- Universal equivalence for the executable layer, not just tested inputs. -/
theorem FloatLayer.equivalence_thm (xs : List Float) (a b : Float) (fuel : Int) :
    FloatLayer.findZero xs a b fuel = FloatLayer.findZeroImperative xs a b fuel := by
  have hv : FloatLayer.validImperative xs a b fuel = FloatLayer.valid xs a b fuel := by
    unfold FloatLayer.validImperative FloatLayer.valid
    rw [poly_equivalence_thm]
  unfold FloatLayer.findZero FloatLayer.findZeroImperative
  rw [hv]
  simp [FloatLayer.bisect, poly_equivalence_thm, bisect_equivalence_thm, Id.run, pure]

/-- The very same structural correspondence holds in the exact real model. -/
theorem RealLayer.equivalence_thm (xs : List ℝ) (a b : ℝ) (fuel : Int) :
    RealLayer.findZero xs a b fuel = RealLayer.findZeroImperative xs a b fuel := by
  classical
  simp [RealLayer.findZero, RealLayer.findZeroImperative, RealLayer.bisect,
    poly_equivalence_thm, bisect_equivalence_thm, Id.run, pure]

theorem RealLayer.imperative_correctness_thm (xs : List ℝ) (a b : ℝ) (fuel : Int)
    (h : RealLayer.Pre xs a b fuel) :
    RealLayer.Post_prop xs a b fuel (RealLayer.findZeroImperative xs a b fuel) := by
  rw [← RealLayer.equivalence_thm]
  exact RealLayer.correctness_thm xs a b fuel h

end humaneval_32_findZero
end Agent
