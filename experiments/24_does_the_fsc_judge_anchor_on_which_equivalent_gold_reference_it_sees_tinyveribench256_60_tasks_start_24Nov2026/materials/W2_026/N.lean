import Mathlib
namespace Agent

/-!
# Statistics quantiles

Translation of `statistics.quantiles` and its checked benchmark wrapper.
Lean lists represent the source's lists and tuples; their element type replaces
Python's dynamic numeric type check (the Python precondition imposes no further
numeric restriction). Counts remain signed integers, and methods remain strings,
so invalid counts and methods are not erased by the interface.

The algorithm is shared by an executable IEEE `Float` layer and exact mathematical
layers (rationals and reals). In particular, the exclusive method has **signed**
weights and can extrapolate beyond the sample. The Float layer actually performs
Float multiplication, addition and division; it is not identified with exact
arithmetic. Structural theorems and the imperative equivalence are polymorphic
in the numerical operations and therefore apply to all these layers.
-/

namespace StatisticsQuantiles

deriving instance DecidableEq for Except

/-- Arithmetic and ordering used by the common algorithm. -/
structure NumberOps (α : Type) where
  zero : α
  le : α → α → Bool
  ofInt : Int → α
  add : α → α → α
  mul : α → α → α
  div : α → α → α

/-- Exceptions retain Python's distinction between StatisticsError and ValueError.
`StatisticsError` is a subclass of `ValueError` in the source. -/
inductive Error where
  | statisticsError (message : String)
  | valueError (message : String)
  deriving DecidableEq, Repr

def preError : Error := .statisticsError
  "benchmark_quantiles requires at least 2 data points, n >= 1, and valid method"

def validMethod (method : String) : Bool :=
  method == "inclusive" || method == "exclusive"

def admissible (data : List α) (n : Int) (method : String) : Bool :=
  decide (2 ≤ data.length) && decide (1 ≤ n) && validMethod method

def sortedData (ops : NumberOps α) (data : List α) : List α :=
  data.mergeSort ops.le

/-- Positions of the two adjacent observations and the signed upper weight. -/
structure Cut where
  lo : Nat
  hi : Nat
  delta : Int
  deriving DecidableEq, Repr

def inclusiveCut (ld n i : Nat) : Cut :=
  let j := i * (ld - 1) / n
  ⟨j, j + 1, (i * (ld - 1) % n : Nat)⟩

def exclusiveJ (ld n i : Nat) : Nat :=
  max 1 (min (ld - 1) (i * (ld + 1) / n))

def exclusiveCut (ld n i : Nat) : Cut :=
  let j := exclusiveJ ld n i
  ⟨j - 1, j, (i : Int) * (ld + 1 : Nat) - (j : Int) * (n : Int)⟩

def cut (ld n i : Nat) (method : String) : Cut :=
  if method = "inclusive" then inclusiveCut ld n i else exclusiveCut ld n i

/-- The source's weighted interpolation; subtraction takes place in Int. -/
def blend (ops : NumberOps α) (a b : α) (n : Nat) (delta : Int) : α :=
  ops.div (ops.add (ops.mul a (ops.ofInt ((n : Int) - delta)))
    (ops.mul b (ops.ofInt delta))) (ops.ofInt (n : Int))

def cutValue (ops : NumberOps α) (xs : List α) (n : Nat) (c : Cut) : α :=
  blend ops (xs.getD c.lo ops.zero) (xs.getD c.hi ops.zero) n c.delta

/-- Functional version of the loop `for i in range(1, n)`. -/
def cuts (ops : NumberOps α) (xs : List α) (n : Nat) (method : String) : List α :=
  (List.range (n - 1)).map fun k =>
    cutValue ops xs n (cut xs.length n (k + 1) method)

def quantiles (ops : NumberOps α) (data : List α)
    (n : Int := 4) (method : String := "exclusive") : Except Error (List α) :=
  if n < 1 then .error (.statisticsError "n must be at least 1") else
  let xs := sortedData ops data
  if xs.length < 2 then .error (.statisticsError "must have at least two data points") else
  if validMethod method then .ok (cuts ops xs n.toNat method)
  else .error (.valueError ("Unknown method: '" ++ method ++ "'"))

def benchmarkQuantiles (ops : NumberOps α) (data : List α)
    (n : Int := 4) (method : String := "exclusive") : Except Error (List α) :=
  if admissible data n method then quantiles ops data n method else .error preError

/-- Exact mathematical arithmetic, instantiated below at both Rat and Real. -/
def mathOps (K : Type) [Field K] [LinearOrder K] [IsStrictOrderedRing K] : NumberOps K where
  zero := 0
  le := fun a b => decide (a ≤ b)
  ofInt := fun n => n
  add := (· + ·)
  mul := (· * ·)
  div := (· / ·)

def ratOps : NumberOps ℚ := mathOps ℚ
noncomputable def realOps : NumberOps ℝ := mathOps ℝ

def floatOps : NumberOps Float where
  zero := 0
  le := fun a b => decide (a ≤ b)
  ofInt := Float.ofInt
  add := (· + ·)
  mul := (· * ·)
  div := (· / ·)

namespace FloatLayer

def benchmark (data : List Float) (n : Int := 4) (method : String := "exclusive") :=
  benchmarkQuantiles floatOps data n method

end FloatLayer

/-! ## Unit tests -/
example : benchmarkQuantiles ratOps [1, 2, 3, 4] = .ok [5/4, 5/2, 15/4] := by native_decide
example : benchmarkQuantiles ratOps [1, 2, 3, 4] 4 "inclusive" =
    .ok [7/4, 5/2, 13/4] := by native_decide
example : benchmarkQuantiles ratOps [1, 2, 3, 4, 5] 2 = .ok [3] := by native_decide
example : benchmarkQuantiles ratOps [4, 1, 3, 2] = .ok [5/4, 5/2, 15/4] := by native_decide
example : benchmarkQuantiles ratOps [0, 10] 4 = .ok [-(5/2), 5, 25/2] := by native_decide
example : benchmarkQuantiles ratOps [3, 7] 1 = .ok [] := by native_decide
example : benchmarkQuantiles ratOps [1] = .error preError := by native_decide
example : benchmarkQuantiles ratOps [1, 2] 0 = .error preError := by native_decide
example : benchmarkQuantiles ratOps [1, 2] (-3) = .error preError := by native_decide
example : benchmarkQuantiles ratOps [1, 2, 3] 4 "invalid" = .error preError := by native_decide

-- Float equality is checked as a Boolean (no mathematical equality is assumed).
example : (match FloatLayer.benchmark [1, 2, 3, 4] with
    | .ok ys => ys == [1.25, 2.5, 3.75]
    | .error _ => false) = true := by native_decide
example : (match FloatLayer.benchmark [1, 2, 3, 4] 4 "inclusive" with
    | .ok ys => ys == [1.75, 2.5, 3.25]
    | .error _ => false) = true := by native_decide
example : (match FloatLayer.benchmark [1.5, 2.5, 3.5, 4.5] 2 with
    | .ok ys => ys == [3.0]
    | .error _ => false) = true := by native_decide
#eval FloatLayer.benchmark [1, 2, 3, 4]
#eval benchmarkQuantiles ratOps ((List.range 11).map Nat.cast) 10
#eval benchmarkQuantiles ratOps ((List.range 10).map fun i => (i + 1 : Nat)) 4

-- Remaining public size checks and direct quantiles exception distinctions.
example : (match benchmarkQuantiles ratOps ((List.range 11).map Nat.cast) 10 with
    | .ok result => decide (result.length = 9)
    | .error _ => false) = true := by native_decide
example : (match benchmarkQuantiles ratOps ((List.range 10).map fun i => (i + 1 : Nat)) 4 with
    | .ok result => decide (result.length = 3)
    | .error _ => false) = true := by native_decide
example : (match benchmarkQuantiles ratOps [1, 2, 3, 4] 4 "exclusive" with
    | .ok result => decide (result.length = 3)
    | .error _ => false) = true := by native_decide
example : (match benchmarkQuantiles ratOps [1, 2, 3, 4] 100 with
    | .ok result => decide (result.length = 99)
    | .error _ => false) = true := by native_decide
example : quantiles ratOps [1, 2] 0 =
    .error (.statisticsError "n must be at least 1") := by native_decide
example : quantiles ratOps [1] =
    .error (.statisticsError "must have at least two data points") := by native_decide
example : quantiles ratOps [1, 2] 4 "invalid" =
    .error (.valueError "Unknown method: 'invalid'") := by native_decide

/-! ## Precondition -/
def Pre (data : List α) (n : Int) (method : String) : Prop :=
  2 ≤ data.length ∧ 1 ≤ n ∧ (method = "inclusive" ∨ method = "exclusive")

instance (data : List α) (n : Int) (method : String) : Decidable (Pre data n method) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

@[simp] theorem admissible_iff (data : List α) (n : Int) (method : String) :
    admissible data n method = true ↔ Pre data n method := by sorry

@[simp] theorem sortedData_length (ops : NumberOps α) (data : List α) :
    (sortedData ops data).length = data.length := by sorry

/-- Normal form of every successful call, proved from the actual validations. -/
theorem benchmark_of_pre (ops : NumberOps α) (data : List α) (n : Int)
    (method : String) (h : Pre data n method) :
    benchmarkQuantiles ops data n method =
      .ok (cuts ops (sortedData ops data) n.toNat method) := by sorry

/-! ## Properties and proofs -/
def validation_prop (ops : NumberOps α) (data : List α) (n : Int) (method : String) : Prop :=
  benchmarkQuantiles ops data n method = .error preError ↔ ¬Pre data n method

theorem validation_thm (ops : NumberOps α) (data : List α) (n : Int) (method : String) :
    validation_prop ops data n method := by sorry

def length_prop (ops : NumberOps α) (data : List α) (n : Int) (method : String) : Prop :=
  ∃ result, benchmarkQuantiles ops data n method = .ok result ∧ result.length = n.toNat - 1

theorem length_thm (ops : NumberOps α) (data : List α) (n : Int) (method : String)
    (h : Pre data n method) : length_prop ops data n method := by sorry

/-- A direct specification of the two Python formulas, independent of Cut. -/
def referenceValue (ops : NumberOps α) (xs : List α) (n i : Nat) (method : String) : α :=
  if method = "inclusive" then
    let j := i * (xs.length - 1) / n
    let delta : Int := (i * (xs.length - 1) % n : Nat)
    blend ops (xs.getD j ops.zero) (xs.getD (j + 1) ops.zero) n delta
  else
    let q := i * (xs.length + 1) / n
    let j := if q < 1 then 1 else if q > xs.length - 1 then xs.length - 1 else q
    let delta : Int := (i : Int) * (xs.length + 1 : Nat) - (j : Int) * (n : Int)
    blend ops (xs.getD (j - 1) ops.zero) (xs.getD j ops.zero) n delta

/-- The min/max expression implements Python's conditional clamp on valid data. -/
theorem clamp_eq (ld n i : Nat) (hl : 2 ≤ ld) :
    exclusiveJ ld n i =
      (if i * (ld + 1) / n < 1 then 1
       else if i * (ld + 1) / n > ld - 1 then ld - 1 else i * (ld + 1) / n) := by sorry

theorem cutValue_eq_reference (ops : NumberOps α) (xs : List α) (n i : Nat)
    (method : String) (hl : 2 ≤ xs.length) :
    cutValue ops xs n (cut xs.length n i method) = referenceValue ops xs n i method := by sorry

def interpolation_prop (ops : NumberOps α) (data : List α) (n : Int) (method : String) : Prop :=
  ∀ result, benchmarkQuantiles ops data n method = .ok result →
    ∀ k, k < n.toNat - 1 → result[k]? =
      some (referenceValue ops (sortedData ops data) n.toNat (k + 1) method)

theorem interpolation_thm (ops : NumberOps α) (data : List α) (n : Int)
    (method : String) (h : Pre data n method) : interpolation_prop ops data n method := by sorry

/-- The loop never uses a default element: the adjacent indices are in range.
The inclusive remainder is a genuine convex weight; the exclusive remainder
is signed and is deliberately NOT constrained to [0,n). -/
def indexing_prop (data : List α) (n : Int) (method : String) : Prop :=
  ∀ i, 1 ≤ i → i < n.toNat →
    let c := cut data.length n.toNat i method
    c.lo + 1 = c.hi ∧ c.hi < data.length ∧
      (method = "inclusive" → 0 ≤ c.delta ∧ c.delta < n ∧
        (i : Int) * (data.length - 1 : Nat) = (c.lo : Int) * n + c.delta)

theorem inclusive_indices (ld n i : Nat) (hl : 2 ≤ ld) (hi : i < n) :
    (inclusiveCut ld n i).hi < ld ∧
    0 ≤ (inclusiveCut ld n i).delta ∧ (inclusiveCut ld n i).delta < (n : Int) ∧
    (i : Int) * (ld - 1 : Nat) =
      ((inclusiveCut ld n i).lo : Int) * (n : Int) + (inclusiveCut ld n i).delta := by sorry

theorem exclusive_indices (ld n i : Nat) (hl : 2 ≤ ld) :
    1 ≤ exclusiveJ ld n i ∧ exclusiveJ ld n i < ld := by sorry

theorem indexing_thm (data : List α) (n : Int) (method : String)
    (h : Pre data n method) : indexing_prop data n method := by sorry

def oneInterval_prop (ops : NumberOps α) (data : List α) (n : Int) (method : String) : Prop :=
  n = 1 → benchmarkQuantiles ops data n method = .ok []

theorem oneInterval_thm (ops : NumberOps α) (data : List α) (n : Int) (method : String)
    (h : Pre data n method) : oneInterval_prop ops data n method := by sorry

def permutation_prop (ops : NumberOps α) (data : List α) : Prop :=
  (sortedData ops data).Perm data

theorem permutation_thm (ops : NumberOps α) (data : List α) : permutation_prop ops data := by sorry


section ExactArithmetic
variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The mathematical layers sort into nondecreasing order, not merely a permutation. -/
def ordering_prop (data : List K) : Prop :=
  (sortedData (mathOps K) data).Sorted (· ≤ ·)

theorem ordering_thm (data : List K) : ordering_prop data := by sorry

/-- Exact arithmetic fact: convex weights interpolate inside the adjacent cell. -/
theorem blend_bounds (a b : K) (n : Nat) (delta : Int)
    (hab : a ≤ b) (hn : 0 < n) (hd : 0 ≤ delta) (hdn : delta ≤ (n : Int)) :
    a ≤ blend (mathOps K) a b n delta ∧ blend (mathOps K) a b n delta ≤ b := by sorry

/-- For inclusive quantiles each cut lies between its two selected observations.
This is intentionally not asserted for exclusive quantiles, which extrapolate. -/
def hull_prop (data : List K) (n : Int) (method : String) : Prop :=
  method = "inclusive" →
    ∀ result, benchmarkQuantiles (mathOps K) data n method = .ok result →
      ∀ k, k < n.toNat - 1 →
        let xs := sortedData (mathOps K) data
        let c := inclusiveCut xs.length n.toNat (k + 1)
        xs.getD c.lo 0 ≤ result.getD k 0 ∧ result.getD k 0 ≤ xs.getD c.hi 0

theorem hull_thm (data : List K) (n : Int) (method : String)
    (h : Pre data n method) : hull_prop data n method := by sorry

/-- Reordering the input cannot affect the mathematical answer. -/
def reorder_prop (data other : List K) (n : Int) (method : String) : Prop :=
  data.Perm other →
    benchmarkQuantiles (mathOps K) data n method = benchmarkQuantiles (mathOps K) other n method

theorem reorder_thm (data other : List K) (n : Int) (method : String) :
    reorder_prop data other n method := by sorry

end ExactArithmetic

/-! ## Order of the returned cut points -/
theorem cut_geometry (ld n i j : Nat) (method : String) (hl : 2 ≤ ld)
    (hn : 0 < n) (hij : i ≤ j) :
    let c := by sorry

section OutputOrder
variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem blend_lower (a b : K) (n : Nat) (delta : Int)
    (hab : a ≤ b) (hn : 0 < n) (hd : 0 ≤ delta) :
    a ≤ blend (mathOps K) a b n delta := by sorry

theorem blend_upper (a b : K) (n : Nat) (delta : Int)
    (hab : a ≤ b) (hn : 0 < n) (hdn : delta ≤ (n : Int)) :
    blend (mathOps K) a b n delta ≤ b := by sorry

theorem blend_delta_mono (a b : K) (n : Nat) (delta epsilon : Int)
    (hab : a ≤ b) (hn : 0 < n) (hd : delta ≤ epsilon) :
    blend (mathOps K) a b n delta ≤ blend (mathOps K) a b n epsilon := by sorry

omit [IsStrictOrderedRing K] in
theorem sorted_getD_mono (xs : List K) (hs : xs.Sorted (· ≤ ·))
    (i j : Nat) (hi : i < xs.length) (hj : j < xs.length) (hij : i ≤ j) :
    xs.getD i 0 ≤ xs.getD j 0 := by sorry

theorem cutValue_mono (xs : List K) (n i j : Nat) (method : String)
    (hs : xs.Sorted (· ≤ ·)) (hl : 2 ≤ xs.length) (hn : 0 < n)
    (hm : method = "inclusive" ∨ method = "exclusive")
    (hi : 1 ≤ i) (hin : i < n) (hj : 1 ≤ j) (hjn : j < n) (hij : i ≤ j) :
    cutValue (mathOps K) xs n (cut xs.length n i method) ≤
      cutValue (mathOps K) xs n (cut xs.length n j method) := by sorry

/-- Both methods return nondecreasing cut points, even where exclusive extrapolates. -/
def monotone_prop (data : List K) (n : Int) (method : String) : Prop :=
  ∀ result, benchmarkQuantiles (mathOps K) data n method = .ok result →
    result.Sorted (· ≤ ·)

theorem monotone_thm (data : List K) (n : Int) (method : String)
    (h : Pre data n method) : monotone_prop data n method := by sorry

end OutputOrder

/-! ## Postcondition
The exact formulas, indices, and exceptional behavior are part of the contract,
not replaced by a weaker bounds-only specification. The ordered-field part
specializes to Real without a finiteness or rationality precondition.
-/
def Post_prop {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (data : List K) (n : Int) (method : String) : Prop :=
  validation_prop (mathOps K) data n method ∧
  length_prop (mathOps K) data n method ∧
  interpolation_prop (mathOps K) data n method ∧
  indexing_prop data n method ∧
  oneInterval_prop (mathOps K) data n method ∧
  permutation_prop (mathOps K) data ∧
  ordering_prop data ∧ monotone_prop data n method ∧ hull_prop data n method ∧
  (∀ other, reorder_prop data other n method)


/-! ## Bounded property-based tests

All lists of length at most four over {-2, 0, 3}, including duplicates, empty
lists, and unsorted lists, are tested with eleven counts and three methods.
Invalid cases are included in validation and reordering tests. Every property
has its own executable check; the postcondition has a combined check as well.

PBT: Real comparisons are not executable. The ordered-field properties
`ordering_prop`, `monotone_prop`, `hull_prop`, `reorder_prop`, and `Post_prop` (and the structural
properties instantiated at Real) are tested at the executable Rat counterpart.
Their theorems above retain their full, unrestricted ordered-field domains.
-/
def smallLists : Nat → List (List ℚ)
  | 0 => [[]]
  | k + 1 => [] :: ([-2, 0, 3] : List ℚ).flatMap
      (fun x => (smallLists k).map (fun xs => x :: xs))

def testCounts : List Int := [-2, -1, 0, 1, 2, 3, 4, 5, 7, 10, 16]
def testMethods : List String := ["inclusive", "exclusive", "invalid"]

def allCases (p : List ℚ → Int → String → Bool) : Bool :=
  (smallLists 4).all fun data =>
    testCounts.all fun n => testMethods.all fun method => p data n method

def onValid (p : List ℚ → Int → String → Bool) (data : List ℚ)
    (n : Int) (method : String) : Bool :=
  !admissible data n method || p data n method

def validationCheck (data : List ℚ) (n : Int) (method : String) : Bool :=
  decide ((benchmarkQuantiles ratOps data n method = .error preError) ↔ ¬Pre data n method)

def lengthCheck (data : List ℚ) (n : Int) (method : String) : Bool :=
  match benchmarkQuantiles ratOps data n method with
  | .ok result => decide (result.length = n.toNat - 1)
  | .error _ => false

def interpolationCheck (data : List ℚ) (n : Int) (method : String) : Bool :=
  match benchmarkQuantiles ratOps data n method with
  | .ok result => (List.range (n.toNat - 1)).all fun k =>
      decide (result[k]? = some (referenceValue ratOps (sortedData ratOps data)
        n.toNat (k + 1) method))
  | .error _ => false

def indexingCheck (data : List ℚ) (n : Int) (method : String) : Bool :=
  (List.range (n.toNat - 1)).all fun k =>
    let i := k + 1
    let c := cut data.length n.toNat i method
    decide (c.lo + 1 = c.hi ∧ c.hi < data.length ∧
      (method = "inclusive" → 0 ≤ c.delta ∧ c.delta < n ∧
        (i : Int) * (data.length - 1 : Nat) = (c.lo : Int) * n + c.delta))

def oneIntervalCheck (data : List ℚ) (n : Int) (method : String) : Bool :=
  decide (n = 1 → benchmarkQuantiles ratOps data n method = .ok [])

def permutationCheck (data : List ℚ) (_n : Int) (_method : String) : Bool :=
  decide ((sortedData ratOps data).Perm data)

def orderingCheck (data : List ℚ) (_n : Int) (_method : String) : Bool :=
  decide ((sortedData ratOps data).Sorted (· ≤ ·))

def monotoneCheck (data : List ℚ) (n : Int) (method : String) : Bool :=
  match benchmarkQuantiles ratOps data n method with
  | .ok result => decide (result.Sorted (· ≤ ·))
  | .error _ => false

def hullCheck (data : List ℚ) (n : Int) (method : String) : Bool :=
  if method = "inclusive" then
    match benchmarkQuantiles ratOps data n method with
    | .ok result => (List.range (n.toNat - 1)).all fun k =>
        let xs := sortedData ratOps data
        let c := inclusiveCut xs.length n.toNat (k + 1)
        decide (xs.getD c.lo 0 ≤ result.getD k 0 ∧ result.getD k 0 ≤ xs.getD c.hi 0)
    | .error _ => false
  else true

/-- Enumerate every permutation rather than relying on a rare random implication. -/
def reorderCheck (data : List ℚ) (n : Int) (method : String) : Bool :=
  data.permutations.all fun other =>
    decide (benchmarkQuantiles ratOps data n method = benchmarkQuantiles ratOps other n method)

def postCheck (data : List ℚ) (n : Int) (method : String) : Bool :=
  validationCheck data n method && lengthCheck data n method &&
  interpolationCheck data n method && indexingCheck data n method &&
  oneIntervalCheck data n method && permutationCheck data n method &&
  orderingCheck data n method && monotoneCheck data n method &&
  hullCheck data n method && reorderCheck data n method

-- PBT for validation_prop, including every generated invalid input.
example : allCases validationCheck = true := by native_decide
-- PBT for length_prop.
example : allCases (onValid lengthCheck) = true := by native_decide
-- PBT for interpolation_prop (both methods, including extrapolation).
example : allCases (onValid interpolationCheck) = true := by native_decide
-- PBT for indexing_prop (including division and signed cast identities).
example : allCases (onValid indexingCheck) = true := by native_decide
-- PBT for oneInterval_prop.
example : allCases (onValid oneIntervalCheck) = true := by native_decide
-- PBT for permutation_prop.
example : allCases permutationCheck = true := by native_decide
-- PBT for ordering_prop, instantiated at Rat.
example : allCases orderingCheck = true := by native_decide
-- PBT for monotone_prop, including exclusive extrapolation.
example : allCases (onValid monotoneCheck) = true := by native_decide
-- PBT for hull_prop, instantiated at Rat.
example : allCases (onValid hullCheck) = true := by native_decide
-- PBT for reorder_prop, checking all permutations, even on invalid inputs.
example : allCases reorderCheck = true := by native_decide
-- PBT for Post_prop, the conjunction of the preceding properties.
example : allCases (onValid postCheck) = true := by native_decide
#eval ((smallLists 4).length, testCounts.length, testMethods.length)
#eval allCases (onValid postCheck)

/-! ## Correctness -/
theorem correctness_thm {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (data : List K) (n : Int) (method : String) :
    Pre data n method → Post_prop data n method := by sorry

/-- Structural and exact-operation-order guarantees for the actual Float code.
This makes no claim that rounded Float arithmetic is real arithmetic. -/
theorem float_correctness_thm (data : List Float) (n : Int) (method : String)
    (h : Pre data n method) :
    length_prop floatOps data n method ∧
    interpolation_prop floatOps data n method ∧
    indexing_prop data n method ∧
    validation_prop floatOps data n method := by sorry

/-! ## Imperative implementation -/
/-- A real mutable loop, appending one cut at a time as in the Python program. -/
def cutsImperative (ops : NumberOps α) (xs : List α) (n : Nat) (method : String) : List α :=
  Id.run do
    let mut result := []
    for k in List.range (n - 1) do
      let i := k + 1
      let c := cut xs.length n i method
      let interpolated := cutValue ops xs n c
      result := result ++ [interpolated]
    return result

def quantilesImperative (ops : NumberOps α) (data : List α)
    (n : Int := 4) (method : String := "exclusive") : Except Error (List α) := Id.run do
  if n < 1 then
    return .error (.statisticsError "n must be at least 1")
  let xs := sortedData ops data
  if xs.length < 2 then
    return .error (.statisticsError "must have at least two data points")
  if validMethod method then
    return .ok (cutsImperative ops xs n.toNat method)
  else
    return .error (.valueError ("Unknown method: '" ++ method ++ "'"))

def benchmarkImperative (ops : NumberOps α) (data : List α)
    (n : Int := 4) (method : String := "exclusive") : Except Error (List α) := Id.run do
  if admissible data n method then
    return quantilesImperative ops data n method
  else
    return .error preError

/-! ## Imperative tests -/
example : benchmarkImperative ratOps [1, 2, 3, 4] = .ok [5/4, 5/2, 15/4] := by native_decide
example : benchmarkImperative ratOps [4, 1, 3, 2] 4 "inclusive" =
    .ok [7/4, 5/2, 13/4] := by native_decide
example : benchmarkImperative ratOps [0, 10] 4 = .ok [-(5/2), 5, 25/2] := by native_decide
example : benchmarkImperative ratOps [3, 7] 1 = .ok [] := by native_decide
example : benchmarkImperative ratOps [1] = .error preError := by native_decide
example : benchmarkImperative ratOps [1, 2] (-1) = .error preError := by native_decide
example : benchmarkImperative ratOps [1, 2] 4 "invalid" = .error preError := by native_decide
example : (match benchmarkImperative floatOps [1.5, 2.5, 3.5, 4.5] 2 with
    | .ok result => result == [3.0]
    | .error _ => false) = true := by native_decide
example : allCases (fun data n method => decide
    (benchmarkQuantiles ratOps data n method = benchmarkImperative ratOps data n method)) =
    true := by native_decide
#eval benchmarkImperative floatOps [1, 2, 3, 4]

/-! ## Functional/imperative equivalence -/
/-- General accumulator invariant for a mutable append loop. -/
theorem append_loop_eq (f : α → β) (is : List α) (acc : List β) :
    (Id.run do
      let mut result := acc
      for i in is do
        result := result ++ [f i]
      return result) = acc ++ is.map f := by sorry

theorem cutsImperative_eq (ops : NumberOps α) (xs : List α) (n : Nat) (method : String) :
    cutsImperative ops xs n method = cuts ops xs n method := by sorry

theorem quantiles_equivalence_thm (ops : NumberOps α) (data : List α) (n : Int) (method : String) :
    quantiles ops data n method = quantilesImperative ops data n method := by sorry

/-- Unconditional equivalence: also covers invalid n, insufficient data, invalid
methods, all Float values, and all exact mathematical inputs. -/
theorem equivalence_thm (ops : NumberOps α) (data : List α) (n : Int) (method : String) :
    benchmarkQuantiles ops data n method = benchmarkImperative ops data n method := by sorry

end StatisticsQuantiles
end Agent
