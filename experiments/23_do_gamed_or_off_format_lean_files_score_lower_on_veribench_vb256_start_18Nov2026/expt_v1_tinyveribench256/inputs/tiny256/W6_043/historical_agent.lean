import Mathlib
namespace Agent

/-!
# Unsafe padding oracle

A translation of the timing-attack example from MIT 6.858 Lecture 20.
Python integers are represented by `Int`; zero-based indices by `Nat`.
The oracle returns `none` precisely when every input equals the padding byte,
and otherwise returns the index of the *first* mismatch. In particular, the
interface reveals more than padding validity: it reveals the matching-prefix
length. No byte-range assumption is imposed, since the Python code has none.
-/

namespace UnsafePaddingOracle

/-- Functional scan, with each successful comparison shifting the tail index. -/
def unsafePaddingOracle : List Int → Int → Option Nat
  | [], _ => none
  | b :: bs, pad =>
      if b = pad then (unsafePaddingOracle bs pad).map Nat.succ else some 0

-- The seven checks from the Python program.
example : unsafePaddingOracle [2, 2] 2 = none := by native_decide
example : unsafePaddingOracle [4, 4, 4, 4] 4 = none := by native_decide
example : unsafePaddingOracle [4, 4, 4, 9] 4 = some 3 := by native_decide
example : unsafePaddingOracle [9, 4, 4, 4] 4 = some 0 := by native_decide
example : unsafePaddingOracle [4, 9, 4, 4] 4 = some 1 := by native_decide
example : unsafePaddingOracle [] 0 = none := by native_decide
example : unsafePaddingOracle [1] 2 = some 0 := by native_decide
-- Values outside the usual byte range remain admissible.
example : unsafePaddingOracle [-3, -3, 300] (-3) = some 2 := by native_decide
#eval unsafePaddingOracle [4, 4, 4, 9] 4
#eval unsafePaddingOracle [] 0

/-- All Python integer lists and padding integers are accepted. -/
def Pre (_block : List Int) (_pad : Int) : Prop := True

/-- Success is exactly universal equality with the padding value. -/
def valid_prop (block : List Int) (pad : Int) : Prop :=
  unsafePaddingOracle block pad = none ↔ ∀ b ∈ block, b = pad

theorem valid_thm (block : List Int) (pad : Int) : valid_prop block pad := by
  unfold valid_prop
  induction block with
  | nil => simp [unsafePaddingOracle]
  | cons b bs ih =>
      by_cases hb : b = pad <;> simp [unsafePaddingOracle, hb, ih]

/-- A returned index is in bounds, is wrong, and every preceding byte is right. -/
def firstFailure_prop (block : List Int) (pad : Int) : Prop :=
  ∀ i : Nat, unsafePaddingOracle block pad = some i ↔
    i < block.length ∧ block[i]? ≠ some pad ∧
      ∀ j : Nat, j < i → block[j]? = some pad

theorem firstFailure_thm (block : List Int) (pad : Int) :
    firstFailure_prop block pad := by
  unfold firstFailure_prop
  induction block with
  | nil => intro i; simp [unsafePaddingOracle]
  | cons b bs ih =>
      intro i
      cases i with
      | zero =>
          by_cases hb : b = pad <;>
            simp [unsafePaddingOracle, hb, Option.map_eq_some_iff]
      | succ i =>
          have hprefix :
              (∀ j : Nat, j < i + 1 → (b :: bs)[j]? = some pad) ↔
                b = pad ∧ ∀ j : Nat, j < i → bs[j]? = some pad := by
            constructor
            · intro h
              constructor
              · simpa using h 0 (Nat.zero_lt_succ i)
              · intro j hj
                simpa using h (j + 1) (Nat.succ_lt_succ hj)
            · rintro ⟨hb, h⟩ j hj
              cases j with
              | zero => simpa using hb
              | succ j => simpa using h j (Nat.lt_of_succ_lt_succ hj)
          rw [hprefix]
          by_cases hb : b = pad <;>
            simp [unsafePaddingOracle, hb, Option.map_eq_some_iff, ih]

/-- Any failure index belongs to the input block. -/
def bounds_prop (block : List Int) (pad : Int) : Prop :=
  ∀ i, unsafePaddingOracle block pad = some i → i < block.length

theorem bounds_thm (block : List Int) (pad : Int) : bounds_prop block pad := by
  intro i hi
  exact ((firstFailure_thm block pad i).mp hi).1

/-- The exact observable failure position is the matching-prefix length.
The suffix after the first wrong byte cannot affect the answer. -/
def leak_prop (pad wrong : Int) (n : Nat) (suffix : List Int) : Prop :=
  wrong ≠ pad →
    unsafePaddingOracle (List.replicate n pad ++ wrong :: suffix) pad = some n

theorem leak_thm (pad wrong : Int) (n : Nat) (suffix : List Int) :
    leak_prop pad wrong n suffix := by
  intro hwrong
  induction n with
  | zero => simp [unsafePaddingOracle, hwrong]
  | succ n ih =>
      simp [List.replicate_succ, unsafePaddingOracle, ih]

/-- Complete functional contract. -/
def Post_prop (block : List Int) (pad : Int) : Prop :=
  valid_prop block pad ∧ firstFailure_prop block pad ∧ bounds_prop block pad

/-! ## Exhaustive bounded property-based tests

The alphabet deliberately includes a negative integer and an integer above 255.
`smallBlocks n` enumerates *all* lists of length at most `n` over this alphabet.
These checks are executable evidence only; the theorems above cover every list
of arbitrary integers, without any length or byte-range restriction.
-/

def testValues : List Int := [-3, 0, 2, 4, 9, 300]

def smallBlocks : Nat → List (List Int)
  | 0 => [[]]
  | n + 1 => [] :: testValues.flatMap (fun b => (smallBlocks n).map (b :: ·))

/-- Check 1,555 blocks against six padding integers (9,330 input pairs). -/
def allSmallCases (test : List Int → Int → Bool) : Bool :=
  (smallBlocks 4).all (fun block => testValues.all (test block))

/-- Executable form of `valid_prop`. -/
def validCheck (block : List Int) (pad : Int) : Bool :=
  (unsafePaddingOracle block pad == none) == block.all (· == pad)

/-- Executable form of `bounds_prop`. -/
def boundsCheck (block : List Int) (pad : Int) : Bool :=
  match unsafePaddingOracle block pad with
  | none => true
  | some i => decide (i < block.length)

/-- Executable first-failure biconditional, checking every in-range index and
one out-of-range index. The bounds check rules out any larger returned index;
for every larger index the right side is false because it is out of bounds. -/
def firstFailureCheck (block : List Int) (pad : Int) : Bool :=
  boundsCheck block pad &&
    (List.range (block.length + 1)).all (fun i =>
      (unsafePaddingOracle block pad == some i) ==
        (decide (i < block.length) && (block[i]? != some pad) &&
          (List.range i).all (fun j => block[j]? == some pad)))

/-- Executable conjunction corresponding to `Post_prop`. -/
def postCheck (block : List Int) (pad : Int) : Bool :=
  validCheck block pad && firstFailureCheck block pad && boundsCheck block pad

-- PBT for valid_prop.
example : allSmallCases validCheck = true := by native_decide
-- PBT for firstFailure_prop (including the reverse implication).
example : allSmallCases firstFailureCheck = true := by native_decide
-- PBT for bounds_prop.
example : allSmallCases boundsCheck = true := by native_decide
-- PBT for leak_prop: all tested padding/wrong values, positions 0 through 7,
-- and all 259 suffixes of length at most 3. Equality cases test the implication.
def leakCheck : Bool :=
  testValues.all (fun pad => testValues.all (fun wrong =>
    (List.range 8).all (fun n => (smallBlocks 3).all (fun suffix =>
      (wrong == pad) ||
        (unsafePaddingOracle (List.replicate n pad ++ wrong :: suffix) pad == some n)))))
example : leakCheck = true := by native_decide
-- PBT for the complete post-condition.
example : allSmallCases postCheck = true := by native_decide
#eval ("post-condition PBT", allSmallCases postCheck)
#eval ("failure-position leakage PBT", leakCheck)

/-- Total correctness on the entire Python input domain. -/
theorem correctness_thm (block : List Int) (pad : Int) :
    Pre block pad → Post_prop block pad := by
  intro _
  exact ⟨valid_thm block pad, firstFailure_thm block pad, bounds_thm block pad⟩

/-! ## Imperative translation
The helper permits an arbitrary initial index, which is useful for the loop
invariant. The public oracle starts at zero, like Python's `enumerate`.
The `return` inside the loop exits immediately at the first mismatch.
-/

def scanImperativeFrom (block : List Int) (pad : Int) (start : Nat) : Option Nat := Id.run do
  let mut i := start
  for b in block do
    if b != pad then
      return some i
    i := i + 1
  return none

def unsafePaddingOracleImperative (block : List Int) (pad : Int) : Option Nat :=
  scanImperativeFrom block pad 0

-- The original Python tests, now against the mutable-state implementation.
example : unsafePaddingOracleImperative [2, 2] 2 = none := by native_decide
example : unsafePaddingOracleImperative [4, 4, 4, 4] 4 = none := by native_decide
example : unsafePaddingOracleImperative [4, 4, 4, 9] 4 = some 3 := by native_decide
example : unsafePaddingOracleImperative [9, 4, 4, 4] 4 = some 0 := by native_decide
example : unsafePaddingOracleImperative [4, 9, 4, 4] 4 = some 1 := by native_decide
example : unsafePaddingOracleImperative [] 0 = none := by native_decide
example : unsafePaddingOracleImperative [1] 2 = some 0 := by native_decide
example : unsafePaddingOracleImperative [-3, -3, 300] (-3) = some 2 := by native_decide
#eval unsafePaddingOracleImperative [4, 4, 4, 9] 4
#eval unsafePaddingOracleImperative [2, 2] 2
-- Additional cross-implementation PBT.
example : allSmallCases (fun block pad =>
    unsafePaddingOracle block pad == unsafePaddingOracleImperative block pad) = true := by
  native_decide

/-- Unfolding one iteration of the actual early-return loop. -/
theorem scanImperativeFrom_cons (b pad : Int) (bs : List Int) (start : Nat) :
    scanImperativeFrom (b :: bs) pad start =
      if b = pad then scanImperativeFrom bs pad (start + 1) else some start := by
  by_cases hb : b = pad <;> simp [scanImperativeFrom, List.forIn_cons, hb]

/-- Loop invariant: a tail-relative failure index is shifted by the current
mutable index; a successful scan remains `none`. -/
theorem scanImperativeFrom_eq (block : List Int) (pad : Int) (start : Nat) :
    scanImperativeFrom block pad start =
      (unsafePaddingOracle block pad).map (fun i => start + i) := by
  induction block generalizing start with
  | nil => rfl
  | cons b bs ih =>
      by_cases hb : b = pad <;>
        simp [scanImperativeFrom_cons, unsafePaddingOracle, hb, ih,
          Option.map_map, Function.comp_def, Nat.add_comm, Nat.add_left_comm]

/-- The functional and imperative programs have identical observable results
on every input, not merely on the bounded test cases. -/
theorem equivalence_thm (block : List Int) (pad : Int) :
    unsafePaddingOracle block pad = unsafePaddingOracleImperative block pad := by
  simpa [unsafePaddingOracleImperative] using (scanImperativeFrom_eq block pad 0).symm

end UnsafePaddingOracle
end Agent
