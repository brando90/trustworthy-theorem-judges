import Mathlib
namespace Agent

/-!
# Safe WebAssembly addressing by zero extension

Translation of `safe_wasm_zero_extend` and its Python checks. All inputs and
addresses are unbounded `Int`s, as in Python: neither addition nor the base
address is restricted to a machine word. Masking an integer to 32 bits is its
Euclidean residue modulo 2^32, including for negative inputs. `none` is the
out-of-bounds trap; `some address` is a successful access.
-/

namespace SafeWasmZeroExtend

/-- The number of distinct unsigned 32-bit offsets (4 GiB). -/
def u32Modulus : Int := 0x100000000

/-- Zero extension of the low 32 bits, never sign extension. -/
def zeroExtend32 (raw : Int) : Int := raw % u32Modulus

/-- The functional translation, with the two bounds checks from Python. -/
def safe_wasm_zero_extend (mem_base raw_u32_offset mem_size : Int) : Option Int :=
  let zero_ext_offset := zeroExtend32 raw_u32_offset
  let effective := mem_base + zero_ext_offset
  if effective < mem_base ∨ effective ≥ mem_base + mem_size then
    none
  else
    some effective

/-- Executable translation of the six assertions in Python's `check`. -/
def check (candidate : Int → Int → Int → Option Int) : Bool :=
  let mem_base : Int := 0x200000000
  let mem_size : Int := 0x100000000
  let atOrAboveBase := fun result : Option Int =>
    match result with
    | none => false
    | some address => decide (mem_base ≤ address)
  decide (candidate mem_base 0x10 mem_size = some (mem_base + 0x10)) &&
  atOrAboveBase (candidate mem_base 0x80000000 mem_size) &&
  atOrAboveBase (candidate mem_base 0xFFFFFFFF mem_size) &&
  decide (candidate mem_base 0 mem_size = some mem_base) &&
  decide (candidate mem_base 0x1000 0x1000 = none) &&
  decide (candidate mem_base (0x1000 - 1) 0x1000 = some (mem_base + 0x1000 - 1))

example : check safe_wasm_zero_extend = true := by native_decide
#eval check safe_wasm_zero_extend
#eval if check safe_wasm_zero_extend then "All tests passed." else "Candidate failed tests"

-- The six checks in the Python source (with exact addresses for checks 2 and 3).
example : safe_wasm_zero_extend 0x200000000 0x10 0x100000000 =
    some (0x200000000 + 0x10) := by native_decide
example : safe_wasm_zero_extend 0x200000000 0x80000000 0x100000000 =
    some (0x200000000 + 0x80000000) := by native_decide
example : safe_wasm_zero_extend 0x200000000 0xFFFFFFFF 0x100000000 =
    some (0x200000000 + 0xFFFFFFFF) := by native_decide
example : safe_wasm_zero_extend 0x200000000 0 0x100000000 =
    some 0x200000000 := by native_decide
example : safe_wasm_zero_extend 0x200000000 0x1000 0x1000 = none := by native_decide
example : safe_wasm_zero_extend 0x200000000 (0x1000 - 1) 0x1000 =
    some (0x200000000 + 0x1000 - 1) := by native_decide

-- Python also permits signed and arbitrarily large integers.
example : safe_wasm_zero_extend 0x200000000 0x100000000 0x100000000 =
    some 0x200000000 := by native_decide
example : safe_wasm_zero_extend (-10) (-1) 0x100000000 =
    some (-10 + 0xFFFFFFFF) := by native_decide
example : safe_wasm_zero_extend 7 0 0 = none := by native_decide
example : safe_wasm_zero_extend 7 0 (-1) = none := by native_decide

#eval safe_wasm_zero_extend 0x200000000 0x80000000 0x100000000
#eval safe_wasm_zero_extend 0x200000000 0x1000 0x1000

/-- No input restrictions: Python's integers may be signed and unbounded. -/
def Pre (_mem_base _raw_u32_offset _mem_size : Int) : Prop := True



private theorem ldiff_mask (n k : Nat) :
    Nat.ldiff (2 ^ k - 1) n = 2 ^ k - (n % 2 ^ k + 1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_ldiff, Nat.testBit_two_pow_sub_one,
    Nat.testBit_two_pow_sub_succ (Nat.mod_lt n (Nat.two_pow_pos k)),
    Nat.testBit_mod_two_pow]
  by_cases h : i < k <;> simp [h]

private theorem land_eq_emod (raw : Int) : Int.land raw 0xFFFFFFFF = raw % 0x100000000 := by
  cases raw with
  | ofNat n =>
    change ((n &&& (2 ^ 32 - 1) : Nat) : Int) = ((n % 2 ^ 32 : Nat) : Int)
    rw [Nat.and_two_pow_sub_one_eq_mod]
  | negSucc n =>
    change ((Nat.ldiff (2 ^ 32 - 1) n : Nat) : Int) = Int.negSucc n % 0x100000000
    rw [ldiff_mask, Int.negSucc_emod n (by norm_num)]
    have h : n % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt n (by norm_num)
    rw [Int.natCast_sub (by omega)]
    push_cast
    omega

/-- The remainder model agrees exactly with Python's bitwise mask. -/
def mask_prop (raw : Int) : Prop :=
  zeroExtend32 raw = Int.land raw 0xFFFFFFFF

theorem mask_thm (raw : Int) : mask_prop raw := by
  exact (land_eq_emod raw).symm

/-- The masked offset is always an unsigned 32-bit integer. -/
def offsetRange_prop (raw : Int) : Prop :=
  0 ≤ zeroExtend32 raw ∧ zeroExtend32 raw < u32Modulus

theorem offsetRange_thm (raw : Int) : offsetRange_prop raw := by
  unfold offsetRange_prop zeroExtend32
  exact ⟨Int.emod_nonneg raw (by norm_num [u32Modulus]),
    Int.emod_lt_of_pos raw (by norm_num [u32Modulus])⟩

/-- Even before the bounds check, zero extension cannot move below the base. -/
def noUnderflow_prop (base raw : Int) : Prop :=
  base ≤ base + zeroExtend32 raw

theorem noUnderflow_thm (base raw : Int) : noUnderflow_prop base raw := by
  have hz : 0 ≤ zeroExtend32 raw := (offsetRange_thm raw).1
  unfold noUnderflow_prop
  omega

/-- An exact, executable characterization of both possible outcomes. -/
def result_prop (base raw size : Int) : Prop :=
  safe_wasm_zero_extend base raw size =
    if zeroExtend32 raw < size then some (base + zeroExtend32 raw) else none

theorem result_thm (base raw size : Int) : result_prop base raw size := by
  have hz : 0 ≤ zeroExtend32 raw := (offsetRange_thm raw).1
  unfold result_prop safe_wasm_zero_extend
  dsimp only
  by_cases hs : zeroExtend32 raw < size
  · have ho : ¬ (base + zeroExtend32 raw < base ∨
        base + zeroExtend32 raw ≥ base + size) := by omega
    rw [if_neg ho, if_pos hs]
  · have ho : base + zeroExtend32 raw < base ∨
        base + zeroExtend32 raw ≥ base + size := by omega
    rw [if_pos ho, if_neg hs]

/-- Every returned address is the computed address and is inside the sandbox. -/
def sandbox_prop (base raw size : Int) : Prop :=
  match safe_wasm_zero_extend base raw size with
  | none => True
  | some address =>
      address = base + zeroExtend32 raw ∧ base ≤ address ∧ address < base + size

theorem sandbox_thm (base raw size : Int) : sandbox_prop base raw size := by
  have hz : 0 ≤ zeroExtend32 raw := (offsetRange_thm raw).1
  unfold sandbox_prop
  rw [result_thm base raw size]
  by_cases hs : zeroExtend32 raw < size
  · simp [hs, hz]
  · simp [hs]

/-- A trap occurs exactly at or beyond the exclusive upper bound. -/
def trap_prop (base raw size : Int) : Prop :=
  safe_wasm_zero_extend base raw size = none ↔ size ≤ zeroExtend32 raw

theorem trap_thm (base raw size : Int) : trap_prop base raw size := by
  unfold trap_prop
  rw [result_thm base raw size]
  by_cases hs : zeroExtend32 raw < size
  · simp [hs, show ¬ size ≤ zeroExtend32 raw by omega]
  · simp [hs, show size ≤ zeroExtend32 raw by omega]

/-- Every masked input succeeds in a 4 GiB (or larger) sandbox. -/
def fullSandbox_prop (base raw size : Int) : Prop :=
  u32Modulus ≤ size →
    safe_wasm_zero_extend base raw size = some (base + zeroExtend32 raw)

theorem fullSandbox_thm (base raw size : Int) : fullSandbox_prop base raw size := by
  intro hsize
  have hz : zeroExtend32 raw < u32Modulus := (offsetRange_thm raw).2
  have hs : zeroExtend32 raw < size := by omega
  rw [result_thm base raw size]
  simp [hs]

/-- Canonical unsigned inputs are unchanged, including those with bit 31 set. -/
def unsignedIdentity_prop (raw : Int) : Prop :=
  0 ≤ raw ∧ raw < u32Modulus → zeroExtend32 raw = raw

theorem unsignedIdentity_thm (raw : Int) : unsignedIdentity_prop raw := by
  intro h
  exact Int.emod_eq_of_lt h.1 h.2

/-- Empty and negative-sized sandboxes reject every input. -/
def nonpositiveSize_prop (base raw size : Int) : Prop :=
  size ≤ 0 → safe_wasm_zero_extend base raw size = none

theorem nonpositiveSize_thm (base raw size : Int) : nonpositiveSize_prop base raw size := by
  intro hs
  have hz : 0 ≤ zeroExtend32 raw := (offsetRange_thm raw).1
  exact (trap_thm base raw size).2 (by omega)

/-- Discarding all higher bits works for arbitrary signed multiples of 2^32. -/
def wrapping_prop (base raw size multiple : Int) : Prop :=
  safe_wasm_zero_extend base (raw + multiple * u32Modulus) size =
    safe_wasm_zero_extend base raw size

theorem wrapping_thm (base raw size multiple : Int) : wrapping_prop base raw size multiple := by
  simp [wrapping_prop, safe_wasm_zero_extend, zeroExtend32]


/-- In particular, bit 31 in a canonical u32 cannot cause sign extension. -/
def highBit_prop (base raw : Int) : Prop :=
  0x80000000 ≤ raw ∧ raw ≤ 0xFFFFFFFF →
    safe_wasm_zero_extend base raw u32Modulus = some (base + raw) ∧
      base ≤ base + raw

theorem highBit_thm (base raw : Int) : highBit_prop base raw := by
  intro h
  have hraw : 0 ≤ raw ∧ raw < u32Modulus := by
    dsimp [u32Modulus]
    omega
  have hid : zeroExtend32 raw = raw := unsignedIdentity_thm raw hraw
  constructor
  · simpa only [hid] using fullSandbox_thm base raw u32Modulus (le_refl _)
  · omega

/-- Postcondition for one call: exact mask, unsigned range, both outcome cases,
    and all safety consequences. Periodicity is proved separately above. -/
def Post_prop (base raw size : Int) : Prop :=
  mask_prop raw ∧
  offsetRange_prop raw ∧
  noUnderflow_prop base raw ∧
  result_prop base raw size ∧
  sandbox_prop base raw size ∧
  trap_prop base raw size ∧
  fullSandbox_prop base raw size ∧
  unsignedIdentity_prop raw ∧
  nonpositiveSize_prop base raw size ∧
  highBit_prop base raw

/-! ## Property-based tests

These are bounded exhaustive tests, not proofs of the universal claims. The
sample sets combine a signed interval with mask boundaries, high-bit values,
and both sides of the 4 KiB and 4 GiB limits. Every `_prop`, including `Post_prop`,
has its own executable check. Implication tests include inputs satisfying their
hypotheses, rather than relying only on vacuous cases.
-/

def testBases : List Int :=
  [-0x300000000, -17, -1, 0, 13, 0x200000000, 0x10000000000000000]

def testOffsets : List Int :=
  (List.range 33).map (fun n => (n : Int) - 16) ++
    [-0x200000001, -0x100000001, -0x100000000, -0xFFFFFFFF,
      0xFFF, 0x1000, 0x1001, 0x7FFFFFFF, 0x80000000, 0x80000001,
      0xFFFFFFFE, 0xFFFFFFFF, 0x100000000, 0x100000001,
      0x180000000, 0x200000010]

def testSizes : List Int :=
  [-0x100000000, -1, 0, 1, 2, 8, 16, 0xFFF, 0x1000, 0x1001,
    0x80000000, 0xFFFFFFFF, 0x100000000, 0x100000001]

def allInputs (p : Int → Int → Int → Bool) : Bool :=
  testBases.all fun base => testOffsets.all fun raw => testSizes.all fun size =>
    p base raw size

-- PBT: mask_prop.
example : testOffsets.all (fun raw =>
    decide (zeroExtend32 raw = Int.land raw 0xFFFFFFFF)) = true := by native_decide

-- PBT: offsetRange_prop.
example : testOffsets.all (fun raw =>
    decide (0 ≤ zeroExtend32 raw ∧ zeroExtend32 raw < u32Modulus)) = true := by
  native_decide

-- PBT: noUnderflow_prop, including signed and unbounded bases.
example : allInputs (fun base raw _ =>
    decide (base ≤ base + zeroExtend32 raw)) = true := by native_decide

-- PBT: result_prop; checks exact returned addresses, not just success flags.
example : allInputs (fun base raw size => decide (
    safe_wasm_zero_extend base raw size =
      if zeroExtend32 raw < size then some (base + zeroExtend32 raw) else none)) =
    true := by native_decide

-- PBT: sandbox_prop.
example : allInputs (fun base raw size =>
    match safe_wasm_zero_extend base raw size with
    | none => true
    | some address => decide (address = base + zeroExtend32 raw ∧
        base ≤ address ∧ address < base + size)) = true := by native_decide

-- PBT: trap_prop (both directions of the iff).
example : allInputs (fun base raw size => decide (
    safe_wasm_zero_extend base raw size = none ↔ size ≤ zeroExtend32 raw)) =
    true := by native_decide

-- PBT: fullSandbox_prop.
example : allInputs (fun base raw size => decide (u32Modulus ≤ size →
    safe_wasm_zero_extend base raw size = some (base + zeroExtend32 raw))) =
    true := by native_decide

-- PBT: unsignedIdentity_prop.
example : testOffsets.all (fun raw => decide (0 ≤ raw ∧ raw < u32Modulus →
    zeroExtend32 raw = raw)) = true := by native_decide

-- PBT: nonpositiveSize_prop.
example : allInputs (fun base raw size => decide (size ≤ 0 →
    safe_wasm_zero_extend base raw size = none)) = true := by native_decide

-- PBT: wrapping_prop, for each multiplier in [-4, 4].
example : allInputs (fun base raw size => (List.range 9).all (fun n =>
    decide (safe_wasm_zero_extend base (raw + ((n : Int) - 4) * u32Modulus) size =
      safe_wasm_zero_extend base raw size))) = true := by native_decide

-- PBT: highBit_prop.
example : testBases.all (fun base => testOffsets.all (fun raw =>
    decide (0x80000000 ≤ raw ∧ raw ≤ 0xFFFFFFFF →
      safe_wasm_zero_extend base raw u32Modulus = some (base + raw) ∧
        base ≤ base + raw))) = true := by native_decide

/-- A computable decision of the entire postcondition; no theorem is used to
    force this check to return true. It evaluates all the properties directly. -/
def postCheck (base raw size : Int) : Bool :=
  @decide (Post_prop base raw size) (by
    unfold Post_prop mask_prop offsetRange_prop noUnderflow_prop result_prop
      sandbox_prop trap_prop fullSandbox_prop unsignedIdentity_prop
      nonpositiveSize_prop highBit_prop
    cases safe_wasm_zero_extend base raw size <;> infer_instance)

-- PBT: Post_prop, with more than 4,000 combinations.
example : allInputs postCheck = true := by native_decide
#eval allInputs postCheck

/-- The executable postcondition check is precisely the stated proposition. -/
theorem postCheck_iff (base raw size : Int) :
    postCheck base raw size = true ↔ Post_prop base raw size := by
  simp only [postCheck, decide_eq_true_eq]

/-- Total correctness for all Python integer inputs; there are no hidden
    nonnegativity or machine-word assumptions on the inputs. -/
theorem correctness_thm (base raw size : Int) :
    Pre base raw size → Post_prop base raw size := by
  intro _
  exact ⟨mask_thm raw, offsetRange_thm raw, noUnderflow_thm base raw,
    result_thm base raw size, sandbox_thm base raw size, trap_thm base raw size,
    fullSandbox_thm base raw size, unsignedIdentity_thm raw,
    nonpositiveSize_thm base raw size, highBit_thm base raw⟩

/-! ## Imperative translation -/

/-- Mutable-state rendition using the literal Python bitwise mask. -/
def safe_wasm_zero_extend_imp (mem_base raw_u32_offset mem_size : Int) : Option Int :=
  Id.run do
    let mut zero_ext_offset := raw_u32_offset
    zero_ext_offset := Int.land zero_ext_offset 0xFFFFFFFF
    let mut effective := mem_base
    effective := effective + zero_ext_offset
    let mut result : Option Int := none
    if effective < mem_base ∨ effective ≥ mem_base + mem_size then
      result := none
    else
      result := some effective
    return result

-- The original harness is also run against the imperative implementation.
example : check safe_wasm_zero_extend_imp = true := by native_decide
example : safe_wasm_zero_extend_imp 0x200000000 0x10 0x100000000 =
    some (0x200000000 + 0x10) := by native_decide
example : safe_wasm_zero_extend_imp 0x200000000 0x80000000 0x100000000 =
    some (0x200000000 + 0x80000000) := by native_decide
example : safe_wasm_zero_extend_imp 0x200000000 0xFFFFFFFF 0x100000000 =
    some (0x200000000 + 0xFFFFFFFF) := by native_decide
example : safe_wasm_zero_extend_imp 0x200000000 0 0x100000000 =
    some 0x200000000 := by native_decide
example : safe_wasm_zero_extend_imp 0x200000000 0x1000 0x1000 = none := by native_decide
example : safe_wasm_zero_extend_imp 0x200000000 (0x1000 - 1) 0x1000 =
    some (0x200000000 + 0x1000 - 1) := by native_decide
example : safe_wasm_zero_extend_imp (-10) (-1) 0x100000000 =
    some (-10 + 0xFFFFFFFF) := by native_decide
example : safe_wasm_zero_extend_imp 7 0 (-1) = none := by native_decide
#eval check safe_wasm_zero_extend_imp
#eval safe_wasm_zero_extend_imp 0x200000000 0x80000000 0x100000000
#eval safe_wasm_zero_extend_imp 0x200000000 0x1000 0x1000

-- Bounded equivalence test, independently of the universal proof below.
example : allInputs (fun base raw size => decide (
    safe_wasm_zero_extend base raw size = safe_wasm_zero_extend_imp base raw size)) =
    true := by native_decide

/-- Kernel-checked correspondence of modulo-based and literal-mask programs. -/
theorem functional_eq_imperative_thm (base raw size : Int) :
    safe_wasm_zero_extend base raw size = safe_wasm_zero_extend_imp base raw size := by
  have hm : Int.land raw 0xFFFFFFFF = zeroExtend32 raw := (mask_thm raw).symm
  simp [safe_wasm_zero_extend, safe_wasm_zero_extend_imp, hm, Id.run]
  rfl

end SafeWasmZeroExtend
end Agent
