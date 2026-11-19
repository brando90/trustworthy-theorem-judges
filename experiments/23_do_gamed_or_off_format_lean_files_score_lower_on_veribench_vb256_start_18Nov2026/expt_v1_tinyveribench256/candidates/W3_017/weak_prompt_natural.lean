/-!
# Safe heap address validation

A Lean 4 translation of the Python `safe_heap_validate` function. It accepts only
addresses in the half-open interval `[heapBase, heapBase + heapSize)`.

This uses plain `Int` arithmetic, like Python's unbounded `int`. It checks only the
bounds it is given. It does not inspect memory mappings or prove that a pointer is valid.
-/

/-- Returns `true` exactly when `heapBase ≤ addr < heapBase + heapSize`.
This matches Python's chained comparison `heap_base <= addr < heap_base + heap_size`.
A zero or negative `heapSize` always gives `false`. -/
def safeHeapValidate (addr heapBase heapSize : Int) : Bool :=
  decide (heapBase ≤ addr) && decide (addr < heapBase + heapSize)

/-! ## The fixed examples from `check()` -/

/-- The `(addr, heapBase, heapSize, expected)` cases from the Python `check()`. -/
def checkCases : List (Int × Int × Int × Bool) :=
  [(120, 100, 50, true),
   (100, 100, 50, true),
   (149, 100, 50, true),
   (0,   100, 50, false),
   (150, 100, 50, false)]

/-- Pure version of `check()`: `true` when every case gives its expected result. -/
def checkAll : Bool :=
  checkCases.all fun (addr, base, size, expected) =>
    safeHeapValidate addr base size == expected

/-- Runtime version of `check()`: throws an error on the first wrong result,
like Python's `AssertionError`. -/
def check : IO Unit := do
  for (addr, base, size, expected) in checkCases do
    let got := safeHeapValidate addr base size
    unless got == expected do
      throw <| IO.userError
        s!"AssertionError: safeHeapValidate {addr} {base} {size} = {got}, expected {expected}"

def main : IO Unit := check

theorem check_inside     : safeHeapValidate 120 100 50 = true  := by decide
theorem check_base       : safeHeapValidate 100 100 50 = true  := by decide
theorem check_last       : safeHeapValidate 149 100 50 = true  := by decide
theorem check_below      : safeHeapValidate 0   100 50 = false := by decide
theorem check_one_past   : safeHeapValidate 150 100 50 = false := by decide

/-- Every case in `check()` passes. This is checked when the file compiles. -/
theorem checkAll_eq_true : checkAll = true := by decide

/-! ## Specification -/

/-- Main specification: the function returns `true` exactly for addresses in the interval. -/
theorem safeHeapValidate_iff (addr heapBase heapSize : Int) :
    safeHeapValidate addr heapBase heapSize = true ↔
      heapBase ≤ addr ∧ addr < heapBase + heapSize := by
  simp [safeHeapValidate]

/-- The function returns `false` exactly for addresses outside the interval. -/
theorem safeHeapValidate_eq_false_iff (addr heapBase heapSize : Int) :
    safeHeapValidate addr heapBase heapSize = false ↔
      ¬ (heapBase ≤ addr ∧ addr < heapBase + heapSize) := by
  rw [← safeHeapValidate_iff addr heapBase heapSize]
  simp

/-- The same specification written with the offset `addr - heapBase`. -/
theorem safeHeapValidate_iff_offset (addr heapBase heapSize : Int) :
    safeHeapValidate addr heapBase heapSize = true ↔
      0 ≤ addr - heapBase ∧ addr - heapBase < heapSize := by
  rw [safeHeapValidate_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩

/-! ## Soundness: what an accepted address guarantees -/

theorem safeHeapValidate_lower {addr heapBase heapSize : Int}
    (hv : safeHeapValidate addr heapBase heapSize = true) : heapBase ≤ addr :=
  ((safeHeapValidate_iff addr heapBase heapSize).mp hv).1

theorem safeHeapValidate_upper {addr heapBase heapSize : Int}
    (hv : safeHeapValidate addr heapBase heapSize = true) : addr < heapBase + heapSize :=
  ((safeHeapValidate_iff addr heapBase heapSize).mp hv).2

/-- If any address is accepted, the heap size must be positive. -/
theorem safeHeapValidate_pos_size {addr heapBase heapSize : Int}
    (hv : safeHeapValidate addr heapBase heapSize = true) : 0 < heapSize := by
  obtain ⟨h1, h2⟩ := (safeHeapValidate_iff addr heapBase heapSize).mp hv
  omega

/-! ## Rejection cases -/

/-- A zero or negative heap size rejects every address. -/
theorem safeHeapValidate_nonpos_size (addr heapBase heapSize : Int) (h : heapSize ≤ 0) :
    safeHeapValidate addr heapBase heapSize = false := by
  rw [safeHeapValidate_eq_false_iff]
  rintro ⟨h1, h2⟩
  omega

/-- Addresses below the heap base are rejected. -/
theorem safeHeapValidate_below (addr heapBase heapSize : Int) (h : addr < heapBase) :
    safeHeapValidate addr heapBase heapSize = false := by
  rw [safeHeapValidate_eq_false_iff]
  rintro ⟨h1, h2⟩
  omega

/-- Addresses at or above the heap end are rejected. -/
theorem safeHeapValidate_at_or_above (addr heapBase heapSize : Int)
    (h : heapBase + heapSize ≤ addr) :
    safeHeapValidate addr heapBase heapSize = false := by
  rw [safeHeapValidate_eq_false_iff]
  rintro ⟨h1, h2⟩
  omega

/-- The address one past the end is rejected, because the upper bound is exclusive. -/
theorem safeHeapValidate_end (heapBase heapSize : Int) :
    safeHeapValidate (heapBase + heapSize) heapBase heapSize = false :=
  safeHeapValidate_at_or_above _ _ _ (by omega)

/-! ## Boundary acceptance -/

/-- The heap base is accepted exactly when the heap size is positive. -/
theorem safeHeapValidate_base_iff (heapBase heapSize : Int) :
    safeHeapValidate heapBase heapBase heapSize = true ↔ 0 < heapSize := by
  rw [safeHeapValidate_iff]
  constructor
  · rintro ⟨_, h⟩; omega
  · intro h; exact ⟨by omega, by omega⟩

/-- For a positive size, the last address `heapBase + heapSize - 1` is accepted. -/
theorem safeHeapValidate_last (heapBase heapSize : Int) (h : 0 < heapSize) :
    safeHeapValidate (heapBase + heapSize - 1) heapBase heapSize = true :=
  (safeHeapValidate_iff _ _ _).mpr ⟨by omega, by omega⟩

/-- A natural-number offset from the base is accepted exactly when it is below the size. -/
theorem safeHeapValidate_offset_nat (heapBase heapSize : Int) (off : Nat) :
    safeHeapValidate (heapBase + off) heapBase heapSize = true ↔ (off : Int) < heapSize := by
  rw [safeHeapValidate_iff]
  constructor
  · rintro ⟨_, h⟩; omega
  · intro h; exact ⟨by omega, by omega⟩

/-! ## Structural properties -/

/-- Growing the heap never rejects an address that was accepted before. -/
theorem safeHeapValidate_mono_size {addr heapBase heapSize heapSize' : Int}
    (hs : heapSize ≤ heapSize')
    (hv : safeHeapValidate addr heapBase heapSize = true) :
    safeHeapValidate addr heapBase heapSize' = true := by
  obtain ⟨h1, h2⟩ := (safeHeapValidate_iff addr heapBase heapSize).mp hv
  exact (safeHeapValidate_iff addr heapBase heapSize').mpr ⟨h1, by omega⟩

/-- Shifting the address and the base by the same amount does not change the result. -/
theorem safeHeapValidate_shift (addr heapBase heapSize k : Int) :
    safeHeapValidate (addr + k) (heapBase + k) heapSize =
      safeHeapValidate addr heapBase heapSize := by
  have h : safeHeapValidate (addr + k) (heapBase + k) heapSize = true ↔
      safeHeapValidate addr heapBase heapSize = true := by
    rw [safeHeapValidate_iff, safeHeapValidate_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
  cases h1 : safeHeapValidate (addr + k) (heapBase + k) heapSize <;>
    cases h2 : safeHeapValidate addr heapBase heapSize <;> simp_all

/-! **TLDR-end:** [heap-validate: Lean translation] `safeHeapValidate` matches the Python
chained comparison on `Int`. The five `check()` cases, the interval specification, rejection
of nonpositive sizes and out-of-range addresses, boundary, monotonicity and shift theorems are
all proved here, using core Lean 4 only. Lean was not available in this session, so this file
has not been compiled. -/
