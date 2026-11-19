import Mathlib
namespace Agent

/-!
# Unsafe heap-write permission

Translation of the Python `unsafe_heap_write` and its three checks. Python's
arbitrary-precision integers are modeled by `Int`, without a nonnegativity
restriction. The function always returns `true`: in particular, it permits
writes larger than the chunk and positive writes to a zero-sized chunk.

This models the permission decision, not an actual memory write. No safety
check is added to repair the vulnerability described in MIT 6.858 Lecture 4.
The functional and mutable-state implementations have identical behavior.
-/

namespace UnsafeHeapOverflow

/-! ## Functional implementation -/

/-- The two sizes are deliberately ignored, exactly as in the Python source. -/
def unsafe_heap_write (_chunk_size _write_size : Int) : Bool :=
  true

/-! ## Unit tests and the Python check routine -/

example : unsafe_heap_write 64 32 = true := by native_decide
example : unsafe_heap_write 64 128 = true := by native_decide
example : unsafe_heap_write 0 1 = true := by native_decide
example : unsafe_heap_write 0 0 = true := by native_decide
example : unsafe_heap_write (-64) 128 = true := by native_decide
example : unsafe_heap_write 64 (-32) = true := by native_decide
example : unsafe_heap_write (-64) (-32) = true := by native_decide

/-- Executable counterpart of the Python assertions and success message. -/
def check : IO Unit := do
  unless unsafe_heap_write 64 32 == true do
    throw (IO.userError "normal case failed")
  unless unsafe_heap_write 64 128 == true do
    throw (IO.userError "vuln: oversized write accepted")
  unless unsafe_heap_write 0 1 == true do
    throw (IO.userError "vuln: zero chunk write accepted")
  IO.println "All tests passed."

#eval check
#eval (unsafe_heap_write 64 32, unsafe_heap_write 64 128, unsafe_heap_write 0 1)

/-! ## Preconditions -/

/-- Every pair of integers is admissible; the Python function validates nothing. -/
def Pre (_chunk_size _write_size : Int) : Prop := True

/-! ## Behavioral properties and kernel-checked proofs -/

/-- Every request is accepted, regardless of the integer inputs. -/
def always_accepts_prop (chunk_size write_size : Int) : Prop :=
  unsafe_heap_write chunk_size write_size = true

theorem always_accepts_thm (chunk_size write_size : Int) :
    always_accepts_prop chunk_size write_size := by
  rfl

/-- A write no larger than the chunk is accepted, too. -/
def fitting_write_prop (chunk_size write_size : Int) : Prop :=
  write_size ≤ chunk_size → unsafe_heap_write chunk_size write_size = true

theorem fitting_write_thm (chunk_size write_size : Int) :
    fitting_write_prop chunk_size write_size := by
  intro _
  rfl

/-- The vulnerability: exceeding the chunk size does not cause rejection. -/
def overflow_accepted_prop (chunk_size write_size : Int) : Prop :=
  chunk_size < write_size → unsafe_heap_write chunk_size write_size = true

theorem overflow_accepted_thm (chunk_size write_size : Int) :
    overflow_accepted_prop chunk_size write_size := by
  intro _
  rfl

/-- Even a zero-sized chunk accepts any write, including every positive write. -/
def zero_chunk_prop (write_size : Int) : Prop :=
  unsafe_heap_write 0 write_size = true

theorem zero_chunk_thm (write_size : Int) : zero_chunk_prop write_size := by
  rfl

/-- Changing either or both input sizes never changes the returned Boolean. -/
def size_independent_prop (chunk_size write_size other_chunk other_write : Int) : Prop :=
  unsafe_heap_write chunk_size write_size = unsafe_heap_write other_chunk other_write

theorem size_independent_thm (chunk_size write_size other_chunk other_write : Int) :
    size_independent_prop chunk_size write_size other_chunk other_write := by
  rfl

/-! ## Postcondition -/

/-- The complete observable behavior, including the unchecked overflow cases. -/
def Post_prop (chunk_size write_size : Int) : Prop :=
  always_accepts_prop chunk_size write_size ∧
  fitting_write_prop chunk_size write_size ∧
  overflow_accepted_prop chunk_size write_size ∧
  zero_chunk_prop write_size ∧
  (∀ other_chunk other_write : Int,
    size_independent_prop chunk_size write_size other_chunk other_write)

/-! ## Property-based tests

These are executable checks of the properties, separate from their proofs.
The randomized tests use their expanded, decidable forms. Implications are
converted to Booleans so a false antecedent does not discard a sample. In the
postcondition check, the comparison sizes are also universally sampled, corresponding to the
last conjunct of `Post_prop`.
-/

-- PBT for always_accepts_prop.
#eval Plausible.Testable.check (∀ chunk_size write_size : Int,
  unsafe_heap_write chunk_size write_size = true)

-- PBT for fitting_write_prop.
#eval Plausible.Testable.check (∀ chunk_size write_size : Int,
  decide (write_size ≤ chunk_size → unsafe_heap_write chunk_size write_size = true) = true)

-- PBT for overflow_accepted_prop.
#eval Plausible.Testable.check (∀ chunk_size write_size : Int,
  decide (chunk_size < write_size → unsafe_heap_write chunk_size write_size = true) = true)

-- PBT for zero_chunk_prop.
#eval Plausible.Testable.check (∀ write_size : Int,
  unsafe_heap_write 0 write_size = true)

-- PBT for size_independent_prop.
#eval Plausible.Testable.check (∀ chunk_size write_size other_chunk other_write : Int,
  unsafe_heap_write chunk_size write_size = unsafe_heap_write other_chunk other_write)

-- PBT for Post_prop, including every conjunct and all four integer inputs.
#eval Plausible.Testable.check (∀ chunk_size write_size other_chunk other_write : Int,
  (unsafe_heap_write chunk_size write_size &&
    decide (write_size ≤ chunk_size → unsafe_heap_write chunk_size write_size = true) &&
    decide (chunk_size < write_size → unsafe_heap_write chunk_size write_size = true) &&
    unsafe_heap_write 0 write_size &&
    (unsafe_heap_write chunk_size write_size ==
      unsafe_heap_write other_chunk other_write)) = true)

/-- Signed small cases, together with the sizes from the original checks. -/
private def testSizes : List Int :=
  (List.range 33).map (fun n => (n : Int) - 16) ++ [-128, -64, 32, 64, 128]

-- Bounded PBT for the full postcondition. All four sizes range independently;
-- the implication tests cover both fitting and overflowing pairs without filtering.
example : (testSizes.all (fun chunk_size =>
    testSizes.all (fun write_size =>
      decide (unsafe_heap_write chunk_size write_size = true ∧
        (write_size ≤ chunk_size → unsafe_heap_write chunk_size write_size = true) ∧
        (chunk_size < write_size → unsafe_heap_write chunk_size write_size = true) ∧
        unsafe_heap_write 0 write_size = true) &&
      testSizes.all (fun other_chunk =>
        testSizes.all (fun other_write =>
          unsafe_heap_write chunk_size write_size ==
            unsafe_heap_write other_chunk other_write))))) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (chunk_size write_size : Int) :
    Pre chunk_size write_size → Post_prop chunk_size write_size := by
  intro _
  exact ⟨always_accepts_thm chunk_size write_size,
    fitting_write_thm chunk_size write_size,
    overflow_accepted_thm chunk_size write_size,
    zero_chunk_thm write_size,
    fun other_chunk other_write =>
      size_independent_thm chunk_size write_size other_chunk other_write⟩

/-! ## Imperative implementation -/

/-- Mutable-state version: permission is set to true without inspecting either size. -/
def unsafe_heap_write_imperative (_chunk_size _write_size : Int) : Bool := Id.run do
  let mut permitted := false
  permitted := true
  return permitted

/-! ## Imperative tests -/

example : unsafe_heap_write_imperative 64 32 = true := by native_decide
example : unsafe_heap_write_imperative 64 128 = true := by native_decide
example : unsafe_heap_write_imperative 0 1 = true := by native_decide
example : unsafe_heap_write_imperative 0 0 = true := by native_decide
example : unsafe_heap_write_imperative (-64) 128 = true := by native_decide
example : unsafe_heap_write_imperative 64 (-32) = true := by native_decide
example : unsafe_heap_write_imperative (-64) (-32) = true := by native_decide

#eval (unsafe_heap_write_imperative 64 32,
  unsafe_heap_write_imperative 64 128, unsafe_heap_write_imperative 0 1)

/-! ## Functional-imperative equivalence -/

theorem functional_imperative_equiv_thm (chunk_size write_size : Int) :
    unsafe_heap_write chunk_size write_size =
      unsafe_heap_write_imperative chunk_size write_size := by
  rfl

end UnsafeHeapOverflow
end Agent
