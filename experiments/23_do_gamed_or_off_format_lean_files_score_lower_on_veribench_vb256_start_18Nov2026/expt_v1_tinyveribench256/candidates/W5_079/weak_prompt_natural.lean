/-
  Unsafe WEP keystream-reuse check: accepts packets without detecting IV reuse.

  Lean 4 translation of the Python `unsafe_wep_check` / `check` program.
  MIT 6.858 Quiz 2, Fall 2013: Wireless / WEP keystream reuse.

  Python `int` is modelled as Lean `Int`; Python `bool` as Lean `Bool`.
-/

namespace UnsafeWep

/-- Approve the request without checking whether `iv1` and `iv2` are equal.

    MIT 6.858 Quiz 2, Fall 2013: Wireless / WEP keystream reuse. -/
def unsafeWepCheck (_iv1 _iv2 : Int) : Bool :=
  true

/-- Reference check that rejects reuse: it approves only when the IVs differ.
    The Python program does not have this function. It is here only to compare against. -/
def safeWepCheck (iv1 iv2 : Int) : Bool :=
  iv1 != iv2

/-- Run the fixed examples from the Python `check` function.
    The Python `assert`s become one boolean conjunction. -/
def check : Bool :=
  unsafeWepCheck 5 5 == true &&
  unsafeWepCheck 1 2 == true &&
  unsafeWepCheck 0 0 == true &&
  unsafeWepCheck 0 5 == true &&
  unsafeWepCheck 5 1 == true

/-! ## The fixed examples, each one checked by the kernel -/

example : unsafeWepCheck 5 5 = true := rfl
example : unsafeWepCheck 1 2 = true := rfl
example : unsafeWepCheck 0 0 = true := rfl
example : unsafeWepCheck 0 5 = true := rfl
example : unsafeWepCheck 5 1 = true := rfl

/-- The Python `check()` passes. -/
theorem check_passes : check = true := rfl

/-! ## Theorems about `unsafeWepCheck` -/

/-- The check approves every pair of IVs. -/
theorem unsafeWepCheck_always_true (iv1 iv2 : Int) :
    unsafeWepCheck iv1 iv2 = true := rfl

/-- IV reuse is always accepted: approval is given even when both IVs are equal. -/
theorem unsafeWepCheck_accepts_reuse (iv : Int) :
    unsafeWepCheck iv iv = true := rfl

/-- The result is the same for any two pairs of IVs, so it carries no
    information about whether reuse happened. -/
theorem unsafeWepCheck_constant (a b c d : Int) :
    unsafeWepCheck a b = unsafeWepCheck c d := rfl

/-- The order of the IVs does not matter. -/
theorem unsafeWepCheck_symm (a b : Int) :
    unsafeWepCheck a b = unsafeWepCheck b a := rfl

/-- The result is the same whether or not the IVs are equal. -/
theorem unsafeWepCheck_ignores_equality (a b : Int) :
    unsafeWepCheck a b = true ↔ (a = b ∨ a ≠ b) := by
  constructor
  · intro _
    exact Classical.em (a = b)
  · intro _
    rfl

/-- There is a pair of reused IVs that the check approves. -/
theorem exists_accepted_reuse :
    ∃ iv1 iv2 : Int, iv1 = iv2 ∧ unsafeWepCheck iv1 iv2 = true :=
  ⟨5, 5, rfl, rfl⟩

/-- The check does not detect reuse: approval does not mean the IVs differ. -/
theorem unsafeWepCheck_not_sound :
    ¬ (∀ iv1 iv2 : Int, unsafeWepCheck iv1 iv2 = true → iv1 ≠ iv2) := by
  intro h
  exact h 0 0 rfl rfl

/-! ## Comparison with the reference check -/

/-- The reference check approves exactly the pairs whose IVs differ. -/
theorem safeWepCheck_spec (iv1 iv2 : Int) :
    safeWepCheck iv1 iv2 = true ↔ iv1 ≠ iv2 := by
  simp [safeWepCheck]

/-- The reference check rejects a reused IV. -/
theorem safeWepCheck_rejects_reuse_example : safeWepCheck 5 5 = false := by
  decide

/-- The unsafe check and the reference check disagree on a reused IV. -/
theorem unsafe_differs_from_safe :
    ∃ iv : Int, unsafeWepCheck iv iv ≠ safeWepCheck iv iv :=
  ⟨5, by decide⟩

/-- The two checks agree on every pair of distinct IVs. -/
theorem unsafe_agrees_with_safe_on_distinct (iv1 iv2 : Int) (h : iv1 ≠ iv2) :
    unsafeWepCheck iv1 iv2 = safeWepCheck iv1 iv2 := by
  rw [unsafeWepCheck_always_true]
  exact ((safeWepCheck_spec iv1 iv2).mpr h).symm

end UnsafeWep

/-- Counterpart of `if __name__ == "__main__": check()`.
    A failed check raises an error, like Python's `AssertionError`. -/
def main : IO Unit := do
  unless UnsafeWep.check do
    throw (IO.userError "AssertionError: check failed")

-- TLDR-end: [wep-lean: translate] I translated the function and its fixed examples to Lean 4 and
-- proved that it approves every IV pair, including reused IVs, so it cannot detect keystream reuse.
-- I could not compile the file here because no Lean toolchain was available in this session.
