/-!
# Safe executable stack (NX bit model)

Safe executable stack: NX bit enforced — stack region addresses are not executable.
`safeExecStack` returns `true` only when `addr` is NOT in the stack region
`[stackStart, stackEnd)`.

Teaching model for MIT 6.858. This integer interval model does not inspect memory
permissions or enforce execution protection.
-/

namespace SafeExecStack

/-- Return `false` when `stackStart ≤ addr < stackEnd`, otherwise `true`.
Empty or reversed intervals return `true` for every address. -/
def safeExecStack (addr stackStart stackEnd : Int) : Bool :=
  if stackStart ≤ addr ∧ addr < stackEnd then false else true

/-- Run the fixed examples and return `true` when all checks pass.
(The Python version raises `AssertionError` on a mismatch; here a mismatch yields `false`.) -/
def check (candidate : Int → Int → Int → Bool) : Bool :=
  candidate 134512640 2147418112 2147483647 == true &&
  candidate 2147422772 2147418112 2147483647 == false &&
  candidate 2147418112 2147418112 2147483647 == false &&
  candidate 2147483647 2147418112 2147483647 == true &&
  candidate 2147418111 2147418112 2147483647 == true

/-! ## The fixed test cases -/

theorem check_safeExecStack : check safeExecStack = true := by decide

example : safeExecStack 134512640 2147418112 2147483647 = true := by decide
example : safeExecStack 2147422772 2147418112 2147483647 = false := by decide
example : safeExecStack 2147418112 2147418112 2147483647 = false := by decide
example : safeExecStack 2147483647 2147418112 2147483647 = true := by decide
example : safeExecStack 2147418111 2147418112 2147483647 = true := by decide

/-! ## Specification -/

/-- An address is non-executable exactly when it lies in `[s, e)`. -/
theorem safeExecStack_eq_false_iff (addr s e : Int) :
    safeExecStack addr s e = false ↔ (s ≤ addr ∧ addr < e) := by
  unfold safeExecStack
  by_cases h : s ≤ addr ∧ addr < e
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]
    exact ⟨fun h' => by cases h', fun h' => absurd h' h⟩

/-- An address is executable exactly when it does not lie in `[s, e)`. -/
theorem safeExecStack_eq_true_iff (addr s e : Int) :
    safeExecStack addr s e = true ↔ ¬(s ≤ addr ∧ addr < e) := by
  unfold safeExecStack
  by_cases h : s ≤ addr ∧ addr < e
  · rw [if_pos h]
    exact ⟨fun h' => by cases h', fun h' => absurd h h'⟩
  · rw [if_neg h]
    exact ⟨fun _ => h, fun _ => rfl⟩

/-- The definition agrees with the Python expression `not (s <= addr < e)`. -/
theorem safeExecStack_eq_not_decide (addr s e : Int) :
    safeExecStack addr s e = !decide (s ≤ addr ∧ addr < e) := by
  unfold safeExecStack
  by_cases h : s ≤ addr ∧ addr < e
  · have hd : decide (s ≤ addr ∧ addr < e) = true := decide_eq_true h
    rw [if_pos h, hd]
    all_goals rfl
  · have hd : decide (s ≤ addr ∧ addr < e) = false := decide_eq_false h
    rw [if_neg h, hd]
    all_goals rfl

/-- Executable exactly when the address is below the stack or at/above its end. -/
theorem safeExecStack_eq_true_iff_outside (addr s e : Int) :
    safeExecStack addr s e = true ↔ (addr < s ∨ e ≤ addr) := by
  rw [safeExecStack_eq_true_iff]
  constructor
  · intro h
    by_cases h1 : s ≤ addr
    · have h2 : ¬ addr < e := fun h2 => h ⟨h1, h2⟩
      exact Or.inr (by omega)
    · exact Or.inl (by omega)
  · intro h ⟨h1, h2⟩
    cases h with
    | inl h3 => omega
    | inr h3 => omega

/-! ## Region facts -/

theorem safeExecStack_below {addr s e : Int} (h : addr < s) :
    safeExecStack addr s e = true := by
  rw [safeExecStack_eq_true_iff]
  intro ⟨h1, h2⟩
  omega

theorem safeExecStack_above {addr s e : Int} (h : e ≤ addr) :
    safeExecStack addr s e = true := by
  rw [safeExecStack_eq_true_iff]
  intro ⟨h1, h2⟩
  omega

theorem safeExecStack_inside {addr s e : Int} (h1 : s ≤ addr) (h2 : addr < e) :
    safeExecStack addr s e = false :=
  (safeExecStack_eq_false_iff addr s e).mpr ⟨h1, h2⟩

/-- The lower bound is inclusive: `stackStart` itself is non-executable (if the stack is nonempty). -/
theorem safeExecStack_start {s e : Int} (h : s < e) :
    safeExecStack s s e = false :=
  safeExecStack_inside (by omega) h

/-- The upper bound is exclusive: `stackEnd` itself is executable. -/
theorem safeExecStack_end (s e : Int) :
    safeExecStack e s e = true :=
  safeExecStack_above (by omega)

/-- Empty or reversed intervals make every address executable. -/
theorem safeExecStack_empty {s e : Int} (h : e ≤ s) (addr : Int) :
    safeExecStack addr s e = true := by
  rw [safeExecStack_eq_true_iff]
  intro ⟨h1, h2⟩
  omega

/-- Some address is non-executable exactly when the stack interval is nonempty. -/
theorem exists_nonexec_iff (s e : Int) :
    (∃ addr, safeExecStack addr s e = false) ↔ s < e := by
  constructor
  · intro ⟨addr, h⟩
    rw [safeExecStack_eq_false_iff] at h
    obtain ⟨h1, h2⟩ := h
    omega
  · intro h
    exact ⟨s, safeExecStack_start h⟩

/-- The model never makes all of memory non-executable. -/
theorem exists_exec (s e : Int) : ∃ addr, safeExecStack addr s e = true :=
  ⟨e, safeExecStack_end s e⟩

/-- Enlarging the stack region can only remove executability. -/
theorem safeExecStack_false_of_subregion {addr s e s' e' : Int}
    (hs : s ≤ s') (he : e' ≤ e) (h : safeExecStack addr s' e' = false) :
    safeExecStack addr s e = false := by
  rw [safeExecStack_eq_false_iff] at h ⊢
  obtain ⟨h1, h2⟩ := h
  exact ⟨by omega, by omega⟩

/-- Translating the address and the stack by the same offset does not change the answer. -/
theorem safeExecStack_shift (addr s e k : Int) :
    safeExecStack (addr + k) (s + k) (e + k) = safeExecStack addr s e := by
  cases h : safeExecStack addr s e with
  | false =>
    rw [safeExecStack_eq_false_iff] at h ⊢
    obtain ⟨h1, h2⟩ := h
    exact ⟨by omega, by omega⟩
  | true =>
    rw [safeExecStack_eq_true_iff] at h ⊢
    intro ⟨h1, h2⟩
    exact h ⟨by omega, by omega⟩

/-! ## The test cases as instances of the general theorems -/

example : safeExecStack 2147418112 2147418112 2147483647 = false :=
  safeExecStack_start (by decide)

example : safeExecStack 2147483647 2147418112 2147483647 = true :=
  safeExecStack_end _ _

example : safeExecStack 2147418111 2147418112 2147483647 = true :=
  safeExecStack_below (by decide)

end SafeExecStack

open SafeExecStack in
def main : IO Unit := do
  if check safeExecStack then
    IO.println "All tests passed."
  else
    throw <| IO.userError "Failed: safeExecStack"
