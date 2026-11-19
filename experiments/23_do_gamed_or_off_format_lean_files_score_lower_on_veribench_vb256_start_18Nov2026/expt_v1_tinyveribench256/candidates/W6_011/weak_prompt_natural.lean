/-!
# Unsafe seccomp filter (teaching model for MIT 6.858)

Lean 4 translation of a Python teaching model. The filter decides whether a
system call is permitted, but it never looks at the filter.

The `allowed` list is a parameter that the function never reads. Every system
call is allowed, so the filter gives no isolation at all.

Background (MIT 6.858, Lecture 6): Firecracker uses seccomp-bpf to restrict
which system calls the virtual machine monitor (VMM) process itself can make.
This limits the damage if the VMM is compromised.

The file contains:
* `unsafeSeccompFilter`, a direct translation of the Python function;
* `check`, a translation of the Python test harness;
* `safeSeccompFilter`, a correct reference filter;
* theorems that state and prove the vulnerability.
-/

namespace Seccomp

/-! ## Translation -/

/-- Decide whether a system call is permitted, ignoring the filter entirely.

The `allowed` list is accepted as a parameter but never consulted. Every
system call is allowed without condition (the vulnerability). -/
def unsafeSeccompFilter (_syscallId : Int) (_allowed : List Int) : Bool :=
  true  -- filter never applied: vulnerability

/-- Run the fixed examples from the Python `check`.

Python raises `AssertionError` on a mismatch. Here a mismatch makes the
result `false` instead. -/
def check (candidate : Int → List Int → Bool) : Bool :=
  candidate 1    [1, 2, 3, 60] == true &&
  candidate 999  [1, 2, 3, 60] == true &&
  candidate 1    []            == true &&
  candidate 0    []            == true &&
  candidate 4096 [1, 2, 3, 60] == true

/-- The module-level `assert check(unsafe_seccomp_filter)`, checked at compile time. -/
theorem check_unsafe : check unsafeSeccompFilter = true := by decide

/-! ## A correct reference filter -/

/-- A correct filter: permit a system call only if it is on the allowlist. -/
def safeSeccompFilter (syscallId : Int) (allowed : List Int) : Bool :=
  decide (syscallId ∈ allowed)

/-! ## Specifications -/

/-- A filter is *sound* if it permits only system calls on the allowlist. -/
def Sound (f : Int → List Int → Bool) : Prop :=
  ∀ s allowed, f s allowed = true → s ∈ allowed

/-- A filter is *complete* if it permits every system call on the allowlist. -/
def Complete (f : Int → List Int → Bool) : Prop :=
  ∀ s allowed, s ∈ allowed → f s allowed = true

/-! ## Theorems about the unsafe filter -/

/-- The unsafe filter permits every system call. -/
theorem unsafe_always_true (s : Int) (allowed : List Int) :
    unsafeSeccompFilter s allowed = true := rfl

/-- The unsafe filter is the constant `true` function. -/
theorem unsafe_eq_const : unsafeSeccompFilter = fun _ _ => true := rfl

/-- The result does not depend on the allowlist. -/
theorem unsafe_ignores_allowlist (s : Int) (a₁ a₂ : List Int) :
    unsafeSeccompFilter s a₁ = unsafeSeccompFilter s a₂ := rfl

/-- The result does not depend on the system call number. -/
theorem unsafe_ignores_syscall (s₁ s₂ : Int) (allowed : List Int) :
    unsafeSeccompFilter s₁ allowed = unsafeSeccompFilter s₂ allowed := rfl

/-- The vulnerability: a system call that is *not* on the allowlist is still permitted. -/
theorem unsafe_permits_unlisted (s : Int) (allowed : List Int) (_h : s ∉ allowed) :
    unsafeSeccompFilter s allowed = true := rfl

/-- Even an empty allowlist ("deny everything") permits every system call. -/
theorem unsafe_empty_allowlist_permits (s : Int) :
    unsafeSeccompFilter s [] = true := rfl

/-- A concrete witness from the test suite: 999 is not listed, yet it is permitted. -/
theorem unsafe_permits_999 :
    (999 : Int) ∉ ([1, 2, 3, 60] : List Int) ∧
      unsafeSeccompFilter 999 [1, 2, 3, 60] = true :=
  ⟨by decide, rfl⟩

/-- The unsafe filter is not sound. -/
theorem unsafe_not_sound : ¬ Sound unsafeSeccompFilter := by
  intro h
  have hmem : (0 : Int) ∈ ([] : List Int) := h 0 [] rfl
  simp at hmem

/-- The unsafe filter is (trivially) complete: it never blocks a legitimate call. -/
theorem unsafe_complete : Complete unsafeSeccompFilter :=
  fun _ _ _ => rfl

/-- The unsafe filter is the most permissive filter: whatever any filter
permits, it permits too. -/
theorem unsafe_most_permissive (f : Int → List Int → Bool) (s : Int)
    (allowed : List Int) :
    f s allowed = true → unsafeSeccompFilter s allowed = true :=
  fun _ => rfl

/-! ## Theorems about the safe filter -/

/-- The safe filter permits a system call exactly when it is on the allowlist. -/
theorem safe_iff (s : Int) (allowed : List Int) :
    safeSeccompFilter s allowed = true ↔ s ∈ allowed := by
  simp [safeSeccompFilter]

theorem safe_sound : Sound safeSeccompFilter := by
  intro s allowed h
  simpa [safeSeccompFilter] using h

theorem safe_complete : Complete safeSeccompFilter := by
  intro s allowed h
  simpa [safeSeccompFilter] using h

/-- With an empty allowlist the safe filter denies everything. -/
theorem safe_empty_allowlist_denies (s : Int) :
    safeSeccompFilter s [] = false := by
  simp [safeSeccompFilter]

/-- Any filter that is both sound and complete agrees with the safe filter. -/
theorem sound_complete_unique (f : Int → List Int → Bool)
    (hs : Sound f) (hc : Complete f) (s : Int) (allowed : List Int) :
    f s allowed = safeSeccompFilter s allowed := by
  by_cases hm : s ∈ allowed
  · simp [safeSeccompFilter, hm, hc s allowed hm]
  · have hf : f s allowed = false := by
      cases hfs : f s allowed with
      | false => rfl
      | true => exact absurd (hs s allowed hfs) hm
    simp [safeSeccompFilter, hm, hf]

/-! ## Comparing the two filters and the tests -/

/-- The two filters disagree on a concrete input taken from the tests. -/
theorem unsafe_ne_safe :
    ∃ s allowed, unsafeSeccompFilter s allowed ≠ safeSeccompFilter s allowed :=
  ⟨999, [1, 2, 3, 60], by decide⟩

/-- Every system call the safe filter permits, the unsafe filter also permits. -/
theorem safe_refines_unsafe (s : Int) (allowed : List Int) :
    safeSeccompFilter s allowed = true → unsafeSeccompFilter s allowed = true :=
  unsafe_most_permissive safeSeccompFilter s allowed

/-- The test suite *rejects* the correct filter: it checks for the vulnerability
instead of for isolation. -/
theorem check_rejects_safe : check safeSeccompFilter = false := by decide

/-- Any constant-`true` candidate passes the test suite. -/
theorem check_accepts_const_true : check (fun _ _ => true) = true := by decide

end Seccomp

/-- Mirrors the Python script's top-level assertion and its `print`. -/
def main : IO Unit := do
  if Seccomp.check Seccomp.unsafeSeccompFilter then
    IO.println "All tests passed."
  else
    throw <| IO.userError "Candidate failed seccomp filter tests"

-- TL;DR: The file translates the Python filter, which always returns `true`, and its
-- test harness into Lean. Its theorems prove that the filter ignores both of its
-- inputs, is complete but not sound, and is the most permissive filter possible.
-- They also prove that the tests reject the correct allowlist filter `safeSeccompFilter`.
-- The file has not been compiled.
