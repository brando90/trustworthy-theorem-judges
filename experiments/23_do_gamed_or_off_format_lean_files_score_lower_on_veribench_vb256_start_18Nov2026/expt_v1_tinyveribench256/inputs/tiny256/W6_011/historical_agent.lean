import Mathlib
namespace Agent

/-!
# Unsafe seccomp filter

Translation of the MIT 6.858 Lecture 6 example in which a seccomp-bpf filter
is never applied. The function accepts a syscall identifier and an allowlist,
but returns `true` without consulting either argument. In particular, an
unlisted syscall remains permitted, even when the allowlist is empty.

`Int` models Python's arbitrary-precision integers, including negative values;
`List Int` permits arbitrary finite lists, including duplicates. There are no
input restrictions. The `check` function is a pure Boolean rendering of the
five Python assertions. These specifications describe the vulnerability, not
the behavior of a repaired filter or a model of an actual isolation escape.
-/

namespace UnsafeSeccompFilter

/-! ## Functional implementation -/

/-- The filter is never applied: every system call is permitted. -/
def unsafe_seccomp_filter (_syscall_id : Int) (_allowed : List Int) : Bool :=
  true

/-- All five Python assertions must succeed for this Boolean harness to pass. -/
def check (candidate : Int → List Int → Bool) : Bool :=
  let allowed : List Int := [1, 2, 3, 60]
  candidate 1 allowed &&
    candidate 999 allowed &&
    candidate 1 [] &&
    candidate 0 [] &&
    candidate 0x1000 allowed

/-! ## Unit tests -/

example : unsafe_seccomp_filter 1 [1, 2, 3, 60] = true := by native_decide
example : unsafe_seccomp_filter 999 [1, 2, 3, 60] = true := by native_decide
example : unsafe_seccomp_filter 1 [] = true := by native_decide
example : unsafe_seccomp_filter 0 [] = true := by native_decide
example : unsafe_seccomp_filter 0x1000 [1, 2, 3, 60] = true := by native_decide
example : unsafe_seccomp_filter (-999) [-1, -1, 0] = true := by native_decide
example : check unsafe_seccomp_filter = true := by native_decide

#eval unsafe_seccomp_filter 999 [1, 2, 3, 60]
#eval check unsafe_seccomp_filter
#eval if check unsafe_seccomp_filter then "All tests passed." else "Candidate failed seccomp filter tests"

/-! ## Precondition -/

/-- Every integer and every finite integer list is admissible. -/
def Pre (_syscall_id : Int) (_allowed : List Int) : Prop := True

/-! ## Properties and kernel-checked proofs -/

/-- The complete return-value semantics, independently of allowlist membership. -/
def unconditional_allow_prop (syscall_id : Int) (allowed : List Int) : Prop :=
  unsafe_seccomp_filter syscall_id allowed = true

theorem unconditional_allow_thm (syscall_id : Int) (allowed : List Int) :
    unconditional_allow_prop syscall_id allowed := by
  rfl

/-- Listed calls are permitted, although the implementation never checks membership. -/
def listed_allowed_prop (syscall_id : Int) (allowed : List Int) : Prop :=
  syscall_id ∈ allowed → unsafe_seccomp_filter syscall_id allowed = true

theorem listed_allowed_thm (syscall_id : Int) (allowed : List Int) :
    listed_allowed_prop syscall_id allowed := by
  intro _
  rfl

/-- The vulnerability: calls absent from the allowlist are also permitted. -/
def unlisted_allowed_prop (syscall_id : Int) (allowed : List Int) : Prop :=
  syscall_id ∉ allowed → unsafe_seccomp_filter syscall_id allowed = true

theorem unlisted_allowed_thm (syscall_id : Int) (allowed : List Int) :
    unlisted_allowed_prop syscall_id allowed := by
  intro _
  rfl

/-- An empty allowlist denies nothing. -/
def empty_filter_prop (syscall_id : Int) : Prop :=
  unsafe_seccomp_filter syscall_id [] = true

theorem empty_filter_thm (syscall_id : Int) : empty_filter_prop syscall_id := by
  rfl

/-- Replacing the entire allowlist cannot change the decision. -/
def filter_ignored_prop (syscall_id : Int) (allowed other : List Int) : Prop :=
  unsafe_seccomp_filter syscall_id allowed = unsafe_seccomp_filter syscall_id other

theorem filter_ignored_thm (syscall_id : Int) (allowed other : List Int) :
    filter_ignored_prop syscall_id allowed other := by
  rfl

/-- Replacing the syscall identifier cannot change the decision either. -/
def syscall_ignored_prop (syscall_id other_id : Int) (allowed : List Int) : Prop :=
  unsafe_seccomp_filter syscall_id allowed = unsafe_seccomp_filter other_id allowed

theorem syscall_ignored_thm (syscall_id other_id : Int) (allowed : List Int) :
    syscall_ignored_prop syscall_id other_id allowed := by
  rfl

/-- The source program's final assertion is valid. -/
theorem check_thm : check unsafe_seccomp_filter = true := by
  rfl

/-! ## Postcondition -/

/-- The conjunction records both unconditional permission and argument independence. -/
def Post_prop (syscall_id : Int) (allowed : List Int) : Prop :=
  unconditional_allow_prop syscall_id allowed ∧
  listed_allowed_prop syscall_id allowed ∧
  unlisted_allowed_prop syscall_id allowed ∧
  empty_filter_prop syscall_id ∧
  (∀ other : List Int, filter_ignored_prop syscall_id allowed other) ∧
  (∀ other_id : Int, syscall_ignored_prop syscall_id other_id allowed)

/-! ## Property-based tests

Randomized checks and bounded Boolean checks are evidence only; none is used
in a named theorem. The bounded inputs include negative and positive IDs,
empty lists, singleton lists, duplicates, and the source program's IDs.
Membership implications are checked as decidable Booleans, rather than by
rejecting random samples that fail a membership precondition.
-/

-- Randomized PBT: unconditional_allow_prop.
#eval Plausible.Testable.check (∀ (syscall_id : Int) (allowed : List Int),
  unsafe_seccomp_filter syscall_id allowed = true)

-- Randomized PBT: empty_filter_prop.
#eval Plausible.Testable.check (∀ syscall_id : Int,
  unsafe_seccomp_filter syscall_id [] = true)

-- Randomized PBT: filter_ignored_prop.
#eval Plausible.Testable.check (∀ (syscall_id : Int) (allowed other : List Int),
  unsafe_seccomp_filter syscall_id allowed = unsafe_seccomp_filter syscall_id other)

-- Randomized PBT: syscall_ignored_prop.
#eval Plausible.Testable.check (∀ (syscall_id other_id : Int) (allowed : List Int),
  unsafe_seccomp_filter syscall_id allowed = unsafe_seccomp_filter other_id allowed)

/-- A bounded domain with both signs and large, nonstandard syscall identifiers. -/
def testSyscalls : List Int :=
  (List.range 65).map (fun n => (n : Int) - 32) ++
    [60, 999, 0x1000, -999, -0x1000, 100000000000000000000]

/-- Lists exercise both membership cases, duplicates, and changes of order. -/
def testFilters : List (List Int) :=
  [[], [1, 2, 3, 60], [60, 3, 2, 1], [-1, 0, 1], [999, 0x1000]] ++
    testSyscalls.map (fun n => [n]) ++
    testSyscalls.map (fun n => [n, n]) ++
    testSyscalls.map (fun n => [n - 1, n, n + 1])

-- Bounded PBT: unconditional_allow_prop.
example : (testSyscalls.all fun syscall_id =>
    testFilters.all fun allowed =>
      decide (unsafe_seccomp_filter syscall_id allowed = true)) = true := by
  native_decide

-- Bounded PBT: listed_allowed_prop. Every ID has a corresponding singleton list.
example : (testSyscalls.all fun syscall_id =>
    testFilters.all fun allowed =>
      decide (syscall_id ∈ allowed → unsafe_seccomp_filter syscall_id allowed = true)) = true := by
  native_decide

-- Bounded PBT: unlisted_allowed_prop. Empty lists exercise this nonvacuously.
example : (testSyscalls.all fun syscall_id =>
    testFilters.all fun allowed =>
      decide (syscall_id ∉ allowed → unsafe_seccomp_filter syscall_id allowed = true)) = true := by
  native_decide

-- Bounded PBT: empty_filter_prop.
example : (testSyscalls.all fun syscall_id =>
    decide (unsafe_seccomp_filter syscall_id [] = true)) = true := by
  native_decide

-- Bounded PBT: filter_ignored_prop, varying both lists independently.
example : (testSyscalls.all fun syscall_id =>
    testFilters.all fun allowed =>
      testFilters.all fun other =>
        decide (unsafe_seccomp_filter syscall_id allowed =
          unsafe_seccomp_filter syscall_id other)) = true := by
  native_decide

-- Bounded PBT: syscall_ignored_prop, varying both IDs independently.
example : (testSyscalls.all fun syscall_id =>
    testSyscalls.all fun other_id =>
      testFilters.all fun allowed =>
        decide (unsafe_seccomp_filter syscall_id allowed =
          unsafe_seccomp_filter other_id allowed)) = true := by
  native_decide

/-- Bounded executable form of every conjunct of Post_prop.
Its two universal conjuncts are tested over the corresponding bounded domains. -/
def postconditionPBT : Bool :=
  testSyscalls.all fun syscall_id =>
    testFilters.all fun allowed =>
      decide (unsafe_seccomp_filter syscall_id allowed = true) &&
      decide (syscall_id ∈ allowed → unsafe_seccomp_filter syscall_id allowed = true) &&
      decide (syscall_id ∉ allowed → unsafe_seccomp_filter syscall_id allowed = true) &&
      decide (unsafe_seccomp_filter syscall_id [] = true) &&
      (testFilters.all fun other =>
        decide (unsafe_seccomp_filter syscall_id allowed =
          unsafe_seccomp_filter syscall_id other)) &&
      (testSyscalls.all fun other_id =>
        decide (unsafe_seccomp_filter syscall_id allowed =
          unsafe_seccomp_filter other_id allowed))

-- Bounded PBT: Post_prop (Pre is true for every tested input).
example : postconditionPBT = true := by native_decide
#eval postconditionPBT

/-! ## Correctness -/

/-- All admissible inputs satisfy the complete specification of the unsafe behavior. -/
theorem correctness_thm (syscall_id : Int) (allowed : List Int) :
    Pre syscall_id allowed → Post_prop syscall_id allowed := by
  intro _
  exact ⟨unconditional_allow_thm syscall_id allowed,
    listed_allowed_thm syscall_id allowed,
    unlisted_allowed_thm syscall_id allowed,
    empty_filter_thm syscall_id,
    fun other => filter_ignored_thm syscall_id allowed other,
    fun other_id => syscall_ignored_thm syscall_id other_id allowed⟩

/-! ## Imperative implementation -/

/-- Mutable-state version: the decision is unconditionally set to permitted. -/
def unsafe_seccomp_filter_imperative (_syscall_id : Int) (_allowed : List Int) : Bool :=
  Id.run do
    let mut permitted := false
    permitted := true
    return permitted

/-! ## Imperative tests -/

example : unsafe_seccomp_filter_imperative 1 [1, 2, 3, 60] = true := by native_decide
example : unsafe_seccomp_filter_imperative 999 [1, 2, 3, 60] = true := by native_decide
example : unsafe_seccomp_filter_imperative 1 [] = true := by native_decide
example : unsafe_seccomp_filter_imperative 0 [] = true := by native_decide
example : unsafe_seccomp_filter_imperative 0x1000 [1, 2, 3, 60] = true := by native_decide
example : check unsafe_seccomp_filter_imperative = true := by native_decide

#eval check unsafe_seccomp_filter_imperative
#eval if check unsafe_seccomp_filter_imperative then "All tests passed." else "Candidate failed seccomp filter tests"

-- Bounded regression check of agreement between the implementations.
example : (testSyscalls.all fun syscall_id =>
    testFilters.all fun allowed =>
      decide (unsafe_seccomp_filter syscall_id allowed =
        unsafe_seccomp_filter_imperative syscall_id allowed)) = true := by
  native_decide

/-! ## Functional-imperative equivalence -/

/-- Pointwise equivalence holds on the entire input domain, not merely the test cases. -/
theorem functional_imperative_equiv_thm (syscall_id : Int) (allowed : List Int) :
    unsafe_seccomp_filter syscall_id allowed =
      unsafe_seccomp_filter_imperative syscall_id allowed := by
  rfl

end UnsafeSeccompFilter
end Agent
