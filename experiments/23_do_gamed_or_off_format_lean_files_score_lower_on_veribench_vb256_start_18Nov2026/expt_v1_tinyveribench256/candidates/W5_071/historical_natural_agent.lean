import Mathlib
namespace Agent

/-!
# Unsafe clickjacking frame check

Translation of the Python `unsafe_frame_check` and its test harness. The check
returns `true` regardless of the number of frame ancestors. In particular,
positive ancestor counts are accepted: this is the clickjacking vulnerability,
not a top-level-only security policy.

Python integers are represented by `Int`. Although negative ancestor counts do
not describe actual frame trees, the Python function accepts them as well, so
there is no nonnegativity precondition. All mathematical claims below describe
the unsafe implementation without repairing it.
-/

namespace UnsafeClickjacking132

-- Functional implementation.
def unsafe_frame_check (_frame_ancestor_count : Int) : Bool :=
  true

-- The three original unit tests, plus a negative input to check the full domain.
example : unsafe_frame_check 0 = true := by native_decide
example : unsafe_frame_check 1 = true := by native_decide
example : unsafe_frame_check 5 = true := by native_decide
example : unsafe_frame_check (-7) = true := by native_decide

/-- Executable counterpart of the Python test harness. -/
def check : IO Unit := do
  unless unsafe_frame_check 0 do
    throw (IO.userError "top-level rejected")
  unless unsafe_frame_check 1 do
    throw (IO.userError "vuln: framed page accepted")
  unless unsafe_frame_check 5 do
    throw (IO.userError "vuln: deeply nested frame accepted")
  IO.println "All tests passed."

#eval check
#eval (unsafe_frame_check 0, unsafe_frame_check 1, unsafe_frame_check 5)

/-- Every integer is admissible, exactly as in the Python function. -/
def Pre (_frame_ancestor_count : Int) : Prop := True

/-- The return value is always `true`, including at the top level. -/
def always_allows_prop (frame_ancestor_count : Int) : Prop :=
  unsafe_frame_check frame_ancestor_count = true

theorem always_allows_thm (frame_ancestor_count : Int) :
    always_allows_prop frame_ancestor_count := by
  rfl

/-- A genuinely framed page is accepted, exhibiting the unsafe behavior. -/
def framed_allowed_prop (frame_ancestor_count : Int) : Prop :=
  0 < frame_ancestor_count → unsafe_frame_check frame_ancestor_count = true

theorem framed_allowed_thm (frame_ancestor_count : Int) :
    framed_allowed_prop frame_ancestor_count := by
  intro _
  rfl

/-- Changing the ancestor count never changes the decision. -/
def ignores_ancestor_count_prop (a b : Int) : Prop :=
  unsafe_frame_check a = unsafe_frame_check b

theorem ignores_ancestor_count_thm (a b : Int) :
    ignores_ancestor_count_prop a b := by
  rfl

/-- The postcondition combines unconditional acceptance, the vulnerability,
and independence from every other possible ancestor count. -/
def Post_prop (frame_ancestor_count : Int) : Prop :=
  always_allows_prop frame_ancestor_count ∧
  framed_allowed_prop frame_ancestor_count ∧
  ∀ other : Int, ignores_ancestor_count_prop frame_ancestor_count other

-- Property-based tests. These check executable forms, not the proofs above.
-- The bounded sample includes all integers from -30 through 30.
def testCounts : List Int :=
  (List.range 61).map (fun n => (n : Int) - 30)

-- PBT for always_allows_prop.
#eval Plausible.Testable.check
  (∀ n : Int, unsafe_frame_check n = true)

example : testCounts.all (fun n => unsafe_frame_check n == true) = true := by
  native_decide

-- PBT for framed_allowed_prop, using Boolean implication to avoid discarded
-- random inputs. The bounded test explicitly includes positive counts and 0.
#eval Plausible.Testable.check
  (∀ n : Int,
    (!(decide (0 < n)) || (unsafe_frame_check n == true)) = true)

example : testCounts.all
    (fun n => !(decide (0 < n)) || (unsafe_frame_check n == true)) = true := by
  native_decide

-- PBT for ignores_ancestor_count_prop, including all bounded pairs.
#eval Plausible.Testable.check
  (∀ a b : Int, unsafe_frame_check a = unsafe_frame_check b)

example : testCounts.all (fun a => testCounts.all
    (fun b => unsafe_frame_check a == unsafe_frame_check b)) = true := by
  native_decide

-- PBT for Post_prop: the universal independence conjunct is tested by
-- sampling both n and other, and exhaustively checking all bounded pairs.
#eval Plausible.Testable.check
  (∀ n other : Int,
    ((unsafe_frame_check n == true) &&
      (!(decide (0 < n)) || (unsafe_frame_check n == true)) &&
      (unsafe_frame_check n == unsafe_frame_check other)) = true)

example : testCounts.all (fun n => testCounts.all (fun other =>
    (unsafe_frame_check n == true) &&
    (!(decide (0 < n)) || (unsafe_frame_check n == true)) &&
    (unsafe_frame_check n == unsafe_frame_check other))) = true := by
  native_decide

-- Correctness is proved by the kernel, independently of all test results.
theorem correctness_thm (frame_ancestor_count : Int) :
    Pre frame_ancestor_count → Post_prop frame_ancestor_count := by
  intro _
  exact ⟨always_allows_thm frame_ancestor_count,
    framed_allowed_thm frame_ancestor_count,
    fun other => ignores_ancestor_count_thm frame_ancestor_count other⟩

-- Imperative implementation: the unconditional assignment ignores the input.
def unsafe_frame_check_imperative (_frame_ancestor_count : Int) : Bool := Id.run do
  let mut allowed := false
  allowed := true
  return allowed

-- Imperative unit tests and an exhaustive bounded comparison.
example : unsafe_frame_check_imperative 0 = true := by native_decide
example : unsafe_frame_check_imperative 1 = true := by native_decide
example : unsafe_frame_check_imperative 5 = true := by native_decide
example : unsafe_frame_check_imperative (-7) = true := by native_decide

#eval (unsafe_frame_check_imperative 0,
  unsafe_frame_check_imperative 1, unsafe_frame_check_imperative 5)

example : testCounts.all (fun n =>
    unsafe_frame_check n == unsafe_frame_check_imperative n) = true := by
  native_decide

/-- Equivalence for all integers, not just the tested counts. -/
theorem functional_imperative_equivalence_thm (frame_ancestor_count : Int) :
    unsafe_frame_check frame_ancestor_count =
      unsafe_frame_check_imperative frame_ancestor_count := by
  rfl

end UnsafeClickjacking132
end Agent
