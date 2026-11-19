import Mathlib
namespace Agent

/-!
# Unsafe Tor guard reuse

Translation of the Python `unsafeGuardReuse` program. Guard identifiers are
unbounded signed integers (`Int`), and a guard history is a `List Int`.
The implementation deliberately returns `true` without examining either input.
In particular, a recently used guard is accepted again: this models the stated
vulnerability, not a safe guard-selection policy. Traffic correlation is the
security motivation; network traffic itself is not modeled here.

The precondition is unrestricted. The specification records unconditional
acceptance, acceptance in both membership cases, and independence from both
arguments. Bounded property-based tests supplement kernel-checked proofs.
-/

namespace UnsafeGuardReuse

/-! ## Functional implementation -/

def unsafeGuardReuse (_guard_node : Int) (_recent_guards : List Int) : Bool :=
  true

/-! ## Unit tests and the Python check routine -/

example : unsafeGuardReuse 5 [5, 6, 7] = true := by native_decide
example : unsafeGuardReuse 5 [] = true := by native_decide
example : unsafeGuardReuse 99 [1, 2, 3] = true := by native_decide
example : unsafeGuardReuse (-5) [-5, -5, 0] = true := by native_decide

#eval unsafeGuardReuse 5 [5, 6, 7]
#eval unsafeGuardReuse 5 []
#eval unsafeGuardReuse 99 [1, 2, 3]

/-- The three assertions and success message from Python's `check`. -/
def check : IO Unit := do
  unless unsafeGuardReuse 5 [5, 6, 7] do
    throw (IO.userError "vuln: reused guard accepted")
  unless unsafeGuardReuse 5 [] do
    throw (IO.userError "normal case")
  unless unsafeGuardReuse 99 [1, 2, 3] do
    throw (IO.userError "fresh guard accepted")
  IO.println "All tests passed."

#eval check

/-! ## Preconditions -/

/-- Every integer guard and every finite history is admissible. -/
def Pre (_guard_node : Int) (_recent_guards : List Int) : Prop := True

/-! ## Semantic properties -/

/-- Acceptance is unconditional. -/
def alwaysAccepts_prop (guard_node : Int) (recent_guards : List Int) : Prop :=
  unsafeGuardReuse guard_node recent_guards = true

theorem alwaysAccepts_thm (guard_node : Int) (recent_guards : List Int) :
    alwaysAccepts_prop guard_node recent_guards := by
  rfl

/-- The unsafe behavior: membership in the history does not prevent acceptance. -/
def reusedGuardAccepted_prop (guard_node : Int) (recent_guards : List Int) : Prop :=
  guard_node ∈ recent_guards → unsafeGuardReuse guard_node recent_guards = true

theorem reusedGuardAccepted_thm (guard_node : Int) (recent_guards : List Int) :
    reusedGuardAccepted_prop guard_node recent_guards := by
  intro _
  rfl

/-- A fresh guard is accepted as well, including when the history is empty. -/
def freshGuardAccepted_prop (guard_node : Int) (recent_guards : List Int) : Prop :=
  guard_node ∉ recent_guards → unsafeGuardReuse guard_node recent_guards = true

theorem freshGuardAccepted_thm (guard_node : Int) (recent_guards : List Int) :
    freshGuardAccepted_prop guard_node recent_guards := by
  intro _
  rfl

/-- Replacing either or both arguments never changes the result. -/
def inputsIgnored_prop (guard_node : Int) (recent_guards : List Int) : Prop :=
  ∀ (other_guard : Int) (other_history : List Int),
    unsafeGuardReuse guard_node recent_guards =
      unsafeGuardReuse other_guard other_history

theorem inputsIgnored_thm (guard_node : Int) (recent_guards : List Int) :
    inputsIgnored_prop guard_node recent_guards := by
  intro other_guard other_history
  rfl

/-! ## Postcondition -/

def Post_prop (guard_node : Int) (recent_guards : List Int) : Prop :=
  alwaysAccepts_prop guard_node recent_guards ∧
  reusedGuardAccepted_prop guard_node recent_guards ∧
  freshGuardAccepted_prop guard_node recent_guards ∧
  inputsIgnored_prop guard_node recent_guards

/-! ## Property-based tests

Exhaustively enumerate guards from -3 through 3, and every history of length
zero, one, or two over those guards. This includes duplicate history entries,
empty histories, and both membership cases. Independence is checked on every
pair of these inputs. All checks below use executable Boolean expressions;
they are tests, not dependencies of any named theorem.
-/

private def pbtGuards : List Int :=
  (List.range 7).map (fun n => (n : Int) - 3)

private def pbtHistories : List (List Int) :=
  [[]] ++ pbtGuards.map (fun g => [g]) ++
    pbtGuards.flatMap (fun g => pbtGuards.map (fun h => [g, h]))

-- PBT for alwaysAccepts_prop (399 guard/history pairs).
example : pbtGuards.all (fun g =>
    pbtHistories.all (fun gs => unsafeGuardReuse g gs)) = true := by
  native_decide

-- PBT for reusedGuardAccepted_prop: Boolean implication from membership.
example : pbtGuards.all (fun g =>
    pbtHistories.all (fun gs =>
      !gs.contains g || unsafeGuardReuse g gs)) = true := by
  native_decide

-- PBT for freshGuardAccepted_prop: Boolean implication from nonmembership.
example : pbtGuards.all (fun g =>
    pbtHistories.all (fun gs =>
      gs.contains g || unsafeGuardReuse g gs)) = true := by
  native_decide

-- PBT for inputsIgnored_prop (159201 pairs of guard/history inputs).
example : pbtGuards.all (fun g =>
    pbtHistories.all (fun gs =>
      pbtGuards.all (fun other =>
        pbtHistories.all (fun otherHistory =>
          unsafeGuardReuse g gs ==
            unsafeGuardReuse other otherHistory)))) = true := by
  native_decide

-- PBT for the full Post_prop conjunction, with its universal comparison
-- exhaustively checked over the same bounded input family.
example : pbtGuards.all (fun g =>
    pbtHistories.all (fun gs =>
      unsafeGuardReuse g gs &&
      (!gs.contains g || unsafeGuardReuse g gs) &&
      (gs.contains g || unsafeGuardReuse g gs) &&
      pbtGuards.all (fun other =>
        pbtHistories.all (fun otherHistory =>
          unsafeGuardReuse g gs ==
            unsafeGuardReuse other otherHistory)))) = true := by
  native_decide

#eval (pbtGuards.length, pbtHistories.length)

/-! ## Correctness -/

theorem correctness_thm (guard_node : Int) (recent_guards : List Int) :
    Pre guard_node recent_guards → Post_prop guard_node recent_guards := by
  intro _
  exact ⟨alwaysAccepts_thm guard_node recent_guards,
    reusedGuardAccepted_thm guard_node recent_guards,
    freshGuardAccepted_thm guard_node recent_guards,
    inputsIgnored_thm guard_node recent_guards⟩

/-! ## Imperative implementation -/

/-- Explicit mutable result; like Python, neither input is inspected. -/
def unsafeGuardReuseImperative (_guard_node : Int)
    (_recent_guards : List Int) : Bool := Id.run do
  let mut accepted := false
  accepted := true
  return accepted

/-! ## Imperative tests -/

example : unsafeGuardReuseImperative 5 [5, 6, 7] = true := by native_decide
example : unsafeGuardReuseImperative 5 [] = true := by native_decide
example : unsafeGuardReuseImperative 99 [1, 2, 3] = true := by native_decide
example : unsafeGuardReuseImperative (-5) [-5, -5, 0] = true := by native_decide

#eval unsafeGuardReuseImperative 5 [5, 6, 7]
#eval unsafeGuardReuseImperative 5 []
#eval unsafeGuardReuseImperative 99 [1, 2, 3]

/-! ## Functional/imperative equivalence -/

theorem functional_imperative_equivalence_thm
    (guard_node : Int) (recent_guards : List Int) :
    unsafeGuardReuse guard_node recent_guards =
      unsafeGuardReuseImperative guard_node recent_guards := by
  rfl

end UnsafeGuardReuse
end Agent
