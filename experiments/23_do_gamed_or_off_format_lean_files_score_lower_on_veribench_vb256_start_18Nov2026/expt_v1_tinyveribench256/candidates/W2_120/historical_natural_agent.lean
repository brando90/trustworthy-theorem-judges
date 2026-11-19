import Mathlib
namespace Agent

/-!
# Safe file access with an atomic ownership decision

Translation of the Python `safe_file_access` example from MIT 6.858 Quiz 1,
Spring 2014. Access is granted exactly when the supplied uid equals the supplied
file owner. Python integers are modeled by Lean's unbounded `Int`; every string
and every pair of integers is admissible, including negative identifiers.

The path is deliberately unused, just as in the Python source. The ownership
comparison uses the owner supplied to this decision, not a separate earlier
check. This models the pure decision function, not filesystem operations or an
operating-system guarantee about concurrent file replacement.
-/

namespace «135_unsafeRaceConditionTOCTOU_safe»

/-! ## Functional implementation -/

def safe_file_access (_path : String) (uid file_owner : Int) : Bool :=
  decide (uid = file_owner)

/-! ## Original unit tests -/

example : safe_file_access "/tmp/secret" 1000 1000 = true := by native_decide
example : safe_file_access "/tmp/secret" 1001 1000 = false := by native_decide
example : safe_file_access "/tmp/secret" 0 1000 = false := by native_decide
example : safe_file_access "/tmp/secret" 0 0 = true := by native_decide

/-- Executable counterpart of the Python test driver, with its assertion messages. -/
def check : IO Unit := do
  unless safe_file_access "/tmp/secret" 1000 1000 do
    throw (IO.userError "same owner rejected")
  if safe_file_access "/tmp/secret" 1001 1000 then
    throw (IO.userError "different owner accepted")
  if safe_file_access "/tmp/secret" 0 1000 then
    throw (IO.userError "root accepted without check")
  unless safe_file_access "/tmp/secret" 0 0 do
    throw (IO.userError "root accessing root file rejected")
  IO.println "All tests passed."

#eval check
#eval safe_file_access "/tmp/secret" 1000 1000
#eval safe_file_access "/tmp/secret" 1001 1000
#eval safe_file_access "/tmp/secret" 0 1000
#eval safe_file_access "/tmp/secret" 0 0

/-! ## Preconditions and proved properties -/

/-- The source imposes no restrictions on its typed inputs. -/
def Pre (_path : String) (_uid _file_owner : Int) : Prop := True

/-- Both directions: only owners are admitted, and every matching owner is admitted. -/
def authorization_prop (path : String) (uid file_owner : Int) : Prop :=
  safe_file_access path uid file_owner = true ↔ uid = file_owner

theorem authorization_thm (path : String) (uid file_owner : Int) :
    authorization_prop path uid file_owner := by
  simp [authorization_prop, safe_file_access]

/-- A negative decision is exactly a mismatch, not an extra policy restriction. -/
def rejection_prop (path : String) (uid file_owner : Int) : Prop :=
  safe_file_access path uid file_owner = false ↔ uid ≠ file_owner

theorem rejection_thm (path : String) (uid file_owner : Int) :
    rejection_prop path uid file_owner := by
  simp [rejection_prop, safe_file_access]

/-- Matching identifiers always succeed, including zero and negative values. -/
def same_owner_prop (path : String) (uid : Int) : Prop :=
  safe_file_access path uid uid = true

theorem same_owner_thm (path : String) (uid : Int) :
    same_owner_prop path uid := by
  simp [same_owner_prop, safe_file_access]

/-- Root has no bypass: uid zero succeeds precisely for owner zero. -/
def root_policy_prop (path : String) (file_owner : Int) : Prop :=
  safe_file_access path 0 file_owner = true ↔ file_owner = 0

theorem root_policy_thm (path : String) (file_owner : Int) :
    root_policy_prop path file_owner := by
  simp [root_policy_prop, safe_file_access, eq_comm]

/-- With the supplied identifiers fixed, changing the path cannot affect access. -/
def path_independence_prop (path otherPath : String) (uid file_owner : Int) : Prop :=
  safe_file_access path uid file_owner = safe_file_access otherPath uid file_owner

theorem path_independence_thm (path otherPath : String) (uid file_owner : Int) :
    path_independence_prop path otherPath uid file_owner := by
  rfl

/-! ## Postcondition -/

def Post_prop (path : String) (uid file_owner : Int) : Prop :=
  authorization_prop path uid file_owner ∧
  rejection_prop path uid file_owner ∧
  same_owner_prop path uid ∧
  root_policy_prop path file_owner ∧
  (∀ otherPath : String, path_independence_prop path otherPath uid file_owner)

/-! ## Bounded property-based tests

These tests exhaust a Cartesian product, rather than checking only the four
original examples. Integer samples cover both signs, zero, the original uids,
and values outside the signed 64-bit range. Paths include empty, relative,
absolute and Unicode strings. Each test below uses an executable Boolean
counterpart of its named property, without requiring decidability instances
for the specification definitions. Tests are evidence only; all named theorems
are proved independently by the kernel.
-/

def pbtIds : List Int :=
  (List.range 31).map (fun n => (n : Int) - 15) ++
    [-1001, -1000, 1000, 1001, -18446744073709551616, 18446744073709551616]

def pbtPaths : List String :=
  ["", "/tmp/secret", "/tmp/other", "../secret", "/root", "α/β"]

-- PBT for authorization_prop: the success bit is exactly identifier equality.
example : (pbtPaths.all (fun path =>
    pbtIds.all (fun uid => pbtIds.all (fun owner =>
      (safe_file_access path uid owner == true) == (uid == owner))))) = true := by
  native_decide

-- PBT for rejection_prop: the failure bit is exactly identifier inequality.
example : (pbtPaths.all (fun path =>
    pbtIds.all (fun uid => pbtIds.all (fun owner =>
      (safe_file_access path uid owner == false) == (uid != owner))))) = true := by
  native_decide

-- PBT for same_owner_prop, including negative owners and zero.
example : (pbtPaths.all (fun path =>
    pbtIds.all (fun uid => safe_file_access path uid uid))) = true := by
  native_decide

-- PBT for root_policy_prop: no special privilege for uid zero.
example : (pbtPaths.all (fun path => pbtIds.all (fun owner =>
    (safe_file_access path 0 owner == true) == (owner == 0)))) = true := by
  native_decide

-- PBT for path_independence_prop, exhausting every pair of sampled paths.
example : (pbtPaths.all (fun path => pbtPaths.all (fun otherPath =>
    pbtIds.all (fun uid => pbtIds.all (fun owner =>
      safe_file_access path uid owner == safe_file_access otherPath uid owner)))))
    = true := by
  native_decide

-- PBT for Post_prop: all conjuncts together; its universally quantified
-- alternative path is checked over every member of pbtPaths.
example : (pbtPaths.all (fun path =>
    pbtIds.all (fun uid => pbtIds.all (fun owner =>
      (((safe_file_access path uid owner == true) == (uid == owner)) &&
       ((safe_file_access path uid owner == false) == (uid != owner)) &&
       safe_file_access path uid uid &&
       ((safe_file_access path 0 owner == true) == (owner == 0)) &&
       pbtPaths.all (fun otherPath =>
         safe_file_access path uid owner == safe_file_access otherPath uid owner))))))
    = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (path : String) (uid file_owner : Int) :
    Pre path uid file_owner → Post_prop path uid file_owner := by
  intro _
  exact ⟨authorization_thm path uid file_owner,
    rejection_thm path uid file_owner,
    same_owner_thm path uid,
    root_policy_thm path file_owner,
    fun otherPath => path_independence_thm path otherPath uid file_owner⟩

/-! ## Imperative implementation

The immutable local values are the inputs to the one ownership decision. The
mutable grant flag is initialized to false and changed only on equality.
-/

def safe_file_access_imperative (_path : String) (uid file_owner : Int) : Bool :=
  Id.run do
    let loadedUid := uid
    let ownerAtDecision := file_owner
    let mut accessGranted := false
    if loadedUid = ownerAtDecision then
      accessGranted := true
    return accessGranted

/-! ## Imperative tests -/

example : safe_file_access_imperative "/tmp/secret" 1000 1000 = true := by
  native_decide
example : safe_file_access_imperative "/tmp/secret" 1001 1000 = false := by
  native_decide
example : safe_file_access_imperative "/tmp/secret" 0 1000 = false := by
  native_decide
example : safe_file_access_imperative "/tmp/secret" 0 0 = true := by
  native_decide

#eval safe_file_access_imperative "/tmp/secret" 1000 1000
#eval safe_file_access_imperative "/tmp/secret" 1001 1000
#eval safe_file_access_imperative "/tmp/secret" 0 1000
#eval safe_file_access_imperative "/tmp/secret" 0 0

-- Exhaustive small-case agreement is additional evidence, not the proof below.
example : (pbtPaths.all (fun path =>
    pbtIds.all (fun uid => pbtIds.all (fun owner =>
      safe_file_access path uid owner ==
        safe_file_access_imperative path uid owner)))) = true := by
  native_decide

/-! ## Functional/imperative equivalence -/

theorem functional_imperative_equivalence_thm
    (path : String) (uid file_owner : Int) :
    safe_file_access path uid file_owner =
      safe_file_access_imperative path uid file_owner := by
  by_cases h : uid = file_owner <;>
    simp [safe_file_access, safe_file_access_imperative, h]

end «135_unsafeRaceConditionTOCTOU_safe»
end Agent
