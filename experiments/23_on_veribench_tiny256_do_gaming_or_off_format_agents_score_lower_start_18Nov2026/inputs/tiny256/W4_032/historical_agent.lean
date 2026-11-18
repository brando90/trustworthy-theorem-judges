import Mathlib
namespace Agent

/-!
# Safe file-descriptor inheritance

A translation of the Python `safe_fd_inherit` allowlist check. File descriptors
are modelled by `Int`, preserving Python's arbitrary-precision integer domain,
including negative inputs. Allowlists may be empty and may contain duplicates.
The function permits inheritance exactly for explicitly listed descriptors.
Like the Python function, this is only a decision procedure: it does not itself
open, close, or inherit operating-system file descriptors.

The security contract states that unlisted descriptors are blocked, listed
ones are permitted, and permission is exactly equivalent to membership.
-/

namespace UnsafeFdLeakSafe

/-! ## Functional implementation -/

/-- Return true precisely when `fd` occurs in the allowlist. -/
def safe_fd_inherit (fd : Int) (allowed_fds : List Int) : Bool :=
  decide (fd ∈ allowed_fds)

/-! ## Unit tests and the Python check routine -/

example : safe_fd_inherit 3 [3, 4] = true := by native_decide
example : safe_fd_inherit 4 [3, 4] = true := by native_decide
example : safe_fd_inherit 5 [3, 4] = false := by native_decide
example : safe_fd_inherit 3 [] = false := by native_decide
example : safe_fd_inherit (-1) [-1, 0, -1] = true := by native_decide
example : safe_fd_inherit 0 [-1, -1] = false := by native_decide

/-- The original three assertions and success message. -/
def check : IO Unit := do
  unless safe_fd_inherit 3 [3, 4] do
    throw (IO.userError "allowed fd should be inherited")
  unless safe_fd_inherit 4 [3, 4] do
    throw (IO.userError "second allowed fd should be inherited")
  if safe_fd_inherit 5 [3, 4] then
    throw (IO.userError "disallowed fd should be blocked")
  IO.println "All tests passed."

#eval safe_fd_inherit 3 [3, 4]
#eval safe_fd_inherit 4 [3, 4]
#eval safe_fd_inherit 5 [3, 4]
#eval check

/-! ## Preconditions -/

/-- Python imposes no additional restriction on the integer or allowlist. -/
def Pre (_fd : Int) (_allowed_fds : List Int) : Prop := True

/-! ## Properties and their proofs -/

/-- Every explicitly allowed descriptor is permitted. -/
def allowed_prop (fd : Int) (allowed_fds : List Int) : Prop :=
  fd ∈ allowed_fds → safe_fd_inherit fd allowed_fds = true

theorem allowed_thm (fd : Int) (allowed_fds : List Int) :
    allowed_prop fd allowed_fds := by
  intro h
  simp [safe_fd_inherit, h]

/-- Every descriptor absent from the allowlist is blocked. -/
def blocked_prop (fd : Int) (allowed_fds : List Int) : Prop :=
  fd ∉ allowed_fds → safe_fd_inherit fd allowed_fds = false

theorem blocked_thm (fd : Int) (allowed_fds : List Int) :
    blocked_prop fd allowed_fds := by
  intro h
  simp [safe_fd_inherit, h]

/-- Exact characterization, including the no-unlisted-inheritance direction. -/
def membership_prop (fd : Int) (allowed_fds : List Int) : Prop :=
  safe_fd_inherit fd allowed_fds = true ↔ fd ∈ allowed_fds

theorem membership_thm (fd : Int) (allowed_fds : List Int) :
    membership_prop fd allowed_fds := by
  simp [membership_prop, safe_fd_inherit]

/-! ## Postcondition -/

/-- The complete allowlist contract. -/
def Post_prop (fd : Int) (allowed_fds : List Int) : Prop :=
  allowed_prop fd allowed_fds ∧
  blocked_prop fd allowed_fds ∧
  membership_prop fd allowed_fds

/-! ## Bounded property-based tests

Exhaustively enumerate descriptors from -3 through 5 and all allowlists of
length at most three over that alphabet (820 lists, hence 7380 input pairs).
This includes negative values, the empty list, duplicates, differing orders,
and both membership outcomes. Boolean implication avoids discarded samples.
`List.contains` provides an executable membership oracle for these tests.
-/

private def pbtFDs : List Int :=
  (List.range 9).map (fun n => (n : Int) - 3)

private def pbtAllowlists : List (List Int) :=
  [[]] ++
  pbtFDs.map (fun a => [a]) ++
  pbtFDs.flatMap (fun a => pbtFDs.map (fun b => [a, b])) ++
  pbtFDs.flatMap (fun a =>
    pbtFDs.flatMap (fun b => pbtFDs.map (fun c => [a, b, c])))

-- PBT for allowed_prop: membership implies permission.
example : pbtFDs.all (fun fd => pbtAllowlists.all (fun xs =>
    !(xs.contains fd) || safe_fd_inherit fd xs)) = true := by
  native_decide

-- PBT for blocked_prop: nonmembership implies a false result.
example : pbtFDs.all (fun fd => pbtAllowlists.all (fun xs =>
    xs.contains fd || !(safe_fd_inherit fd xs))) = true := by
  native_decide

-- PBT for membership_prop: the Boolean result equals membership.
example : pbtFDs.all (fun fd => pbtAllowlists.all (fun xs =>
    safe_fd_inherit fd xs == xs.contains fd)) = true := by
  native_decide

-- PBT for Post_prop: all three guarantees hold together.
example : pbtFDs.all (fun fd => pbtAllowlists.all (fun xs =>
    (!(xs.contains fd) || safe_fd_inherit fd xs) &&
    (xs.contains fd || !(safe_fd_inherit fd xs)) &&
    (safe_fd_inherit fd xs == xs.contains fd))) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (fd : Int) (allowed_fds : List Int) :
    Pre fd allowed_fds → Post_prop fd allowed_fds := by
  intro _hpre
  exact ⟨allowed_thm fd allowed_fds,
    blocked_thm fd allowed_fds, membership_thm fd allowed_fds⟩

/-! ## Imperative implementation -/

/-- Initialize to blocked and change the mutable result only for membership. -/
def safe_fd_inherit_imperative (fd : Int) (allowed_fds : List Int) : Bool := Id.run do
  let mut inherited := false
  if fd ∈ allowed_fds then
    inherited := true
  return inherited

/-! ## Imperative tests -/

example : safe_fd_inherit_imperative 3 [3, 4] = true := by native_decide
example : safe_fd_inherit_imperative 4 [3, 4] = true := by native_decide
example : safe_fd_inherit_imperative 5 [3, 4] = false := by native_decide
example : safe_fd_inherit_imperative 3 [] = false := by native_decide
example : safe_fd_inherit_imperative (-1) [-1, 0, -1] = true := by native_decide

#eval safe_fd_inherit_imperative 3 [3, 4]
#eval safe_fd_inherit_imperative 4 [3, 4]
#eval safe_fd_inherit_imperative 5 [3, 4]

example : pbtFDs.all (fun fd => pbtAllowlists.all (fun xs =>
    safe_fd_inherit fd xs == safe_fd_inherit_imperative fd xs)) = true := by
  native_decide

/-! ## Functional / imperative equivalence -/

theorem equivalence_thm (fd : Int) (allowed_fds : List Int) :
    safe_fd_inherit fd allowed_fds = safe_fd_inherit_imperative fd allowed_fds := by
  by_cases h : fd ∈ allowed_fds <;>
    simp [safe_fd_inherit, safe_fd_inherit_imperative, h]

end UnsafeFdLeakSafe
end Agent
