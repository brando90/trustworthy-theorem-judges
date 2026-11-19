import Mathlib
namespace Agent

/-!
# Unsafe profile sandbox

Translation of the Python `unsafeProfileExec` and its four-assertion test harness.
Python integers are represented by `Int`, with no nonnegativity or UID-isolation
restriction. The function always returns `true`: equal UIDs, distinct UIDs, and
root are all accepted. This models the Boolean behavior of the vulnerable code;
it does not claim to implement process execution or filesystem access.

`check` represents assertion failure by `Except.error`, preserving the order and
messages of the Python assertions. The successful print is performed by `#eval`.
Theorems use kernel-checked proofs; `native_decide` is used only for tests.
-/

namespace UnsafeProfileSandbox

-- 1. Functional implementation and the Python assertion harness.
def unsafeProfileExec (_profileUid _serverUid : Int) : Bool :=
  true

def check (candidate : Int → Int → Bool) : Except String Bool :=
  if candidate 42 1000 then
    if candidate 1000 1000 then
      if candidate 0 0 then
        if candidate 2 3 then
          .ok true
        else
          .error "distinct uids accepted"
      else
        .error "root uid accepted (vuln)"
    else
      .error "UID collision accepted (vuln)"
  else
    .error "normal execution failed"

-- Executable equality for testing assertion-harness results.
deriving instance DecidableEq for Except

-- 2. Fixed unit tests, including all four original assertions.
example : unsafeProfileExec 42 1000 = true := by native_decide
example : unsafeProfileExec 1000 1000 = true := by native_decide
example : unsafeProfileExec 0 0 = true := by native_decide
example : unsafeProfileExec 2 3 = true := by native_decide
example : unsafeProfileExec (-42) (-1000) = true := by native_decide
example : check unsafeProfileExec = .ok true := by native_decide

-- The assertion harness also preserves the individual failure messages.
example : check (fun _ _ => false) = .error "normal execution failed" := by
  native_decide
example : check (fun p s => !(p == 1000 && s == 1000)) =
    .error "UID collision accepted (vuln)" := by native_decide
example : check (fun p s => !(p == 0 && s == 0)) =
    .error "root uid accepted (vuln)" := by native_decide
example : check (fun p s => !(p == 2 && s == 3)) =
    .error "distinct uids accepted" := by native_decide

#eval unsafeProfileExec 42 1000
#eval unsafeProfileExec 1000 1000
#eval unsafeProfileExec 0 0
#eval unsafeProfileExec 2 3
#eval check unsafeProfileExec
#eval (do
  match check unsafeProfileExec with
  | .ok true => IO.println "All tests passed."
  | .ok false => throw (IO.userError "Candidate failed tests")
  | .error message => throw (IO.userError message) : IO Unit)

-- 3. No UID validity or separation assumption is made by the Python function.
def Pre (_profileUid _serverUid : Int) : Prop := True

-- 4. Behavioral properties and kernel-checked proofs.
def alwaysExecutes_prop (profileUid serverUid : Int) : Prop :=
  unsafeProfileExec profileUid serverUid = true

theorem alwaysExecutes_thm (profileUid serverUid : Int) :
    alwaysExecutes_prop profileUid serverUid := by
  rfl

-- Acceptance of collisions is precisely the absence of the advertised check.
def collisionAccepted_prop (uid : Int) : Prop :=
  unsafeProfileExec uid uid = true

theorem collisionAccepted_thm (uid : Int) : collisionAccepted_prop uid := by
  rfl

-- This includes the original (0, 0) test, but also every profile with server UID 0.
def rootServerAccepted_prop (profileUid : Int) : Prop :=
  unsafeProfileExec profileUid 0 = true

theorem rootServerAccepted_thm (profileUid : Int) :
    rootServerAccepted_prop profileUid := by
  rfl

def distinctUidsAccepted_prop (profileUid serverUid : Int) : Prop :=
  profileUid ≠ serverUid → unsafeProfileExec profileUid serverUid = true

theorem distinctUidsAccepted_thm (profileUid serverUid : Int) :
    distinctUidsAccepted_prop profileUid serverUid := by
  intro _
  rfl

-- Both arguments can be changed arbitrarily without changing the result.
def uidIndependent_prop (profileUid serverUid otherProfileUid otherServerUid : Int) : Prop :=
  unsafeProfileExec profileUid serverUid =
    unsafeProfileExec otherProfileUid otherServerUid

theorem uidIndependent_thm (profileUid serverUid otherProfileUid otherServerUid : Int) :
    uidIndependent_prop profileUid serverUid otherProfileUid otherServerUid := by
  rfl

-- 5. The postcondition combines the behavior, vulnerability, and public checks.
def Post_prop (profileUid serverUid : Int) : Prop :=
  alwaysExecutes_prop profileUid serverUid ∧
  collisionAccepted_prop serverUid ∧
  rootServerAccepted_prop profileUid ∧
  distinctUidsAccepted_prop profileUid serverUid ∧
  (∀ otherProfileUid otherServerUid : Int,
    uidIndependent_prop profileUid serverUid otherProfileUid otherServerUid) ∧
  check unsafeProfileExec = .ok true

-- 6. Bounded PBTs: exhaustive over a grid, not a restriction on theorem domains.
-- The grid includes negatives, root, all four public examples, and large UIDs.
def uidSamples : List Int :=
  (List.range 21).map (fun n => (n : Int) - 10) ++ [-1000, 42, 1000]

-- PBT for alwaysExecutes_prop: every pair in the grid.
example : uidSamples.all (fun p =>
    uidSamples.all (fun s => unsafeProfileExec p s)) = true := by
  native_decide

-- PBT for collisionAccepted_prop: every diagonal pair in the grid.
example : uidSamples.all (fun uid => unsafeProfileExec uid uid) = true := by
  native_decide

-- PBT for rootServerAccepted_prop: every profile with server UID zero.
example : uidSamples.all (fun p => unsafeProfileExec p 0) = true := by
  native_decide

-- PBT for distinctUidsAccepted_prop: executable implication, not a domain change.
example : uidSamples.all (fun p =>
    uidSamples.all (fun s =>
      if p != s then unsafeProfileExec p s else true)) = true := by
  native_decide

-- PBT for uidIndependent_prop: every quadruple in the grid.
example : uidSamples.all (fun p =>
    uidSamples.all (fun s =>
      uidSamples.all (fun p' =>
        uidSamples.all (fun s' =>
          unsafeProfileExec p s == unsafeProfileExec p' s')))) = true := by
  native_decide

-- Executable form of Post_prop at one sampled pair of alternative UIDs.
-- The nested grid check below samples its universally quantified component too.
def postCheck (p s p' s' : Int) : Bool :=
  unsafeProfileExec p s &&
  unsafeProfileExec s s &&
  unsafeProfileExec p 0 &&
  (if p != s then unsafeProfileExec p s else true) &&
  (unsafeProfileExec p s == unsafeProfileExec p' s') &&
  (match check unsafeProfileExec with
   | .ok true => true
   | _ => false)

-- PBT for the full Post_prop conjunction, including the original check harness.
example : uidSamples.all (fun p =>
    uidSamples.all (fun s =>
      uidSamples.all (fun p' =>
        uidSamples.all (fun s' => postCheck p s p' s')))) = true := by
  native_decide

#eval uidSamples.all (fun p =>
  uidSamples.all (fun s =>
    uidSamples.all (fun p' =>
      uidSamples.all (fun s' => postCheck p s p' s'))))

-- 7. Correctness on all Python integer inputs, not merely the PBT grid.
theorem correctness_thm (profileUid serverUid : Int) :
    Pre profileUid serverUid → Post_prop profileUid serverUid := by
  intro _
  refine ⟨alwaysExecutes_thm profileUid serverUid,
    collisionAccepted_thm serverUid,
    rootServerAccepted_thm profileUid,
    distinctUidsAccepted_thm profileUid serverUid, ?_, ?_⟩
  · intro otherProfileUid otherServerUid
    exact uidIndependent_thm profileUid serverUid otherProfileUid otherServerUid
  · rfl

-- 8. Imperative implementation: the result is assigned unconditionally.
def unsafeProfileExecImperative (_profileUid _serverUid : Int) : Bool := Id.run do
  let mut accepted := false
  accepted := true
  return accepted

-- 9. Imperative tests.
example : unsafeProfileExecImperative 42 1000 = true := by native_decide
example : unsafeProfileExecImperative 1000 1000 = true := by native_decide
example : unsafeProfileExecImperative 0 0 = true := by native_decide
example : unsafeProfileExecImperative 2 3 = true := by native_decide
example : check unsafeProfileExecImperative = .ok true := by native_decide

#eval unsafeProfileExecImperative 42 1000
#eval unsafeProfileExecImperative 1000 1000
#eval unsafeProfileExecImperative 0 0
#eval unsafeProfileExecImperative 2 3
#eval check unsafeProfileExecImperative

-- Bounded equivalence test complements, but does not replace, the proof below.
example : uidSamples.all (fun p =>
    uidSamples.all (fun s =>
      unsafeProfileExec p s == unsafeProfileExecImperative p s)) = true := by
  native_decide

-- 10. Kernel-checked equivalence for arbitrary integer UIDs.
theorem functional_eq_imperative_thm (profileUid serverUid : Int) :
    unsafeProfileExec profileUid serverUid =
      unsafeProfileExecImperative profileUid serverUid := by
  rfl

end UnsafeProfileSandbox
end Agent
