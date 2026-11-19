import Mathlib
namespace Agent

/-!
# Unsafe PID namespace isolation

Translation of the MIT 6.858 namespace-isolation example. Python integers are
modelled by `Int`, and dictionaries by finite `Std.HashMap Int Int` values.
The resolver deliberately ignores all three arguments, including membership in
the dictionary. It therefore accepts same-namespace, cross-namespace, and unknown
PIDs. The properties below document this vulnerability; they do not claim that
this implementation enforces isolation. No positivity or membership assumption
is imposed on the inputs.
-/

namespace UnsafeNamespaceIsolation

abbrev PidNamespaceMap := Std.HashMap Int Int

/-- An empty Python dictionary. -/
def emptyMap : PidNamespaceMap := Std.HashMap.ofList []

/-- The namespace dictionary from the Python test harness. -/
def ns_map : PidNamespaceMap :=
  Std.HashMap.ofList [(1, 0), (2, 0), (100, 1), (101, 1), (200, 2)]

/-- Unsafe by design: neither the PID nor its namespace is checked. -/
def unsafe_namespace_resolve (_process_ns : Int) (_pid : Int)
    (_pid_ns_map : PidNamespaceMap) : Bool :=
  true

/-- The conjunction of the five Python assertions (false denotes assertion failure). -/
def check (candidate : Int → Int → PidNamespaceMap → Bool) : Bool :=
  candidate 1 100 ns_map &&
  candidate 1 1 ns_map &&
  candidate 1 200 ns_map &&
  candidate 1 9999 ns_map &&
  candidate 1 100 emptyMap

/-! ## Unit tests: the five original assertions -/

example : unsafe_namespace_resolve 1 100 ns_map = true := by native_decide
example : unsafe_namespace_resolve 1 1 ns_map = true := by native_decide
example : unsafe_namespace_resolve 1 200 ns_map = true := by native_decide
example : unsafe_namespace_resolve 1 9999 ns_map = true := by native_decide
example : unsafe_namespace_resolve 1 100 emptyMap = true := by native_decide
example : check unsafe_namespace_resolve = true := by native_decide

#eval unsafe_namespace_resolve 1 100 ns_map
#eval unsafe_namespace_resolve 1 1 ns_map
#eval unsafe_namespace_resolve 1 200 ns_map
#eval unsafe_namespace_resolve 1 9999 ns_map
#eval unsafe_namespace_resolve 1 100 emptyMap
#eval if check unsafe_namespace_resolve then "All tests passed."
      else "Candidate failed namespace isolation tests"

/-! ## Preconditions and semantic properties -/

/-- The Python function is total on its declared domain. -/
def Pre (_process_ns _pid : Int) (_pid_ns_map : PidNamespaceMap) : Prop := True

/-- Every request is accepted, even without a map entry. -/
def alwaysVisible_prop (process_ns pid : Int) (pid_ns_map : PidNamespaceMap) : Prop :=
  unsafe_namespace_resolve process_ns pid pid_ns_map = true

theorem alwaysVisible_thm (process_ns pid : Int) (pid_ns_map : PidNamespaceMap) :
    alwaysVisible_prop process_ns pid pid_ns_map := by
  rfl

/-- The expected same-namespace case is accepted. -/
def sameNamespace_prop (process_ns pid : Int) (pid_ns_map : PidNamespaceMap) : Prop :=
  pid_ns_map[pid]? = some process_ns →
    unsafe_namespace_resolve process_ns pid pid_ns_map = true

theorem sameNamespace_thm (process_ns pid : Int) (pid_ns_map : PidNamespaceMap) :
    sameNamespace_prop process_ns pid pid_ns_map := by
  intro _
  rfl

/-- The vulnerability: any PID owned by a different namespace is also accepted. -/
def crossNamespace_prop (process_ns pid : Int) (pid_ns_map : PidNamespaceMap) : Prop :=
  ∀ owner : Int, pid_ns_map[pid]? = some owner → owner ≠ process_ns →
    unsafe_namespace_resolve process_ns pid pid_ns_map = true

theorem crossNamespace_thm (process_ns pid : Int) (pid_ns_map : PidNamespaceMap) :
    crossNamespace_prop process_ns pid pid_ns_map := by
  intro _ _ _
  rfl

/-- Even an absent PID is accepted. -/
def unknownPid_prop (process_ns pid : Int) (pid_ns_map : PidNamespaceMap) : Prop :=
  pid_ns_map[pid]? = none → unsafe_namespace_resolve process_ns pid pid_ns_map = true

theorem unknownPid_thm (process_ns pid : Int) (pid_ns_map : PidNamespaceMap) :
    unknownPid_prop process_ns pid pid_ns_map := by
  intro _
  rfl

/-- Acceptance does not require a nonempty dictionary. -/
def emptyMap_prop (process_ns pid : Int) : Prop :=
  unsafe_namespace_resolve process_ns pid emptyMap = true

theorem emptyMap_thm (process_ns pid : Int) : emptyMap_prop process_ns pid := by
  rfl

/-- Changing any or all inputs has no effect on the answer. -/
def argumentIndependence_prop (process_ns pid : Int) (pid_ns_map : PidNamespaceMap)
    (other_ns other_pid : Int) (other_map : PidNamespaceMap) : Prop :=
  unsafe_namespace_resolve process_ns pid pid_ns_map =
    unsafe_namespace_resolve other_ns other_pid other_map

theorem argumentIndependence_thm (process_ns pid : Int) (pid_ns_map : PidNamespaceMap)
    (other_ns other_pid : Int) (other_map : PidNamespaceMap) :
    argumentIndependence_prop process_ns pid pid_ns_map other_ns other_pid other_map := by
  rfl

/-- Kernel-checked success of the original assertion harness. -/
theorem check_thm : check unsafe_namespace_resolve = true := by
  rfl

/-- All guarantees concern the unsafe behavior, not a repaired implementation. -/
def Post_prop (process_ns pid : Int) (pid_ns_map : PidNamespaceMap) : Prop :=
  alwaysVisible_prop process_ns pid pid_ns_map ∧
  sameNamespace_prop process_ns pid pid_ns_map ∧
  crossNamespace_prop process_ns pid pid_ns_map ∧
  unknownPid_prop process_ns pid pid_ns_map ∧
  emptyMap_prop process_ns pid ∧
  (∀ other_ns other_pid other_map,
    argumentIndependence_prop process_ns pid pid_ns_map other_ns other_pid other_map) ∧
  check unsafe_namespace_resolve = true

/-! ## Bounded property-based tests

Exhaust all partial dictionaries on keys {-1, 0, 1}, with each present key
assigned a namespace in {-1, 0, 1}, and also test the source dictionary.
There are 4^3 + 1 = 65 maps, including the empty map. The Cartesian input
space has 4 * 8 * 65 = 2080 cases. Independence checks every pair of cases.
Both matching and mismatching namespaces and absent PIDs occur, so the
conditional tests are not vacuous. These tests are evidence only: none is
used to prove a semantic theorem.
-/

def sampledNamespaces : List Int := [-1, 0, 1, 2]
def sampledPids : List Int := [-1, 0, 1, 2, 100, 101, 200, 9999]
def sampledOwners : List (Option Int) := [none, some (-1), some 0, some 1]

def sampledMaps : List PidNamespaceMap :=
  ns_map :: (sampledOwners.flatMap fun a =>
    sampledOwners.flatMap fun b =>
      sampledOwners.map fun c =>
        ([(-1, a), (0, b), (1, c)] : List (Int × Option Int)).foldl
          (fun m entry => match entry.2 with
            | none => m
            | some owner => m.insert entry.1 owner) emptyMap)

/-- Exhaustive quantification over the bounded input space. -/
def allInputs (test : Int → Int → PidNamespaceMap → Bool) : Bool :=
  sampledNamespaces.all fun process_ns =>
    sampledPids.all fun pid => sampledMaps.all (test process_ns pid)

/-- Executable form of `alwaysVisible_prop`. -/
def alwaysVisibleCheck (process_ns pid : Int) (m : PidNamespaceMap) : Bool :=
  unsafe_namespace_resolve process_ns pid m

/-- Executable implication corresponding to `sameNamespace_prop`. -/
def sameNamespaceCheck (process_ns pid : Int) (m : PidNamespaceMap) : Bool :=
  (m[pid]? != some process_ns) || unsafe_namespace_resolve process_ns pid m

/-- Only the unique looked-up owner can satisfy the property's lookup premise. -/
def crossNamespaceCheck (process_ns pid : Int) (m : PidNamespaceMap) : Bool :=
  match m[pid]? with
  | none => true
  | some owner => (owner == process_ns) || unsafe_namespace_resolve process_ns pid m

/-- Executable implication corresponding to `unknownPid_prop`. -/
def unknownPidCheck (process_ns pid : Int) (m : PidNamespaceMap) : Bool :=
  (m[pid]?).isSome || unsafe_namespace_resolve process_ns pid m

/-- Executable form of `emptyMap_prop`. -/
def emptyMapCheck (process_ns pid : Int) : Bool :=
  unsafe_namespace_resolve process_ns pid emptyMap

/-- Executable form of `argumentIndependence_prop`. -/
def argumentIndependenceCheck (process_ns pid : Int) (m : PidNamespaceMap)
    (other_ns other_pid : Int) (other_map : PidNamespaceMap) : Bool :=
  unsafe_namespace_resolve process_ns pid m ==
    unsafe_namespace_resolve other_ns other_pid other_map

-- PBT for alwaysVisible_prop.
example : allInputs alwaysVisibleCheck = true := by native_decide
-- PBT for sameNamespace_prop.
example : allInputs sameNamespaceCheck = true := by native_decide
-- PBT for crossNamespace_prop.
example : allInputs crossNamespaceCheck = true := by native_decide
-- PBT for unknownPid_prop.
example : allInputs unknownPidCheck = true := by native_decide
-- PBT for emptyMap_prop.
example : (sampledNamespaces.all fun process_ns =>
    sampledPids.all (emptyMapCheck process_ns)) = true := by native_decide
-- PBT for argumentIndependence_prop, over all pairs of sampled inputs.
example : (allInputs fun process_ns pid m =>
    allInputs (argumentIndependenceCheck process_ns pid m)) = true := by native_decide

/-- Bounded executable conjunction corresponding to the entire postcondition. -/
def postCheck (process_ns pid : Int) (m : PidNamespaceMap) : Bool :=
  alwaysVisibleCheck process_ns pid m &&
  sameNamespaceCheck process_ns pid m &&
  crossNamespaceCheck process_ns pid m &&
  unknownPidCheck process_ns pid m &&
  emptyMapCheck process_ns pid &&
  allInputs (argumentIndependenceCheck process_ns pid m) &&
  check unsafe_namespace_resolve

-- PBT for Post_prop; Pre is True, so every sampled input is admissible.
example : allInputs postCheck = true := by native_decide

#eval [("always visible", allInputs alwaysVisibleCheck),
       ("same namespace", allInputs sameNamespaceCheck),
       ("cross namespace", allInputs crossNamespaceCheck),
       ("unknown PID", allInputs unknownPidCheck),
       ("empty map", sampledNamespaces.all fun ns => sampledPids.all (emptyMapCheck ns)),
       ("argument independence", allInputs fun ns pid m =>
         allInputs (argumentIndependenceCheck ns pid m)),
       ("postcondition", allInputs postCheck)]

/-! ## Correctness with respect to the unsafe specification -/

theorem correctness_thm (process_ns pid : Int) (pid_ns_map : PidNamespaceMap) :
    Pre process_ns pid pid_ns_map → Post_prop process_ns pid pid_ns_map := by
  intro _
  refine ⟨alwaysVisible_thm process_ns pid pid_ns_map,
    sameNamespace_thm process_ns pid pid_ns_map,
    crossNamespace_thm process_ns pid pid_ns_map,
    unknownPid_thm process_ns pid pid_ns_map,
    emptyMap_thm process_ns pid, ?_, check_thm⟩
  intro other_ns other_pid other_map
  exact argumentIndependence_thm process_ns pid pid_ns_map other_ns other_pid other_map

/-! ## Imperative implementation and tests -/

/-- A mutable result is set unconditionally; the map is still never inspected. -/
def unsafe_namespace_resolve_imperative (_process_ns : Int) (_pid : Int)
    (_pid_ns_map : PidNamespaceMap) : Bool := Id.run do
  let mut visible := false
  visible := true
  return visible

example : unsafe_namespace_resolve_imperative 1 100 ns_map = true := by native_decide
example : unsafe_namespace_resolve_imperative 1 1 ns_map = true := by native_decide
example : unsafe_namespace_resolve_imperative 1 200 ns_map = true := by native_decide
example : unsafe_namespace_resolve_imperative 1 9999 ns_map = true := by native_decide
example : unsafe_namespace_resolve_imperative 1 100 emptyMap = true := by native_decide
example : check unsafe_namespace_resolve_imperative = true := by native_decide
#eval check unsafe_namespace_resolve_imperative
#eval allInputs fun ns pid m =>
  unsafe_namespace_resolve ns pid m == unsafe_namespace_resolve_imperative ns pid m

/-! ## Functional/imperative equivalence on the full input domain -/

theorem functional_imperative_equivalence_thm (process_ns pid : Int)
    (pid_ns_map : PidNamespaceMap) :
    unsafe_namespace_resolve process_ns pid pid_ns_map =
      unsafe_namespace_resolve_imperative process_ns pid pid_ns_map := by
  rfl

end UnsafeNamespaceIsolation
end Agent
