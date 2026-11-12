import Mathlib

/-!
# Exhaustive topological sorting

This file formalizes the permutation-search implementation from the Python
program.  A graph is a list of outgoing-neighbor lists.  Since Lean's input
type already guarantees the outer and inner values are lists of naturals,
malformation means that a neighbor is outside `0 .. graph.length - 1`.
-/

namespace topological_sort

abbrev Graph := List (List Nat)

/-- The directed edges encoded by an adjacency list, tagged with source indices. -/
def edges (graph : Graph) : List (Nat × Nat) :=
  graph.zipIdx.flatMap fun (neighbors, source) =>
    neighbors.map fun target => (source, target)

/-- Executable validation of all neighbor indices. -/
def pre (graph : Graph) : Bool :=
  graph.all fun neighbors => neighbors.all fun v => v < graph.length

/-- Propositional meaning of a topological order. -/
def IsTopologicalOrder (graph : Graph) (order : List Nat) : Prop :=
  order.Perm (List.range graph.length) ∧
    (edges graph).all (fun e => order.idxOf e.1 < order.idxOf e.2) = true

/-- The executable checker used by the search and tests. -/
def isTopologicalOrder (graph : Graph) (order : List Nat) : Bool :=
  decide (order.Perm (List.range graph.length)) &&
    (edges graph).all (fun e => order.idxOf e.1 < order.idxOf e.2)

/-- Search permutations in their library enumeration order and return the first valid one. -/
def topologicalSort (graph : Graph) : Option (List Nat) :=
  if pre graph then
    (List.range graph.length).permutations.find? (isTopologicalOrder graph)
  else
    none

/-! ## Unit tests -/

example : topologicalSort [[1], [2], []] = some [0, 1, 2] := by native_decide
example : (topologicalSort [[1, 2], [3], [3], []]).any
    (isTopologicalOrder [[1, 2], [3], [3], []]) = true := by native_decide
example : topologicalSort [] = some [] := by native_decide
example : topologicalSort [[], [], []] = some [0, 1, 2] := by native_decide
example : topologicalSort [[2], [], []] = some [0, 1, 2] := by native_decide
example : topologicalSort [[1], [0]] = none := by native_decide
example : topologicalSort [[0]] = none := by native_decide
example : topologicalSort [[2]] = none := by native_decide

#eval topologicalSort [[1], [2], []]
#eval topologicalSort [[1, 2], [3], [3], []]
#eval topologicalSort ([] : Graph)
#eval topologicalSort [[1], [0]]

/-! ## Specification and correctness -/

/-- Lean's typed counterpart of the Python `pre` predicate. -/
def Pre (graph : Graph) : Prop := pre graph = true

/-- The Boolean checker agrees exactly with its propositional specification. -/
def checker_prop (graph : Graph) (order : List Nat) : Prop :=
  isTopologicalOrder graph order = true ↔ IsTopologicalOrder graph order

theorem checker_thm (graph : Graph) (order : List Nat) :
    checker_prop graph order := by
  simp [checker_prop, isTopologicalOrder, IsTopologicalOrder, Bool.and_eq_true,
    decide_eq_true_eq]

/-- Every returned list is a genuine topological order of a well-formed graph. -/
def sound_prop (graph : Graph) : Prop :=
  ∀ order, topologicalSort graph = some order →
    Pre graph ∧ IsTopologicalOrder graph order

theorem sound_thm (graph : Graph) : sound_prop graph := by
  intro order hresult
  unfold topologicalSort at hresult
  by_cases hp : pre graph = true
  · rw [if_pos hp] at hresult
    have hcheck := List.find?_some hresult
    exact ⟨hp, (checker_thm graph order).mp hcheck⟩
  · rw [if_neg hp] at hresult
    simp at hresult

/-- If a well-formed graph has an order, exhaustive search returns an order. -/
def complete_prop (graph : Graph) : Prop :=
  Pre graph → (∃ order, IsTopologicalOrder graph order) →
    ∃ order, topologicalSort graph = some order

theorem complete_thm (graph : Graph) : complete_prop graph := by
  intro hp hexists
  change pre graph = true at hp
  rcases hexists with ⟨witness, hwitness⟩
  have hmem : witness ∈ (List.range graph.length).permutations :=
    List.mem_permutations.mpr hwitness.1
  have hcheck : isTopologicalOrder graph witness = true :=
    (checker_thm graph witness).mpr hwitness
  unfold topologicalSort
  rw [if_pos hp]
  cases hfind : (List.range graph.length).permutations.find?
      (isTopologicalOrder graph) with
  | none =>
      have hall := List.find?_eq_none.mp hfind witness hmem
      exact False.elim (hall hcheck)
  | some order => exact ⟨order, rfl⟩

/-- Failure means precisely malformed input or absence of any topological order. -/
def failure_prop (graph : Graph) : Prop :=
  topologicalSort graph = none ↔
    ¬ Pre graph ∨ ¬ ∃ order, IsTopologicalOrder graph order

theorem failure_thm (graph : Graph) : failure_prop graph := by
  constructor
  · intro hnone
    by_cases hp : Pre graph
    · right
      intro hexists
      rcases complete_thm graph hp hexists with ⟨order, horder⟩
      rw [hnone] at horder
      simp at horder
    · exact Or.inl hp
  · intro hfailure
    rcases hfailure with hbad | hnoorder
    · change pre graph ≠ true at hbad
      simp [topologicalSort, hbad]
    · by_contra hnotnone
      cases hresult : topologicalSort graph with
      | none => exact hnotnone hresult
      | some order =>
          have hs := sound_thm graph order hresult
          exact hnoorder ⟨order, hs.2⟩

/-- Full postcondition: sound success and an exact characterization of failure. -/
def Post_prop (graph : Graph) : Prop :=
  sound_prop graph ∧ failure_prop graph

/-- Correctness under the Python input-validity precondition. -/
theorem topologicalSort_correct (graph : Graph) :
    Pre graph → Post_prop graph := by
  intro _
  exact ⟨sound_thm graph, failure_thm graph⟩

/-! ## Imperative presentation -/

/-- The same search presented using `Id.run` and mutable result state. -/
def topologicalSortImperative (graph : Graph) : Option (List Nat) := Id.run do
  let mut result : Option (List Nat) := none
  if pre graph then
    result := (List.range graph.length).permutations.find?
      (isTopologicalOrder graph)
  return result

example : topologicalSortImperative [[1], [2], []] = some [0, 1, 2] := by
  native_decide
example : topologicalSortImperative ([] : Graph) = some [] := by native_decide
example : topologicalSortImperative [[1], [0]] = none := by native_decide
example : topologicalSortImperative [[2]] = none := by native_decide

#eval topologicalSortImperative [[1, 2], [3], [3], []]
#eval topologicalSortImperative [[], [], []]

/-- Functional and imperative presentations compute exactly the same result. -/
theorem functional_eq_imperative (graph : Graph) :
    topologicalSort graph = topologicalSortImperative graph := by
  by_cases hp : pre graph = true <;>
    simp [topologicalSort, topologicalSortImperative, hp]

end topological_sort
