import Mathlib

/-!
# Topological sorting for finite directed graphs

Formalization of a brute-force topological sort. A directed graph is given as an
adjacency list `graph` over vertices `0, …, n-1`, where `graph[u]` is the list of
out-neighbors of `u`. The algorithm enumerates all permutations of the vertices
and returns the first one passing an executable topological-order checker; it
returns `none` when the graph is malformed or no topological order exists (in
particular, when the graph contains a directed cycle).

Contents:
* `pre` / `Pre`: well-formedness of an adjacency-list graph.
* `isTopologicalOrder` / `IsTopOrder`: executable checker and its specification.
* `topologicalSort`: functional implementation (permutation search), with unit
  tests, properties, a post-condition and a `Pre → Post` correctness theorem.
* `topologicalSortImpl`: imperative implementation in `Id` with mutable state,
  plus a theorem proving it coincides with the functional one.

Edge cases mirror the Python source: empty graphs yield `some []`, disconnected
DAGs list every vertex exactly once, cyclic graphs yield `none`, and malformed
adjacency lists yield `none`.
-/

namespace topological_sort

universe u

/-! ## Functional implementation -/

/-- Boolean precondition: every neighbor entry is a valid vertex index `< n`. -/
def pre (graph : List (List Nat)) : Bool :=
  graph.all fun ns => ns.all fun v => decide (v < graph.length)

/-- Executable check that `order` is a permutation of `List.range n`. -/
def isPermRange (n : Nat) (order : List Nat) : Bool :=
  decide (order.length = n) &&
  (List.range n).all (fun v => decide (v ∈ order)) &&
  decide (order.Nodup)

/-- Executable topological-order checker: `order` is a permutation of the
vertices and every edge `u → v` has `u` before `v` in `order`. -/
def isTopologicalOrder (graph : List (List Nat)) (order : List Nat) : Bool :=
  pre graph &&
  isPermRange graph.length order &&
  (List.range graph.length).all (fun u =>
    (graph[u]!).all (fun v => decide (order.idxOf u < order.idxOf v)))

/-- Functional topological sort: the first vertex permutation passing the
checker, or `none` if the graph is malformed or no such permutation exists. -/
def topologicalSort (graph : List (List Nat)) : Option (List Nat) :=
  if pre graph then
    (List.permutations (List.range graph.length)).find? (isTopologicalOrder graph)
  else
    none

/-! ## Unit tests -/

example : topologicalSort [[1], [2], []] = some [0, 1, 2] := by native_decide
example : isTopologicalOrder [[1], [2], []] [0, 1, 2] = true := by native_decide
example : topologicalSort [[1, 2], [3], [3], []] = some [0, 1, 2, 3] := by native_decide
example : isTopologicalOrder [[1, 2], [3], [3], []] [0, 2, 1, 3] = true := by native_decide
example : topologicalSort ([] : List (List Nat)) = some [] := by native_decide
example : topologicalSort [[], [], []] = some [0, 1, 2] := by native_decide
example : topologicalSort [[2], [], []] = some [0, 1, 2] := by native_decide
example : topologicalSort [[1], [0]] = none := by native_decide
example : topologicalSort [[0]] = none := by native_decide
example : topologicalSort [[2]] = none := by native_decide
example : isTopologicalOrder [[1], [2], []] [1, 0, 2] = false := by native_decide
-- Python's `candidate([[1], "not a list"])` case is ill-typed in Lean; the
-- corresponding malformed-input behavior is captured by `pre` being `false`.

#eval topologicalSort [[1], [2], []]
#eval topologicalSort [[1, 2], [3], [3], []]
#eval topologicalSort [[1], [0]]
#eval isTopologicalOrder [[1], [2], []] [0, 2, 1]

/-! ## Pre-condition -/

/-- Well-formedness of an adjacency-list graph over vertices `0, …, n-1`. -/
def Pre (graph : List (List Nat)) : Prop :=
  ∀ ns ∈ graph, ∀ v ∈ ns, v < graph.length

/-- The Boolean precondition decides the propositional one. -/
theorem pre_iff_Pre (graph : List (List Nat)) : pre graph = true ↔ Pre graph := by
  unfold pre Pre
  simp only [List.all_eq_true, decide_eq_true_eq]

/-! ## Topological-order specification and properties -/

/-- Specification: `order` is a topological order of `graph`, i.e. `graph` is
well-formed, `order` is a permutation of the vertices, and every edge `u → v`
appears in `order` with `u` before `v`. -/
def IsTopOrder (graph : List (List Nat)) (order : List Nat) : Prop :=
  Pre graph ∧
  List.Perm order (List.range graph.length) ∧
  ∀ u : Nat, ∀ hu : u < graph.length, ∀ v ∈ graph[u]'hu,
    order.idxOf u < order.idxOf v

/-- The executable checker decides the specification. -/
theorem isTopologicalOrder_iff (graph : List (List Nat)) (order : List Nat) :
    isTopologicalOrder graph order = true ↔ IsTopOrder graph order := by
  unfold isTopologicalOrder isPermRange
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨⟨hpre, ⟨hlen, hsub⟩, _hnodup⟩, hedge⟩
    refine ⟨(pre_iff_Pre graph).mp hpre, ?_, ?_⟩
    · have hsub' : List.range graph.length ⊆ order :=
        fun v hv => hsub v (List.mem_range.mp hv)
      have hsp : List.Subperm (List.range graph.length) order :=
        List.Nodup.subperm List.nodup_range hsub'
      have hlen' : order.length ≤ (List.range graph.length).length := by simp [hlen]
      exact (hsp.perm_of_length_le hlen').symm
    · intro u hu v hv
      rw [← getElem!_pos graph u hu] at hv
      exact hedge u hu v hv
  · rintro ⟨hpre, hperm, hedge⟩
    refine ⟨⟨(pre_iff_Pre graph).mpr hpre, ⟨?_, ?_⟩, ?_⟩, ?_⟩
    · exact hperm.length_eq.trans List.length_range
    · intro v hv
      exact hperm.symm.subset (List.mem_range.mpr hv)
    · exact hperm.nodup_iff.mpr List.nodup_range
    · intro u hu v hv
      rw [getElem!_pos graph u hu] at hv
      exact hedge u hu v hv

/-- Any order returned by `topologicalSort` satisfies the specification. -/
theorem topologicalSort_some {graph : List (List Nat)} {order : List Nat}
    (h : topologicalSort graph = some order) : IsTopOrder graph order := by
  unfold topologicalSort at h
  split at h
  next => exact (isTopologicalOrder_iff graph order).mp (List.find?_some h)
  next => simp at h

/-- Property: a successful search implies the graph is well-formed. -/
def topologicalSort_pre_prop : Prop :=
  ∀ (graph : List (List Nat)) (order : List Nat),
    topologicalSort graph = some order → Pre graph

/-- Property: any returned order is a permutation of the vertices. -/
def topologicalSort_perm_prop : Prop :=
  ∀ (graph : List (List Nat)) (order : List Nat),
    topologicalSort graph = some order → List.Perm order (List.range graph.length)

/-- Property: any returned order respects every edge of the graph. -/
def topologicalSort_edges_prop : Prop :=
  ∀ (graph : List (List Nat)) (order : List Nat),
    topologicalSort graph = some order →
    ∀ u : Nat, ∀ hu : u < graph.length, ∀ v ∈ graph[u]'hu,
      order.idxOf u < order.idxOf v

/-- Property: the search is complete — if a topological order exists,
one is returned. -/
def topologicalSort_complete_prop : Prop :=
  ∀ graph : List (List Nat), Pre graph →
    (∃ order, IsTopOrder graph order) → ∃ order, topologicalSort graph = some order

/-- Property: a `none` result means no topological order exists. -/
def topologicalSort_none_prop : Prop :=
  ∀ graph : List (List Nat), topologicalSort graph = none → Pre graph →
    ¬ ∃ order, IsTopOrder graph order

theorem topologicalSort_pre_thm : topologicalSort_pre_prop :=
  fun _ _ h => (topologicalSort_some h).1

theorem topologicalSort_perm_thm : topologicalSort_perm_prop :=
  fun _ _ h => (topologicalSort_some h).2.1

theorem topologicalSort_edges_thm : topologicalSort_edges_prop :=
  fun _ _ h => (topologicalSort_some h).2.2

/-- Helper: a Boolean-search over a list succeeds when some element of the list
satisfies the predicate. -/
theorem find?_some_of_mem {α : Type u} {l : List α} {p : α → Bool} {a : α}
    (ha : a ∈ l) (hp : p a = true) : ∃ b, l.find? p = some b := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    rw [List.find?_cons]
    by_cases hx : p x = true
    · exact ⟨x, by simp [hx]⟩
    · have hx' : p x = false := by revert hx; cases p x <;> simp
      rw [hx']
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact absurd hp hx
      · exact ih ha'

theorem topologicalSort_complete_thm : topologicalSort_complete_prop := by
  intro graph hpre hEx
  obtain ⟨order₀, htop⟩ := hEx
  have hpreb : pre graph = true := (pre_iff_Pre graph).mpr hpre
  have hchk : isTopologicalOrder graph order₀ = true :=
    (isTopologicalOrder_iff graph order₀).mpr htop
  have hmem : order₀ ∈ List.permutations (List.range graph.length) :=
    List.mem_permutations.mpr htop.2.1
  unfold topologicalSort
  rw [if_pos hpreb]
  exact find?_some_of_mem hmem hchk

theorem topologicalSort_none_thm : topologicalSort_none_prop := by
  intro graph hnone hpre hex
  obtain ⟨order, hsome⟩ := topologicalSort_complete_thm graph hpre hex
  rw [hnone] at hsome
  simp at hsome

/-! ## Post-condition -/

/-- Post-condition of `topologicalSort graph`: the conjunction of the stated
properties of the result. -/
def Post_prop (graph : List (List Nat)) (result : Option (List Nat)) : Prop :=
  (∀ order, result = some order → Pre graph) ∧
  (∀ order, result = some order → List.Perm order (List.range graph.length)) ∧
  (∀ order, result = some order →
    ∀ u : Nat, ∀ hu : u < graph.length, ∀ v ∈ graph[u]'hu,
      order.idxOf u < order.idxOf v) ∧
  (Pre graph → (∃ order, IsTopOrder graph order) →
    ∃ order, result = some order) ∧
  (result = none → Pre graph → ¬ ∃ order, IsTopOrder graph order)

/-! ## Property-based tests -/

/-- Executable soundness check (counterpart of `topologicalSort_pre_thm`,
`topologicalSort_perm_thm` and `topologicalSort_edges_thm` combined): any
returned order passes the full checker. -/
def soundCheck (graph : List (List Nat)) : Bool :=
  match topologicalSort graph with
  | none => true
  | some order => isTopologicalOrder graph order

/-- Executable counterpart of `topologicalSort_perm_prop`. -/
def permCheck (graph : List (List Nat)) : Bool :=
  match topologicalSort graph with
  | none => true
  | some order => isPermRange graph.length order

/-- Executable counterpart of `topologicalSort_edges_prop`. -/
def edgeCheck (graph : List (List Nat)) : Bool :=
  match topologicalSort graph with
  | none => true
  | some order =>
    (List.range graph.length).all fun u =>
      (graph[u]!).all fun v => decide (order.idxOf u < order.idxOf v)

/-- Executable counterpart of `topologicalSort_complete_prop`. -/
def completeCheck (graph : List (List Nat)) : Bool :=
  if (List.permutations (List.range graph.length)).any (isTopologicalOrder graph) then
    (topologicalSort graph).isSome
  else
    true

/-- Executable counterpart of `topologicalSort_none_prop`. -/
def noneCheck (graph : List (List Nat)) : Bool :=
  if (topologicalSort graph).isNone then
    !(List.permutations (List.range graph.length)).any (isTopologicalOrder graph)
  else
    true

/-- Executable counterpart of `Post_prop`. -/
def postCheck (graph : List (List Nat)) : Bool :=
  soundCheck graph && permCheck graph && edgeCheck graph &&
  completeCheck graph && noneCheck graph

/-- Truncate an arbitrary sampled graph to at most 4 vertices with entries in
`0 … 4`, keeping the permutation search small while including malformed graphs. -/
def cap (g : List (List Nat)) : List (List Nat) :=
  (g.take 4).map (List.map (· % 5))

-- Randomized PBT: soundness (`pre`/`perm`/`edges` properties)
#eval Plausible.Testable.check (∀ g : List (List Nat), soundCheck (cap g) = true)

-- Randomized PBT: permutation property
#eval Plausible.Testable.check (∀ g : List (List Nat), permCheck (cap g) = true)

-- Randomized PBT: edge property
#eval Plausible.Testable.check (∀ g : List (List Nat), edgeCheck (cap g) = true)

-- Randomized PBT: completeness property
#eval Plausible.Testable.check (∀ g : List (List Nat), completeCheck (cap g) = true)

-- Randomized PBT: `none` property
#eval Plausible.Testable.check (∀ g : List (List Nat), noneCheck (cap g) = true)

-- Randomized PBT: post-condition
#eval Plausible.Testable.check (∀ g : List (List Nat), postCheck (cap g) = true)

/-- All 3-vertex graphs whose adjacency lists are sublists of `[0,1,2,3]`
(vertex `3` is out of range, so malformed graphs are included). -/
def smallGraphs : List (List (List Nat)) :=
  let adj := (List.range 4).sublists
  adj.flatMap fun a => adj.flatMap fun b => adj.map fun c => [a, b, c]

/-- All 2-vertex graphs whose adjacency lists are sublists of `[0,1,2]`. -/
def smallGraphs2 : List (List (List Nat)) :=
  let adj := (List.range 3).sublists
  adj.flatMap fun a => adj.map fun b => [a, b]

-- Bounded (exhaustive) PBTs over all small graphs
example : smallGraphs.all soundCheck = true := by native_decide
example : smallGraphs.all permCheck = true := by native_decide
example : smallGraphs.all edgeCheck = true := by native_decide
example : smallGraphs.all completeCheck = true := by native_decide
example : smallGraphs.all noneCheck = true := by native_decide
example : smallGraphs.all postCheck = true := by native_decide
example : smallGraphs2.all postCheck = true := by native_decide
example : postCheck ([] : List (List Nat)) = true := by native_decide

/-! ## Correctness theorem -/

/-- Correctness: under the precondition, the functional implementation
satisfies the post-condition. -/
theorem topologicalSort_correct (graph : List (List Nat)) (hpre : Pre graph) :
    Post_prop graph (topologicalSort graph) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro order hr
    exact topologicalSort_pre_thm graph order hr
  · intro order hr
    exact topologicalSort_perm_thm graph order hr
  · intro order hr
    exact topologicalSort_edges_thm graph order hr
  · intro _ hex
    exact topologicalSort_complete_thm graph hpre hex
  · intro hnone _
    exact topologicalSort_none_thm graph hnone hpre

/-! ## Imperative implementation -/

/-- Imperative topological sort: a mutable-result loop (in `Id`) over all vertex
permutations, keeping the first one that passes the checker. -/
def topologicalSortImpl (graph : List (List Nat)) : Option (List Nat) := Id.run do
  if pre graph then
    let mut result : Option (List Nat) := none
    for order in List.permutations (List.range graph.length) do
      if result.isNone && isTopologicalOrder graph order then
        result := some order
    return result
  else
    return none

/-! ## Imperative tests -/

example : topologicalSortImpl [[1], [2], []] = some [0, 1, 2] := by native_decide
example : topologicalSortImpl [[1, 2], [3], [3], []] = some [0, 1, 2, 3] := by native_decide
example : topologicalSortImpl ([] : List (List Nat)) = some [] := by native_decide
example : topologicalSortImpl [[], [], []] = some [0, 1, 2] := by native_decide
example : topologicalSortImpl [[2], [], []] = some [0, 1, 2] := by native_decide
example : topologicalSortImpl [[1], [0]] = none := by native_decide
example : topologicalSortImpl [[0]] = none := by native_decide
example : topologicalSortImpl [[2]] = none := by native_decide

#eval topologicalSortImpl [[1, 2], [3], [3], []]
#eval topologicalSortImpl [[1], [0]]

/-! ## Equivalence of the functional and imperative implementations -/

theorem id_bind {α β : Type u} (x : Id α) (f : α → Id β) : x >>= f = f x := rfl
theorem id_pure {α : Type u} (x : α) : (pure x : Id α) = x := rfl

/-- The mutable search loop returns the first permutation passing the checker,
exactly like `List.find?` (once a result is set it never changes). -/
theorem loop_eq (graph : List (List Nat)) (perms : List (List Nat))
    (init : Option (List Nat)) :
    (Id.run do
      let mut result := init
      for order in perms do
        if result.isNone && isTopologicalOrder graph order then
          result := some order
      return result) =
    (match init with
     | some x => some x
     | none => perms.find? (isTopologicalOrder graph)) := by
  induction perms generalizing init with
  | nil => cases init <;> rfl
  | cons a as ih =>
    by_cases h : (init.isNone && isTopologicalOrder graph a) = true
    · have step : (Id.run do
          let mut result := init
          for order in (a :: as) do
            if result.isNone && isTopologicalOrder graph order then
              result := some order
          return result) =
        (Id.run do
          let mut result := some a
          for order in as do
            if result.isNone && isTopologicalOrder graph order then
              result := some order
          return result) := by
        simp only [List.forIn_cons, id_bind, id_pure, Id.run]
        rw [if_pos h]
      rw [step]
      cases init with
      | some x => simp at h
      | none =>
        have h' : isTopologicalOrder graph a = true := h
        rw [ih]
        simp [List.find?, h']
    · have step : (Id.run do
          let mut result := init
          for order in (a :: as) do
            if result.isNone && isTopologicalOrder graph order then
              result := some order
          return result) =
        (Id.run do
          let mut result := init
          for order in as do
            if result.isNone && isTopologicalOrder graph order then
              result := some order
          return result) := by
        simp only [List.forIn_cons, id_bind, id_pure, Id.run]
        rw [if_neg h]
      rw [step]
      cases init with
      | some x => rw [ih]
      | none =>
        have h'' : isTopologicalOrder graph a = false := by
          revert h; cases (isTopologicalOrder graph a) <;> simp
        rw [ih]
        simp [List.find?, h'']

theorem topologicalSortImpl_eq (graph : List (List Nat)) :
    topologicalSortImpl graph = topologicalSort graph := by
  unfold topologicalSort topologicalSortImpl
  by_cases hpre : pre graph = true
  · rw [if_pos hpre, if_pos hpre, loop_eq]
  · rw [if_neg hpre, if_neg hpre]
    rfl

-- Equivalence check on all small graphs
example : smallGraphs.all (fun g =>
    decide (topologicalSortImpl g = topologicalSort g)) = true := by native_decide

end topological_sort
