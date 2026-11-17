import Mathlib
import Plausible

/-!
# Topological Sorting for Finite Directed Graphs

This file provides a Lean 4 formalization of topological sorting for finite directed graphs
represented as adjacency lists (`List (List Nat)`), translated from the Python reference
implementation.

## Overview
- `pre`: Executable validity check ensuring every neighbor index `v` satisfies `v < graph.length`.
- `is_topological_order`: Executable checker verifying that `order` is a permutation of
  `0 .. graph.length - 1` and every directed edge `(u, v)` satisfies
  `order.idxOf u < order.idxOf v`.
- `topological_sort`: Functional implementation searching `(List.range graph.length).permutations`
  for the first valid topological ordering.
- `Pre`, `IsTopologicalOrder`, `Post_prop`: Propositional specifications and properties
  covering soundness, completeness, vertex coverage, edge/reachability ordering, empty/edgeless
  graphs, forward DAGs, malformed graphs, and cycle impossibility.
- `pre_imp`, `is_topological_order_imp`, `topological_sort_imp`: Imperative implementations
  using `Id.run do` with mutable state, together with verified equivalence theorems.
-/

namespace topological_sort

set_option linter.dupNamespace false

/-! ## 4. Implementation (Functional Definitions) -/

/-- Check that `graph` is a valid adjacency-list graph over vertices `0 .. graph.length - 1`. -/
def pre (graph : List (List Nat)) : Bool :=
  let n := graph.length
  graph.all (fun neighbors => neighbors.all (fun v => v < n))

/-- Executable checker verifying whether `order` is a valid topological ordering of `graph`. -/
def is_topological_order (graph : List (List Nat)) (order : List Nat) : Bool :=
  if !pre graph then
    false
  else if order.mergeSort != List.range graph.length then
    false
  else
    (List.range graph.length).all (fun u =>
      (graph[u]!).all (fun v => order.idxOf u < order.idxOf v))

/-- Return the first topological ordering of `graph` in `(List.range graph.length).permutations`,
or `none` if `graph` is malformed or contains a directed cycle. -/
def topological_sort (graph : List (List Nat)) : Option (List Nat) :=
  if !pre graph then
    none
  else
    let n := graph.length
    (List.range n).permutations.find? (fun order => is_topological_order graph order)

/-- Executable test suite mirroring the Python `check` function. -/
def check (candidate : List (List Nat) → Option (List Nat)) : Bool :=
  let g1 : List (List Nat) := [[1], [2], []]
  let c1 := candidate g1 == some [0, 1, 2]
  let c1_valid := match candidate g1 with
    | some order1 => is_topological_order g1 order1
    | none => false

  let g2 : List (List Nat) := [[1, 2], [3], [3], []]
  let c2_valid := match candidate g2 with
    | some order2 => is_topological_order g2 order2 && order2.mergeSort == [0, 1, 2, 3]
    | none => false

  let g3 : List (List Nat) := []
  let c3 := candidate g3 == some []

  let g4 : List (List Nat) := [[], [], []]
  let c4 := candidate g4 == some [0, 1, 2]

  let g5 : List (List Nat) := [[2], [], []]
  let c5_valid := match candidate g5 with
    | some order5 => is_topological_order g5 order5 && decide (order5.idxOf 0 < order5.idxOf 2)
    | none => false

  let c_cycle := candidate [[1], [0]] == none
  let c_self_loop := candidate [[0]] == none
  let c_malformed := candidate [[2]] == none

  c1 && c1_valid && c2_valid && c3 && c4 && c5_valid && c_cycle && c_self_loop && c_malformed

/-! ## 5. Unit Tests -/

#eval topological_sort [[1], [2], []]
#eval topological_sort [[1, 2], [3], [3], []]
#eval topological_sort []
#eval topological_sort [[], [], []]
#eval topological_sort [[2], [], []]
#eval topological_sort [[1], [0]]
#eval topological_sort [[0]]
#eval topological_sort [[2]]
#eval check topological_sort

example : topological_sort [[1], [2], []] = some [0, 1, 2] := by native_decide
example : is_topological_order [[1], [2], []] [0, 1, 2] = true := by native_decide
example : topological_sort [[1, 2], [3], [3], []] = some [0, 1, 2, 3] := by native_decide
example : is_topological_order [[1, 2], [3], [3], []] [0, 1, 2, 3] = true := by native_decide
example : is_topological_order [[1, 2], [3], [3], []] [0, 2, 1, 3] = true := by native_decide
example : topological_sort [] = some [] := by native_decide
example : topological_sort [[], [], []] = some [0, 1, 2] := by native_decide
example : topological_sort [[2], [], []] = some [0, 1, 2] := by native_decide
example : is_topological_order [[2], [], []] [0, 1, 2] = true := by native_decide
example : topological_sort [[1], [0]] = none := by native_decide
example : topological_sort [[0]] = none := by native_decide
example : topological_sort [[2]] = none := by native_decide
example : topological_sort [[], [0], [1]] = some [2, 1, 0] := by native_decide
example : check topological_sort = true := by native_decide

/-! ## 6. Pre-condition Predicate -/

/-- Propositional precondition: every neighbor vertex in every adjacency list is `< graph.length`. -/
def Pre (graph : List (List Nat)) : Prop :=
  ∀ neighbors ∈ graph, ∀ v ∈ neighbors, v < graph.length

/-- Equivalence between executable `pre` and propositional `Pre`. -/
theorem pre_iff_Pre (graph : List (List Nat)) :
    pre graph = true ↔ Pre graph := by
  simp [pre, Pre, List.all_eq_true]

instance (graph : List (List Nat)) : Decidable (Pre graph) :=
  decidable_of_iff (pre graph = true) (pre_iff_Pre graph)

/-- Indexed formulation of `Pre`. -/
theorem Pre_iff_getElem (graph : List (List Nat)) :
    Pre graph ↔ ∀ (u : Nat) (hu : u < graph.length), ∀ v ∈ graph[u], v < graph.length := by
  simp only [Pre, List.mem_iff_getElem]
  constructor
  · intro h u hu v hv
    exact h graph[u] ⟨u, hu, rfl⟩ v hv
  · rintro h neighbors ⟨u, hu, rfl⟩ v hv
    exact h u hu v hv

/-! ## 7. Property Propositions and Theorems -/

/-- Helper theorem: `order.mergeSort = List.range n` iff `order.Perm (List.range n)`. -/
theorem mergeSort_eq_range_iff (order : List Nat) (n : Nat) :
    order.mergeSort = List.range n ↔ order.Perm (List.range n) := by
  constructor
  · intro h
    rw [← h]
    exact (List.mergeSort_perm order (· ≤ ·)).symm
  · intro h
    have hs1 : List.Sorted (· ≤ ·) (order.mergeSort (fun a b => decide (a ≤ b))) :=
      List.sorted_mergeSort' (· ≤ ·) order
    have hs2 : List.Sorted (· ≤ ·) (List.range n) :=
      List.pairwise_lt_range.imp Nat.le_of_lt
    exact List.eq_of_perm_of_sorted ((List.mergeSort_perm order _).trans h) hs1 hs2

/-- Helper theorem: `order.Perm (List.range n)` iff `order.Nodup` and `∀ v, v ∈ order ↔ v < n`. -/
theorem perm_range_iff (order : List Nat) (n : Nat) :
    order.Perm (List.range n) ↔ order.Nodup ∧ ∀ v, v ∈ order ↔ v < n := by
  constructor
  · intro h
    refine ⟨h.nodup_iff.mpr List.nodup_range, fun v => ?_⟩
    rw [h.mem_iff, List.mem_range]
  · rintro ⟨hnodup, hmem⟩
    exact (List.perm_ext_iff_of_nodup hnodup List.nodup_range).mpr
      (fun v => by rw [hmem, List.mem_range])

/-- Helper theorem: `(List.range n).idxOf u = u` for `u < n`. -/
theorem idxOf_range {n u : Nat} (h : u < n) : (List.range n).idxOf u = u := by
  have h1 : u < (List.range n).length := by simpa using h
  have h2 := List.idxOf_getElem List.nodup_range u h1
  simpa using h2

/-- Propositional specification of a valid topological ordering of `graph`. -/
def IsTopologicalOrder (graph : List (List Nat)) (order : List Nat) : Prop :=
  Pre graph ∧
  order.Perm (List.range graph.length) ∧
  ∀ (u : Nat) (hu : u < graph.length), ∀ v ∈ graph[u], order.idxOf u < order.idxOf v

/-- Equivalence between executable `is_topological_order` and propositional `IsTopologicalOrder`. -/
theorem is_topological_order_iff (graph : List (List Nat)) (order : List Nat) :
    is_topological_order graph order = true ↔ IsTopologicalOrder graph order := by
  unfold is_topological_order IsTopologicalOrder
  by_cases hpre : pre graph = true
  · have hPre : Pre graph := (pre_iff_Pre graph).mp hpre
    by_cases hsort : order.mergeSort = List.range graph.length
    · have hPerm : order.Perm (List.range graph.length) :=
        (mergeSort_eq_range_iff order graph.length).mp hsort
      have hne : (order.mergeSort != List.range graph.length) = false :=
        bne_eq_false_iff_eq.mpr hsort
      simp only [hpre, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hne,
        List.all_eq_true, List.mem_range, decide_eq_true_eq]
      constructor
      · intro hedge
        refine ⟨hPre, hPerm, fun u hu v hv => ?_⟩
        have hget : graph[u]! = graph[u] := getElem!_pos graph u hu
        exact hedge u hu v (hget ▸ hv)
      · rintro ⟨_, _, hedge⟩ u hu v hv
        have hget : graph[u]! = graph[u] := getElem!_pos graph u hu
        exact hedge u hu v (hget ▸ hv)
    · have hNotPerm : ¬ order.Perm (List.range graph.length) :=
        fun hp => hsort ((mergeSort_eq_range_iff order graph.length).mpr hp)
      have hne : (order.mergeSort != List.range graph.length) = true :=
        bne_iff_ne.mpr hsort
      simp [hpre, hne, hNotPerm]
  · have hNotPre : ¬ Pre graph := fun hp => hpre ((pre_iff_Pre graph).mpr hp)
    have hpre_false : pre graph = false := Bool.eq_false_iff.mpr hpre
    simp [hpre_false, hNotPre]

instance (graph : List (List Nat)) (order : List Nat) :
    Decidable (IsTopologicalOrder graph order) :=
  decidable_of_iff (is_topological_order graph order = true) (is_topological_order_iff graph order)

/-- Directed edge relation on vertices of `graph`. -/
def IsEdge (graph : List (List Nat)) (u v : Nat) : Prop :=
  ∃ (hu : u < graph.length), v ∈ graph[u]

/-- A directed graph has a cycle if some vertex can reach itself via a non-empty directed walk. -/
def HasCycle (graph : List (List Nat)) : Prop :=
  ∃ u, Relation.TransGen (IsEdge graph) u u

/-- Property 1: Malformed adjacency lists (violating `Pre`) return `none`. -/
def malformed_none_prop (graph : List (List Nat)) : Prop :=
  ¬ Pre graph → topological_sort graph = none

theorem malformed_none_thm (graph : List (List Nat)) : malformed_none_prop graph := by
  intro hnot
  unfold topological_sort
  have hpre : pre graph = false :=
    Bool.eq_false_iff.mpr (fun h => hnot ((pre_iff_Pre graph).mp h))
  simp [hpre]

/-- Property 2: Soundness — any returned ordering satisfies `Pre`, `is_topological_order`,
and `IsTopologicalOrder`. -/
def soundness_prop (graph : List (List Nat)) : Prop :=
  ∀ order, topological_sort graph = some order →
    Pre graph ∧ is_topological_order graph order = true ∧ IsTopologicalOrder graph order

theorem soundness_thm (graph : List (List Nat)) : soundness_prop graph := by
  intro order hsort
  unfold topological_sort at hsort
  by_cases hpre : pre graph = true
  · simp only [hpre, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hsort
    have htopo : is_topological_order graph order = true := List.find?_some hsort
    exact ⟨(pre_iff_Pre graph).mp hpre, htopo, (is_topological_order_iff graph order).mp htopo⟩
  · have hpre_false : pre graph = false := Bool.eq_false_iff.mpr hpre
    simp [hpre_false] at hsort

/-- Property 3: Vertex coverage — any returned ordering is a permutation of `0 .. n - 1`,
has length `n`, contains no duplicates, and includes every vertex `0 .. n - 1` exactly once. -/
def vertex_coverage_prop (graph : List (List Nat)) : Prop :=
  ∀ order, topological_sort graph = some order →
    order.Perm (List.range graph.length) ∧
    order.length = graph.length ∧
    order.Nodup ∧
    (∀ v, v ∈ order ↔ v < graph.length)

theorem vertex_coverage_thm (graph : List (List Nat)) : vertex_coverage_prop graph := by
  intro order hsort
  have ⟨_, _, _, hperm, _⟩ := soundness_thm graph order hsort
  have ⟨hnodup, hmem⟩ := (perm_range_iff order graph.length).mp hperm
  have hlen : order.length = graph.length := by
    simpa using hperm.length_eq
  exact ⟨hperm, hlen, hnodup, hmem⟩

/-- Property 4: Edge ordering — in any returned ordering, every directed edge `(u, v)`
satisfies `order.idxOf u < order.idxOf v`. -/
def edge_ordering_prop (graph : List (List Nat)) : Prop :=
  ∀ order, topological_sort graph = some order →
    ∀ (u : Nat) (hu : u < graph.length), ∀ v ∈ graph[u], order.idxOf u < order.idxOf v

theorem edge_ordering_thm (graph : List (List Nat)) : edge_ordering_prop graph := by
  intro order hsort
  have ⟨_, _, _, _, hedge⟩ := soundness_thm graph order hsort
  exact hedge

/-- Helper lemma: indices strictly increase along any non-empty directed walk in a valid
topological ordering. -/
theorem idxOf_lt_of_transGen {graph : List (List Nat)} {order : List Nat}
    (hedge : ∀ (u : Nat) (hu : u < graph.length), ∀ v ∈ graph[u], order.idxOf u < order.idxOf v)
    {u v : Nat} (hpath : Relation.TransGen (IsEdge graph) u v) :
    order.idxOf u < order.idxOf v := by
  induction hpath with
  | single h =>
    rcases h with ⟨hu, hv⟩
    exact hedge u hu _ hv
  | tail _ h ih =>
    rcases h with ⟨hw, hv⟩
    exact Nat.lt_trans ih (hedge _ hw _ hv)

/-- Property 5: Reachability ordering — in any returned ordering, if `v` is reachable from `u`
via a non-empty directed path, then `order.idxOf u < order.idxOf v`. -/
def reachability_ordering_prop (graph : List (List Nat)) : Prop :=
  ∀ order, topological_sort graph = some order →
    ∀ u v, Relation.TransGen (IsEdge graph) u v → order.idxOf u < order.idxOf v

theorem reachability_ordering_thm (graph : List (List Nat)) : reachability_ordering_prop graph := by
  intro order hsort u v hpath
  exact idxOf_lt_of_transGen (edge_ordering_thm graph order hsort) hpath

/-- Property 6: Completeness — `topological_sort graph = none` iff no topological ordering
exists, and `topological_sort graph` returns `some order` iff a valid topological ordering exists. -/
def completeness_prop (graph : List (List Nat)) : Prop :=
  (topological_sort graph = none ↔ ∀ order, ¬ IsTopologicalOrder graph order) ∧
  ((∃ candidate, IsTopologicalOrder graph candidate) ↔ ∃ order, topological_sort graph = some order)

theorem completeness_thm (graph : List (List Nat)) : completeness_prop graph := by
  have h_none_iff : topological_sort graph = none ↔ ∀ order, ¬ IsTopologicalOrder graph order := by
    constructor
    · intro hnone order htopo
      have hPre : Pre graph := htopo.1
      have hpre : pre graph = true := (pre_iff_Pre graph).mpr hPre
      have hperm : order ∈ (List.range graph.length).permutations :=
        List.mem_permutations.mpr htopo.2.1
      have hbool : is_topological_order graph order = true :=
        (is_topological_order_iff graph order).mpr htopo
      unfold topological_sort at hnone
      simp only [hpre, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.find?_eq_none] at hnone
      exact hnone order hperm hbool
    · intro hno
      cases hsort : topological_sort graph with
      | none => rfl
      | some order =>
        exfalso
        exact hno order (soundness_thm graph order hsort).2.2
  refine ⟨h_none_iff, ?_⟩
  constructor
  · rintro ⟨candidate, hcand⟩
    cases hsort : topological_sort graph with
    | some order => exact ⟨order, rfl⟩
    | none =>
      exfalso
      exact (h_none_iff.mp hsort) candidate hcand
  · rintro ⟨order, hsort⟩
    exact ⟨order, (soundness_thm graph order hsort).2.2⟩

/-- Property 7: Empty graph has the empty topological order `[]`. -/
def empty_graph_prop (graph : List (List Nat)) : Prop :=
  graph = [] → topological_sort graph = some []

theorem empty_graph_thm (graph : List (List Nat)) : empty_graph_prop graph := by
  rintro rfl
  simp [topological_sort, pre, is_topological_order, List.permutations]

/-- Property 8: Forward DAG canonical order — if `Pre graph` holds and every edge `(u, v)`
satisfies `u < v`, then `topological_sort graph = some (List.range graph.length)`. -/
def forward_dag_prop (graph : List (List Nat)) : Prop :=
  Pre graph →
  (∀ (u : Nat) (hu : u < graph.length), ∀ v ∈ graph[u], u < v) →
  topological_sort graph = some (List.range graph.length)

theorem forward_dag_thm (graph : List (List Nat)) : forward_dag_prop graph := by
  intro hPre hforward
  have hpre : pre graph = true := (pre_iff_Pre graph).mpr hPre
  have htopo : IsTopologicalOrder graph (List.range graph.length) := by
    refine ⟨hPre, List.Perm.refl _, fun u hu v hv => ?_⟩
    have hv_lt : v < graph.length := (Pre_iff_getElem graph).mp hPre u hu v hv
    rw [idxOf_range hu, idxOf_range hv_lt]
    exact hforward u hu v hv
  have hbool : is_topological_order graph (List.range graph.length) = true :=
    (is_topological_order_iff graph (List.range graph.length)).mpr htopo
  unfold topological_sort
  simp [hpre, List.permutations, hbool]

/-- Property 9: Disconnected edgeless graphs return `some (List.range graph.length)`. -/
def edgeless_graph_prop (graph : List (List Nat)) : Prop :=
  (∀ neighbors ∈ graph, neighbors = []) →
  topological_sort graph = some (List.range graph.length)

theorem edgeless_graph_thm (graph : List (List Nat)) : edgeless_graph_prop graph := by
  intro hedgeless
  have hPre : Pre graph := by
    intro neighbors hmem v hv
    rw [hedgeless neighbors hmem] at hv
    cases hv
  apply forward_dag_thm graph hPre
  intro u hu v hv
  have hmem : graph[u] ∈ graph := List.getElem_mem hu
  rw [hedgeless graph[u] hmem] at hv
  cases hv

/-- Property 10: Cycle impossibility — if `graph` has any directed cycle,
`topological_sort graph = none`. -/
def cycle_none_prop (graph : List (List Nat)) : Prop :=
  HasCycle graph → topological_sort graph = none

theorem cycle_none_thm (graph : List (List Nat)) : cycle_none_prop graph := by
  rintro ⟨u, hcycle⟩
  cases hsort : topological_sort graph with
  | none => rfl
  | some order =>
    exfalso
    have hlt := reachability_ordering_thm graph order hsort u u hcycle
    exact Nat.lt_irrefl _ hlt

/-- Property 11: Self-loop impossibility — if any vertex has an edge to itself,
`topological_sort graph = none`. -/
def self_loop_none_prop (graph : List (List Nat)) : Prop :=
  (∃ (u : Nat) (hu : u < graph.length), u ∈ graph[u]) →
  topological_sort graph = none

theorem self_loop_none_thm (graph : List (List Nat)) : self_loop_none_prop graph := by
  rintro ⟨u, hu, hloop⟩
  exact cycle_none_thm graph ⟨u, Relation.TransGen.single ⟨hu, hloop⟩⟩

/-- Property 12: Two-cycle impossibility — if any two vertices have mutual edges between them,
`topological_sort graph = none`. -/
def two_cycle_none_prop (graph : List (List Nat)) : Prop :=
  (∃ (u v : Nat) (hu : u < graph.length) (hv : v < graph.length),
    v ∈ graph[u] ∧ u ∈ graph[v]) →
  topological_sort graph = none

theorem two_cycle_none_thm (graph : List (List Nat)) : two_cycle_none_prop graph := by
  rintro ⟨u, v, hu, hv, huv, hvu⟩
  apply cycle_none_thm graph
  exact ⟨u, Relation.TransGen.tail (Relation.TransGen.single ⟨hu, huv⟩) ⟨hv, hvu⟩⟩

/-- Property 13: Unique vertex count — in any returned ordering, every vertex `v < graph.length`
appears with multiplicity `1`, and every `v ≥ graph.length` appears with multiplicity `0`. -/
def unique_vertex_count_prop (graph : List (List Nat)) : Prop :=
  ∀ order, topological_sort graph = some order →
    (∀ v < graph.length, order.count v = 1) ∧
    (∀ v, graph.length ≤ v → order.count v = 0)

theorem unique_vertex_count_thm (graph : List (List Nat)) : unique_vertex_count_prop graph := by
  intro order hsort
  have ⟨hperm, _, _, _⟩ := vertex_coverage_thm graph order hsort
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · rw [hperm.count_eq]
    exact List.count_eq_one_of_mem List.nodup_range (List.mem_range.mpr hv)
  · rw [hperm.count_eq]
    exact List.count_eq_zero.mpr (by simp [List.mem_range, Nat.not_lt.mpr hv])

/-- Property 14: Position bijection — in any returned ordering, `order.idxOf` and indexing
into `order` form inverse bijections on `0 .. graph.length - 1`. -/
def index_bijection_prop (graph : List (List Nat)) : Prop :=
  ∀ order, topological_sort graph = some order →
    (∀ v < graph.length,
      ∃ (hi : order.idxOf v < order.length), order[order.idxOf v] = v) ∧
    (∀ (i : Nat) (hi : i < order.length),
      order[i] < graph.length ∧ order.idxOf order[i] = i) ∧
    (∀ u < graph.length, ∀ v < graph.length,
      order.idxOf u = order.idxOf v → u = v)

theorem index_bijection_thm (graph : List (List Nat)) : index_bijection_prop graph := by
  intro order hsort
  have ⟨_, _, hnodup, hmem⟩ := vertex_coverage_thm graph order hsort
  refine ⟨fun v hv => ?_, fun i hi => ?_, fun u hu v hv heq => ?_⟩
  · have hvin : v ∈ order := (hmem v).mpr hv
    have hidx : order.idxOf v < order.length := List.idxOf_lt_length_of_mem hvin
    exact ⟨hidx, List.getElem_idxOf hidx⟩
  · have hget_in : order[i] ∈ order := List.getElem_mem hi
    exact ⟨(hmem order[i]).mp hget_in, List.idxOf_getElem hnodup i hi⟩
  · have hu_in : u ∈ order := (hmem u).mpr hu
    have hv_in : v ∈ order := (hmem v).mpr hv
    have h1 : order.idxOf u < order.length := List.idxOf_lt_length_of_mem hu_in
    have h2 : order.idxOf v < order.length := List.idxOf_lt_length_of_mem hv_in
    have hg1 := List.getElem_idxOf h1
    have hg2 := List.getElem_idxOf h2
    rw [← hg1, ← hg2]
    simp [heq]

/-- Property 15: First-permutation selection — any returned ordering is the first candidate
in `(List.range graph.length).permutations` satisfying `is_topological_order graph`. -/
def first_permutation_prop (graph : List (List Nat)) : Prop :=
  ∀ order, topological_sort graph = some order →
    ∃ as bs,
      (List.range graph.length).permutations = as ++ order :: bs ∧
      is_topological_order graph order = true ∧
      ∀ cand ∈ as, is_topological_order graph cand = false ∧ ¬ IsTopologicalOrder graph cand

theorem first_permutation_thm (graph : List (List Nat)) : first_permutation_prop graph := by
  intro order hsort
  have ⟨hPre, _, _⟩ := soundness_thm graph order hsort
  have hpre : pre graph = true := (pre_iff_Pre graph).mpr hPre
  unfold topological_sort at hsort
  simp only [hpre, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    List.find?_eq_some_iff_append] at hsort
  rcases hsort with ⟨htopo, as, bs, hperm_eq, hbefore⟩
  refine ⟨as, bs, hperm_eq, htopo, fun cand hcand => ?_⟩
  have hfalse : is_topological_order graph cand = false := by
    simpa using hbefore cand hcand
  refine ⟨hfalse, fun hCandTopo => ?_⟩
  have htrue : is_topological_order graph cand = true :=
    (is_topological_order_iff graph cand).mpr hCandTopo
  rw [htrue] at hfalse
  contradiction

/-! ## 8. Post-condition -/

/-- Post-condition combining all core behavioral properties of `topological_sort`. -/
def Post_prop (graph : List (List Nat)) : Prop :=
  malformed_none_prop graph ∧
  soundness_prop graph ∧
  vertex_coverage_prop graph ∧
  edge_ordering_prop graph ∧
  reachability_ordering_prop graph ∧
  completeness_prop graph ∧
  empty_graph_prop graph ∧
  forward_dag_prop graph ∧
  edgeless_graph_prop graph ∧
  cycle_none_prop graph ∧
  self_loop_none_prop graph ∧
  two_cycle_none_prop graph ∧
  unique_vertex_count_prop graph ∧
  index_bijection_prop graph ∧
  first_permutation_prop graph

/-! ## 9. Property-Based Tests (PBTs) -/

/-- Representative sample of graphs (empty, edgeless, connected DAGs, disconnected DAGs,
cycles, self-loops, and malformed adjacency lists) for bounded PBTs. -/
def sample_graphs : List (List (List Nat)) :=
  [ [],
    [[]],
    [[0]],
    [[1]],
    [[2]],
    [[], []],
    [[1], []],
    [[], [0]],
    [[1], [0]],
    [[0], []],
    [[], [1]],
    [[1, 2], []],
    [[], [], []],
    [[1], [2], []],
    [[2], [], []],
    [[], [0], [1]],
    [[1, 2], [2], []],
    [[1], [2], [0]],
    [[1, 2], [3], [3], []],
    [[3], [0], [1], [2]] ]

/-- Executable boolean check for `malformed_none_prop`. -/
def check_malformed_none (graph : List (List Nat)) : Bool :=
  if !pre graph then topological_sort graph == none else true

/-- Executable boolean check for `soundness_prop`. -/
def check_soundness (graph : List (List Nat)) : Bool :=
  match topological_sort graph with
  | none => true
  | some order => pre graph && is_topological_order graph order

/-- Executable boolean check for `vertex_coverage_prop`. -/
def check_vertex_coverage (graph : List (List Nat)) : Bool :=
  match topological_sort graph with
  | none => true
  | some order =>
    order.mergeSort == List.range graph.length &&
    order.length == graph.length &&
    decide order.Nodup &&
    (List.range graph.length).all (fun v => decide (v ∈ order)) &&
    order.all (fun v => decide (v < graph.length))

/-- Executable boolean check for `edge_ordering_prop`. -/
def check_edge_ordering (graph : List (List Nat)) : Bool :=
  match topological_sort graph with
  | none => true
  | some order =>
    (List.range graph.length).all (fun u =>
      (graph[u]!).all (fun v => decide (order.idxOf u < order.idxOf v)))

/-- Executable boolean check for 2-step `reachability_ordering_prop`. -/
def check_reachability_ordering (graph : List (List Nat)) : Bool :=
  match topological_sort graph with
  | none => true
  | some order =>
    (List.range graph.length).all (fun u =>
      (graph[u]!).all (fun w =>
        decide (order.idxOf u < order.idxOf w) &&
        (if w < graph.length then
          (graph[w]!).all (fun v => decide (order.idxOf u < order.idxOf v))
        else true)))

/-- Executable boolean check for `completeness_prop`. -/
def check_completeness (graph : List (List Nat)) : Bool :=
  let has_valid_perm :=
    (List.range graph.length).permutations.any (fun cand => is_topological_order graph cand)
  match topological_sort graph with
  | none => !has_valid_perm
  | some order => has_valid_perm && is_topological_order graph order

/-- Executable boolean check for `empty_graph_prop`. -/
def check_empty_graph (graph : List (List Nat)) : Bool :=
  if graph.isEmpty then topological_sort graph == some [] else true

/-- Executable boolean check for `forward_dag_prop`. -/
def check_forward_dag (graph : List (List Nat)) : Bool :=
  let is_forward :=
    pre graph &&
    (List.range graph.length).all (fun u => (graph[u]!).all (fun v => decide (u < v)))
  if is_forward then topological_sort graph == some (List.range graph.length) else true

/-- Executable boolean check for `edgeless_graph_prop`. -/
def check_edgeless_graph (graph : List (List Nat)) : Bool :=
  if graph.all List.isEmpty then
    topological_sort graph == some (List.range graph.length)
  else
    true

/-- Executable boolean check for `self_loop_none_prop`. -/
def check_self_loop_none (graph : List (List Nat)) : Bool :=
  let has_self_loop :=
    (List.range graph.length).any (fun u => decide (u ∈ graph[u]!))
  if has_self_loop then topological_sort graph == none else true

/-- Executable boolean check for `two_cycle_none_prop`. -/
def check_two_cycle_none (graph : List (List Nat)) : Bool :=
  let has_two_cycle :=
    (List.range graph.length).any (fun u =>
      (List.range graph.length).any (fun v =>
        decide (v ∈ graph[u]! ∧ u ∈ graph[v]!)))
  if has_two_cycle then topological_sort graph == none else true

/-- Executable boolean check for `cycle_none_prop` (up to 3-step cycles). -/
def check_cycle_none (graph : List (List Nat)) : Bool :=
  let has_short_cycle :=
    (List.range graph.length).any (fun u =>
      (graph[u]!).any (fun v =>
        decide (v == u) ||
        (if v < graph.length then
          (graph[v]!).any (fun w =>
            decide (w == u) ||
            (if w < graph.length then (graph[w]!).any (fun z => decide (z == u)) else false))
        else false)))
  if has_short_cycle then topological_sort graph == none else true

/-- Executable boolean check for `unique_vertex_count_prop`. -/
def check_unique_vertex_count (graph : List (List Nat)) : Bool :=
  match topological_sort graph with
  | none => true
  | some order =>
    (List.range graph.length).all (fun v => order.count v == 1) &&
    order.count graph.length == 0

/-- Executable boolean check for `index_bijection_prop`. -/
def check_index_bijection (graph : List (List Nat)) : Bool :=
  match topological_sort graph with
  | none => true
  | some order =>
    let n := graph.length
    (List.range n).all (fun v =>
      order.idxOf v < order.length && order[order.idxOf v]! == v) &&
    (List.range order.length).all (fun i =>
      order[i]! < n && order.idxOf order[i]! == i)

/-- Executable boolean check for `first_permutation_prop`. -/
def check_first_permutation (graph : List (List Nat)) : Bool :=
  match topological_sort graph with
  | none => true
  | some order =>
    let perms := (List.range graph.length).permutations
    let idx := perms.idxOf order
    idx < perms.length &&
    is_topological_order graph order &&
    (perms.take idx).all (fun cand => !is_topological_order graph cand)

/-- Executable boolean check for `Post_prop`. -/
def check_post (graph : List (List Nat)) : Bool :=
  check_malformed_none graph &&
  check_soundness graph &&
  check_vertex_coverage graph &&
  check_edge_ordering graph &&
  check_reachability_ordering graph &&
  check_completeness graph &&
  check_empty_graph graph &&
  check_forward_dag graph &&
  check_edgeless_graph graph &&
  check_cycle_none graph &&
  check_self_loop_none graph &&
  check_two_cycle_none graph &&
  check_unique_vertex_count graph &&
  check_index_bijection graph &&
  check_first_permutation graph

-- Bounded PBTs over `sample_graphs`
example : sample_graphs.all check_malformed_none = true := by native_decide
example : sample_graphs.all check_soundness = true := by native_decide
example : sample_graphs.all check_vertex_coverage = true := by native_decide
example : sample_graphs.all check_edge_ordering = true := by native_decide
example : sample_graphs.all check_reachability_ordering = true := by native_decide
example : sample_graphs.all check_completeness = true := by native_decide
example : sample_graphs.all check_empty_graph = true := by native_decide
example : sample_graphs.all check_forward_dag = true := by native_decide
example : sample_graphs.all check_edgeless_graph = true := by native_decide
example : sample_graphs.all check_cycle_none = true := by native_decide
example : sample_graphs.all check_self_loop_none = true := by native_decide
example : sample_graphs.all check_two_cycle_none = true := by native_decide
example : sample_graphs.all check_unique_vertex_count = true := by native_decide
example : sample_graphs.all check_index_bijection = true := by native_decide
example : sample_graphs.all check_first_permutation = true := by native_decide
example : sample_graphs.all check_post = true := by native_decide

-- Randomized PBTs using Plausible (size-bounded to keep factorial permutation search fast)
#eval Plausible.Testable.check (∀ g : List (List Nat), check_malformed_none (g.take 4) = true) { maxSize := 4 }
#eval Plausible.Testable.check (∀ g : List (List Nat), check_soundness (g.take 4) = true) { maxSize := 4 }
#eval Plausible.Testable.check (∀ g : List (List Nat), check_vertex_coverage (g.take 4) = true) { maxSize := 4 }
#eval Plausible.Testable.check (∀ g : List (List Nat), check_edge_ordering (g.take 4) = true) { maxSize := 4 }
#eval Plausible.Testable.check (∀ g : List (List Nat), check_reachability_ordering (g.take 4) = true) { maxSize := 4 }
#eval Plausible.Testable.check (∀ g : List (List Nat), check_completeness (g.take 4) = true) { maxSize := 4 }
#eval Plausible.Testable.check (∀ g : List (List Nat), check_empty_graph (g.take 4) = true) { maxSize := 4 }
#eval Plausible.Testable.check (∀ g : List (List Nat), check_forward_dag (g.take 4) = true) { maxSize := 4 }
#eval Plausible.Testable.check (∀ g : List (List Nat), check_edgeless_graph (g.take 4) = true) { maxSize := 4 }
#eval Plausible.Testable.check (∀ g : List (List Nat), check_cycle_none (g.take 4) = true) { maxSize := 4 }
#eval Plausible.Testable.check (∀ g : List (List Nat), check_self_loop_none (g.take 4) = true) { maxSize := 4 }
#eval Plausible.Testable.check (∀ g : List (List Nat), check_two_cycle_none (g.take 4) = true) { maxSize := 4 }
#eval Plausible.Testable.check (∀ g : List (List Nat), check_unique_vertex_count (g.take 4) = true) { maxSize := 4 }
#eval Plausible.Testable.check (∀ g : List (List Nat), check_index_bijection (g.take 4) = true) { maxSize := 4 }
#eval Plausible.Testable.check (∀ g : List (List Nat), check_first_permutation (g.take 4) = true) { maxSize := 4 }
#eval Plausible.Testable.check (∀ g : List (List Nat), check_post (g.take 4) = true) { maxSize := 4 }

/-! ## 10. Correctness Theorem (`Pre -> Post`) -/

/-- Unconditional post-condition theorem holding for all graphs. -/
theorem topological_sort_post (graph : List (List Nat)) : Post_prop graph :=
  ⟨malformed_none_thm graph,
   soundness_thm graph,
   vertex_coverage_thm graph,
   edge_ordering_thm graph,
   reachability_ordering_thm graph,
   completeness_thm graph,
   empty_graph_thm graph,
   forward_dag_thm graph,
   edgeless_graph_thm graph,
   cycle_none_thm graph,
   self_loop_none_thm graph,
   two_cycle_none_thm graph,
   unique_vertex_count_thm graph,
   index_bijection_thm graph,
   first_permutation_thm graph⟩

/-- Main correctness theorem: `Pre graph → Post_prop graph`. -/
theorem topological_sort_correct (graph : List (List Nat)) (_hpre : Pre graph) :
    Post_prop graph :=
  topological_sort_post graph

/-! ## 11. Imperative Implementation -/

/-- Imperative helper for universal quantification over a list using `Id.run do` and mutable state. -/
def all_imp (p : α → Bool) (l : List α) : Bool := Id.run do
  let mut ok : Bool := true
  for x in l do
    if !p x then
      ok := false
      break
  return ok

/-- Imperative helper for finding the first element satisfying `p` using `Id.run do` and mutable state. -/
def find_imp (p : α → Bool) (l : List α) : Option α := Id.run do
  let mut result : Option α := none
  for x in l do
    if p x then
      result := some x
      break
  return result

/-- Imperative implementation of `pre` using `Id.run do` and mutable state. -/
def pre_imp (graph : List (List Nat)) : Bool := Id.run do
  let n := graph.length
  let mut valid : Bool := true
  for neighbors in graph do
    if !all_imp (fun v => v < n) neighbors then
      valid := false
      break
  return valid

/-- Imperative implementation of `is_topological_order` using `Id.run do` and mutable state. -/
def is_topological_order_imp (graph : List (List Nat)) (order : List Nat) : Bool := Id.run do
  if !pre_imp graph then
    return false
  if order.mergeSort != List.range graph.length then
    return false
  let mut ok : Bool := true
  for u in List.range graph.length do
    if !all_imp (fun v => order.idxOf u < order.idxOf v) (graph[u]!) then
      ok := false
      break
  return ok

/-- Imperative implementation of `topological_sort` using `Id.run do` and mutable state. -/
def topological_sort_imp (graph : List (List Nat)) : Option (List Nat) := Id.run do
  if !pre_imp graph then
    return none
  let n := graph.length
  let mut result : Option (List Nat) := none
  for candidate in (List.range n).permutations do
    if is_topological_order_imp graph candidate then
      result := some candidate
      break
  return result

/-! ## 12. Imperative Tests -/

#eval topological_sort_imp [[1], [2], []]
#eval topological_sort_imp [[1, 2], [3], [3], []]
#eval topological_sort_imp []
#eval topological_sort_imp [[], [], []]
#eval topological_sort_imp [[2], [], []]
#eval topological_sort_imp [[1], [0]]
#eval topological_sort_imp [[0]]
#eval topological_sort_imp [[2]]
#eval check topological_sort_imp

example : topological_sort_imp [[1], [2], []] = some [0, 1, 2] := by native_decide
example : is_topological_order_imp [[1], [2], []] [0, 1, 2] = true := by native_decide
example : topological_sort_imp [[1, 2], [3], [3], []] = some [0, 1, 2, 3] := by native_decide
example : topological_sort_imp [] = some [] := by native_decide
example : topological_sort_imp [[], [], []] = some [0, 1, 2] := by native_decide
example : topological_sort_imp [[2], [], []] = some [0, 1, 2] := by native_decide
example : topological_sort_imp [[1], [0]] = none := by native_decide
example : topological_sort_imp [[0]] = none := by native_decide
example : topological_sort_imp [[2]] = none := by native_decide
example : check topological_sort_imp = true := by native_decide
example : sample_graphs.all (fun g => topological_sort g == topological_sort_imp g) = true := by
  native_decide

/-! ## 13. Equivalence Theorem (Functional = Imperative) -/

/-- Equivalence between `all_imp` and `List.all`. -/
theorem all_imp_eq_all (p : α → Bool) (l : List α) :
    all_imp p l = l.all p := by
  unfold all_imp
  simp only [List.forIn_eq_foldlM]
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldlM_cons, List.all_cons]
    cases hx : p x
    · simp only [Bool.not_false, ↓reduceIte, Bool.false_and]
      clear ih
      induction xs with
      | nil => rfl
      | cons y ys ihy => exact ihy
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.true_and]
      exact ih

/-- Equivalence between `find_imp` and `List.find?`. -/
theorem find_imp_eq_find? (p : α → Bool) (l : List α) :
    find_imp p l = l.find? p := by
  unfold find_imp
  simp only [List.forIn_eq_foldlM]
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldlM_cons, List.find?_cons]
    cases hx : p x
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ih
    · simp only [↓reduceIte]
      clear ih
      induction xs with
      | nil => rfl
      | cons y ys ihy => exact ihy

/-- Equivalence between functional `pre` and imperative `pre_imp`. -/
theorem pre_equiv (graph : List (List Nat)) :
    pre graph = pre_imp graph := by
  have h : pre_imp graph = all_imp (fun neighbors => all_imp (fun v => v < graph.length) neighbors) graph := rfl
  rw [h, all_imp_eq_all]
  unfold pre
  dsimp only
  congr 1
  funext neighbors
  exact (all_imp_eq_all _ neighbors).symm

/-- Equivalence between functional `is_topological_order` and imperative `is_topological_order_imp`. -/
theorem is_topological_order_equiv (graph : List (List Nat)) (order : List Nat) :
    is_topological_order graph order = is_topological_order_imp graph order := by
  unfold is_topological_order is_topological_order_imp
  rw [← pre_equiv graph]
  cases hpre : pre graph
  · rfl
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases hsort : (order.mergeSort != List.range graph.length)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      change ((List.range graph.length).all fun u =>
        graph[u]!.all fun v => decide (order.idxOf u < order.idxOf v)) =
        all_imp (fun u => all_imp (fun v => decide (order.idxOf u < order.idxOf v)) graph[u]!)
          (List.range graph.length)
      rw [all_imp_eq_all]
      congr 1
      funext u
      exact (all_imp_eq_all _ graph[u]!).symm
    · rfl

/-- Main equivalence theorem: functional `topological_sort` equals imperative `topological_sort_imp`. -/
theorem topological_sort_equiv (graph : List (List Nat)) :
    topological_sort graph = topological_sort_imp graph := by
  unfold topological_sort topological_sort_imp
  rw [← pre_equiv graph]
  cases hpre : pre graph
  · rfl
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    change List.find? (fun order => is_topological_order graph order)
        (List.range graph.length).permutations =
      find_imp (fun candidate => is_topological_order_imp graph candidate)
        (List.range graph.length).permutations
    rw [find_imp_eq_find?]
    congr 1
    funext candidate
    exact is_topological_order_equiv graph candidate

end topological_sort
