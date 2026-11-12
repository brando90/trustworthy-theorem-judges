import Mathlib
import Plausible

/-!
# Topological Sorting for Finite Directed Graphs

Formalization of the Python `topological_sort` program for finite directed graphs
represented as adjacency lists over vertices `0..n-1`.

Edge cases handled:
- Empty graphs have the empty topological order.
- Disconnected DAGs include every vertex `0..n-1` exactly once.
- Directed cycles (including self-loops and 2-cycles) return `none` because no topological order exists.
- Malformed adjacency lists (with out-of-range vertex indices) return `none`.
-/

set_option linter.dupNamespace false

namespace topological_sort

/-! ## 1. Functional Implementation -/

/-- Check that `graph` is a valid adjacency-list graph over vertices `0..n-1`. -/
def pre (graph : List (List Nat)) : Bool :=
  let n := graph.length
  graph.all (fun neighbors => neighbors.all (fun v => v < n))

/-- Executable checker for whether `order` is a valid topological ordering of `graph`. -/
def is_topological_order (graph : List (List Nat)) (order : List Nat) : Bool :=
  if !pre graph then
    false
  else if order.mergeSort != List.range graph.length then
    false
  else
    (List.range graph.length).all (fun u =>
      (graph[u]!).all (fun v => order.idxOf u < order.idxOf v))

/-- Return a topological ordering of a directed graph, if one exists.
Searches all vertex permutations of `0..n-1` and returns the first one that
satisfies `is_topological_order`. Returns `none` if the graph is malformed or
contains a directed cycle. -/
def topological_sort (graph : List (List Nat)) : Option (List Nat) :=
  if !pre graph then
    none
  else
    let n := graph.length
    ((List.range n).permutations).find? (fun order => is_topological_order graph order)

/-! ## 2. Unit Tests -/

-- g1 = [[1], [2], []]
example : topological_sort [[1], [2], []] = some [0, 1, 2] := by native_decide
example : is_topological_order [[1], [2], []] [0, 1, 2] = true := by native_decide

-- g2 = [[1, 2], [3], [3], []]
example : topological_sort [[1, 2], [3], [3], []] = some [0, 1, 2, 3] := by native_decide
example : is_topological_order [[1, 2], [3], [3], []] [0, 1, 2, 3] = true := by native_decide
example : is_topological_order [[1, 2], [3], [3], []] [0, 2, 1, 3] = true := by native_decide

-- g3 = []
example : topological_sort [] = some [] := by native_decide
example : is_topological_order [] [] = true := by native_decide

-- g4 = [[], [], []]
example : topological_sort [[], [], []] = some [0, 1, 2] := by native_decide

-- g5 = [[2], [], []]
example : topological_sort [[2], [], []] = some [0, 1, 2] := by native_decide
example : is_topological_order [[2], [], []] [0, 1, 2] = true := by native_decide
example : ([0, 1, 2] : List Nat).idxOf 0 < ([0, 1, 2] : List Nat).idxOf 2 := by native_decide

-- Cycles and malformed graphs
example : topological_sort [[1], [0]] = none := by native_decide
example : topological_sort [[0]] = none := by native_decide
example : topological_sort [[2]] = none := by native_decide
example : pre [[2]] = false := by native_decide

#eval topological_sort [[1], [2], []]
#eval topological_sort [[1, 2], [3], [3], []]
#eval topological_sort []
#eval topological_sort [[], [], []]
#eval topological_sort [[2], [], []]
#eval topological_sort [[1], [0]]
#eval topological_sort [[0]]
#eval topological_sort [[2]]

/-! ## 3. Pre-condition -/

/-- Pre-condition: every neighbor in every adjacency list is a valid vertex `< graph.length`. -/
def Pre (graph : List (List Nat)) : Prop :=
  ∀ neighbors ∈ graph, ∀ v ∈ neighbors, v < graph.length

/-- Equivalence between the executable `pre` checker and the propositional `Pre`. -/
theorem pre_iff_Pre (graph : List (List Nat)) : pre graph = true ↔ Pre graph := by
  simp [pre, Pre]

/-! ## 4. Property Propositions and Theorems -/

/-- Helper lemma: sorting a list of naturals equals `List.range n` iff it is a permutation of `List.range n`. -/
theorem mergeSort_eq_range_iff_perm (order : List Nat) (n : Nat) :
    order.mergeSort = List.range n ↔ order.Perm (List.range n) := by
  constructor
  · intro h
    have hp : (order.mergeSort).Perm order := List.mergeSort_perm order (· ≤ ·)
    rw [h] at hp
    exact hp.symm
  · intro h
    have hp : (order.mergeSort).Perm (List.range n) := (List.mergeSort_perm order (· ≤ ·)).trans h
    have hs1 : List.Pairwise (fun a b => decide (a ≤ b) = true) order.mergeSort :=
      List.sorted_mergeSort
        (fun a b c hab hbc => by simp at hab hbc ⊢; omega)
        (fun a b => by simp; omega)
        order
    have hs1' : List.Pairwise (· ≤ ·) order.mergeSort :=
      hs1.imp (fun hle => of_decide_eq_true hle)
    have hs2 : List.Pairwise (· ≤ ·) (List.range n) :=
      List.pairwise_lt_range.imp (fun hlt => Nat.le_of_lt hlt)
    exact hp.eq_of_sorted (fun _ _ _ _ h1 h2 => Nat.le_antisymm h1 h2) hs1' hs2

/-- Propositional specification of a valid topological ordering. -/
def IsTopologicalOrder (graph : List (List Nat)) (order : List Nat) : Prop :=
  Pre graph ∧
  order.Perm (List.range graph.length) ∧
  ∀ (u : Nat) (hu : u < graph.length), ∀ v ∈ graph[u], order.idxOf u < order.idxOf v

/-- Exact correspondence between executable `is_topological_order` and `IsTopologicalOrder`. -/
theorem is_topological_order_iff (graph : List (List Nat)) (order : List Nat) :
    is_topological_order graph order = true ↔ IsTopologicalOrder graph order := by
  unfold is_topological_order IsTopologicalOrder
  by_cases hpre : pre graph = true
  · have hPre : Pre graph := (pre_iff_Pre graph).mp hpre
    by_cases hsort : order.mergeSort = List.range graph.length
    · have hperm : order.Perm (List.range graph.length) :=
        (mergeSort_eq_range_iff_perm order graph.length).mp hsort
      simp [hpre, hsort, hPre, hperm]
      constructor
      · intro hall u hu v hv
        have h1 := hall u hu
        simp [hu] at h1
        exact h1 v hv
      · intro hall u hu v hv
        simp [hu] at hv
        exact hall u hu v hv
    · have hperm : ¬ order.Perm (List.range graph.length) := by
        intro hp
        exact hsort ((mergeSort_eq_range_iff_perm order graph.length).mpr hp)
      simp [hpre, hsort, hPre, hperm]
  · have hPre : ¬ Pre graph := by
      intro hp
      exact hpre ((pre_iff_Pre graph).mpr hp)
    simp [hpre, hPre]

/-- Property 1: Malformed graphs (violating `Pre`) return `none`. -/
def malformed_none_prop (graph : List (List Nat)) : Prop :=
  ¬ Pre graph → topological_sort graph = none

theorem malformed_none_thm (graph : List (List Nat)) : malformed_none_prop graph := by
  intro hnot
  unfold topological_sort
  have hpre : pre graph = false := by
    cases h : pre graph with
    | false => rfl
    | true => exact False.elim (hnot ((pre_iff_Pre graph).mp h))
  simp [hpre]

/-- Property 2: Soundness — any returned ordering satisfies `is_topological_order`. -/
def soundness_prop (graph : List (List Nat)) : Prop :=
  ∀ order, topological_sort graph = some order → is_topological_order graph order = true

theorem soundness_thm (graph : List (List Nat)) : soundness_prop graph := by
  intro order hsome
  unfold topological_sort at hsome
  by_cases hpre : pre graph = true
  · simp [hpre] at hsome
    exact List.find?_some hsome
  · simp [hpre] at hsome

/-- Property 3: Permutation property — any returned ordering is a permutation of `0..n-1`. -/
def perm_range_prop (graph : List (List Nat)) : Prop :=
  ∀ order, topological_sort graph = some order → order.Perm (List.range graph.length)

theorem perm_range_thm (graph : List (List Nat)) : perm_range_prop graph := by
  intro order hsome
  have hvalid := (is_topological_order_iff graph order).mp (soundness_thm graph order hsome)
  exact hvalid.2.1

/-- Property 4: Sortedness equivalence — sorting any returned ordering yields `List.range graph.length`. -/
def sorted_eq_range_prop (graph : List (List Nat)) : Prop :=
  ∀ order, topological_sort graph = some order → order.mergeSort = List.range graph.length

theorem sorted_eq_range_thm (graph : List (List Nat)) : sorted_eq_range_prop graph := by
  intro order hsome
  exact (mergeSort_eq_range_iff_perm order graph.length).mpr (perm_range_thm graph order hsome)

/-- Property 5: Length preservation — any returned ordering has length equal to `graph.length`. -/
def length_eq_prop (graph : List (List Nat)) : Prop :=
  ∀ order, topological_sort graph = some order → order.length = graph.length

theorem length_eq_thm (graph : List (List Nat)) : length_eq_prop graph := by
  intro order hsome
  have hp := perm_range_thm graph order hsome
  simpa using hp.length_eq

/-- Property 6: No duplicate vertices — any returned ordering is duplicate-free. -/
def nodup_prop (graph : List (List Nat)) : Prop :=
  ∀ order, topological_sort graph = some order → order.Nodup

theorem nodup_thm (graph : List (List Nat)) : nodup_prop graph := by
  intro order hsome
  have hp := perm_range_thm graph order hsome
  exact hp.symm.nodup_iff.mp List.nodup_range

/-- Property 7: Vertex membership — every vertex `0..n-1` appears in any returned ordering. -/
def mem_vertices_prop (graph : List (List Nat)) : Prop :=
  ∀ order, topological_sort graph = some order → ∀ v, v ∈ order ↔ v < graph.length

theorem mem_vertices_thm (graph : List (List Nat)) : mem_vertices_prop graph := by
  intro order hsome v
  have hp := perm_range_thm graph order hsome
  rw [hp.mem_iff, List.mem_range]

/-- Property 8: Edge precedence — for every directed edge `u → v`, `u` appears before `v` in `order`. -/
def edge_order_prop (graph : List (List Nat)) : Prop :=
  ∀ order, topological_sort graph = some order →
    ∀ (u : Nat) (hu : u < graph.length), ∀ v ∈ graph[u], order.idxOf u < order.idxOf v

theorem edge_order_thm (graph : List (List Nat)) : edge_order_prop graph := by
  intro order hsome
  have hvalid := (is_topological_order_iff graph order).mp (soundness_thm graph order hsome)
  exact hvalid.2.2

/-- Property 9: Completeness — `topological_sort` returns `none` iff no valid topological order exists. -/
def completeness_prop (graph : List (List Nat)) : Prop :=
  topological_sort graph = none ↔ ∀ order, is_topological_order graph order = false

theorem completeness_thm (graph : List (List Nat)) : completeness_prop graph := by
  unfold completeness_prop topological_sort
  by_cases hpre : pre graph = true
  · simp [hpre]
    constructor
    · intro hnone order
      by_cases hperm : order.Perm (List.range graph.length)
      · exact hnone order hperm
      · cases h : is_topological_order graph order with
        | false => rfl
        | true =>
          have hvalid := (is_topological_order_iff graph order).mp h
          exact False.elim (hperm hvalid.2.1)
    · intro hall order _
      exact hall order
  · simp [hpre]
    intro order
    cases h : is_topological_order graph order with
    | false => rfl
    | true =>
      have hvalid := (is_topological_order_iff graph order).mp h
      exact False.elim (hpre ((pre_iff_Pre graph).mpr hvalid.1))

/-- Property 10: Existence equivalence — a topological order exists iff `topological_sort` returns `some`. -/
def exists_order_iff_isSome_prop (graph : List (List Nat)) : Prop :=
  (∃ order, IsTopologicalOrder graph order) ↔ (topological_sort graph).isSome = true

theorem exists_order_iff_isSome_thm (graph : List (List Nat)) : exists_order_iff_isSome_prop graph := by
  unfold exists_order_iff_isSome_prop
  constructor
  · rintro ⟨order, hvalid⟩
    have htrue : is_topological_order graph order = true :=
      (is_topological_order_iff graph order).mpr hvalid
    cases h : topological_sort graph with
    | some _ => rfl
    | none =>
      have hfalse := (completeness_thm graph).mp h order
      rw [htrue] at hfalse
      contradiction
  · intro hisSome
    cases h : topological_sort graph with
    | none => rw [h] at hisSome; contradiction
    | some order =>
      exact ⟨order, (is_topological_order_iff graph order).mp (soundness_thm graph order h)⟩

/-- Directed edge relation on `graph`. -/
def HasEdge (graph : List (List Nat)) (u v : Nat) : Prop :=
  ∃ hu : u < graph.length, v ∈ graph[u]

/-- Non-empty directed path reachability relation (transitive closure of `HasEdge`). -/
def Reaches (graph : List (List Nat)) (u v : Nat) : Prop :=
  Relation.TransGen (HasEdge graph) u v

/-- Property 11: Path precedence — if `u` reaches `v` via a non-empty directed path, `u` precedes `v`. -/
def reachability_order_prop (graph : List (List Nat)) : Prop :=
  ∀ order, topological_sort graph = some order →
    ∀ u v, Reaches graph u v → order.idxOf u < order.idxOf v

theorem reachability_order_thm (graph : List (List Nat)) : reachability_order_prop graph := by
  intro order hsome u v hreach
  induction hreach with
  | single hedge =>
    rcases hedge with ⟨hu, hv⟩
    exact edge_order_thm graph order hsome u hu _ hv
  | tail _ hedge ih =>
    rcases hedge with ⟨hw, hv⟩
    exact Nat.lt_trans ih (edge_order_thm graph order hsome _ hw _ hv)

/-- Property 12: General cycle impossibility — any graph with a directed cycle returns `none`. -/
def cycle_none_prop (graph : List (List Nat)) : Prop :=
  (∃ u, Reaches graph u u) → topological_sort graph = none

theorem cycle_none_thm (graph : List (List Nat)) : cycle_none_prop graph := by
  rintro ⟨u, hcycle⟩
  cases h : topological_sort graph with
  | none => rfl
  | some order =>
    have hlt := reachability_order_thm graph order h u u hcycle
    exact False.elim (Nat.lt_irrefl _ hlt)

/-- Property 13: Self-loop returns `none`. -/
def self_loop_none_prop (graph : List (List Nat)) : Prop :=
  (∃ (u : Nat) (hu : u < graph.length), u ∈ graph[u]) → topological_sort graph = none

theorem self_loop_none_thm (graph : List (List Nat)) : self_loop_none_prop graph := by
  rintro ⟨u, hu, hmem⟩
  exact cycle_none_thm graph ⟨u, Relation.TransGen.single ⟨hu, hmem⟩⟩

/-- Property 14: Two-cycle returns `none`. -/
def two_cycle_none_prop (graph : List (List Nat)) : Prop :=
  (∃ (u v : Nat) (hu : u < graph.length) (hv : v < graph.length), v ∈ graph[u] ∧ u ∈ graph[v]) →
    topological_sort graph = none

theorem two_cycle_none_thm (graph : List (List Nat)) : two_cycle_none_prop graph := by
  rintro ⟨u, v, hu, hv, huv, hvu⟩
  exact cycle_none_thm graph ⟨u, Relation.TransGen.tail (Relation.TransGen.single ⟨hu, huv⟩) ⟨hv, hvu⟩⟩

/-- Helper lemma: index of `k < n` in `List.range n` is `k`. -/
theorem idxOf_range {n k : Nat} (hk : k < n) : (List.range n).idxOf k = k := by
  have hlen : k < (List.range n).length := by simpa using hk
  have h := List.idxOf_getElem List.nodup_range k hlen
  simpa using h

/-- Property 15: Forward-edge DAGs — if every edge `u → v` has `u < v`, the canonical order `0..n-1` is returned. -/
def dag_monotone_order_prop (graph : List (List Nat)) : Prop :=
  Pre graph →
  (∀ (u : Nat) (hu : u < graph.length), ∀ v ∈ graph[u], u < v) →
  topological_sort graph = some (List.range graph.length)

theorem dag_monotone_order_thm (graph : List (List Nat)) : dag_monotone_order_prop graph := by
  intro hPre hmono
  have hpre : pre graph = true := (pre_iff_Pre graph).mpr hPre
  have hvalid : IsTopologicalOrder graph (List.range graph.length) := by
    refine ⟨hPre, List.Perm.refl _, ?_⟩
    intro u hu v hv
    have hmem : graph[u] ∈ graph := List.getElem_mem hu
    have hv_lt : v < graph.length := hPre graph[u] hmem v hv
    rw [idxOf_range hu, idxOf_range hv_lt]
    exact hmono u hu v hv
  have htrue : is_topological_order graph (List.range graph.length) = true :=
    (is_topological_order_iff graph (List.range graph.length)).mpr hvalid
  unfold topological_sort
  simp [hpre, List.permutations, htrue]

/-- Property 16: Disconnected edgeless graph of size `n` returns `List.range n`. -/
def edgeless_graph_prop (n : Nat) : Prop :=
  topological_sort (List.replicate n []) = some (List.range n)

theorem edgeless_graph_thm (n : Nat) : edgeless_graph_prop n := by
  unfold edgeless_graph_prop
  have h := dag_monotone_order_thm (List.replicate n [])
    (by intro ns hns v hv; rcases List.mem_replicate.mp hns with ⟨_, rfl⟩; contradiction)
    (by intro u hu v hv; simp at hv)
  simpa using h

/-- Property 17: Empty graph returns `some []`. -/
def empty_graph_prop : Prop :=
  topological_sort [] = some []

theorem empty_graph_thm : empty_graph_prop := by
  simpa using edgeless_graph_thm 0

/-! ## 5. Post-condition -/

/-- Post-condition conjunction of all core semantic properties of `topological_sort`. -/
def Post_prop (graph : List (List Nat)) : Prop :=
  soundness_prop graph ∧
  perm_range_prop graph ∧
  sorted_eq_range_prop graph ∧
  length_eq_prop graph ∧
  nodup_prop graph ∧
  mem_vertices_prop graph ∧
  edge_order_prop graph ∧
  completeness_prop graph ∧
  exists_order_iff_isSome_prop graph ∧
  reachability_order_prop graph ∧
  cycle_none_prop graph ∧
  self_loop_none_prop graph ∧
  two_cycle_none_prop graph ∧
  dag_monotone_order_prop graph

/-! ## 6. Property-Based Tests (PBTs) -/

/-- Sample suite of small graphs for exhaustive bounded property-based checks. -/
def sampleGraphs : List (List (List Nat)) :=
  [ []
  , [[]]
  , [[0]]
  , [[1]]
  , [[], []]
  , [[1], []]
  , [[], [0]]
  , [[1], [0]]
  , [[0], []]
  , [[], [1]]
  , [[2]]
  , [[], [], []]
  , [[1], [2], []]
  , [[2], [], [1]]
  , [[2], [0], [1]]
  , [[1], [2], [0]]
  , [[1, 2], [2], []]
  , [[1, 2], [3], [3], []]
  , [[3], [0], [1], [2]]
  ]

/-- Project arbitrary `List (List Nat)` into a small graph (size `≤ 4`). -/
def smallGraph (raw : List (List Nat)) : List (List Nat) :=
  (raw.take 4).map (fun ns => ns.take 4)

-- Executable Boolean checkers for each property
def check_malformed_none (g : List (List Nat)) : Bool :=
  pre g || topological_sort g == none

def check_soundness (g : List (List Nat)) : Bool :=
  match topological_sort g with
  | none => true
  | some order => is_topological_order g order

def check_sorted_eq_range (g : List (List Nat)) : Bool :=
  match topological_sort g with
  | none => true
  | some order => order.mergeSort == List.range g.length

def check_length_eq (g : List (List Nat)) : Bool :=
  match topological_sort g with
  | none => true
  | some order => order.length == g.length

def check_nodup (g : List (List Nat)) : Bool :=
  match topological_sort g with
  | none => true
  | some order => decide order.Nodup

def check_mem_vertices (g : List (List Nat)) : Bool :=
  match topological_sort g with
  | none => true
  | some order => (List.range g.length).all (fun v => decide (v ∈ order))

def check_edge_order (g : List (List Nat)) : Bool :=
  match topological_sort g with
  | none => true
  | some order =>
    (List.range g.length).all (fun u =>
      (g[u]!).all (fun v => order.idxOf u < order.idxOf v))

def check_completeness (g : List (List Nat)) : Bool :=
  (topological_sort g == none) ==
    ((List.range g.length).permutations.all (fun order => !is_topological_order g order))

def check_self_loop_none (g : List (List Nat)) : Bool :=
  !((List.range g.length).any (fun u => decide (u ∈ g[u]!))) || topological_sort g == none

def check_two_cycle_none (g : List (List Nat)) : Bool :=
  !((List.range g.length).any (fun u =>
    (List.range g.length).any (fun v => decide (v ∈ g[u]! ∧ u ∈ g[v]!)))) ||
  topological_sort g == none

def check_dag_monotone (raw : List (List Nat)) : Bool :=
  let base := smallGraph raw
  let g := base.zipIdx.map (fun (ns, u) => ns.filter (fun v => u < v && v < base.length))
  topological_sort g == some (List.range g.length)

def check_post (g : List (List Nat)) : Bool :=
  check_malformed_none g &&
  check_soundness g &&
  check_sorted_eq_range g &&
  check_length_eq g &&
  check_nodup g &&
  check_mem_vertices g &&
  check_edge_order g &&
  check_completeness g &&
  check_self_loop_none g &&
  check_two_cycle_none g

-- Randomized & Bounded PBTs for every property and Post_prop
#eval Plausible.Testable.check (∀ raw : List (List Nat), check_malformed_none (smallGraph raw) = true)
example : sampleGraphs.all check_malformed_none = true := by native_decide

#eval Plausible.Testable.check (∀ raw : List (List Nat), check_soundness (smallGraph raw) = true)
example : sampleGraphs.all check_soundness = true := by native_decide

#eval Plausible.Testable.check (∀ raw : List (List Nat), check_sorted_eq_range (smallGraph raw) = true)
example : sampleGraphs.all check_sorted_eq_range = true := by native_decide

#eval Plausible.Testable.check (∀ raw : List (List Nat), check_length_eq (smallGraph raw) = true)
example : sampleGraphs.all check_length_eq = true := by native_decide

#eval Plausible.Testable.check (∀ raw : List (List Nat), check_nodup (smallGraph raw) = true)
example : sampleGraphs.all check_nodup = true := by native_decide

#eval Plausible.Testable.check (∀ raw : List (List Nat), check_mem_vertices (smallGraph raw) = true)
example : sampleGraphs.all check_mem_vertices = true := by native_decide

#eval Plausible.Testable.check (∀ raw : List (List Nat), check_edge_order (smallGraph raw) = true)
example : sampleGraphs.all check_edge_order = true := by native_decide

#eval Plausible.Testable.check (∀ raw : List (List Nat), check_completeness (smallGraph raw) = true)
example : sampleGraphs.all check_completeness = true := by native_decide

#eval Plausible.Testable.check (∀ raw : List (List Nat), check_self_loop_none (smallGraph raw) = true)
example : sampleGraphs.all check_self_loop_none = true := by native_decide

#eval Plausible.Testable.check (∀ raw : List (List Nat), check_two_cycle_none (smallGraph raw) = true)
example : sampleGraphs.all check_two_cycle_none = true := by native_decide

#eval Plausible.Testable.check (∀ raw : List (List Nat), check_dag_monotone raw = true)
example : (List.range 6).all (fun n =>
  topological_sort (List.replicate n []) == some (List.range n)) = true := by native_decide

#eval Plausible.Testable.check (∀ raw : List (List Nat), check_post (smallGraph raw) = true)
example : sampleGraphs.all check_post = true := by native_decide

/-! ## 7. Correctness Theorem (Pre -> Post) -/

/-- Main correctness theorem: under `Pre graph`, `Post_prop graph` holds. -/
theorem correctness_thm (graph : List (List Nat)) (_hpre : Pre graph) : Post_prop graph :=
  ⟨ soundness_thm graph
  , perm_range_thm graph
  , sorted_eq_range_thm graph
  , length_eq_thm graph
  , nodup_thm graph
  , mem_vertices_thm graph
  , edge_order_thm graph
  , completeness_thm graph
  , exists_order_iff_isSome_thm graph
  , reachability_order_thm graph
  , cycle_none_thm graph
  , self_loop_none_thm graph
  , two_cycle_none_thm graph
  , dag_monotone_order_thm graph ⟩

/-! ## 8. Imperative Implementation -/

/-- Imperative pre-condition check using `Id.run do` and mutable state. -/
def pre_imp (graph : List (List Nat)) : Bool := Id.run do
  let n := graph.length
  let mut valid : Bool := true
  for neighbors in graph do
    if !neighbors.all (fun v => v < n) then
      valid := false
      break
  return valid

/-- Imperative topological-order checker using `Id.run do` and mutable state. -/
def is_topological_order_imp (graph : List (List Nat)) (order : List Nat) : Bool := Id.run do
  if !pre_imp graph then
    return false
  if order.mergeSort != List.range graph.length then
    return false
  let mut valid : Bool := true
  for u in List.range graph.length do
    if !(graph[u]!).all (fun v => order.idxOf u < order.idxOf v) then
      valid := false
      break
  return valid

/-- Imperative topological sort using `Id.run do` and mutable state. -/
def topological_sort_imp (graph : List (List Nat)) : Option (List Nat) := Id.run do
  if !pre_imp graph then
    return none
  let n := graph.length
  let mut result : Option (List Nat) := none
  for order in (List.range n).permutations do
    if is_topological_order_imp graph order then
      result := some order
      break
  return result

/-! ## 9. Imperative Tests -/

example : topological_sort_imp [[1], [2], []] = some [0, 1, 2] := by native_decide
example : topological_sort_imp [[1, 2], [3], [3], []] = some [0, 1, 2, 3] := by native_decide
example : topological_sort_imp [] = some [] := by native_decide
example : topological_sort_imp [[], [], []] = some [0, 1, 2] := by native_decide
example : topological_sort_imp [[2], [], []] = some [0, 1, 2] := by native_decide
example : topological_sort_imp [[1], [0]] = none := by native_decide
example : topological_sort_imp [[0]] = none := by native_decide
example : topological_sort_imp [[2]] = none := by native_decide
example : sampleGraphs.all (fun g => topological_sort g == topological_sort_imp g) = true := by native_decide

#eval topological_sort_imp [[1], [2], []]
#eval topological_sort_imp [[1, 2], [3], [3], []]
#eval topological_sort_imp []
#eval topological_sort_imp [[], [], []]
#eval topological_sort_imp [[2], [], []]
#eval topological_sort_imp [[1], [0]]
#eval topological_sort_imp [[0]]
#eval topological_sort_imp [[2]]

/-! ## 10. Equivalence Theorem (Functional = Imperative) -/

/-- Helper lemma: imperative `for` loop with early break on `!p x` equals `List.all`. -/
theorem forIn_all_eq (p : α → Bool) (xs : List α) :
    (Id.run do
      let mut valid : Bool := true
      for x in xs do
        if !p x then
          valid := false
          break
      return valid) = xs.all p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [Id.run, List.forIn_cons, List.all_cons]
    cases h : p x
    · simp [bind, pure]
    · simpa [h, bind, pure] using ih

/-- Helper lemma: imperative `for` loop with early break on `p x` equals `List.find?`. -/
theorem forIn_find?_eq (p : α → Bool) (xs : List α) :
    (Id.run do
      let mut result : Option α := none
      for x in xs do
        if p x then
          result := some x
          break
      return result) = xs.find? p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [Id.run, List.forIn_cons, List.find?_cons]
    cases h : p x
    · simpa [h, bind, pure] using ih
    · simp [bind, pure]

/-- Equivalence between `pre_imp` and `pre`. -/
theorem pre_equivalence_thm (graph : List (List Nat)) :
    pre_imp graph = pre graph := by
  unfold pre_imp pre
  exact forIn_all_eq (fun neighbors => neighbors.all (fun v => v < graph.length)) graph

/-- Equivalence between `is_topological_order_imp` and `is_topological_order`. -/
theorem is_topological_order_equivalence_thm (graph : List (List Nat)) (order : List Nat) :
    is_topological_order_imp graph order = is_topological_order graph order := by
  unfold is_topological_order_imp is_topological_order
  rw [pre_equivalence_thm]
  cases h1 : pre graph
  · rfl
  · cases h2 : (order.mergeSort != List.range graph.length)
    · exact forIn_all_eq (fun u => (graph[u]!).all (fun v => order.idxOf u < order.idxOf v)) (List.range graph.length)
    · rfl

/-- Proposition stating functional and imperative `topological_sort` agree on `graph`. -/
def equivalence_prop (graph : List (List Nat)) : Prop :=
  topological_sort graph = topological_sort_imp graph

-- PBT for equivalence_prop
#eval Plausible.Testable.check (∀ raw : List (List Nat),
  (topological_sort (smallGraph raw) == topological_sort_imp (smallGraph raw)) = true)

/-- Main equivalence theorem: functional `topological_sort` equals imperative `topological_sort_imp`. -/
theorem equivalence_thm (graph : List (List Nat)) : equivalence_prop graph := by
  unfold equivalence_prop topological_sort topological_sort_imp
  rw [pre_equivalence_thm]
  cases hpre : pre graph
  · rfl
  · change List.find? (fun order => is_topological_order graph order) (List.range graph.length).permutations =
      (Id.run do
        let mut result : Option (List Nat) := none
        for order in (List.range graph.length).permutations do
          if is_topological_order_imp graph order then
            result := some order
            break
        return result)
    have heq : (fun order => is_topological_order_imp graph order) = (fun order => is_topological_order graph order) := by
      funext order
      exact is_topological_order_equivalence_thm graph order
    have hfind := forIn_find?_eq (fun order => is_topological_order_imp graph order) (List.range graph.length).permutations
    rw [heq] at hfind
    exact hfind.symm

end topological_sort
