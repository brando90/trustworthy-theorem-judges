import Mathlib
import Plausible

/-!
# Topological sorting

Lean 4 formalization of topological sorting for finite directed graphs given as
adjacency lists. The functional implementation follows the Python reference:
validate the adjacency list (`pre`), enumerate the permutations of `0 .. n-1`
in lexicographic order (the order produced by `itertools.permutations(range(n))`),
and return the first permutation that is a topological order. Malformed
adjacency lists and directed cycles yield `none`.

Python type errors such as a non-list neighbor entry are excluded by Lean's type
system. Out-of-range neighbor indices are the representable malformed case.
-/

namespace topological_sort

/-- Index of the first occurrence of `v` in `order`, or `order.length` if absent.
When `order` is a permutation of `0 .. n-1` this is the unique position, matching
Python's `{v: i for i, v in enumerate(order)}`. -/
def position (order : List Nat) (v : Nat) : Nat :=
  order.findIdx (· == v)

/-- Python `pre`: every neighbor lies in `0 .. n-1`. -/
def pre (graph : List (List Nat)) : Bool :=
  graph.all fun neighbors => neighbors.all fun v => v < graph.length

/-- Python `sorted(order) == list(range(n))`. -/
def isPermutationOfRange (n : Nat) (order : List Nat) : Bool :=
  order.mergeSort (fun a b => decide (a ≤ b)) == List.range n

/-- Every recorded edge points strictly forward in `order`. -/
def edgesRespected (graph : List (List Nat)) (order : List Nat) : Bool :=
  (List.range graph.length).all fun u =>
    (graph.getD u []).all fun v => position order u < position order v

/-- Executable checker used by the search and by the Python tests. -/
def isTopologicalOrder (graph : List (List Nat)) (order : List Nat) : Bool :=
  pre graph && isPermutationOfRange graph.length order && edgesRespected graph order

/-- All permutations of `xs`, sorted lexicographically. -/
def lexPermutations (xs : List Nat) : List (List Nat) :=
  (List.permutations' xs).mergeSort (fun a b => decide (a ≤ b))

/-- Functional topological sort: the lexicographically least topological order. -/
def topologicalSort (graph : List (List Nat)) : Option (List Nat) :=
  if pre graph then
    (lexPermutations (List.range graph.length)).find? (isTopologicalOrder graph)
  else
    none

/-- Directed edge `u → v`, requiring `u` to be a real vertex. -/
def hasEdge (graph : List (List Nat)) (u v : Nat) : Bool :=
  decide (u < graph.length) && decide (v ∈ graph.getD u [])

/-! ## Unit tests -/

example : topologicalSort [[1], [2], []] = some [0, 1, 2] := by native_decide
example : topologicalSort [[1, 2], [3], [3], []] = some [0, 1, 2, 3] := by native_decide
example : topologicalSort ([] : List (List Nat)) = some [] := by native_decide
example : topologicalSort [[], [], []] = some [0, 1, 2] := by native_decide
example : topologicalSort [[2], [], []] = some [0, 1, 2] := by native_decide
example : topologicalSort [[], [0]] = some [1, 0] := by native_decide
example : topologicalSort [[], [0], []] = some [1, 0, 2] := by native_decide
example : topologicalSort [[1], [0]] = none := by native_decide
example : topologicalSort [[0]] = none := by native_decide
example : topologicalSort [[2]] = none := by native_decide
example : isTopologicalOrder [[1, 2], [3], [3], []] [0, 1, 2, 3] = true := by native_decide
example : isTopologicalOrder [[2], [], []] [0, 1, 2] = true := by native_decide

#eval topologicalSort [[1], [2], []]
#eval topologicalSort [[1, 2], [3], [3], []]
#eval topologicalSort ([[], [0], []] : List (List Nat))
#eval topologicalSort [[1], [0]]
#eval topologicalSort [[2]]

/-! ## Pre-condition -/

/-- The graph is a valid adjacency list on vertices `0 .. n-1`. -/
def Pre (graph : List (List Nat)) : Prop :=
  pre graph = true

theorem Pre_iff (graph : List (List Nat)) :
    Pre graph ↔ ∀ neighbors ∈ graph, ∀ v ∈ neighbors, v < graph.length := by
  unfold Pre pre
  simp [List.all_eq_true]

/-! ## Supporting lemmas -/

theorem lexPermutations_pairwise (xs : List Nat) :
    (lexPermutations xs).Pairwise (· ≤ ·) := by
  unfold lexPermutations
  have h := List.sorted_mergeSort
    (le := fun a b : List Nat => decide (a ≤ b))
    (trans := by
      intro a b c hab hbc
      simp only [decide_eq_true_eq] at hab hbc ⊢
      exact le_trans hab hbc)
    (total := by
      intro a b
      rcases le_total a b with h | h
      · simp [h]
      · simp [h])
    (List.permutations' xs)
  simpa [decide_eq_true_eq] using h

theorem mem_lexPermutations {xs p : List Nat} :
    p ∈ lexPermutations xs ↔ List.Perm p xs := by
  unfold lexPermutations
  rw [List.mem_mergeSort, List.mem_permutations']

theorem isPermutationOfRange_perm {n : Nat} {order : List Nat}
    (h : isPermutationOfRange n order = true) :
    List.Perm order (List.range n) := by
  unfold isPermutationOfRange at h
  have heq : order.mergeSort (fun a b => decide (a ≤ b)) = List.range n := by
    simpa [beq_iff_eq] using h
  have hperm := List.mergeSort_perm order (fun a b => decide (a ≤ b))
  exact (heq ▸ hperm).symm

theorem find?_le_of_mem {p : List Nat → Bool} {l : List (List Nat)} {a b : List Nat}
    (hsorted : l.Pairwise (· ≤ ·))
    (hfind : l.find? p = some b)
    (hmem : a ∈ l) (hpa : p a = true) :
    b ≤ a := by
  rw [List.find?_eq_some_iff_append] at hfind
  obtain ⟨_hb, as, bs, rfl, has⟩ := hfind
  rw [List.pairwise_append] at hsorted
  obtain ⟨_, hrest, _⟩ := hsorted
  rw [List.pairwise_cons] at hrest
  obtain ⟨hbs, _⟩ := hrest
  simp only [List.mem_append, List.mem_cons] at hmem
  rcases hmem with hmem | rfl | hmem
  · have hfalse : (!p a) = true := has a hmem
    rw [hpa] at hfalse
    simp at hfalse
  · exact le_rfl
  · exact hbs a hmem

theorem lex_map_succ {xs ys : List Nat} (h : List.Lex (· < ·) xs ys) :
    List.Lex (· < ·) (xs.map Nat.succ) (ys.map Nat.succ) := by
  induction h with
  | nil => simp
  | rel hlt =>
    simp
    exact List.Lex.rel (Nat.succ_lt_succ hlt)
  | cons _h ih =>
    simp
    exact List.Lex.cons ih

theorem map_succ_mono {xs ys : List Nat} (h : xs ≤ ys) :
    xs.map Nat.succ ≤ ys.map Nat.succ := by
  rcases le_iff_lt_or_eq.mp h with hlt | heq
  · have hlex : List.Lex (· < ·) xs ys := by simpa [List.lt_iff_lex_lt] using hlt
    have : xs.map Nat.succ < ys.map Nat.succ := by
      simpa [List.lt_iff_lex_lt] using lex_map_succ hlex
    exact le_of_lt this
  · simp [heq]

theorem map_pred_succ_of_pos (ps : List Nat) (hpos : ∀ x ∈ ps, 0 < x) :
    (ps.map Nat.pred).map Nat.succ = ps := by
  induction ps with
  | nil => simp
  | cons x xs ih =>
    have hx : 0 < x := hpos x List.mem_cons_self
    have hxs : ∀ y ∈ xs, 0 < y := fun y hy => hpos y (List.mem_cons_of_mem _ hy)
    simp [ih hxs]
    omega

theorem map_pred_map_succ_range (n : Nat) :
    ((List.range n).map Nat.succ).map Nat.pred = List.range n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ]
    simp [List.map_append, ih]

theorem range_succ_eq_cons_map_succ (n : Nat) :
    List.range (n + 1) = 0 :: (List.range n).map Nat.succ := by
  induction n with
  | zero => decide
  | succ n ih =>
    calc
      List.range (n + 2) = List.range (n + 1) ++ [n + 1] := by rw [List.range_succ]
      _ = (0 :: (List.range n).map Nat.succ) ++ [n + 1] := by rw [ih]
      _ = 0 :: ((List.range n).map Nat.succ ++ [n + 1]) := by simp
      _ = 0 :: ((List.range (n + 1)).map Nat.succ) := by
        rw [List.range_succ]
        simp [List.map_append]

theorem range_le_of_perm (n : Nat) (p : List Nat) (h : List.Perm p (List.range n)) :
    List.range n ≤ p := by
  induction n generalizing p with
  | zero =>
    have hp : p = [] := by simpa using h.eq_nil
    simp [hp]
  | succ n ih =>
    rw [range_succ_eq_cons_map_succ]
    cases p with
    | nil => simp at h
    | cons a ps =>
      have ha_mem : a ∈ List.range (n + 1) := (List.Perm.mem_iff h).mp List.mem_cons_self
      have ha_lt : a < n + 1 := List.mem_range.mp ha_mem
      by_cases ha : a = 0
      · subst ha
        apply List.cons_le_cons
        have hperm : List.Perm (0 :: ps) (0 :: (List.range n).map Nat.succ) := by
          simpa [range_succ_eq_cons_map_succ] using h
        have hps : List.Perm ps ((List.range n).map Nat.succ) := (List.perm_cons 0).mp hperm
        have hnodup : (0 :: ps).Nodup := (List.Perm.nodup_iff h).mpr List.nodup_range
        have hnot : 0 ∉ ps := by
          simp only [List.nodup_cons] at hnodup
          exact hnodup.1
        have hpos : ∀ x ∈ ps, 0 < x := by
          intro x hx
          have hxmem : x ∈ List.range (n + 1) :=
            (List.Perm.mem_iff h).mp (List.mem_cons_of_mem 0 hx)
          have hxne : x ≠ 0 := fun heq => hnot (heq ▸ hx)
          have hxlt : x < n + 1 := List.mem_range.mp hxmem
          omega
        have hq : List.Perm (ps.map Nat.pred) (List.range n) := by
          have hmap := hps.map Nat.pred
          simpa [map_pred_map_succ_range n] using hmap
        have hle : List.range n ≤ ps.map Nat.pred := ih _ hq
        rw [show ps = (ps.map Nat.pred).map Nat.succ from (map_pred_succ_of_pos ps hpos).symm]
        exact map_succ_mono hle
      · have hlt : (0 :: (List.range n).map Nat.succ) < a :: ps := by
          simpa [List.lt_iff_lex_lt] using (List.Lex.rel (show 0 < a from by omega))
        exact le_of_lt hlt

theorem pre_replicate_nil (n : Nat) : pre (List.replicate n []) = true := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp [pre, List.replicate_succ, ih]

theorem getD_replicate_nil (n u : Nat) :
    (List.replicate n ([] : List Nat)).getD u ([] : List Nat) = [] := by
  induction n generalizing u with
  | zero => simp
  | succ n ih =>
    cases u with
    | zero => simp [List.replicate_succ, List.getD]
    | succ u => simp [List.replicate_succ, List.getD, ih]

theorem edges_replicate_nil (n : Nat) (order : List Nat) :
    edgesRespected (List.replicate n []) order = true := by
  unfold edgesRespected
  rw [List.all_eq_true]
  intro u _hu
  simp [getD_replicate_nil n u]

theorem mergeSort_range (n : Nat) :
    (List.range n).mergeSort (fun a b => decide (a ≤ b)) = List.range n := by
  apply List.mergeSort_of_sorted
  have h := List.sorted_le_range n
  simpa [List.Sorted, decide_eq_true_eq] using h

theorem isPerm_range (n : Nat) : isPermutationOfRange n (List.range n) = true := by
  unfold isPermutationOfRange
  rw [mergeSort_range]
  simp

theorem isTopo_range_replicate (n : Nat) :
    isTopologicalOrder (List.replicate n []) (List.range n) = true := by
  unfold isTopologicalOrder
  simp [pre_replicate_nil n, isPerm_range n, edges_replicate_nil n (List.range n)]

theorem edge_forward_aux (graph : List (List Nat)) (order : List Nat)
    (h : edgesRespected graph order = true) {u v : Nat}
    (hu : u < graph.length) (hv : v ∈ graph.getD u []) :
    position order u < position order v := by
  unfold edgesRespected at h
  have hall := List.all_eq_true.mp h
  have hu' : u ∈ List.range graph.length := List.mem_range.mpr hu
  have hvu := hall u hu'
  have hall2 := List.all_eq_true.mp hvu
  have hlt := hall2 v hv
  simpa using hlt

theorem topo_parts (graph : List (List Nat)) (order : List Nat)
    (h : isTopologicalOrder graph order = true) :
    pre graph = true ∧ isPermutationOfRange graph.length order = true ∧
      edgesRespected graph order = true := by
  unfold isTopologicalOrder at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h12, hedges⟩ := h
  rw [Bool.and_eq_true] at h12
  obtain ⟨hpre, hperm⟩ := h12
  exact ⟨hpre, hperm, hedges⟩

theorem edge_forward (graph : List (List Nat)) (order : List Nat) (u v : Nat)
    (htopo : isTopologicalOrder graph order = true)
    (hedge : hasEdge graph u v = true) :
    position order u < position order v := by
  obtain ⟨_, _, hedges⟩ := topo_parts graph order htopo
  unfold hasEdge at hedge
  rw [Bool.and_eq_true] at hedge
  obtain ⟨hu, hv⟩ := hedge
  rw [decide_eq_true_eq] at hu hv
  exact edge_forward_aux graph order hedges hu hv

/-- A positive-length directed walk. A cycle is a walk from a vertex to itself. -/
inductive HasPath (graph : List (List Nat)) : Nat → Nat → Prop
  | edge {u v : Nat} : hasEdge graph u v = true → HasPath graph u v
  | cons {u v w : Nat} : hasEdge graph u v = true → HasPath graph v w → HasPath graph u w

theorem path_pos_lt (graph : List (List Nat)) (order : List Nat) (u v : Nat)
    (htopo : isTopologicalOrder graph order = true)
    (hpath : HasPath graph u v) :
    position order u < position order v := by
  induction hpath with
  | edge hedge =>
    exact edge_forward graph order _ _ htopo hedge
  | cons hedge _hrest ih =>
    exact Nat.lt_trans (edge_forward graph order _ _ htopo hedge) ih

/-! ## Properties and theorems -/

def invalid_none_prop (graph : List (List Nat)) : Prop :=
  pre graph = false → topologicalSort graph = none

theorem invalid_none_thm (graph : List (List Nat)) : invalid_none_prop graph := by
  intro h
  simp [topologicalSort, h]

def soundness_prop (graph : List (List Nat)) : Prop :=
  ∀ order, topologicalSort graph = some order → isTopologicalOrder graph order = true

theorem soundness_thm (graph : List (List Nat)) : soundness_prop graph := by
  intro order h
  unfold topologicalSort at h
  by_cases hp : pre graph = true
  · simp [hp] at h
    exact List.find?_some h
  · simp [hp] at h

def completeness_prop (graph : List (List Nat)) : Prop :=
  ∀ order, isTopologicalOrder graph order = true → (topologicalSort graph).isSome

theorem completeness_thm (graph : List (List Nat)) : completeness_prop graph := by
  intro order h
  obtain ⟨hp, hpermBool, _⟩ := topo_parts graph order h
  have hperm : List.Perm order (List.range graph.length) :=
    isPermutationOfRange_perm hpermBool
  have hmem : order ∈ lexPermutations (List.range graph.length) :=
    mem_lexPermutations.mpr hperm
  simp [topologicalSort, hp, List.find?_isSome]
  exact ⟨order, hmem, h⟩

def lex_minimal_prop (graph : List (List Nat)) : Prop :=
  ∀ order, topologicalSort graph = some order →
    ∀ order', isTopologicalOrder graph order' = true → order ≤ order'

theorem lex_minimal_thm (graph : List (List Nat)) : lex_minimal_prop graph := by
  intro order h order' h'
  have hp : pre graph = true := by
    unfold topologicalSort at h
    by_cases hp : pre graph = true
    · exact hp
    · simp [hp] at h
  simp [topologicalSort, hp] at h
  obtain ⟨_, hpermBool, _⟩ := topo_parts graph order' h'
  have hperm : List.Perm order' (List.range graph.length) :=
    isPermutationOfRange_perm hpermBool
  have hmem : order' ∈ lexPermutations (List.range graph.length) :=
    mem_lexPermutations.mpr hperm
  exact find?_le_of_mem (lexPermutations_pairwise _) h hmem h'

def none_iff_prop (graph : List (List Nat)) : Prop :=
  topologicalSort graph = none ↔ ∀ order, isTopologicalOrder graph order = false

theorem none_iff_thm (graph : List (List Nat)) : none_iff_prop graph := by
  constructor
  · intro h order
    by_contra hpos
    have htrue : isTopologicalOrder graph order = true := by
      cases hres : isTopologicalOrder graph order <;> simp_all
    have hsome := completeness_thm graph order htrue
    simp [h] at hsome
  · intro h
    by_cases hp : pre graph = true
    · rw [topologicalSort, if_pos hp, List.find?_eq_none]
      intro order _hmem
      have hfalse := h order
      simpa using hfalse
    · rw [topologicalSort, if_neg hp]

def covers_vertices_prop (graph : List (List Nat)) : Prop :=
  ∀ order, topologicalSort graph = some order →
    List.Perm order (List.range graph.length)

theorem covers_vertices_thm (graph : List (List Nat)) : covers_vertices_prop graph := by
  intro order h
  have htopo := soundness_thm graph order h
  obtain ⟨_, hpermBool, _⟩ := topo_parts graph order htopo
  exact isPermutationOfRange_perm hpermBool

def respects_edges_prop (graph : List (List Nat)) : Prop :=
  ∀ order, topologicalSort graph = some order →
    ∀ u v, hasEdge graph u v = true → position order u < position order v

theorem respects_edges_thm (graph : List (List Nat)) : respects_edges_prop graph := by
  intro order h u v hedge
  exact edge_forward graph order u v (soundness_thm graph order h) hedge

def lex_unique_prop (graph : List (List Nat)) : Prop :=
  ∀ order order', topologicalSort graph = some order →
    isTopologicalOrder graph order' = true → order' ≤ order → order = order'

theorem lex_unique_thm (graph : List (List Nat)) : lex_unique_prop graph := by
  intro order order' h h' hle
  exact le_antisymm (lex_minimal_thm graph order h order' h') hle

def cycle_none_prop (graph : List (List Nat)) : Prop :=
  (∃ u, HasPath graph u u) → topologicalSort graph = none

theorem cycle_none_thm (graph : List (List Nat)) : cycle_none_prop graph := by
  intro hcycle
  obtain ⟨u, hpath⟩ := hcycle
  by_cases hp : pre graph = true
  · rw [topologicalSort, if_pos hp, List.find?_eq_none]
    intro order _hmem
    cases htopo : isTopologicalOrder graph order with
    | true =>
      have hlt := path_pos_lt graph order u u htopo hpath
      exact absurd hlt (Nat.lt_irrefl _)
    | false => simp
  · rw [topologicalSort, if_neg hp]

theorem self_loop_none_thm : topologicalSort [[0]] = none := by
  have hpath : HasPath [[0]] 0 0 := HasPath.edge (by decide)
  exact cycle_none_thm [[0]] ⟨0, hpath⟩

theorem two_cycle_none_thm : topologicalSort [[1], [0]] = none := by
  have h01 : hasEdge [[1], [0]] 0 1 = true := by decide
  have h10 : hasEdge [[1], [0]] 1 0 = true := by decide
  exact cycle_none_thm [[1], [0]] ⟨0, HasPath.cons h01 (HasPath.edge h10)⟩

theorem malformed_out_of_range_thm : topologicalSort [[2]] = none := by
  have hp : pre [[2]] = false := by decide
  exact invalid_none_thm [[2]] hp

def no_edges_prop (n : Nat) : Prop :=
  topologicalSort (List.replicate n []) = some (List.range n)

theorem no_edges_thm (n : Nat) : no_edges_prop n := by
  unfold no_edges_prop
  have hpre := pre_replicate_nil n
  have htopo := isTopo_range_replicate n
  rw [topologicalSort, if_pos hpre, List.length_replicate]
  have hmem : List.range n ∈ lexPermutations (List.range n) :=
    mem_lexPermutations.mpr (List.Perm.refl _)
  have hsorted := lexPermutations_pairwise (List.range n)
  cases hlist : lexPermutations (List.range n) with
  | nil => simp [hlist] at hmem
  | cons p ps =>
    have hp_le_range : p ≤ List.range n := by
      have hs := hsorted
      rw [hlist] at hs
      rw [List.pairwise_cons] at hs
      have hmem' : List.range n ∈ p :: ps := by simpa [hlist] using hmem
      simp only [List.mem_cons] at hmem'
      rcases hmem' with rfl | hmem'
      · exact le_rfl
      · exact hs.1 _ hmem'
    have hp_mem : p ∈ lexPermutations (List.range n) := by
      rw [hlist]
      exact List.mem_cons_self
    have hrange_le_p : List.range n ≤ p :=
      range_le_of_perm n p (mem_lexPermutations.mp hp_mem)
    have hp_eq : p = List.range n := le_antisymm hp_le_range hrange_le_p
    have hp_topo : isTopologicalOrder (List.replicate n []) p = true := by
      simpa [hp_eq] using htopo
    rw [List.find?_cons_of_pos hp_topo, hp_eq]

def empty_graph_prop : Prop :=
  topologicalSort [] = some []

theorem empty_graph_thm : empty_graph_prop := by
  have h := no_edges_thm 0
  simpa [empty_graph_prop, no_edges_prop, List.replicate_zero, List.range_zero] using h

def edgeless_identity_prop (graph : List (List Nat)) : Prop :=
  (∀ ns ∈ graph, ns = []) → topologicalSort graph = some (List.range graph.length)

theorem all_nil_eq_replicate (graph : List (List Nat))
    (h : ∀ ns ∈ graph, ns = []) :
    graph = List.replicate graph.length [] := by
  induction graph with
  | nil => simp
  | cons ns g ih =>
    have hns : ns = [] := h ns List.mem_cons_self
    have hg : ∀ ns' ∈ g, ns' = [] := fun ns' hmem => h ns' (List.mem_cons_of_mem _ hmem)
    rw [hns, ih hg, List.length_cons, List.length_replicate, List.replicate_succ]

theorem edgeless_identity_thm (graph : List (List Nat)) : edgeless_identity_prop graph := by
  intro h
  have hg := all_nil_eq_replicate graph h
  rw [hg, List.length_replicate]
  exact no_edges_thm graph.length

/-! ## Post-condition -/

def Post_prop (graph : List (List Nat)) : Prop :=
  invalid_none_prop graph ∧
  soundness_prop graph ∧
  completeness_prop graph ∧
  lex_minimal_prop graph ∧
  none_iff_prop graph ∧
  covers_vertices_prop graph ∧
  respects_edges_prop graph ∧
  lex_unique_prop graph ∧
  cycle_none_prop graph ∧
  edgeless_identity_prop graph

/-! ## Property-based tests -/

def subsetsOf : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 =>
    let prev := subsetsOf n
    prev ++ prev.map (fun s => s ++ [n])

def productAdj (n : Nat) : List (List (List Nat)) :=
  let choices := subsetsOf n
  (List.range n).foldl (fun acc _ =>
    acc.flatMap fun g => choices.map fun c => g ++ [c]) [[]]

/-- All simple digraphs on at most 3 vertices, plus malformed and cyclic samples. -/
def testGraphs : List (List (List Nat)) :=
  ((List.range 4).flatMap productAdj) ++
  [[[2]], [[5]], [[1], [2]], [[0, 4]], [[1, 1], [0]], [[], [3], []],
   [[2], [0], [1]], [[0]], [[1], [0]]]

def invalid_none_bool (g : List (List Nat)) : Bool :=
  pre g || (topologicalSort g).isNone

def soundness_bool (g : List (List Nat)) : Bool :=
  match topologicalSort g with
  | none => true
  | some order => isTopologicalOrder g order

def completeness_bool (g : List (List Nat)) : Bool :=
  let anyTopo := (lexPermutations (List.range g.length)).any (isTopologicalOrder g)
  anyTopo == (topologicalSort g).isSome

def lex_minimal_bool (g : List (List Nat)) : Bool :=
  match topologicalSort g with
  | none => true
  | some order =>
    (lexPermutations (List.range g.length)).all fun order' =>
      !(isTopologicalOrder g order') || decide (order ≤ order')

def none_iff_bool (g : List (List Nat)) : Bool :=
  let noOrder := (lexPermutations (List.range g.length)).all fun order =>
    !(isTopologicalOrder g order)
  ((topologicalSort g).isNone) == noOrder

def covers_vertices_bool (g : List (List Nat)) : Bool :=
  match topologicalSort g with
  | none => true
  | some order => isPermutationOfRange g.length order

def respects_edges_bool (g : List (List Nat)) : Bool :=
  match topologicalSort g with
  | none => true
  | some order =>
    (List.range g.length).all fun u =>
      (g.getD u []).all fun v =>
        !(hasEdge g u v) || position order u < position order v

def lex_unique_bool (g : List (List Nat)) : Bool :=
  match topologicalSort g with
  | none => true
  | some order =>
    (lexPermutations (List.range g.length)).all fun order' =>
      !(isTopologicalOrder g order') || !(decide (order' ≤ order)) || order == order'

def boolMatrixGet (m : List (List Bool)) (i j : Nat) : Bool :=
  (m.getD i []).getD j false

def warshall (graph : List (List Nat)) : List (List Bool) :=
  let n := graph.length
  let init := (List.range n).map fun u =>
    (List.range n).map fun v => hasEdge graph u v
  (List.range n).foldl (fun m k =>
    (List.range n).map fun u =>
      (List.range n).map fun v =>
        boolMatrixGet m u v || (boolMatrixGet m u k && boolMatrixGet m k v)) init

def hasCycleBool (graph : List (List Nat)) : Bool :=
  let m := warshall graph
  (List.range graph.length).any fun u => boolMatrixGet m u u

def cycle_none_bool (g : List (List Nat)) : Bool :=
  !hasCycleBool g || (topologicalSort g).isNone

def edgeless_identity_bool (g : List (List Nat)) : Bool :=
  if g.any (fun ns => !ns.isEmpty) then true
  else if g.length > 5 then true
  else topologicalSort g == some (List.range g.length)

def post_bool (g : List (List Nat)) : Bool :=
  invalid_none_bool g && soundness_bool g && completeness_bool g &&
    lex_minimal_bool g && none_iff_bool g && covers_vertices_bool g &&
    respects_edges_bool g && lex_unique_bool g && cycle_none_bool g &&
    edgeless_identity_bool g

example : testGraphs.all invalid_none_bool = true := by native_decide
example : testGraphs.all soundness_bool = true := by native_decide
example : testGraphs.all completeness_bool = true := by native_decide
example : testGraphs.all lex_minimal_bool = true := by native_decide
example : testGraphs.all none_iff_bool = true := by native_decide
example : testGraphs.all covers_vertices_bool = true := by native_decide
example : testGraphs.all respects_edges_bool = true := by native_decide
example : testGraphs.all lex_unique_bool = true := by native_decide
example : testGraphs.all cycle_none_bool = true := by native_decide
example : testGraphs.all edgeless_identity_bool = true := by native_decide
example : testGraphs.all post_bool = true := by native_decide

example : (List.range 5).all (fun n =>
    topologicalSort (List.replicate n []) == some (List.range n)) = true := by
  native_decide

#eval Plausible.Testable.check (∀ g : List (List Nat),
  !(decide (g.length ≤ 3)) || invalid_none_bool g)
#eval Plausible.Testable.check (∀ g : List (List Nat),
  !(decide (g.length ≤ 3)) || soundness_bool g)
#eval Plausible.Testable.check (∀ g : List (List Nat),
  !(decide (g.length ≤ 3)) || completeness_bool g)
#eval Plausible.Testable.check (∀ g : List (List Nat),
  !(decide (g.length ≤ 3)) || lex_minimal_bool g)
#eval Plausible.Testable.check (∀ g : List (List Nat),
  !(decide (g.length ≤ 3)) || none_iff_bool g)
#eval Plausible.Testable.check (∀ g : List (List Nat),
  !(decide (g.length ≤ 3)) || covers_vertices_bool g)
#eval Plausible.Testable.check (∀ g : List (List Nat),
  !(decide (g.length ≤ 3)) || respects_edges_bool g)
#eval Plausible.Testable.check (∀ g : List (List Nat),
  !(decide (g.length ≤ 3)) || lex_unique_bool g)
#eval Plausible.Testable.check (∀ g : List (List Nat),
  !(decide (g.length ≤ 3)) || cycle_none_bool g)
#eval Plausible.Testable.check (∀ g : List (List Nat),
  !(decide (g.length ≤ 3)) || edgeless_identity_bool g)
#eval Plausible.Testable.check (∀ g : List (List Nat),
  !(decide (g.length ≤ 3)) || post_bool g)

/-! ## Correctness -/

theorem correctness_thm (graph : List (List Nat)) (_h : Pre graph) : Post_prop graph :=
  ⟨invalid_none_thm graph, soundness_thm graph, completeness_thm graph,
    lex_minimal_thm graph, none_iff_thm graph, covers_vertices_thm graph,
    respects_edges_thm graph, lex_unique_thm graph, cycle_none_thm graph,
    edgeless_identity_thm graph⟩

theorem correctness_total_thm (graph : List (List Nat)) : Post_prop graph :=
  ⟨invalid_none_thm graph, soundness_thm graph, completeness_thm graph,
    lex_minimal_thm graph, none_iff_thm graph, covers_vertices_thm graph,
    respects_edges_thm graph, lex_unique_thm graph, cycle_none_thm graph,
    edgeless_identity_thm graph⟩

/-! ## Imperative implementation -/

def scanPerms (graph : List (List Nat)) : List (List Nat) → Option (List Nat)
  | [] =>
    Id.run do
      let mut result : Option (List Nat) := none
      return result
  | p :: ps =>
    Id.run do
      let mut accepted : Bool := isTopologicalOrder graph p
      if accepted then
        let mut chosen : Option (List Nat) := some p
        return chosen
      else
        return scanPerms graph ps

def topologicalSortImp (graph : List (List Nat)) : Option (List Nat) :=
  Id.run do
    let mut g := graph
    let mut wellFormed : Bool := pre g
    if !wellFormed then
      return none
    let mut candidates : List (List Nat) := lexPermutations (List.range g.length)
    return scanPerms g candidates

/-! ## Imperative tests -/

example : topologicalSortImp [[1], [2], []] = some [0, 1, 2] := by native_decide
example : topologicalSortImp [[1, 2], [3], [3], []] = some [0, 1, 2, 3] := by native_decide
example : topologicalSortImp ([] : List (List Nat)) = some [] := by native_decide
example : topologicalSortImp [[], [], []] = some [0, 1, 2] := by native_decide
example : topologicalSortImp [[], [0]] = some [1, 0] := by native_decide
example : topologicalSortImp [[1], [0]] = none := by native_decide
example : topologicalSortImp [[0]] = none := by native_decide
example : topologicalSortImp [[2]] = none := by native_decide

#eval topologicalSortImp [[1], [2], []]
#eval topologicalSortImp [[], [0], []]
#eval topologicalSortImp [[1], [0]]

/-! ## Equivalence -/

theorem scanPerms_eq_find? (graph : List (List Nat)) (perms : List (List Nat)) :
    scanPerms graph perms = perms.find? (isTopologicalOrder graph) := by
  induction perms with
  | nil =>
    simp [scanPerms, Id.run, pure]
  | cons p ps ih =>
    simp [scanPerms, Id.run, pure, ih]
    split <;> simp_all [List.find?]

theorem equivalence_thm (graph : List (List Nat)) :
    topologicalSort graph = topologicalSortImp graph := by
  simp [topologicalSort, topologicalSortImp, Id.run, pure, bind, scanPerms_eq_find?]
  by_cases h : pre graph = true
  · simp [h, pure_bind, bind_pure_comp]
  · have hfalse : pre graph = false := by
      cases hp : pre graph <;> simp_all
    simp [h, hfalse, pure_bind, bind_pure_comp]

end topological_sort
