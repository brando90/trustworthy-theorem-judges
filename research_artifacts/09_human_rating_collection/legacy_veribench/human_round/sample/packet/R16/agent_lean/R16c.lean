import Mathlib

/-!
# Topological sorting for finite directed graphs

A Lean 4 translation of a Python reference implementation of topological sorting.

A directed graph on the vertices `0, 1, ..., n-1` is represented by an adjacency
list `g : List (List Nat)` of length `n`, where `g[u]` lists the outgoing
neighbours of `u`.

* A graph is *well formed* (`Pre` / `preB`) when every neighbour is a vertex,
  i.e. `v < n` for every `v ∈ g[u]`.
* `isTopoOrder g order` is the executable checker: `order` must be a
  rearrangement of `0, ..., n-1` and every edge `u → v` must go forwards.
* `topSort g` searches all permutations of `0, ..., n-1` (exactly like the
  Python `itertools.permutations` loop) and returns the first topological
  order, or `none` when the graph is malformed or contains a directed cycle.

The file contains a functional implementation, an imperative implementation
using `Id.run do` with mutable state, unit tests, the pre/post-conditions with
proofs, and a proof that the two implementations agree.
-/

namespace topological_sort

/-! ## Functional implementation -/

/-- Executable version of the Python `pre`: every neighbour listed in the
adjacency list must be a legal vertex index. -/
def preB (g : List (List Nat)) : Bool :=
  g.all (fun ns => ns.all (fun v => v < g.length))

/-- Executable version of the Python `is_topological_order`: the graph must be
well formed, `order` must be a rearrangement of `0, ..., n-1` (Python compares
`sorted(order)` with `list(range(n))`), and every edge must point forwards. -/
def isTopoOrder (g : List (List Nat)) (order : List Nat) : Bool :=
  preB g &&
  (order.mergeSort (fun a b => a ≤ b) == List.range g.length) &&
  (List.range g.length).all (fun u => (g[u]!).all (fun v => order.idxOf u < order.idxOf v))

/-- Functional version of the Python `topological_sort`: return the first
permutation of `0, ..., n-1` that is a topological order, or `none`. -/
def topSort (g : List (List Nat)) : Option (List Nat) :=
  if preB g then
    (List.range g.length).permutations.find? (fun order => isTopoOrder g order)
  else
    none

/-! ## Unit tests (the Python `check` function) -/

-- `g1 = [[1], [2], []]`
example : topSort [[1], [2], []] = some [0, 1, 2] := by native_decide
example : isTopoOrder [[1], [2], []] [0, 1, 2] = true := by native_decide

-- `g2 = [[1, 2], [3], [3], []]`
example : topSort [[1, 2], [3], [3], []] = some [0, 1, 2, 3] := by native_decide
example : (topSort [[1, 2], [3], [3], []]).any (fun o => isTopoOrder [[1, 2], [3], [3], []] o) := by
  native_decide
example : (topSort [[1, 2], [3], [3], []]).any (fun o => o.toFinset = {0, 1, 2, 3}) := by
  native_decide

-- `g3 = []`
example : topSort [] = some [] := by native_decide

-- `g4 = [[], [], []]`
example : topSort [[], [], []] = some [0, 1, 2] := by native_decide

-- `g5 = [[2], [], []]`: vertex `0` must precede vertex `2`.
example : (topSort [[2], [], []]).any (fun o => o.idxOf 0 < o.idxOf 2) := by native_decide
example : (topSort [[2], [], []]).any (fun o => isTopoOrder [[2], [], []] o) := by native_decide

-- Cycles have no topological order.
example : topSort [[1], [0]] = none := by native_decide
example : topSort [[0]] = none := by native_decide

-- Malformed adjacency lists (neighbour out of range) have no topological order.
example : topSort [[2]] = none := by native_decide
example : preB [[2]] = false := by native_decide

#eval topSort [[1], [2], []]
#eval topSort [[1, 2], [3], [3], []]
#eval topSort ([] : List (List Nat))
#eval topSort [[], [], []]
#eval topSort [[2], [], []]
#eval topSort [[1], [0]]
#eval topSort [[0]]
#eval topSort [[2]]

/-! ## Pre-condition -/

/-- The Python `pre`: `g` is a valid adjacency-list graph on `0, ..., n-1`. -/
def Pre (g : List (List Nat)) : Prop :=
  ∀ ns ∈ g, ∀ v ∈ ns, v < g.length

theorem preB_iff (g : List (List Nat)) : preB g = true ↔ Pre g := by
  simp [preB, Pre]

instance (g : List (List Nat)) : Decidable (Pre g) :=
  decidable_of_iff _ (preB_iff g)

/-! ## Specification properties -/

/-- Semantic reading of `isTopoOrder`: the graph is well formed, `order`
enumerates every vertex exactly once, and every edge points forwards. -/
def IsTopoOrder (g : List (List Nat)) (order : List Nat) : Prop :=
  Pre g ∧ order.Perm (List.range g.length) ∧
    ∀ u, ∀ h : u < g.length, ∀ v ∈ g[u], order.idxOf u < order.idxOf v

/-- The executable checker decides the semantic property. -/
def checker_prop (g : List (List Nat)) (order : List Nat) : Prop :=
  isTopoOrder g order = true ↔ IsTopoOrder g order

/-- A returned order really is a topological order. -/
def sound_prop (g : List (List Nat)) : Prop :=
  ∀ order, topSort g = some order → IsTopoOrder g order

/-- A returned order contains every vertex exactly once. -/
def perm_prop (g : List (List Nat)) : Prop :=
  ∀ order, topSort g = some order → order.Perm (List.range g.length)

/-- A returned order respects every edge. -/
def edges_prop (g : List (List Nat)) : Prop :=
  ∀ order, topSort g = some order →
    ∀ u, ∀ h : u < g.length, ∀ v ∈ g[u], order.idxOf u < order.idxOf v

/-- `none` is returned only when no topological order exists at all. -/
def complete_prop (g : List (List Nat)) : Prop :=
  topSort g = none → ∀ order, ¬ IsTopoOrder g order

/-- Malformed graphs return `none`. -/
def malformed_prop (g : List (List Nat)) : Prop :=
  ¬ Pre g → topSort g = none

/-- Graphs containing a directed cycle return `none`: a cycle is a nonempty
walk `u → path → u` returning to its starting vertex. -/
def cyclic_prop (g : List (List Nat)) : Prop :=
  ∀ (u : Nat) (path : List Nat),
    List.Chain (fun a b => ∃ h : a < g.length, b ∈ g[a]) u (path ++ [u]) →
    topSort g = none

/-! ### Basic facts about the checker -/

theorem isTopoOrder_pre {g : List (List Nat)} {order : List Nat}
    (h : isTopoOrder g order = true) : Pre g := by
  simp only [isTopoOrder, Bool.and_eq_true] at h
  exact (preB_iff g).mp h.1.1

theorem isTopoOrder_perm {g : List (List Nat)} {order : List Nat}
    (h : isTopoOrder g order = true) : order.Perm (List.range g.length) := by
  simp only [isTopoOrder, Bool.and_eq_true, beq_iff_eq] at h
  have hp := List.mergeSort_perm order (fun a b => decide (a ≤ b))
  rw [h.1.2] at hp
  exact hp.symm

theorem isTopoOrder_edges {g : List (List Nat)} {order : List Nat}
    (h : isTopoOrder g order = true) :
    ∀ u, ∀ hu : u < g.length, ∀ v ∈ g[u], order.idxOf u < order.idxOf v := by
  simp only [isTopoOrder, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  intro u hu v hv
  have hall := h.2 u hu
  rw [getElem!_pos g u hu] at hall
  exact hall v hv

theorem isTopoOrder_of {g : List (List Nat)} {order : List Nat}
    (hpre : Pre g) (hperm : order.Perm (List.range g.length))
    (hedge : ∀ u, ∀ hu : u < g.length, ∀ v ∈ g[u], order.idxOf u < order.idxOf v) :
    isTopoOrder g order = true := by
  have hsorted : order.mergeSort (fun a b => decide (a ≤ b)) = List.range g.length := by
    have hperm' : (order.mergeSort (fun a b => decide (a ≤ b))).Perm (List.range g.length) :=
      (List.mergeSort_perm _ _).trans hperm
    have h1 : (order.mergeSort (fun a b => decide (a ≤ b))).Sorted (· ≤ ·) :=
      List.sorted_mergeSort' (fun a b : Nat => a ≤ b) order
    have h2 : (List.range g.length).Sorted (· ≤ ·) :=
      List.pairwise_lt_range.imp le_of_lt
    exact List.eq_of_perm_of_sorted hperm' h1 h2
  simp only [isTopoOrder, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq]
  refine ⟨⟨(preB_iff g).mpr hpre, hsorted⟩, ?_⟩
  intro u hu
  rw [getElem!_pos g u hu]
  intro v hv
  exact hedge u hu v hv

theorem checker_thm (g : List (List Nat)) (order : List Nat) : checker_prop g order := by
  constructor
  · intro h
    exact ⟨isTopoOrder_pre h, isTopoOrder_perm h, isTopoOrder_edges h⟩
  · rintro ⟨hpre, hperm, hedge⟩
    exact isTopoOrder_of hpre hperm hedge

/-! ### Correctness of `topSort` -/

theorem topSort_eq_some {g : List (List Nat)} {order : List Nat}
    (h : topSort g = some order) : isTopoOrder g order = true := by
  unfold topSort at h
  split at h
  · exact List.find?_some h
  · exact absurd h (by simp)

theorem sound_thm (g : List (List Nat)) : sound_prop g := by
  intro order h
  exact (checker_thm g order).mp (topSort_eq_some h)

theorem perm_thm (g : List (List Nat)) : perm_prop g := by
  intro order h
  exact isTopoOrder_perm (topSort_eq_some h)

theorem edges_thm (g : List (List Nat)) : edges_prop g := by
  intro order h
  exact isTopoOrder_edges (topSort_eq_some h)

theorem complete_thm (g : List (List Nat)) : complete_prop g := by
  intro hnone order horder
  have hcheck : isTopoOrder g order = true := (checker_thm g order).mpr horder
  have hpre : preB g = true := (preB_iff g).mpr horder.1
  unfold topSort at hnone
  rw [if_pos hpre] at hnone
  have hmem : order ∈ (List.range g.length).permutations :=
    List.mem_permutations.mpr horder.2.1
  exact List.find?_eq_none.mp hnone order hmem hcheck

theorem malformed_thm (g : List (List Nat)) : malformed_prop g := by
  intro h
  unfold topSort
  rw [if_neg]
  intro hb
  exact h ((preB_iff g).mp hb)

/-- The search succeeds exactly when a topological order exists. -/
theorem topSort_isSome_iff (g : List (List Nat)) :
    (topSort g).isSome ↔ ∃ order, IsTopoOrder g order := by
  constructor
  · intro h
    obtain ⟨order, ho⟩ := Option.isSome_iff_exists.mp h
    exact ⟨order, sound_thm g order ho⟩
  · rintro ⟨order, ho⟩
    cases hres : topSort g with
    | none => exact absurd ho (complete_thm g hres order)
    | some o => simp

/-- Self-loops make a topological order impossible (Python: `[[0]] ↦ None`). -/
theorem topSort_selfLoop (g : List (List Nat)) (u : Nat) (hu : u < g.length)
    (hloop : u ∈ g[u]) : topSort g = none := by
  cases hres : topSort g with
  | none => rfl
  | some order =>
      exact absurd (edges_thm g order hres u hu u hloop) (lt_irrefl _)

/-- Two-cycles make a topological order impossible (Python: `[[1],[0]] ↦ None`). -/
theorem topSort_twoCycle (g : List (List Nat)) (u v : Nat) (hu : u < g.length)
    (hv : v < g.length) (huv : v ∈ g[u]) (hvu : u ∈ g[v]) : topSort g = none := by
  cases hres : topSort g with
  | none => rfl
  | some order =>
      have h1 := edges_thm g order hres u hu v huv
      have h2 := edges_thm g order hres v hv u hvu
      exact absurd (h1.trans h2) (lt_irrefl _)

/-- Any directed cycle makes a topological order impossible. -/
theorem cyclic_thm (g : List (List Nat)) : cyclic_prop g := by
  intro u path hchain
  cases hres : topSort g with
  | none => rfl
  | some order =>
      exfalso
      have hstep : ∀ a b, (∃ h : a < g.length, b ∈ g[a]) →
          order.idxOf a < order.idxOf b := by
        rintro a b ⟨h, hb⟩
        exact edges_thm g order hres a h b hb
      have hchain' : List.Chain (fun a b => order.idxOf a < order.idxOf b) u (path ++ [u]) :=
        hchain.imp hstep
      haveI : IsTrans Nat (fun a b => order.idxOf a < order.idxOf b) :=
        ⟨fun _ _ _ hab hbc => lt_trans hab hbc⟩
      have hpair := List.chain_iff_pairwise.mp hchain'
      have hmem : u ∈ path ++ [u] := by simp
      exact absurd (List.rel_of_pairwise_cons hpair hmem) (lt_irrefl _)

/-! ## Post-condition and overall correctness -/

/-- Full post-condition: the conjunction of all specification properties. -/
def Post_prop (g : List (List Nat)) : Prop :=
  sound_prop g ∧ perm_prop g ∧ edges_prop g ∧ complete_prop g ∧ malformed_prop g ∧ cyclic_prop g

/-- Correctness: for every well-formed graph the result satisfies the
post-condition. -/
theorem correctness_thm (g : List (List Nat)) (_h : Pre g) : Post_prop g :=
  ⟨sound_thm g, perm_thm g, edges_thm g, complete_thm g, malformed_thm g, cyclic_thm g⟩

/-! ## Imperative implementation -/

/-- Imperative version of the search loop, using mutable state: scan the
permutations of `0, ..., n-1` and keep the first one that is a topological
order. -/
def topSortImp (g : List (List Nat)) : Option (List Nat) := Id.run do
  if !preB g then
    return none
  let mut res : Option (List Nat) := none
  for order in (List.range g.length).permutations do
    res := if res.isNone && isTopoOrder g order then some order else res
  return res

/-! ### Imperative tests -/

example : topSortImp [[1], [2], []] = some [0, 1, 2] := by native_decide
example : topSortImp [[1, 2], [3], [3], []] = some [0, 1, 2, 3] := by native_decide
example : topSortImp [] = some [] := by native_decide
example : topSortImp [[], [], []] = some [0, 1, 2] := by native_decide
example : (topSortImp [[2], [], []]).any (fun o => o.idxOf 0 < o.idxOf 2) := by native_decide
example : topSortImp [[1], [0]] = none := by native_decide
example : topSortImp [[0]] = none := by native_decide
example : topSortImp [[2]] = none := by native_decide

#eval topSortImp [[1], [2], []]
#eval topSortImp [[1, 2], [3], [3], []]
#eval topSortImp [[1], [0]]

/-! ### Equivalence of the two implementations -/

/-- The loop of `topSortImp`, written as a `foldl`, keeps the first element
satisfying the checker — i.e. it computes `List.find?`. -/
theorem foldl_eq_find? (g : List (List Nat)) (l : List (List Nat))
    (init : Option (List Nat)) :
    l.foldl (fun r order => if (r.isNone && isTopoOrder g order) = true then some order else r)
        init
      = match init with
        | some x => some x
        | none => l.find? (fun o => isTopoOrder g o) := by
  induction l generalizing init with
  | nil => cases init <;> rfl
  | cons a t ih =>
      rw [List.foldl_cons, ih]
      cases init with
      | some x => simp
      | none =>
        by_cases h : isTopoOrder g a = true
        · rw [List.find?_cons_of_pos h]; simp [h]
        · simp only [Bool.not_eq_true] at h
          rw [List.find?_cons_of_neg (by simp [h])]; simp [h]

/-- The imperative implementation agrees with the functional one. -/
theorem topSortImp_eq_topSort (g : List (List Nat)) : topSortImp g = topSort g := by
  unfold topSortImp topSort
  by_cases h : preB g = true
  · simp only [h, Bool.not_true, Id.run, bind, pure]
    rw [if_neg (by simp), List.forIn_yield_eq_foldl, foldl_eq_find?]
    simp
  · simp only [Bool.not_eq_true] at h
    simp only [h, Bool.not_false, if_pos, Id.run]
    rfl

end topological_sort
