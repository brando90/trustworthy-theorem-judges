import Mathlib

/-!
# Topological sorting for finite directed graphs

Lean 4 translation of the Python program `topological_sort.py`.

A directed graph on the vertices `0..n-1` is an adjacency list
`graph : List (List Nat)` where `graph[u]` holds the outgoing neighbours of `u`.

* `validGraph` is the Python `pre` check: every neighbour index lies in `0..n-1`
  (the "list of lists of ints" shape is enforced by the Lean type, and `0 ≤ v`
  is automatic for `Nat`).
* `isTopologicalOrder` is the Python checker `is_topological_order`.
* `topologicalSort` enumerates the permutations of `0..n-1` in the same
  (lexicographic) order as `itertools.permutations(range(n))` and returns the
  first one accepted by the checker; it returns `none` for malformed graphs and
  for graphs containing a directed cycle.

Edge cases (from the Python docstring):
* the empty graph has the empty topological order,
* disconnected DAGs include every vertex exactly once,
* cycles yield `none` because no topological order exists,
* malformed adjacency lists yield `none`.
-/

namespace topological_sort

/-! ## Functional implementation -/

/-- Python `pre`: every neighbour index is a vertex `0 ≤ v < n` of the graph. -/
def validGraph (graph : List (List Nat)) : Bool :=
  graph.all (fun ns => ns.all (fun v => v < graph.length))

/-- Python `position[v]`: the index of vertex `v` in `order`. -/
def position (order : List Nat) (v : Nat) : Nat := order.idxOf v

/-- The literal Python test `sorted(order) == list(range(n))`. -/
def sortedEqRange (order : List Nat) (n : Nat) : Bool :=
  order.mergeSort (fun a b => decide (a ≤ b)) == List.range n

/-- Python `is_topological_order`.  The test `sorted(order) == list(range(n))` is
modelled as "`order` is a permutation of `range n`" (see `sortedEqRange_iff_perm`
below for the equivalence with the literal test `sortedEqRange`). -/
def isTopologicalOrder (graph : List (List Nat)) (order : List Nat) : Bool :=
  validGraph graph &&
  decide (order.Perm (List.range graph.length)) &&
  (List.range graph.length).all (fun u =>
    (graph.getD u []).all (fun v => position order u < position order v))

/-- Permutations of `xs` in the order produced by `itertools.permutations`
(lexicographic order when `xs` is sorted).  `fuel` bounds the recursion; it is
always instantiated with `xs.length`. -/
def permsAux : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | fuel + 1, xs => xs.flatMap (fun x => (permsAux fuel (xs.erase x)).map (x :: ·))

/-- All permutations of `xs`, in `itertools.permutations` order. -/
def perms (xs : List Nat) : List (List Nat) := permsAux xs.length xs

/-- Python `topological_sort`: the first permutation of `range n` (in
lexicographic order) accepted by the checker, or `none`. -/
def topologicalSort (graph : List (List Nat)) : Option (List Nat) :=
  if validGraph graph then
    (perms (List.range graph.length)).find? (fun order => isTopologicalOrder graph order)
  else
    none

/-! ## Unit tests (the Python `check` function) -/

example : topologicalSort [[1], [2], []] = some [0, 1, 2] := by native_decide
example : (topologicalSort [[1], [2], []]).all
    (fun o => isTopologicalOrder [[1], [2], []] o) = true := by native_decide
example : (topologicalSort [[1, 2], [3], [3], []]).isSome = true := by native_decide
example : (topologicalSort [[1, 2], [3], [3], []]).all
    (fun o => isTopologicalOrder [[1, 2], [3], [3], []] o) = true := by native_decide
example : (topologicalSort [[1, 2], [3], [3], []]).all
    (fun o => decide (o.Perm [0, 1, 2, 3])) = true := by native_decide
example : topologicalSort [] = some [] := by native_decide
example : topologicalSort [[], [], []] = some [0, 1, 2] := by native_decide
example : (topologicalSort [[2], [], []]).isSome = true := by native_decide
example : (topologicalSort [[2], [], []]).all
    (fun o => isTopologicalOrder [[2], [], []] o && decide (o.idxOf 0 < o.idxOf 2)) = true := by
  native_decide
example : topologicalSort [[1], [0]] = none := by native_decide
example : topologicalSort [[0]] = none := by native_decide
example : topologicalSort [[2]] = none := by native_decide
-- `[[1], "not a list"]` is not expressible as a `List (List Nat)`: the Lean type
-- system performs the `isinstance` part of the Python `pre` check statically.
example : validGraph [[2]] = false := by native_decide
example : isTopologicalOrder [[1], [2], []] [0, 1, 2] = true := by native_decide
example : isTopologicalOrder [[1], [2], []] [2, 1, 0] = false := by native_decide
example : isTopologicalOrder [[1], [2], []] [0, 1] = false := by native_decide
example : sortedEqRange [2, 0, 1] 3 = true := by native_decide
example : sortedEqRange [0, 0, 1] 3 = false := by native_decide
example : sortedEqRange [0, 1] 3 = false := by native_decide
example : perms [0, 1, 2] = [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]] := by
  native_decide

#eval topologicalSort [[1], [2], []]          -- some [0, 1, 2]
#eval topologicalSort [[1, 2], [3], [3], []]  -- some [0, 1, 2, 3]
#eval topologicalSort []                      -- some []
#eval topologicalSort [[], [], []]            -- some [0, 1, 2]
#eval topologicalSort [[2], [], []]           -- some [0, 1, 2]
#eval topologicalSort [[1], [0]]              -- none
#eval topologicalSort [[0]]                   -- none
#eval topologicalSort [[2]]                   -- none
#eval topologicalSort [[], [0]]               -- some [1, 0]

/-! ## Pre-condition -/

/-- Pre-condition: the Python `pre` predicate (a well-formed adjacency list over
the vertices `0..n-1`). -/
def Pre (graph : List (List Nat)) : Prop := validGraph graph = true

/-! ## Properties -/

/-- Soundness: a returned order passes the Python checker `is_topological_order`. -/
def sound_prop : Prop :=
  ∀ (graph : List (List Nat)) (order : List Nat),
    topologicalSort graph = some order → isTopologicalOrder graph order = true

/-- Completeness: `none` is returned only when no topological order exists. -/
def complete_prop : Prop :=
  ∀ (graph : List (List Nat)),
    topologicalSort graph = none → ∀ order : List Nat, isTopologicalOrder graph order = false

/-- Malformed adjacency lists (an index outside `0..n-1`) give `none`. -/
def malformed_prop : Prop :=
  ∀ graph : List (List Nat), validGraph graph = false → topologicalSort graph = none

/-- Every vertex appears exactly once in a returned order. -/
def perm_prop : Prop :=
  ∀ (graph : List (List Nat)) (order : List Nat),
    topologicalSort graph = some order → order.Perm (List.range graph.length)

/-- Every edge `u → v` of the graph is respected by a returned order. -/
def edges_prop : Prop :=
  ∀ (graph : List (List Nat)) (order : List Nat),
    topologicalSort graph = some order →
      ∀ u v : Nat, u < graph.length → v ∈ graph.getD u [] → position order u < position order v

/-- A self loop is a cycle: no order is returned. -/
def self_loop_prop : Prop :=
  ∀ (graph : List (List Nat)) (u : Nat),
    u < graph.length → u ∈ graph.getD u [] → topologicalSort graph = none

/-- A two-cycle `u → v → u` is a cycle: no order is returned. -/
def two_cycle_prop : Prop :=
  ∀ (graph : List (List Nat)) (u v : Nat),
    u < graph.length → v < graph.length →
    v ∈ graph.getD u [] → u ∈ graph.getD v [] → topologicalSort graph = none

/-- Any directed cycle `v → c₀ → ⋯ → cₖ → v` (a self loop when `c = []`) rules out a
topological order: "cycles return `None` because no topological order exists". -/
def cycle_prop : Prop :=
  ∀ (graph : List (List Nat)) (v : Nat) (c : List Nat),
    (∀ u ∈ v :: c, u < graph.length) →
    List.Chain (fun a b => b ∈ graph.getD a []) v c →
    v ∈ graph.getD (c.getLastD v) [] →
    topologicalSort graph = none

/-- Specification of the checker `is_topological_order`: the graph is well formed,
`order` is a permutation of the vertices, and every edge goes forward. -/
def checker_prop : Prop :=
  ∀ (graph : List (List Nat)) (order : List Nat),
    isTopologicalOrder graph order = true ↔
      validGraph graph = true ∧ order.Perm (List.range graph.length) ∧
      ∀ u < graph.length, ∀ v ∈ graph.getD u [], position order u < position order v

/-- The returned order is the first valid permutation in the enumeration order of
`itertools.permutations(range(n))`, i.e. the lexicographically smallest one. -/
def lex_first_prop : Prop :=
  ∀ (graph : List (List Nat)) (order order' : List Nat),
    topologicalSort graph = some order → isTopologicalOrder graph order' = true →
      ¬ List.Lex (· < ·) order' order

/-- The empty graph has the empty topological order. -/
def empty_prop : Prop := topologicalSort [] = some []

/-- An edge-free graph on `n` vertices is sorted as `[0, 1, …, n-1]`. -/
def no_edges_prop : Prop :=
  ∀ n : Nat, topologicalSort (List.replicate n []) = some (List.range n)

/-- An order is returned iff some topological order exists. -/
def isSome_iff_prop : Prop :=
  ∀ graph : List (List Nat),
    (topologicalSort graph).isSome = true ↔ ∃ order : List Nat, isTopologicalOrder graph order = true

/-! ### Auxiliary lemmas about the checker and the permutation enumeration -/

theorem validGraph_of_isTopologicalOrder {graph : List (List Nat)} {order : List Nat}
    (h : isTopologicalOrder graph order = true) : validGraph graph = true := by
  unfold isTopologicalOrder at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

theorem perm_of_isTopologicalOrder {graph : List (List Nat)} {order : List Nat}
    (h : isTopologicalOrder graph order = true) : order.Perm (List.range graph.length) := by
  unfold isTopologicalOrder at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

theorem edges_of_isTopologicalOrder {graph : List (List Nat)} {order : List Nat}
    (h : isTopologicalOrder graph order = true) {u v : Nat}
    (hu : u < graph.length) (hv : v ∈ graph.getD u []) :
    position order u < position order v := by
  unfold isTopologicalOrder at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  exact h.2 u hu v hv

/-- The literal Python test `sorted(order) == list(range(n))` holds exactly when
`order` is a permutation of `range n`. -/
theorem sortedEqRange_iff_perm (order : List Nat) (n : Nat) :
    sortedEqRange order n = true ↔ order.Perm (List.range n) := by
  unfold sortedEqRange
  rw [beq_iff_eq]
  constructor
  · intro h
    rw [← h]
    exact (List.mergeSort_perm order _).symm
  · intro h
    have h1 : (order.mergeSort (fun a b => decide (a ≤ b))).Perm (List.range n) :=
      (List.mergeSort_perm order _).trans h
    have h2 : (order.mergeSort (fun a b => decide (a ≤ b))).Pairwise
        (fun a b => decide (a ≤ b) = true) :=
      List.sorted_mergeSort (fun a b c hab hbc => by simp at *; omega)
        (fun a b => by simp; omega) order
    have h3 : (order.mergeSort (fun a b => decide (a ≤ b))).Sorted (· ≤ ·) :=
      h2.imp (fun h => by simpa using h)
    have h4 : (List.range n).Sorted (· ≤ ·) := List.pairwise_lt_range.imp le_of_lt
    exact List.eq_of_perm_of_sorted h1 h3 h4

/-- Along a directed walk the positions in a topological order never decrease. -/
theorem position_le_of_chain {graph : List (List Nat)} {order : List Nat}
    (h : isTopologicalOrder graph order = true) :
    ∀ (c : List Nat) (v : Nat), (∀ u ∈ v :: c, u < graph.length) →
      List.Chain (fun a b => b ∈ graph.getD a []) v c →
      position order v ≤ position order (c.getLastD v)
  | [], v, _, _ => le_refl _
  | w :: rest, v, hmem, hchain => by
    rw [List.chain_cons] at hchain
    have hv : v < graph.length := hmem v (by simp)
    have h1 : position order v < position order w :=
      edges_of_isTopologicalOrder h hv hchain.1
    have h2 := position_le_of_chain h rest w
      (fun u hu => hmem u (by simp at hu ⊢; tauto)) hchain.2
    rw [List.getLastD_cons]
    omega

/-- Every permutation of `xs` is enumerated by `permsAux xs.length xs`. -/
theorem mem_permsAux_of_perm : ∀ (fuel : Nat) (xs l : List Nat),
    xs.length = fuel → l.Perm xs → l ∈ permsAux fuel xs
  | 0, xs, l, hlen, hperm => by
    have hxs : xs = [] := List.eq_nil_of_length_eq_zero hlen
    subst hxs
    have hl : l = [] := hperm.eq_nil
    simp [permsAux, hl]
  | fuel + 1, xs, l, hlen, hperm => by
    cases l with
    | nil =>
      have := hperm.length_eq
      simp at this
      omega
    | cons y l' =>
      have hy : y ∈ xs := hperm.subset (List.mem_cons_self)
      have hperm' : l'.Perm (xs.erase y) :=
        (hperm.trans (List.perm_cons_erase hy)).cons_inv
      have hlen' : (xs.erase y).length = fuel := by
        rw [List.length_erase_of_mem hy]; omega
      have ih := mem_permsAux_of_perm fuel (xs.erase y) l' hlen' hperm'
      simp only [permsAux, List.mem_flatMap, List.mem_map]
      exact ⟨y, hy, l', ih, rfl⟩

theorem mem_perms_of_perm {xs l : List Nat} (h : l.Perm xs) : l ∈ perms xs :=
  mem_permsAux_of_perm xs.length xs l rfl h

/-- For a sorted input the enumeration is strictly increasing in lexicographic order. -/
theorem pairwise_lex_permsAux : ∀ (fuel : Nat) (xs : List Nat),
    xs.length = fuel → xs.Pairwise (· < ·) →
    (permsAux fuel xs).Pairwise (List.Lex (· < ·))
  | 0, xs, _, _ => by simp [permsAux]
  | fuel + 1, xs, hlen, hsorted => by
    simp only [permsAux]
    rw [List.pairwise_flatMap]
    constructor
    · intro x hx
      rw [List.pairwise_map]
      have hlen' : (xs.erase x).length = fuel := by
        rw [List.length_erase_of_mem hx]; omega
      have hsorted' : (xs.erase x).Pairwise (· < ·) := hsorted.sublist List.erase_sublist
      have ih := pairwise_lex_permsAux fuel (xs.erase x) hlen' hsorted'
      exact ih.imp (fun h => List.Lex.cons h)
    · refine hsorted.imp ?_
      intro a b hab p hp q hq
      rw [List.mem_map] at hp hq
      obtain ⟨p', _, rfl⟩ := hp
      obtain ⟨q', _, rfl⟩ := hq
      exact List.Lex.rel hab

theorem pairwise_lex_perms_range (n : Nat) :
    (perms (List.range n)).Pairwise (List.Lex (· < ·)) :=
  pairwise_lex_permsAux _ _ rfl List.pairwise_lt_range

/-- The first enumerated permutation of `xs` is `xs` itself. -/
theorem permsAux_head? : ∀ xs : List Nat, (permsAux xs.length xs).head? = some xs
  | [] => rfl
  | x :: xs' => by
    have ih := permsAux_head? xs'
    simp only [List.length_cons, permsAux, List.flatMap_cons, List.erase_cons_head]
    cases hp : permsAux xs'.length xs' with
    | nil => simp [hp] at ih
    | cons p rest =>
      rw [hp] at ih
      simp at ih
      subst ih
      simp

/-! ### Theorems -/

theorem sound_thm : sound_prop := by
  intro graph order h
  unfold topologicalSort at h
  split_ifs at h with hv
  exact List.find?_some h

theorem malformed_thm : malformed_prop := by
  intro graph hv
  unfold topologicalSort
  simp [hv]

theorem complete_thm : complete_prop := by
  intro graph h order
  unfold topologicalSort at h
  split_ifs at h with hv
  · rw [List.find?_eq_none] at h
    by_contra hc
    simp only [Bool.not_eq_false] at hc
    have hmem : order ∈ perms (List.range graph.length) :=
      mem_perms_of_perm (perm_of_isTopologicalOrder hc)
    exact h order hmem hc
  · simp only [Bool.not_eq_true] at hv
    simp [isTopologicalOrder, hv]

theorem perm_thm : perm_prop := by
  intro graph order h
  exact perm_of_isTopologicalOrder (sound_thm graph order h)

theorem edges_thm : edges_prop := by
  intro graph order h u v hu hv
  exact edges_of_isTopologicalOrder (sound_thm graph order h) hu hv

theorem self_loop_thm : self_loop_prop := by
  intro graph u hu hmem
  cases h : topologicalSort graph with
  | none => rfl
  | some order =>
    have := edges_thm graph order h u u hu hmem
    exact absurd this (lt_irrefl _)

theorem two_cycle_thm : two_cycle_prop := by
  intro graph u v hu hv huv hvu
  cases h : topologicalSort graph with
  | none => rfl
  | some order =>
    have h1 := edges_thm graph order h u v hu huv
    have h2 := edges_thm graph order h v u hv hvu
    omega

theorem cycle_thm : cycle_prop := by
  intro graph v c hmem hchain hback
  cases h : topologicalSort graph with
  | none => rfl
  | some order =>
    have hs := sound_thm graph order h
    have h1 := position_le_of_chain hs c v hmem hchain
    have hlast : c.getLastD v < graph.length := hmem _ List.getLastD_mem_cons
    have h2 := edges_of_isTopologicalOrder hs hlast hback
    omega

theorem checker_thm : checker_prop := by
  intro graph order
  unfold isTopologicalOrder
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  tauto

theorem lex_first_thm : lex_first_prop := by
  intro graph order order' hsome hvalid hlex
  unfold topologicalSort at hsome
  split_ifs at hsome with hv
  · rw [List.find?_eq_some_iff_append] at hsome
    obtain ⟨_, as, bs, heq, hall⟩ := hsome
    have hmem : order' ∈ perms (List.range graph.length) :=
      mem_perms_of_perm (perm_of_isTopologicalOrder hvalid)
    have hpw := pairwise_lex_perms_range graph.length
    rw [heq] at hmem hpw
    rw [List.pairwise_append, List.pairwise_cons] at hpw
    obtain ⟨_, ⟨hafter, _⟩, _⟩ := hpw
    rw [List.mem_append, List.mem_cons] at hmem
    rcases hmem with h | h | h
    · have := hall order' h
      simp [hvalid] at this
    · subst h
      exact asymm hlex hlex
    · exact asymm (hafter order' h) hlex

theorem empty_thm : empty_prop := by
  unfold empty_prop topologicalSort
  rfl

theorem no_edges_thm : no_edges_prop := by
  intro n
  have hv : validGraph (List.replicate n []) = true := by simp [validGraph]
  have hlen : (List.replicate n ([] : List Nat)).length = n := List.length_replicate
  have hh := permsAux_head? (List.range n)
  rw [List.length_range] at hh
  obtain ⟨rest, hrest⟩ : ∃ rest, permsAux n (List.range n) = List.range n :: rest := by
    cases hp : permsAux n (List.range n) with
    | nil => simp [hp] at hh
    | cons p rest =>
      rw [hp] at hh
      simp at hh
      exact ⟨rest, by rw [hh]⟩
  unfold topologicalSort
  rw [if_pos hv]
  simp only [perms, hlen, List.length_range, hrest]
  rw [List.find?_cons_of_pos]
  simp only [isTopologicalOrder, hv, hlen, Bool.true_and, decide_eq_true (List.Perm.refl _),
    List.all_eq_true, List.mem_range]
  intro u hu v hv'
  simp [List.getD_eq_getElem?_getD, hu] at hv'

theorem isSome_iff_thm : isSome_iff_prop := by
  intro graph
  constructor
  · intro h
    rw [Option.isSome_iff_exists] at h
    obtain ⟨order, horder⟩ := h
    exact ⟨order, sound_thm graph order horder⟩
  · rintro ⟨order, horder⟩
    cases h : topologicalSort graph with
    | none =>
      have := complete_thm graph h order
      rw [horder] at this
      simp at this
    | some o => rfl

/-! ## Post-condition -/

/-- Post-condition of `topological_sort`:
* a returned order passes the checker, contains every vertex exactly once and is
  the lexicographically first valid order (the first one found by
  `itertools.permutations`);
* `none` is returned exactly when no topological order exists;
* malformed graphs give `none`. -/
def Post_prop (graph : List (List Nat)) (result : Option (List Nat)) : Prop :=
  (∀ order : List Nat, result = some order →
      isTopologicalOrder graph order = true ∧
      order.Perm (List.range graph.length) ∧
      (∀ order' : List Nat, isTopologicalOrder graph order' = true →
        ¬ List.Lex (· < ·) order' order)) ∧
  (result = none → ∀ order : List Nat, isTopologicalOrder graph order = false) ∧
  (validGraph graph = false → result = none)

/-! ## Property-based tests -/

/-- Test helper: all lists of length `k` whose entries are drawn from `choices`. -/
def allLists {α : Type} (k : Nat) (choices : List α) : List (List α) :=
  match k with
  | 0 => [[]]
  | k + 1 => choices.flatMap (fun c => (allLists k choices).map (c :: ·))

/-- Test helper: all graphs on `n` vertices whose neighbour lists are sublists of
`range m` (all valid iff `m ≤ n`). -/
def allGraphs (n m : Nat) : List (List (List Nat)) := allLists n (List.range m).sublists

/-- Test helper: `c` describes a closed walk `v → c₀ → ⋯ → cₖ → v` of `g` inside the
vertex range (the hypotheses of `cycle_prop`). -/
def cycleCheck (g : List (List Nat)) (v : Nat) (c : List Nat) : Bool :=
  (v :: c).all (· < g.length) &&
  decide (List.Chain (fun a b => b ∈ g.getD a []) v c) &&
  (g.getD (c.getLastD v) []).contains v

/-- Executable form of `Post_prop` (candidate orders range over all permutations,
the only orders the checker can accept). -/
def postCheck (graph : List (List Nat)) : Bool :=
  let n := graph.length
  let result := topologicalSort graph
  (match result with
   | some order =>
       isTopologicalOrder graph order && decide (order.Perm (List.range n)) &&
       (perms (List.range n)).all (fun order' =>
         !isTopologicalOrder graph order' || !decide (List.Lex (· < ·) order' order))
   | none => (perms (List.range n)).all (fun order' => !isTopologicalOrder graph order')) &&
  (validGraph graph || result.isNone)

example : (allGraphs 0 0).length = 1 := by native_decide
example : (allGraphs 3 3).length = 512 := by native_decide

-- Bounded PBTs: exhaustive over all graphs on ≤ 3 vertices with valid neighbour lists.
example : (allGraphs 0 0).all postCheck = true := by native_decide
example : (allGraphs 1 1).all postCheck = true := by native_decide
example : (allGraphs 2 2).all postCheck = true := by native_decide
example : (allGraphs 3 3).all postCheck = true := by native_decide
-- sound_prop
example : (allGraphs 3 3).all (fun g => (topologicalSort g).all (isTopologicalOrder g)) = true := by
  native_decide
-- complete_prop
example : (allGraphs 3 3).all (fun g =>
    (topologicalSort g).isSome || (perms (List.range 3)).all (fun o => !isTopologicalOrder g o)) = true := by
  native_decide
-- perm_prop
example : (allGraphs 3 3).all (fun g =>
    (topologicalSort g).all (fun o => decide (o.Perm (List.range 3)))) = true := by native_decide
-- edges_prop
example : (allGraphs 3 3).all (fun g => (topologicalSort g).all (fun o =>
    (List.range 3).all (fun u => (g.getD u []).all (fun v => position o u < position o v)))) = true := by
  native_decide
-- lex_first_prop
example : (allGraphs 3 3).all (fun g => (topologicalSort g).all (fun o =>
    (perms (List.range 3)).all (fun o' =>
      !isTopologicalOrder g o' || !decide (List.Lex (· < ·) o' o)))) = true := by native_decide
-- self_loop_prop / two_cycle_prop
example : (allGraphs 3 3).all (fun g =>
    !((List.range 3).any (fun u => (g.getD u []).contains u)) || (topologicalSort g).isNone) = true := by
  native_decide
example : (allGraphs 3 3).all (fun g =>
    !((List.range 3).any (fun u => (List.range 3).any (fun v =>
        (g.getD u []).contains v && (g.getD v []).contains u))) || (topologicalSort g).isNone) = true := by
  native_decide
-- cycle_prop: every closed walk `v → c₀ → ⋯ → cₖ → v` of length ≤ 3 forces `none`.
example : (allGraphs 3 3).all (fun g => (List.range 3).all (fun v =>
    ((List.range 3).flatMap (fun k => allLists k (List.range 3))).all (fun c =>
      !cycleCheck g v c || (topologicalSort g).isNone))) = true := by native_decide
-- checker_prop
example : (allGraphs 3 3).all (fun g => (perms (List.range 3) ++ [[0, 0, 1], [0, 1], []]).all (fun o =>
    isTopologicalOrder g o == (validGraph g && sortedEqRange o 3 &&
      (List.range 3).all (fun u => (g.getD u []).all (fun v => position o u < position o v))))) = true := by
  native_decide
-- sortedEqRange_iff_perm
example : (allLists 3 (List.range 4)).all (fun o => sortedEqRange o 3 == decide (o.Perm (List.range 3))) = true := by
  native_decide
-- malformed_prop: neighbour lists drawn from `range 4` on 3 vertices (some are invalid).
example : (allGraphs 3 4).all (fun g => validGraph g || (topologicalSort g).isNone) = true := by
  native_decide
example : (allGraphs 2 4).all postCheck = true := by native_decide
-- no_edges_prop / empty_prop
example : (List.range 7).all (fun n => topologicalSort (List.replicate n []) == some (List.range n)) = true := by
  native_decide
-- isSome_iff_prop
example : (allGraphs 3 3).all (fun g =>
    (topologicalSort g).isSome == (perms (List.range 3)).any (fun o => isTopologicalOrder g o)) = true := by
  native_decide

-- Randomized PBTs (Plausible).  Random graphs are truncated to at most 5 vertices (so
-- the permutation search stays cheap) and neighbour indices are reduced modulo 6, which
-- yields a mix of valid and malformed graphs.
def shrinkGraph (g : List (List Nat)) : List (List Nat) :=
  (g.take 5).map (fun ns => ns.map (· % 6))

-- Post_prop
#eval Plausible.Testable.check (∀ g : List (List Nat), postCheck (shrinkGraph g) = true)
-- sound_prop
#eval Plausible.Testable.check (∀ g : List (List Nat),
  (topologicalSort (shrinkGraph g)).all (isTopologicalOrder (shrinkGraph g)) = true)
-- perm_prop
#eval Plausible.Testable.check (∀ g : List (List Nat),
  (topologicalSort (shrinkGraph g)).all
    (fun o => decide (o.Perm (List.range (shrinkGraph g).length))) = true)
-- edges_prop
#eval Plausible.Testable.check (∀ g : List (List Nat),
  (topologicalSort (shrinkGraph g)).all (fun o => (List.range (shrinkGraph g).length).all
    (fun u => ((shrinkGraph g).getD u []).all (fun v => position o u < position o v))) = true)
-- complete_prop (over all permutations, the only orders the checker can accept)
#eval Plausible.Testable.check (∀ g : List (List Nat),
  ((topologicalSort (shrinkGraph g)).isSome ||
    (perms (List.range (shrinkGraph g).length)).all
      (fun o => !isTopologicalOrder (shrinkGraph g) o)) = true)
-- lex_first_prop
#eval Plausible.Testable.check (∀ g : List (List Nat),
  (topologicalSort (shrinkGraph g)).all (fun o =>
    (perms (List.range (shrinkGraph g).length)).all (fun o' =>
      !isTopologicalOrder (shrinkGraph g) o' || !decide (List.Lex (· < ·) o' o))) = true)
-- malformed_prop (on untruncated indices; at most 7 vertices)
#eval Plausible.Testable.check (∀ g : List (List Nat),
  (validGraph (g.take 7) || (topologicalSort (g.take 7)).isNone) = true)
-- self_loop_prop
#eval Plausible.Testable.check (∀ g : List (List Nat),
  (!((List.range (shrinkGraph g).length).any (fun u => ((shrinkGraph g).getD u []).contains u)) ||
    (topologicalSort (shrinkGraph g)).isNone) = true)
-- cycle_prop
#eval Plausible.Testable.check (∀ (g : List (List Nat)) (v : Nat) (c : List Nat),
  (!cycleCheck (shrinkGraph g) (v % 6) (c.map (· % 6)) ||
    (topologicalSort (shrinkGraph g)).isNone) = true)
-- sortedEqRange_iff_perm
#eval Plausible.Testable.check (∀ (o : List Nat) (n : Nat),
  sortedEqRange o n == decide (o.Perm (List.range n)))
-- isSome_iff_prop
#eval Plausible.Testable.check (∀ g : List (List Nat),
  ((topologicalSort (shrinkGraph g)).isSome ==
    (perms (List.range (shrinkGraph g).length)).any (fun o => isTopologicalOrder (shrinkGraph g) o)) = true)
-- checker implies validity
#eval Plausible.Testable.check (∀ g : List (List Nat), ∀ o : List Nat,
  (!isTopologicalOrder g o || validGraph g) = true)
-- no_edges_prop / empty_prop
#eval Plausible.Testable.check (∀ n : Nat,
  topologicalSort (List.replicate (n % 7) []) = some (List.range (n % 7)))

/-! ## Correctness theorem -/

theorem topologicalSort_correct_thm (graph : List (List Nat)) (_ : Pre graph) :
    Post_prop graph (topologicalSort graph) := by
  refine ⟨?_, ?_, ?_⟩
  · intro order hs
    exact ⟨sound_thm graph order hs, perm_thm graph order hs,
      fun order' ho' => lex_first_thm graph order order' hs ho'⟩
  · intro hn order
    exact complete_thm graph hn order
  · intro hv
    exact malformed_thm graph hv

/-- The post-condition in fact holds for every input (the Python function handles
malformed graphs itself by returning `None`). -/
theorem topologicalSort_total_thm (graph : List (List Nat)) :
    Post_prop graph (topologicalSort graph) := by
  refine ⟨?_, ?_, ?_⟩
  · intro order hs
    exact ⟨sound_thm graph order hs, perm_thm graph order hs,
      fun order' ho' => lex_first_thm graph order order' hs ho'⟩
  · intro hn order
    exact complete_thm graph hn order
  · intro hv
    exact malformed_thm graph hv

/-! ## Imperative implementation -/

/-- Imperative checker (Python `is_topological_order`): nested loops over the
adjacency list with a mutable flag. -/
def isTopologicalOrderImp (graph : List (List Nat)) (order : List Nat) : Bool := Id.run do
  if !validGraph graph then
    return false
  let n := graph.length
  if !(decide (order.Perm (List.range n))) then
    return false
  let mut ok := true
  for u in List.range n do
    for v in graph.getD u [] do
      if !(position order u < position order v) then
        ok := false
  return ok

/-- Imperative search (Python `topological_sort`): iterate over the candidate
permutations with a mutable result, stopping at the first valid one. -/
def topologicalSortImp (graph : List (List Nat)) : Option (List Nat) := Id.run do
  if !validGraph graph then
    return none
  let n := graph.length
  let mut result : Option (List Nat) := none
  for candidate in perms (List.range n) do
    if isTopologicalOrderImp graph candidate then
      result := some candidate
      break
  return result

/-! ## Imperative tests -/

example : topologicalSortImp [[1], [2], []] = some [0, 1, 2] := by native_decide
example : (topologicalSortImp [[1, 2], [3], [3], []]).all
    (fun o => isTopologicalOrderImp [[1, 2], [3], [3], []] o) = true := by native_decide
example : topologicalSortImp [] = some [] := by native_decide
example : topologicalSortImp [[], [], []] = some [0, 1, 2] := by native_decide
example : (topologicalSortImp [[2], [], []]).all
    (fun o => isTopologicalOrderImp [[2], [], []] o && decide (o.idxOf 0 < o.idxOf 2)) = true := by
  native_decide
example : topologicalSortImp [[1], [0]] = none := by native_decide
example : topologicalSortImp [[0]] = none := by native_decide
example : topologicalSortImp [[2]] = none := by native_decide
example : isTopologicalOrderImp [[1], [2], []] [2, 1, 0] = false := by native_decide
example : (allGraphs 3 4).all (fun g => topologicalSortImp g == topologicalSort g) = true := by
  native_decide

#eval topologicalSortImp [[1], [2], []]
#eval topologicalSortImp [[1], [0]]

/-! ## Equivalence of the functional and imperative implementations -/

/-! Small lemmas about the `Id` monad and `for` loops, used to reduce the
imperative programs to their functional counterparts. -/

theorem Id_bind_eq {α β : Type} (x : Id α) (f : α → Id β) : (x >>= f) = f x := rfl
theorem Id_pure_eq {α : Type} (x : α) : (pure x : Id α) = x := rfl
theorem Id_run_eq {α : Type} (x : Id α) : Id.run x = x := rfl

/-- Body of the inner loop of `isTopologicalOrderImp`: clearing the flag when a
check fails is the same as `and`-ing the check into the flag. -/
theorem ite_not_yield (c r : Bool) :
    (if (!c) = true then ForInStep.yield false
      else ForInStep.yield r : Id (ForInStep Bool)) = ForInStep.yield (r && c) := by
  cases c <;> cases r <;> rfl

/-- A `for` loop that `and`s a predicate into a flag computes `List.all`. -/
theorem forIn_yield_and {α : Type} (l : List α) (b : Bool) (p : α → Bool) :
    (forIn (m := Id) l b fun a r => (ForInStep.yield (r && p a) : Id (ForInStep Bool))) =
      (b && l.all p) := by
  induction l generalizing b with
  | nil => simp only [List.forIn_nil, Id_pure_eq, List.all_nil, Bool.and_true]
  | cons a l ih =>
    rw [List.forIn_cons]
    simp only [Id_bind_eq, ih, List.all_cons, Bool.and_assoc]

/-- A `for` loop that `break`s at the first element satisfying `p` computes
`List.find?`. -/
theorem forIn_find {α : Type} (l : List α) (p : α → Bool) :
    (forIn (m := Id) l (none : Option α) fun c r =>
        (if p c = true then ForInStep.done (some c) else ForInStep.yield r :
          Id (ForInStep (Option α)))) = l.find? p := by
  induction l with
  | nil => simp only [List.forIn_nil, Id_pure_eq, List.find?_nil]
  | cons c l ih =>
    rw [List.forIn_cons]
    by_cases h : p c = true
    · simp only [Id_bind_eq, if_pos h, List.find?_cons_of_pos h]
      rfl
    · simp only [Id_bind_eq, if_neg h, List.find?_cons_of_neg h]
      exact ih

/-- The imperative checker agrees with the functional checker. -/
theorem isTopologicalOrderImp_eq_thm (graph : List (List Nat)) (order : List Nat) :
    isTopologicalOrderImp graph order = isTopologicalOrder graph order := by
  unfold isTopologicalOrderImp isTopologicalOrder
  simp only [Id_run_eq, Id_bind_eq, Id_pure_eq]
  simp only [ite_not_yield, forIn_yield_and, Bool.true_and]
  by_cases hv : validGraph graph = true
  · by_cases hp : order.Perm (List.range graph.length)
    · simp [hv, hp]
    · simp [hv, hp]
  · simp [hv]

/-- The imperative topological sort agrees with the functional one. -/
theorem topologicalSortImp_eq_thm (graph : List (List Nat)) :
    topologicalSortImp graph = topologicalSort graph := by
  unfold topologicalSortImp topologicalSort
  simp only [Id_run_eq, Id_bind_eq, Id_pure_eq]
  simp only [forIn_find]
  by_cases hv : validGraph graph = true
  · have hfun : isTopologicalOrderImp graph = fun order => isTopologicalOrder graph order :=
      funext (isTopologicalOrderImp_eq_thm graph)
    simp [hv, hfun]
  · simp [hv]

/-- Consequently the imperative implementation satisfies the same specification. -/
theorem topologicalSortImp_correct_thm (graph : List (List Nat)) (_ : Pre graph) :
    Post_prop graph (topologicalSortImp graph) := by
  rw [topologicalSortImp_eq_thm]
  exact topologicalSort_total_thm graph

end topological_sort
