import Mathlib

/-!
# Topological sorting for finite directed graphs

Lean 4 translation of the Python program `topological_sort.py`.

A directed graph over the vertices `0 .. n-1` is an adjacency list
`graph : List (List Nat)`, where `graph[u]` lists the outgoing neighbours of `u`.

* `pre graph` is the Python `pre`: every neighbour must be a vertex `v < n`.
  The Python `isinstance` checks (the graph is a list, every entry is a list,
  every neighbour is an `int`) and the lower bound `0 <= v` are enforced by
  Lean's types: a non-list entry such as `"not a list"` or a negative vertex is
  not expressible as a `List (List Nat)`.
* `is_topological_order graph order` is the executable checker of the Python
  program: `pre graph`, `sorted(order) == list(range(n))` (via `mergeSort`) and
  `position[u] < position[v]` for every edge `u → v` (positions via `idxOf`).
* `topological_sort graph` enumerates all permutations of `range n` in the
  lexicographic order produced by `itertools.permutations` and returns the first
  one accepted by the checker; it returns `none` for a malformed graph or when
  no topological order exists (the graph contains a directed cycle).

Edge cases from the Python docstring:
- the empty graph has the empty topological order (`empty_thm`);
- disconnected DAGs contain every vertex exactly once (`vertices_thm`);
- cycles return `none` because no topological order exists (`complete_thm`);
- malformed adjacency lists return `none` (`malformed_thm`).
-/

namespace topological_sort

/-! ## Functional implementation -/

/-- Python `pre`: the graph is a valid adjacency list over `0 .. n-1`, i.e. every
neighbour `v` satisfies `0 <= v < n` (the lower bound is automatic for `Nat`). -/
def pre (graph : List (List Nat)) : Bool :=
  graph.all fun ns => ns.all fun v => v < graph.length

/-- All permutations of `xs`, built with `k` levels of recursion: a permutation is
some element `x ∈ xs` (taken in list order) followed by a permutation of
`xs.erase x`.  For `k = xs.length` and a sorted `xs` this is exactly the
lexicographic enumeration of `itertools.permutations(xs)`. -/
def lexPermsAux : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | k + 1, xs => xs.flatMap fun x => (lexPermsAux k (xs.erase x)).map (x :: ·)

/-- `itertools.permutations(xs)`: all permutations of `xs` in lexicographic order
(when `xs` is sorted). -/
def lexPerms (xs : List Nat) : List (List Nat) :=
  lexPermsAux xs.length xs

/-- `all(position[u] < position[v] for u, ns in enumerate(graph) for v in ns)`,
where `u` is the index of the adjacency list `ns` (starting from the given
counter) and `position[x] = order.idxOf x`. -/
def edgesOk (order : List Nat) : Nat → List (List Nat) → Bool
  | _, [] => true
  | u, ns :: rest =>
    (ns.all fun v => order.idxOf u < order.idxOf v) && edgesOk order (u + 1) rest

/-- Python `is_topological_order`: the executable checker. -/
def is_topological_order (graph : List (List Nat)) (order : List Nat) : Bool :=
  pre graph && (order.mergeSort == List.range graph.length) && edgesOk order 0 graph

/-- Python `topological_sort`: the first permutation of `range n` (in the order
of `itertools.permutations`) accepted by `is_topological_order`, or `none`. -/
def topological_sort (graph : List (List Nat)) : Option (List Nat) :=
  if pre graph then
    (lexPerms (List.range graph.length)).find? fun order => is_topological_order graph order
  else
    none

/-! ## Unit tests (the Python `check` function) -/

-- g1 = [[1], [2], []]
example : topological_sort [[1], [2], []] = some [0, 1, 2] := by native_decide
example : (topological_sort [[1], [2], []]).all
    (fun order => is_topological_order [[1], [2], []] order) = true := by native_decide
-- g2 = [[1, 2], [3], [3], []]
example : (topological_sort [[1, 2], [3], [3], []]).isSome = true := by native_decide
example : (topological_sort [[1, 2], [3], [3], []]).all
    (fun order => is_topological_order [[1, 2], [3], [3], []] order) = true := by native_decide
example : (topological_sort [[1, 2], [3], [3], []]).all
    (fun order => order.mergeSort == [0, 1, 2, 3]) = true := by native_decide
example : topological_sort [[1, 2], [3], [3], []] = some [0, 1, 2, 3] := by native_decide
-- g3 = []
example : topological_sort [] = some [] := by native_decide
-- g4 = [[], [], []]
example : topological_sort [[], [], []] = some [0, 1, 2] := by native_decide
-- g5 = [[2], [], []]
example : (topological_sort [[2], [], []]).all
    (fun order => is_topological_order [[2], [], []] order) = true := by native_decide
example : (topological_sort [[2], [], []]).all
    (fun order => order.idxOf 0 < order.idxOf 2) = true := by native_decide
example : topological_sort [[2], [], []] = some [0, 1, 2] := by native_decide
-- cycles
example : topological_sort [[1], [0]] = none := by native_decide
example : topological_sort [[0]] = none := by native_decide
-- malformed: neighbour out of range
example : topological_sort [[2]] = none := by native_decide
example : pre [[2]] = false := by native_decide
-- `[[1], "not a list"]` is not a `List (List Nat)`; such inputs are rejected by typing.
-- the checker itself
example : is_topological_order [[1], [2], []] [0, 1, 2] = true := by native_decide
example : is_topological_order [[1], [2], []] [0, 2, 1] = false := by native_decide
example : is_topological_order [[1], [2], []] [0, 1] = false := by native_decide
example : is_topological_order [[2]] [0] = false := by native_decide
-- enumeration order of `itertools.permutations(range(3))`
example : lexPerms [0, 1, 2] =
    [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]] := by native_decide

#eval topological_sort [[1], [2], []]
#eval topological_sort [[1, 2], [3], [3], []]
#eval topological_sort [[], [], []]
#eval topological_sort [[1], [0]]
#eval topological_sort [[2]]

/-! ## Pre-condition -/

/-- The graph is a well-formed adjacency list over `0 .. n-1` (Python `pre`). -/
def Pre (graph : List (List Nat)) : Prop :=
  ∀ ns ∈ graph, ∀ v ∈ ns, v < graph.length

theorem pre_iff (graph : List (List Nat)) : pre graph = true ↔ Pre graph := by
  simp [pre, Pre]

/-- `order` is a topological order of `graph`: it lists every vertex `0 .. n-1`
exactly once and places `u` before `v` for every edge `u → v`. -/
def IsTopologicalOrder (graph : List (List Nat)) (order : List Nat) : Prop :=
  order.Perm (List.range graph.length) ∧
    ∀ (u : Nat) (hu : u < graph.length), ∀ v ∈ graph[u], order.idxOf u < order.idxOf v

/-! ## Helper lemmas -/

theorem mem_lexPermsAux : ∀ (k : Nat) (xs order : List Nat), xs.length = k →
    (order ∈ lexPermsAux k xs ↔ order.Perm xs)
  | 0, xs, order, h => by
    rw [List.length_eq_zero_iff] at h
    subst h
    simp [lexPermsAux, List.perm_nil]
  | k + 1, xs, order, h => by
    simp only [lexPermsAux, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨x, hx, rest, hrest, rfl⟩
      have hlen : (xs.erase x).length = k := by
        rw [List.length_erase_of_mem hx, h]
        rfl
      rw [mem_lexPermsAux k _ _ hlen] at hrest
      exact List.cons_perm_iff_perm_erase.mpr ⟨hx, hrest⟩
    · intro hperm
      cases order with
      | nil =>
        have := hperm.length_eq
        simp [h] at this
      | cons x rest =>
        rw [List.cons_perm_iff_perm_erase] at hperm
        obtain ⟨hx, hrest⟩ := hperm
        have hlen : (xs.erase x).length = k := by
          rw [List.length_erase_of_mem hx, h]
          rfl
        exact ⟨x, hx, rest, (mem_lexPermsAux k _ _ hlen).mpr hrest, rfl⟩

theorem mem_lexPerms (xs order : List Nat) : order ∈ lexPerms xs ↔ order.Perm xs :=
  mem_lexPermsAux xs.length xs order rfl

theorem pairwise_lexPermsAux : ∀ (k : Nat) (xs : List Nat), xs.length = k →
    xs.Pairwise (· < ·) → (lexPermsAux k xs).Pairwise (List.Lex (· < ·))
  | 0, xs, _, _ => by simp [lexPermsAux]
  | k + 1, xs, h, hs => by
    simp only [lexPermsAux]
    rw [List.pairwise_flatMap]
    constructor
    · intro x hx
      rw [List.pairwise_map]
      have hlen : (xs.erase x).length = k := by
        rw [List.length_erase_of_mem hx, h]
        rfl
      have ih := pairwise_lexPermsAux k (xs.erase x) hlen (hs.sublist List.erase_sublist)
      exact ih.imp fun hab => List.Lex.cons hab
    · refine hs.imp ?_
      intro a b hab
      simp only [List.mem_map]
      rintro x ⟨ra, -, rfl⟩ y ⟨rb, -, rfl⟩
      exact List.Lex.rel hab

theorem pairwise_lexPerms_range (n : Nat) :
    (lexPerms (List.range n)).Pairwise (List.Lex (· < ·)) :=
  pairwise_lexPermsAux _ (List.range n) rfl List.pairwise_lt_range

/-- `find?` returns the first element satisfying `p`; in a `Pairwise R` list every
other element satisfying `p` is `R`-after it. -/
theorem find?_first {α : Type} {R : α → α → Prop} {p : α → Bool} :
    ∀ {l : List α} {a : α}, l.Pairwise R → l.find? p = some a →
      ∀ b ∈ l, p b = true → a = b ∨ R a b
  | [], _, _, hf => by simp at hf
  | x :: rest, a, hp, hf => by
    rw [List.pairwise_cons] at hp
    intro b hb hpb
    by_cases hx : p x = true
    · rw [List.find?_cons_of_pos hx] at hf
      cases hf
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inl rfl
      · exact Or.inr (hp.1 b hb')
    · rw [List.find?_cons_of_neg hx] at hf
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd hpb hx
      · exact find?_first hp.2 hf b hb' hpb

theorem mergeSort_eq_range_iff (order : List Nat) (n : Nat) :
    order.mergeSort = List.range n ↔ order.Perm (List.range n) := by
  constructor
  · intro h
    rw [← h]
    exact (List.mergeSort_perm order _).symm
  · intro h
    apply List.Perm.eq_of_sorted (le := fun a b => a ≤ b)
    · intro a b _ _ hab hba
      exact le_antisymm hab hba
    · have := List.sorted_mergeSort (le := fun a b : Nat => decide (a ≤ b)) ?_ ?_ order
      · exact this.imp fun h => by simpa using h
      · intro a b c hab hbc
        simp only [decide_eq_true_eq] at *
        omega
      · intro a b
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        omega
    · exact List.pairwise_le_range
    · exact (List.mergeSort_perm order _).trans h

theorem edgesOk_iff (order : List Nat) : ∀ (u : Nat) (gs : List (List Nat)),
    edgesOk order u gs = true ↔
      ∀ (i : Nat) (hi : i < gs.length), ∀ v ∈ gs[i], order.idxOf (u + i) < order.idxOf v
  | u, [] => by simp [edgesOk]
  | u, ns :: rest => by
    simp only [edgesOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
      edgesOk_iff order (u + 1) rest]
    constructor
    · rintro ⟨h0, hrest⟩ i hi v hv
      cases i with
      | zero => simpa using h0 v (by simpa using hv)
      | succ i =>
        have := hrest i (by simpa using hi) v (by simpa using hv)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
    · intro h
      refine ⟨fun v hv => by simpa using h 0 (by simp) v (by simpa using hv), ?_⟩
      intro i hi v hv
      have := h (i + 1) (by simpa using hi) v (by simpa using hv)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem is_topological_order_iff (graph : List (List Nat)) (order : List Nat) :
    is_topological_order graph order = true ↔ Pre graph ∧ IsTopologicalOrder graph order := by
  simp only [is_topological_order, Bool.and_eq_true, beq_iff_eq, pre_iff,
    edgesOk_iff, mergeSort_eq_range_iff, IsTopologicalOrder, Nat.zero_add, and_assoc]

theorem pre_of_some (graph : List (List Nat)) (order : List Nat)
    (h : topological_sort graph = some order) : pre graph = true := by
  by_contra hp
  unfold topological_sort at h
  rw [if_neg hp] at h
  exact Option.noConfusion h

/-! ## Properties -/

/-- Malformed adjacency lists (some neighbour is not a vertex) return `None`. -/
def malformed_prop (graph : List (List Nat)) : Prop :=
  ¬ Pre graph → topological_sort graph = none

theorem malformed_thm (graph : List (List Nat)) : malformed_prop graph := by
  intro h
  unfold topological_sort
  rw [if_neg]
  rwa [pre_iff]

/-- The empty graph has the empty topological order. -/
def empty_prop : Prop :=
  topological_sort [] = some []

theorem empty_thm : empty_prop := by
  simp [empty_prop, topological_sort, pre, lexPerms, lexPermsAux, is_topological_order, edgesOk]

/-- Soundness: every returned order is accepted by the executable checker. -/
def sound_prop (graph : List (List Nat)) : Prop :=
  ∀ order, topological_sort graph = some order → is_topological_order graph order = true

theorem sound_thm (graph : List (List Nat)) : sound_prop graph := by
  intro order h
  have hp := pre_of_some graph order h
  unfold topological_sort at h
  rw [if_pos hp] at h
  exact List.find?_some h

/-- Every vertex `0 .. n-1` occurs exactly once in the result (this also covers
disconnected DAGs): the result is a permutation of `range n`. -/
def vertices_prop (graph : List (List Nat)) : Prop :=
  ∀ order, topological_sort graph = some order → order.Perm (List.range graph.length)

theorem vertices_thm (graph : List (List Nat)) : vertices_prop graph := by
  intro order h
  exact ((is_topological_order_iff graph order).mp (sound_thm graph order h)).2.1

/-- Every edge `u → v` is respected: `u` is placed before `v` in the result. -/
def edges_prop (graph : List (List Nat)) : Prop :=
  ∀ order, topological_sort graph = some order →
    ∀ (u : Nat) (hu : u < graph.length), ∀ v ∈ graph[u], order.idxOf u < order.idxOf v

theorem edges_thm (graph : List (List Nat)) : edges_prop graph := by
  intro order h
  exact ((is_topological_order_iff graph order).mp (sound_thm graph order h)).2.2

/-- The result, when present, is a topological order. -/
def result_prop (graph : List (List Nat)) : Prop :=
  ∀ order, topological_sort graph = some order → IsTopologicalOrder graph order

theorem result_thm (graph : List (List Nat)) : result_prop graph := by
  intro order h
  exact ((is_topological_order_iff graph order).mp (sound_thm graph order h)).2

/-- Completeness: for a well-formed graph, `None` is returned only when no
topological order exists at all (the graph contains a directed cycle). -/
def complete_prop (graph : List (List Nat)) : Prop :=
  Pre graph → topological_sort graph = none → ∀ order, ¬ IsTopologicalOrder graph order

theorem complete_thm (graph : List (List Nat)) : complete_prop graph := by
  intro hpre hnone order hord
  have hp : pre graph = true := (pre_iff graph).mpr hpre
  unfold topological_sort at hnone
  rw [if_pos hp, List.find?_eq_none] at hnone
  have hmem : order ∈ lexPerms (List.range graph.length) := (mem_lexPerms _ _).mpr hord.1
  exact hnone order hmem ((is_topological_order_iff graph order).mpr ⟨hpre, hord⟩)

/-- For a well-formed graph, the search succeeds iff a topological order exists. -/
def isSome_iff_prop (graph : List (List Nat)) : Prop :=
  Pre graph → ((topological_sort graph).isSome = true ↔ ∃ order, IsTopologicalOrder graph order)

theorem isSome_iff_thm (graph : List (List Nat)) : isSome_iff_prop graph := by
  intro hpre
  constructor
  · intro h
    obtain ⟨order, hord⟩ := Option.isSome_iff_exists.mp h
    exact ⟨order, result_thm graph order hord⟩
  · rintro ⟨order, hord⟩
    by_contra hn
    have hn' : topological_sort graph = none := by
      cases hr : topological_sort graph with
      | none => rfl
      | some o => rw [hr] at hn; exact absurd rfl hn
    exact complete_thm graph hpre hn' order hord

/-- The result is the first permutation accepted in the enumeration order of
`itertools.permutations(range(n))`, i.e. the lexicographically smallest
topological order. -/
def lexmin_prop (graph : List (List Nat)) : Prop :=
  ∀ order, topological_sort graph = some order →
    ∀ order', IsTopologicalOrder graph order' → order ≤ order'

theorem lexmin_thm (graph : List (List Nat)) : lexmin_prop graph := by
  intro order h order' hord'
  have hp := pre_of_some graph order h
  unfold topological_sort at h
  rw [if_pos hp] at h
  have hpair := pairwise_lexPerms_range graph.length
  have hmem : order' ∈ lexPerms (List.range graph.length) := (mem_lexPerms _ _).mpr hord'.1
  have hp' : is_topological_order graph order' = true :=
    (is_topological_order_iff graph order').mpr ⟨(pre_iff graph).mp hp, hord'⟩
  rcases find?_first hpair h order' hmem hp' with heq | hlt
  · exact le_of_eq heq
  · exact le_of_lt hlt

/-! ## Post-condition -/

/-- Post-condition of `topological_sort graph = result` (for a well-formed graph):
the result is a topological order, it is the lexicographically smallest one, and
`none` is returned exactly when no topological order exists. -/
def Post_prop (graph : List (List Nat)) (result : Option (List Nat)) : Prop :=
  (∀ order, result = some order → IsTopologicalOrder graph order) ∧
  (∀ order, result = some order → ∀ order', IsTopologicalOrder graph order' → order ≤ order') ∧
  (result = none → ∀ order, ¬ IsTopologicalOrder graph order)

/-! ## Property-based tests -/

/-- Executable form of `IsTopologicalOrder` for testing (independent of `mergeSort`). -/
def isTopologicalOrderB (graph : List (List Nat)) (order : List Nat) : Bool :=
  decide (order.Perm (List.range graph.length)) &&
    (List.range graph.length).all fun u =>
      (graph.getD u []).all fun v => order.idxOf u < order.idxOf v

/-- Executable form of `Post_prop graph (topological_sort graph)`; the quantifiers over
orders are checked over Mathlib's (differently ordered) `List.permutations`. -/
def postCheck (graph : List (List Nat)) : Bool :=
  let perms := (List.range graph.length).permutations
  match topological_sort graph with
  | some order =>
    isTopologicalOrderB graph order &&
      perms.all fun order' => !isTopologicalOrderB graph order' || decide (order ≤ order')
  | none => perms.all fun order' => !isTopologicalOrderB graph order'

/-- All lists of length `k` with entries drawn from `choices`. -/
def allListsOfLen (choices : List α) : Nat → List (List α)
  | 0 => [[]]
  | k + 1 => choices.flatMap fun c => (allListsOfLen choices k).map (c :: ·)

/-- All well-formed graphs on `n` vertices (each adjacency list is a sublist of `range n`). -/
def allGraphs (n : Nat) : List (List (List Nat)) :=
  allListsOfLen (List.range n).sublists n

-- malformed_prop
#eval Plausible.Testable.check (cfg := { maxSize := 5 })
  (∀ graph : List (List Nat), pre graph = false → (topological_sort graph).isNone = true)
example : ((allListsOfLen (List.range 4).sublists 3).filter fun g => !pre g).all
    (fun g => (topological_sort g).isNone) = true := by native_decide
example : ((allListsOfLen (List.range 3).sublists 2).filter fun g => !pre g).all
    (fun g => (topological_sort g).isNone) = true := by native_decide

-- sound_prop
#eval Plausible.Testable.check (cfg := { maxSize := 5 })
  (∀ graph : List (List Nat),
    (topological_sort graph).all (fun order => is_topological_order graph order) = true)
example : (allGraphs 3).all
    (fun g => (topological_sort g).all fun order => is_topological_order g order) = true := by
  native_decide

-- vertices_prop
#eval Plausible.Testable.check (cfg := { maxSize := 5 })
  (∀ graph : List (List Nat),
    (topological_sort graph).all
      (fun order => decide (order.Perm (List.range graph.length))) = true)
example : (allGraphs 3).all
    (fun g => (topological_sort g).all fun order =>
      decide (order.Perm (List.range g.length))) = true := by native_decide

-- edges_prop
#eval Plausible.Testable.check (cfg := { maxSize := 5 })
  (∀ graph : List (List Nat),
    (topological_sort graph).all (fun order => (List.range graph.length).all fun u =>
      (graph.getD u []).all fun v => order.idxOf u < order.idxOf v) = true)
example : (allGraphs 3).all
    (fun g => (topological_sort g).all fun order => (List.range g.length).all fun u =>
      (g.getD u []).all fun v => order.idxOf u < order.idxOf v) = true := by native_decide

-- result_prop
#eval Plausible.Testable.check (cfg := { maxSize := 5 })
  (∀ graph : List (List Nat),
    (topological_sort graph).all (fun order => isTopologicalOrderB graph order) = true)
example : (allGraphs 3).all
    (fun g => (topological_sort g).all fun order => isTopologicalOrderB g order) = true := by
  native_decide

-- complete_prop
#eval Plausible.Testable.check (cfg := { maxSize := 5 })
  (∀ graph : List (List Nat), pre graph = true → (topological_sort graph).isNone = true →
    (List.range graph.length).permutations.all
      (fun order => !isTopologicalOrderB graph order) = true)
example : (allGraphs 3).all
    (fun g => !(topological_sort g).isNone ||
      (List.range g.length).permutations.all fun order => !isTopologicalOrderB g order) = true := by
  native_decide

-- isSome_iff_prop
#eval Plausible.Testable.check (cfg := { maxSize := 5 })
  (∀ graph : List (List Nat), pre graph = true →
    ((topological_sort graph).isSome =
      (List.range graph.length).permutations.any fun order => isTopologicalOrderB graph order))
example : (allGraphs 3).all
    (fun g => (topological_sort g).isSome ==
      (List.range g.length).permutations.any fun order => isTopologicalOrderB g order) = true := by
  native_decide

-- lexmin_prop
#eval Plausible.Testable.check (cfg := { maxSize := 5 })
  (∀ graph : List (List Nat),
    (topological_sort graph).all (fun order =>
      (List.range graph.length).permutations.all fun order' =>
        !isTopologicalOrderB graph order' || decide (order ≤ order')) = true)
example : (allGraphs 3).all
    (fun g => (topological_sort g).all fun order =>
      (List.range g.length).permutations.all fun order' =>
        !isTopologicalOrderB g order' || decide (order ≤ order')) = true := by native_decide

-- Post_prop
#eval Plausible.Testable.check (cfg := { maxSize := 5 })
  (∀ graph : List (List Nat), pre graph = true → postCheck graph = true)
example : (allGraphs 0).all postCheck = true := by native_decide
example : (allGraphs 1).all postCheck = true := by native_decide
example : (allGraphs 2).all postCheck = true := by native_decide
example : (allGraphs 3).all postCheck = true := by native_decide

/-! ## Correctness theorem -/

theorem correctness_thm (graph : List (List Nat)) (hpre : Pre graph) :
    Post_prop graph (topological_sort graph) :=
  ⟨result_thm graph, lexmin_thm graph, complete_thm graph hpre⟩

end topological_sort
