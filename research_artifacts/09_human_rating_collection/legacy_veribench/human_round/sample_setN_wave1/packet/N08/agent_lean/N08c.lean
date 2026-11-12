import Mathlib

/-!
# Topological sorting for finite directed graphs

Formalisation of the Python program `topological_sort.py`.

The Python program represents a finite directed graph on the vertex set `{0, …, n-1}` by an
adjacency list `graph : List[List[int]]` in which `graph[u]` holds the out-neighbours of `u`.

* `pre` checks that the adjacency list is well formed, i.e. that every listed neighbour is
  an integer vertex index in `0 .. n-1`.  Python must additionally reject, at run time,
  entries that are not lists (`candidate([[1], "not a list"]) is None`) and negative
  integers; both malformed shapes are excluded statically by the Lean type
  `List (List Nat)`, so only the bounds check remains to be modelled.
* `isTopologicalOrder` is the executable checker of the Python program: `order` must be a
  permutation of `0 .. n-1` (Python: `sorted(order) == list(range(len(graph)))`) and every
  edge `u -> v` must satisfy `position[u] < position[v]`.
* `topologicalSort` searches the vertex permutations (Python's `permutations(range(n))`)
  and returns the first one that passes the checker.  It returns `none` when the graph is
  malformed, and also when the graph contains a directed cycle, because then no permutation
  passes the checker.
* `topologicalSortImp` is an imperative version (mutable accumulator, a single scan over the
  candidate list) which is proved equivalent to the functional one.

Implementation notes.  `sortedAsc` is our own insertion sort rather than `List.mergeSort`,
and the candidate enumeration uses `List.permutations'` rather than `List.permutations`:
both are defined by structural recursion, hence closed instances reduce in the Lean kernel
and the ground tests below can be proved with `decide` (no `native_decide` inside a theorem).
`List.permutations' (List.range n)` starts with the identity ordering `[0, …, n-1]`, exactly
like `itertools.permutations(range(n))`, so the ground results of the Python `check`
function are reproduced one by one, and the proved property `FirstMatch_prop` states that the
result is the first candidate passing the checker in the searched enumeration.

The enumeration *order* of `List.permutations'` is not literally the lexicographic order of
`itertools.permutations`.  The property-based test `LexMin_bool` below therefore checks,
exhaustively for all 512 graphs on three vertices and on the curated family, that the
returned ordering is also the lexicographically smallest topological order, i.e. the value
the Python program returns.  (Independently, the two enumerations were compared outside Lean
on all 66067 graphs with at most four vertices and on 4000 random graphs with up to seven
vertices: no input was found on which the two programs return different results.)

All theorems are proved by the Lean kernel: no `sorry`, no `admit`, no `native_decide`, no
new axiom.  `native_decide` is used only in `example` unit tests and property-based tests.
-/

namespace topological_sort

/-!
## Implementation
-/

/-- Mirrors Python's `pre`: every neighbour listed in the adjacency list must be a vertex
index in `0 .. n-1`.  (The dynamic type checks of the Python version are covered by the
Lean type `List (List Nat)`.) -/
def pre (graph : List (List Nat)) : Bool :=
  graph.all fun ns => ns.all fun v => decide (v < graph.length)

/-- `positionOf order v` is the position of vertex `v` in the candidate ordering, i.e.
Python's `position = {v: i for i, v in enumerate(order)}`.  The checker only uses it on
orderings that are permutations of the vertices, where the first index of `v` is *the*
index of `v`. -/
def positionOf (order : List Nat) (v : Nat) : Nat := order.idxOf v

/-- Insert `x` into an ascending list, keeping it ascending (auxiliary for `sortedAsc`). -/
def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x <= y then x :: y :: ys else y :: insertSorted x ys

/-- `sortedAsc l` is Python's `sorted(l)`: ascending insertion sort, defined by structural
recursion so that closed instances reduce in the kernel. -/
def sortedAsc : List Nat → List Nat
  | [] => []
  | x :: xs => insertSorted x (sortedAsc xs)

theorem insertSorted_perm (x : Nat) :
    ∀ l : List Nat, (insertSorted x l).Perm (x :: l) := by
  intro l
  induction l with
  | nil => exact List.Perm.refl _
  | cons y ys ih =>
    show (if x <= y then x :: y :: ys else y :: insertSorted x ys).Perm (x :: y :: ys)
    split
    · exact List.Perm.refl _
    · exact (List.Perm.cons y ih).trans (List.Perm.swap x y ys)

/-- Insertion sort permutes the input. -/
theorem sortedAsc_perm : ∀ l : List Nat, (sortedAsc l).Perm l := by
  intro l
  induction l with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
    show (insertSorted x (sortedAsc xs)).Perm (x :: xs)
    exact (insertSorted_perm x (sortedAsc xs)).trans (List.Perm.cons x ih)

/-- Every element of `insertSorted x l` is `x` or an element of `l`. -/
theorem mem_insertSorted (x : Nat) :
    ∀ (l : List Nat) (b : Nat), b ∈ insertSorted x l → b = x ∨ b ∈ l := by
  intro l
  induction l with
  | nil =>
    intro b hb
    have h1 : insertSorted x [] = [x] := rfl
    rw [h1] at hb
    simp at hb
    exact Or.inl hb
  | cons y ys ih =>
    intro b hb
    have h1 : insertSorted x (y :: ys) =
        if x <= y then x :: y :: ys else y :: insertSorted x ys := rfl
    rw [h1] at hb
    by_cases hxy : x <= y
    · rw [if_pos hxy] at hb
      rcases List.mem_cons.mp hb with hbx | hb
      · exact Or.inl hbx
      · exact Or.inr hb
    · rw [if_neg hxy] at hb
      rcases List.mem_cons.mp hb with hby | hb
      · exact Or.inr (List.mem_cons.mpr (Or.inl hby))
      · rcases ih b hb with hbx | hb'
        · exact Or.inl hbx
        · exact Or.inr (List.mem_cons.mpr (Or.inr hb'))

/-- Insertion into an ascending list keeps it ascending. -/
theorem insertSorted_sorted (x : Nat) :
    ∀ l : List Nat, List.Sorted (· ≤ ·) l → List.Sorted (· ≤ ·) (insertSorted x l) := by
  intro l
  induction l with
  | nil =>
    intro _
    show List.Pairwise (· ≤ ·) [x]
    exact List.Pairwise.cons (by simp) List.Pairwise.nil
  | cons y ys ih =>
    intro hl
    have h1 : insertSorted x (y :: ys) =
        if x <= y then x :: y :: ys else y :: insertSorted x ys := rfl
    rw [h1]
    have hy : ∀ b ∈ ys, y ≤ b := (List.sorted_cons.mp hl).1
    have hys : List.Sorted (· ≤ ·) ys := (List.sorted_cons.mp hl).2
    split
    · next hxy =>
      show List.Pairwise (· ≤ ·) (x :: y :: ys)
      refine List.Pairwise.cons ?_ (List.Pairwise.cons hy hys)
      intro b hb
      rcases List.mem_cons.mp hb with hby | hb
      · rw [hby]; exact hxy
      · exact Nat.le_trans hxy (hy b hb)
    · next hxy =>
      show List.Pairwise (· ≤ ·) (y :: insertSorted x ys)
      refine List.Pairwise.cons ?_ (ih hys)
      intro b hb
      rcases mem_insertSorted x ys b hb with hbx | hb'
      · rw [hbx]; exact Nat.le_of_not_le hxy
      · exact hy b hb'

/-- `sortedAsc` produces an ascending list. -/
theorem sortedAsc_sorted : ∀ l : List Nat, List.Sorted (· ≤ ·) (sortedAsc l) := by
  intro l
  induction l with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    show List.Sorted (· ≤ ·) (insertSorted x (sortedAsc xs))
    exact insertSorted_sorted x (sortedAsc xs) ih

/-- Sorting a permutation of `0 .. n-1` gives back `0 .. n-1`: the propositional content of
Python's `sorted(order) == list(range(len(graph)))`. -/
theorem sortedAsc_eq_range_of_perm {n : Nat} {order : List Nat}
    (h : order.Perm (List.range n)) : sortedAsc order = List.range n :=
  List.eq_of_perm_of_sorted ((sortedAsc_perm order).trans h) (sortedAsc_sorted order)
    (List.sorted_le_range n)

/-- Executable checker, mirroring Python's `is_topological_order`. -/
def isTopologicalOrder (graph : List (List Nat)) (order : List Nat) : Bool :=
  pre graph &&
    decide (sortedAsc order = List.range graph.length) &&
    graph.zipIdx.all fun p => p.1.all fun v => decide (positionOf order p.2 < positionOf order v)

/-- The candidate orderings searched by `topologicalSort`: all permutations of the vertex
list `[0, …, n-1]`, i.e. Python's `permutations(range(n))`.  The first candidate is the
identity ordering, as in `itertools.permutations`. -/
def candidates (graph : List (List Nat)) : List (List Nat) :=
  (List.range graph.length).permutations'

/-- Mirrors Python's `topological_sort`: the first candidate permutation passing the
checker, or `none` if the graph is malformed or no permutation passes. -/
def topologicalSort (graph : List (List Nat)) : Option (List Nat) :=
  if pre graph then (candidates graph).find? (isTopologicalOrder graph) else none

/-!
## Unit tests (functional implementation)
-/

example : pre [[1], [2], []] = true := by native_decide
example : pre [[1], [0]] = true := by native_decide
example : pre [[2]] = false := by native_decide
example : pre [] = true := by native_decide
#eval pre [[1], [2], []]
#eval pre [[2]]

example : isTopologicalOrder [[1], [2], []] [0, 1, 2] = true := by native_decide
example : isTopologicalOrder [[1], [2], []] [1, 0, 2] = false := by native_decide
example : isTopologicalOrder [[1], [2], []] [0, 1] = false := by native_decide
example : isTopologicalOrder [] [] = true := by native_decide
#eval isTopologicalOrder [[1], [2], []] [0, 1, 2]
#eval isTopologicalOrder [[1], [2], []] [2, 1, 0]
#eval candidates [[1], [2], []]

-- Python: `assert candidate(g1) == [0, 1, 2]`
example : topologicalSort [[1], [2], []] = some [0, 1, 2] := by native_decide
#eval topologicalSort [[1], [2], []]
theorem check_g1 : topologicalSort [[1], [2], []] = some [0, 1, 2] := by decide
-- Python: `order1 is not None and is_topological_order(g1, order1)`
theorem check_g1_valid : isTopologicalOrder [[1], [2], []] [0, 1, 2] = true := by decide
-- Python: `order2 is not None and is_topological_order(g2, order2)`
example : topologicalSort [[1, 2], [3], [3], []] = some [0, 1, 2, 3] := by native_decide
#eval topologicalSort [[1, 2], [3], [3], []]
theorem check_g2 : topologicalSort [[1, 2], [3], [3], []] = some [0, 1, 2, 3] := by decide
theorem check_g2_valid : isTopologicalOrder [[1, 2], [3], [3], []] [0, 1, 2, 3] = true := by decide
-- Python: `assert set(order2) == {0, 1, 2, 3}`
theorem check_g2_set : ((topologicalSort [[1, 2], [3], [3], []]).getD []).dedup = [0, 1, 2, 3] :=
  by decide
-- Python: `assert candidate(g3) == []` for the empty graph
example : topologicalSort [] = some [] := by native_decide
#eval topologicalSort ([] : List (List Nat))
theorem check_g3 : topologicalSort [] = some [] := by decide
-- Python: `assert candidate(g4) == [0, 1, 2]` for the disconnected edgeless graph
example : topologicalSort [[], [], []] = some [0, 1, 2] := by native_decide
#eval topologicalSort [[], [], []]
theorem check_g4 : topologicalSort [[], [], []] = some [0, 1, 2] := by decide
-- Python: `order5 is not None and is_topological_order(g5, order5)`, `order5.index(0) < order5.index(2)`
example : topologicalSort [[2], [], []] = some [0, 1, 2] := by native_decide
example : ((topologicalSort [[2], [], []]).getD []).idxOf 0 <
    ((topologicalSort [[2], [], []]).getD []).idxOf 2 := by native_decide
#eval topologicalSort [[2], [], []]
theorem check_g5 : topologicalSort [[2], [], []] = some [0, 1, 2] := by decide
theorem check_g5_index :
    ((topologicalSort [[2], [], []]).getD []).idxOf 0 <
      ((topologicalSort [[2], [], []]).getD []).idxOf 2 := by decide
-- Python: `assert candidate([[1], [0]]) is None` and `assert candidate([[0]]) is None`
example : topologicalSort [[1], [0]] = none := by native_decide
example : topologicalSort [[0]] = none := by native_decide
#eval topologicalSort [[1], [0]]
#eval topologicalSort [[0]]
theorem check_cycle : topologicalSort [[1], [0]] = none := by decide
theorem check_selfLoop : topologicalSort [[0]] = none := by decide
-- Python: `assert candidate([[2]]) is None` (malformed: vertex 2 is out of range)
example : topologicalSort [[2]] = none := by native_decide
example : topologicalSort [[5], [0]] = none := by native_decide
#eval topologicalSort [[2]]
theorem check_malformed : topologicalSort [[2]] = none := by decide
-- Python: `assert candidate([[1], "not a list"]) is None`.  An entry that is not a list of
-- integers is not representable at the Lean type `List (List Nat)`; the closest representable
-- malformed input is an out-of-range vertex, covered by `check_malformed` above.

/-!
## Pre-condition
-/

/-- Pre-condition: `graph` is a well formed adjacency list over the vertices `0 .. n-1`,
i.e. the propositional content of Python's `pre`. -/
def Pre (graph : List (List Nat)) : Prop :=
  ∀ ns ∈ graph, ∀ v ∈ ns, v < graph.length

/-- The executable check `pre` agrees with the pre-condition `Pre`. -/
theorem pre_spec (graph : List (List Nat)) : pre graph = true ↔ Pre graph := by
  simp only [pre, Pre, List.all_eq_true, decide_eq_true_iff]

/-- The executable checker `isTopologicalOrder` holds exactly when the graph is well formed,
`order` is a permutation of the vertices (Python: `sorted(order) == list(range(n))`) and
every arc goes forward in `order`. -/
theorem isTopologicalOrder_spec (graph : List (List Nat)) (order : List Nat) :
    isTopologicalOrder graph order = true ↔
      (pre graph = true ∧ sortedAsc order = List.range graph.length ∧
        ∀ p ∈ graph.zipIdx, ∀ v ∈ p.1, positionOf order p.2 < positionOf order v) := by
  simp only [isTopologicalOrder, Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true,
    and_assoc]

/-- Converse of the checker specification: a well formed graph together with an ordering that
lists every vertex exactly once and sends every arc forward passes the checker. -/
theorem isTopologicalOrder_complete (graph : List (List Nat)) (order : List Nat)
    (hpre : pre graph = true) (hperm : order.Perm (List.range graph.length))
    (hedges : ∀ p ∈ graph.zipIdx, ∀ v ∈ p.1, positionOf order p.2 < positionOf order v) :
    isTopologicalOrder graph order = true :=
  (isTopologicalOrder_spec graph order).mpr
    ⟨hpre, sortedAsc_eq_range_of_perm hperm, hedges⟩

/-- Technical helper: `l.find? p = some a` holds exactly when `a` occurs in `l`, satisfies
`p`, and every element strictly before that occurrence fails `p`.  This is the "returns the
first candidate that passes the checker" semantics of the Python search loop. -/
theorem find?_eq_some_iff {α : Type} {p : α → Bool} {l : List α} {a : α} :
    l.find? p = some a ↔
      ∃ l₁ l₂, l = l₁ ++ a :: l₂ ∧ (∀ b ∈ l₁, p b = false) ∧ p a = true := by
  constructor
  · intro h
    induction l generalizing a with
    | nil => simp at h
    | cons x xs ih =>
      rw [List.find?_cons] at h
      split at h
      · next hpx =>
        have hxa : x = a := by injection h
        refine ⟨[], xs, ?_, by simp, ?_⟩
        · simp [hxa]
        · rw [← hxa]; exact hpx
      · next hpx =>
        obtain ⟨l₁, l₂, hl, hl₁, ha⟩ := ih h
        refine ⟨x :: l₁, l₂, ?_, ?_, ha⟩
        · simp [hl]
        · intro b hb
          simp only [List.mem_cons] at hb
          rcases hb with rfl | hb
          · exact hpx
          · exact hl₁ b hb
  · rintro ⟨l₁, l₂, rfl, hl₁, ha⟩
    induction l₁ with
    | nil => simp [ha]
    | cons x xs ih =>
      have hx : p x = false := hl₁ x (by simp)
      have hrest : ∀ b ∈ xs, p b = false := fun b hb => hl₁ b (by simp [hb])
      simp [hx, ih hrest]

/-!
## Reachability

Used to state that a returned ordering certifies the absence of *any* directed cycle
(Python: "Cycles return None because no topological order exists").
-/

/-- `Edge graph u v` means `v ∈ graph[u]`, i.e. `u -> v` is an arc of the graph. -/
def Edge (graph : List (List Nat)) (u v : Nat) : Prop :=
  ∃ p ∈ graph.zipIdx, p.2 = u ∧ v ∈ p.1

/-- `Reaches graph u v` means there is a directed path of length ≥ 1 from `u` to `v`. -/
inductive Reaches (graph : List (List Nat)) : Nat → Nat → Prop
  | edge {u v : Nat} : Edge graph u v → Reaches graph u v
  | step {u v w : Nat} : Edge graph u v → Reaches graph v w → Reaches graph u w

/-!
## Properties
-/

/-- A malformed adjacency list yields `none` (Python: `if not pre(graph): return None`). -/
def PreChecked_prop (graph : List (List Nat)) (res : Option (List Nat)) : Prop :=
  ¬ Pre graph → res = none

theorem PreChecked_thm (graph : List (List Nat)) :
    PreChecked_prop graph (topologicalSort graph) := by
  intro h
  have h' : ¬ pre graph = true := by rwa [pre_spec]
  have hf : pre graph = false := Bool.eq_false_of_not_eq_true h'
  simp [topologicalSort, hf]

/-- Soundness: a returned ordering passes the executable checker. -/
def Sound_prop (graph : List (List Nat)) (res : Option (List Nat)) : Prop :=
  ∀ order, res = some order → isTopologicalOrder graph order = true

theorem Sound_thm (graph : List (List Nat)) : Sound_prop graph (topologicalSort graph) := by
  intro order ho
  by_cases h : pre graph = true
  · have hfind : (candidates graph).find? (isTopologicalOrder graph) = some order := by
      simpa [topologicalSort, h] using ho
    obtain ⟨l₁, l₂, hl, hl₁, ha⟩ := find?_eq_some_iff.mp hfind
    exact ha
  · have hf : pre graph = false := Bool.eq_false_of_not_eq_true h
    have hnone : topologicalSort graph = none := by simp [topologicalSort, hf]
    rw [hnone] at ho
    injection ho

/-- The returned ordering is one of the candidate permutations that were searched. -/
def Member_prop (graph : List (List Nat)) (res : Option (List Nat)) : Prop :=
  ∀ order, res = some order → order ∈ candidates graph

theorem Member_thm (graph : List (List Nat)) : Member_prop graph (topologicalSort graph) := by
  intro order ho
  by_cases h : pre graph = true
  · have hfind : (candidates graph).find? (isTopologicalOrder graph) = some order := by
      simpa [topologicalSort, h] using ho
    obtain ⟨l₁, l₂, hl, _, _⟩ := find?_eq_some_iff.mp hfind
    rw [hl]
    simp
  · have hf : pre graph = false := Bool.eq_false_of_not_eq_true h
    have hnone : topologicalSort graph = none := by simp [topologicalSort, hf]
    rw [hnone] at ho
    injection ho

/-- A returned ordering is a permutation of the vertices `0 .. n-1`. -/
def Perm_prop (graph : List (List Nat)) (res : Option (List Nat)) : Prop :=
  ∀ order, res = some order → order.Perm (List.range graph.length)

theorem Perm_thm (graph : List (List Nat)) : Perm_prop graph (topologicalSort graph) := by
  intro order ho
  have hspec := (isTopologicalOrder_spec graph order).mp (Sound_thm graph order ho)
  have hperm : order.Perm (sortedAsc order) := (sortedAsc_perm order).symm
  rwa [hspec.2.1] at hperm

/-- A returned ordering contains every vertex exactly once
(Python: `set(order2) == {0, 1, 2, 3}`, "Disconnected DAGs include every vertex exactly
once"). -/
def Size_prop (graph : List (List Nat)) (res : Option (List Nat)) : Prop :=
  ∀ order, res = some order → order.length = graph.length ∧ order.Nodup

theorem Size_thm (graph : List (List Nat)) : Size_prop graph (topologicalSort graph) := by
  intro order ho
  have hp := Perm_thm graph order ho
  exact ⟨hp.length_eq.trans List.length_range, hp.symm.nodup List.nodup_range⟩

/-- Every arc of the graph goes forward in a returned ordering. -/
def Edges_prop (graph : List (List Nat)) (res : Option (List Nat)) : Prop :=
  ∀ order, res = some order →
    ∀ p ∈ graph.zipIdx, ∀ v ∈ p.1, positionOf order p.2 < positionOf order v

theorem Edges_thm (graph : List (List Nat)) : Edges_prop graph (topologicalSort graph) := by
  intro order ho
  exact ((isTopologicalOrder_spec graph order).mp (Sound_thm graph order ho)).2.2

/-- Completeness: for a well formed graph, whenever a topological order exists the search
finds one, i.e. the result is not `none`. -/
def Complete_prop (graph : List (List Nat)) (res : Option (List Nat)) : Prop :=
  Pre graph → (∃ order, isTopologicalOrder graph order = true) → ∃ order, res = some order

theorem Complete_thm (graph : List (List Nat)) : Complete_prop graph (topologicalSort graph) := by
  intro hpre ⟨order, horder⟩
  have hspec := (isTopologicalOrder_spec graph order).mp horder
  have hperm : order.Perm (sortedAsc order) := (sortedAsc_perm order).symm
  have hperm' : order.Perm (List.range graph.length) := by rwa [hspec.2.1] at hperm
  have hmem : order ∈ candidates graph := List.mem_permutations'.mpr hperm'
  have htrue : pre graph = true := (pre_spec graph).mpr hpre
  have hfind : (candidates graph).find? (isTopologicalOrder graph) ≠ none := by
    intro hcontra'
    have hcontra := List.find?_eq_none.mp hcontra'
    exact hcontra order hmem horder
  obtain ⟨order', horder'⟩ := Option.ne_none_iff_exists.mp hfind
  exact ⟨order', by simp [topologicalSort, htrue, horder']⟩

/-- Completeness in mathematical form: if the graph is well formed and some ordering of the
vertices sends every arc forward, then the permutation search returns an ordering. -/
theorem CompleteMath_thm (graph : List (List Nat)) (hpre : Pre graph)
    (h : ∃ order, order.Perm (List.range graph.length) ∧
      ∀ p ∈ graph.zipIdx, ∀ v ∈ p.1, positionOf order p.2 < positionOf order v) :
    ∃ order, topologicalSort graph = some order :=
  Complete_thm graph hpre
    ⟨h.choose, isTopologicalOrder_complete graph h.choose ((pre_spec graph).mpr hpre)
      h.choose_spec.1 h.choose_spec.2⟩

/-- For a well formed graph the result is `none` exactly when no topological order exists
(Python: "Cycles return None because no topological order exists"). -/
def None_prop (graph : List (List Nat)) (res : Option (List Nat)) : Prop :=
  Pre graph → (res = none ↔ ¬ ∃ order, isTopologicalOrder graph order = true)

theorem None_thm (graph : List (List Nat)) : None_prop graph (topologicalSort graph) := by
  intro hpre
  have htrue : pre graph = true := (pre_spec graph).mpr hpre
  constructor
  · intro hnone ⟨order, horder⟩
    have hspec := (isTopologicalOrder_spec graph order).mp horder
    have hperm : order.Perm (sortedAsc order) := (sortedAsc_perm order).symm
    have hperm' : order.Perm (List.range graph.length) := by rwa [hspec.2.1] at hperm
    have hmem : order ∈ candidates graph := List.mem_permutations'.mpr hperm'
    have hall :=
      (List.find?_eq_none.mp (by simpa [topologicalSort, htrue] using hnone)) order hmem
    exact hall horder
  · intro hno
    simp only [topologicalSort, htrue, if_true]
    rw [List.find?_eq_none]
    intro x hx hpx
    exact hno ⟨x, hpx⟩

/-- The returned ordering is the *first* candidate permutation that passes the checker:
no candidate listed before it passes. -/
def FirstMatch_prop (graph : List (List Nat)) (res : Option (List Nat)) : Prop :=
  ∀ order, res = some order →
    ∃ l₁ l₂, candidates graph = l₁ ++ order :: l₂ ∧
      ∀ q ∈ l₁, isTopologicalOrder graph q = false

theorem FirstMatch_thm (graph : List (List Nat)) :
    FirstMatch_prop graph (topologicalSort graph) := by
  intro order ho
  by_cases h : pre graph = true
  · have hfind : (candidates graph).find? (isTopologicalOrder graph) = some order := by
      simpa [topologicalSort, h] using ho
    obtain ⟨l₁, l₂, hl, hl₁, _⟩ := find?_eq_some_iff.mp hfind
    exact ⟨l₁, l₂, hl, hl₁⟩
  · have hf : pre graph = false := Bool.eq_false_of_not_eq_true h
    have hnone : topologicalSort graph = none := by simp [topologicalSort, hf]
    rw [hnone] at ho
    injection ho

/-- A graph with a result has no self loop (Python: `candidate([[0]]) is None`). -/
def NoSelfLoop_prop (graph : List (List Nat)) (res : Option (List Nat)) : Prop :=
  res ≠ none → ∀ p ∈ graph.zipIdx, p.2 ∉ p.1

theorem NoSelfLoop_thm (graph : List (List Nat)) :
    NoSelfLoop_prop graph (topologicalSort graph) := by
  intro hres p hp
  by_contra hself
  obtain ⟨order, ho⟩ := Option.ne_none_iff_exists.mp hres
  have he := Edges_thm graph order ho.symm p hp p.2 (by simpa using hself)
  exact Nat.lt_irrefl _ he

/-- A graph with a result has no directed 2-cycle (Python: `candidate([[1], [0]]) is None`). -/
def NoTwoCycle_prop (graph : List (List Nat)) (res : Option (List Nat)) : Prop :=
  res ≠ none → ∀ p ∈ graph.zipIdx, ∀ v ∈ p.1, ∀ q ∈ graph.zipIdx, q.2 = v → p.2 ∉ q.1

theorem NoTwoCycle_thm (graph : List (List Nat)) :
    NoTwoCycle_prop graph (topologicalSort graph) := by
  intro hres p hp v hv q hq hq2
  by_contra hback
  obtain ⟨order, ho⟩ := Option.ne_none_iff_exists.mp hres
  have h1 := Edges_thm graph order ho.symm p hp v hv
  have h2 := Edges_thm graph order ho.symm q hq p.2 (by simpa using hback)
  rw [hq2] at h2
  exact Nat.lt_irrefl _ (Nat.lt_trans h1 h2)

/-- A graph with a result is acyclic: no vertex reaches itself along directed arcs. -/
def Acyclic_prop (graph : List (List Nat)) (res : Option (List Nat)) : Prop :=
  res ≠ none → ∀ u : Nat, ¬ Reaches graph u u

theorem Acyclic_thm (graph : List (List Nat)) : Acyclic_prop graph (topologicalSort graph) := by
  intro hres u hu
  obtain ⟨order, ho⟩ := Option.ne_none_iff_exists.mp hres
  have he := Edges_thm graph order ho.symm
  have key : ∀ v w : Nat, Reaches graph v w → positionOf order v < positionOf order w := by
    intro v w h
    induction h with
    | @edge x y hxy =>
      obtain ⟨p, hp, hpx, hpy⟩ := hxy
      have hlt := he p hp y hpy
      rwa [hpx] at hlt
    | @step x y z hxy _ ih =>
      obtain ⟨p, hp, hpx, hpy⟩ := hxy
      have hlt := he p hp y hpy
      rw [hpx] at hlt
      exact Nat.lt_trans hlt ih
  exact Nat.lt_irrefl _ (key u u hu)

/-- The empty graph has the empty topological order (Python: `assert candidate(g3) == []`). -/
def Empty_prop (graph : List (List Nat)) (res : Option (List Nat)) : Prop :=
  graph = [] → res = some []

theorem Empty_thm (graph : List (List Nat)) : Empty_prop graph (topologicalSort graph) := by
  intro hg
  subst hg
  decide

/-!
## Post-condition
-/

/-- Post-condition: conjunction of all the properties above. -/
def Post_prop (graph : List (List Nat)) (res : Option (List Nat)) : Prop :=
  PreChecked_prop graph res ∧ Sound_prop graph res ∧ Member_prop graph res ∧
    Perm_prop graph res ∧ Size_prop graph res ∧
    Edges_prop graph res ∧ Complete_prop graph res ∧ None_prop graph res ∧
    FirstMatch_prop graph res ∧ NoSelfLoop_prop graph res ∧ NoTwoCycle_prop graph res ∧
    Acyclic_prop graph res ∧ Empty_prop graph res

/-!
## Property-based tests

Every `_prop` above has an executable Boolean counterpart `*_bool`.  The tests below check
those counterparts
(a) exhaustively on all `2^(n*n)` graphs over the vertices `0 .. n-1` for `n = 3`,
(b) on a curated list containing all graphs of the Python `check` function plus malformed and
cyclic ones, and
(c) on random inputs generated by `Plausible`.
-/

/-- Boolean counterpart of `PreChecked_prop`. -/
def PreChecked_bool (graph : List (List Nat)) (res : Option (List Nat)) : Bool :=
  pre graph || res.isNone

/-- Boolean counterpart of `Sound_prop`. -/
def Sound_bool (graph : List (List Nat)) (res : Option (List Nat)) : Bool :=
  res.all fun o => isTopologicalOrder graph o

/-- Boolean counterpart of `Member_prop`. -/
def Member_bool (graph : List (List Nat)) (res : Option (List Nat)) : Bool :=
  res.all fun o => (candidates graph).any (fun q => q == o)

/-- Boolean counterpart of `Perm_prop`. -/
def Perm_bool (graph : List (List Nat)) (res : Option (List Nat)) : Bool :=
  res.all fun o => sortedAsc o == List.range graph.length

/-- Boolean counterpart of `Size_prop` (length plus "no vertex twice"). -/
def Size_bool (graph : List (List Nat)) (res : Option (List Nat)) : Bool :=
  res.all fun o => o.length == graph.length && o.dedup.length == o.length

/-- Boolean counterpart of `Edges_prop`. -/
def Edges_bool (graph : List (List Nat)) (res : Option (List Nat)) : Bool :=
  res.all fun o => graph.zipIdx.all fun p =>
    p.1.all fun v => decide (positionOf o p.2 < positionOf o v)

/-- Boolean counterpart of `Complete_prop`: a result exists iff some candidate passes. -/
def Complete_bool (graph : List (List Nat)) (res : Option (List Nat)) : Bool :=
  res.isSome == (candidates graph).any (isTopologicalOrder graph)

/-- Boolean counterpart of `None_prop`: `none` iff no candidate passes. -/
def None_bool (graph : List (List Nat)) (res : Option (List Nat)) : Bool :=
  res.isNone == !(candidates graph).any (isTopologicalOrder graph)

/-- Boolean counterpart of `FirstMatch_prop`: no candidate before the result passes. -/
def FirstMatch_bool (graph : List (List Nat)) (res : Option (List Nat)) : Bool :=
  res.all fun o => ((candidates graph).takeWhile (fun q => q != o)).all
    fun q => isTopologicalOrder graph q == false

/-- Boolean counterpart of `NoSelfLoop_prop`. -/
def NoSelfLoop_bool (graph : List (List Nat)) (res : Option (List Nat)) : Bool :=
  res.isNone || graph.zipIdx.all fun p => p.1.all fun v => v != p.2

/-- Boolean counterpart of `NoTwoCycle_prop`. -/
def NoTwoCycle_bool (graph : List (List Nat)) (res : Option (List Nat)) : Bool :=
  res.isNone || graph.zipIdx.all fun p => p.1.all fun v =>
    graph.zipIdx.all fun q => !((q.2 == v) && q.1.any (fun w => w == p.2))

/-- Vertices reachable from `u` along ≥ 1 arc; the closure saturates after
`graph.length + 1` rounds.  Used for the executable counterpart of `Acyclic_prop`. -/
def closureFrom (graph : List (List Nat)) (u : Nat) : List Nat :=
  (List.range (graph.length + 1)).foldl
    (fun acc _ => (acc ++ acc.flatMap (fun x => graph.getD x [])).dedup) (graph.getD u [])

/-- Boolean counterpart of `Acyclic_prop`: no vertex reaches itself. -/
def Acyclic_bool (graph : List (List Nat)) (res : Option (List Nat)) : Bool :=
  res.isNone || (List.range graph.length).all fun u =>
    !(closureFrom graph u).any (fun v => v == u)

/-- Boolean counterpart of `Empty_prop`. -/
def Empty_bool (graph : List (List Nat)) (res : Option (List Nat)) : Bool :=
  (graph != []) || res == some []

/-- Strict lexicographic comparison of two orderings (executable). -/
def lexLess : List Nat → List Nat → Bool
  | [], _ :: _ => true
  | _, [] => false
  | x :: xs, y :: ys => if x == y then lexLess xs ys else decide (x < y)

/-- The result is the lexicographically smallest topological order, i.e. the value returned by
the Python program, which searches `itertools.permutations` in lexicographic order.  This is
checked exhaustively on small graphs below; the proved statement about the search itself is
`FirstMatch_prop`. -/
def LexMin_bool (graph : List (List Nat)) (res : Option (List Nat)) : Bool :=
  res.all fun o => (candidates graph).all fun q =>
    isTopologicalOrder graph q == false || !lexLess q o

/-- Boolean counterpart of `Post_prop`. -/
def Post_bool (graph : List (List Nat)) (res : Option (List Nat)) : Bool :=
  PreChecked_bool graph res && Sound_bool graph res && Member_bool graph res &&
    Perm_bool graph res &&
    Size_bool graph res && Edges_bool graph res && Complete_bool graph res &&
    None_bool graph res && FirstMatch_bool graph res && NoSelfLoop_bool graph res &&
    NoTwoCycle_bool graph res && Acyclic_bool graph res && Empty_bool graph res

/-- Adjacency list of the graph on the vertices `0 .. n-1` whose arc set is `es`; the result
always satisfies `Pre`. -/
def graphOfPairs (n : Nat) (es : List (Nat × Nat)) : List (List Nat) :=
  (List.range n).map fun u => es.filterMap fun e => if e.1 == u then some e.2 else none

/-- All `2^(n*n)` graphs on the vertex set `0 .. n-1`. -/
def allGraphs (n : Nat) : List (List (List Nat)) :=
  ((List.range n).product (List.range n)).sublists.map (graphOfPairs n)

/-- Curated test graphs: the graphs of the Python `check` function, plus malformed,
cyclic and disconnected ones. -/
def testGraphs : List (List (List Nat)) :=
  [ [], [[1], [2], []], [[1, 2], [3], [3], []], [[], [], []], [[2], [], []], [[1], [0]], [[0]],
    [[2]], [[5], [0]], [[1], []], [[], [0]], [[3], [2], [1], []], [[1], [2], [3], []],
    [[2], [0], []], [[1], [2], [0]], [[0], [1], [2]], [[1, 2, 3], [], [], []],
    [[], [1], [2], [3]], [[2, 3], [], [3], []], [[1], [2], [1]], [[], [], [], []],
    [[1], [2], [], [1]], [[0, 1], [1], []], [[7]] ]

/-- The input family of the bounded property-based tests: exhaustive for three vertices. -/
def pbtGraphs : List (List (List Nat)) := testGraphs ++ allGraphs 3

#eval pbtGraphs.length

-- Bounded (exhaustive for `n ≤ 3`) property-based tests, one per property.
example : pbtGraphs.all (fun g => PreChecked_bool g (topologicalSort g)) = true :=
  by native_decide
example : pbtGraphs.all (fun g => Sound_bool g (topologicalSort g)) = true := by native_decide
example : pbtGraphs.all (fun g => Member_bool g (topologicalSort g)) = true := by native_decide
example : pbtGraphs.all (fun g => Perm_bool g (topologicalSort g)) = true := by native_decide
example : pbtGraphs.all (fun g => Size_bool g (topologicalSort g)) = true := by native_decide
example : pbtGraphs.all (fun g => Edges_bool g (topologicalSort g)) = true := by native_decide
example : pbtGraphs.all (fun g => Complete_bool g (topologicalSort g)) = true := by native_decide
example : pbtGraphs.all (fun g => None_bool g (topologicalSort g)) = true := by native_decide
example : pbtGraphs.all (fun g => FirstMatch_bool g (topologicalSort g)) = true :=
  by native_decide
example : pbtGraphs.all (fun g => NoSelfLoop_bool g (topologicalSort g)) = true :=
  by native_decide
example : pbtGraphs.all (fun g => NoTwoCycle_bool g (topologicalSort g)) = true :=
  by native_decide
example : pbtGraphs.all (fun g => Acyclic_bool g (topologicalSort g)) = true := by native_decide
example : pbtGraphs.all (fun g => Empty_bool g (topologicalSort g)) = true := by native_decide
example : pbtGraphs.all (fun g => LexMin_bool g (topologicalSort g)) = true := by native_decide
example : pbtGraphs.all (fun g => Post_bool g (topologicalSort g)) = true := by native_decide
/-- Executable counterpart of `Pre`, computed through `zipIdx` instead of nested `all`s;
`pre_spec` is the proved link between `pre` and `Pre`. -/
def Pre_bool (graph : List (List Nat)) : Bool :=
  graph.zipIdx.all fun p => p.1.all fun v => decide (v < graph.length)

-- The checker agrees with an independent executable characterisation of
-- `isTopologicalOrder_spec`: well formed graph, `order` has exactly the vertices
-- `0 .. n-1` (length, no duplicates, and every vertex occurs), and every arc goes forward.
example : pbtGraphs.all (fun g => (candidates g).all (fun o =>
    isTopologicalOrder g o == (pre g && o.length == g.length && o.dedup.length == g.length &&
      (List.range g.length).all (fun v => o.any (fun w => w == v)) &&
      g.zipIdx.all fun p => p.1.all fun v => decide (positionOf o p.2 < positionOf o v)))) = true :=
  by native_decide
-- `pre` agrees with the executable counterpart of `Pre` on the whole family.
example : pbtGraphs.all (fun g => pre g == Pre_bool g) = true := by native_decide

/-! Randomized property-based tests (Plausible).  `smallGraph n es` turns raw pairs into a
graph on `n % 5` vertices, which keeps the permutation search cheap while still producing
well formed, cyclic, acyclic and disconnected instances. -/

def smallGraph (n : Nat) (es : List (Nat × Nat)) : List (List Nat) :=
  let m := n % 5
  graphOfPairs m (es.map fun e => (e.1 % m, e.2 % m))

def pbtPreChecked (n : Nat) (es : List (Nat × Nat)) : Bool :=
  PreChecked_bool (smallGraph n es) (topologicalSort (smallGraph n es))
def pbtSound (n : Nat) (es : List (Nat × Nat)) : Bool :=
  Sound_bool (smallGraph n es) (topologicalSort (smallGraph n es))
def pbtMember (n : Nat) (es : List (Nat × Nat)) : Bool :=
  Member_bool (smallGraph n es) (topologicalSort (smallGraph n es))
def pbtPerm (n : Nat) (es : List (Nat × Nat)) : Bool :=
  Perm_bool (smallGraph n es) (topologicalSort (smallGraph n es))
def pbtSize (n : Nat) (es : List (Nat × Nat)) : Bool :=
  Size_bool (smallGraph n es) (topologicalSort (smallGraph n es))
def pbtEdges (n : Nat) (es : List (Nat × Nat)) : Bool :=
  Edges_bool (smallGraph n es) (topologicalSort (smallGraph n es))
def pbtComplete (n : Nat) (es : List (Nat × Nat)) : Bool :=
  Complete_bool (smallGraph n es) (topologicalSort (smallGraph n es))
def pbtNone (n : Nat) (es : List (Nat × Nat)) : Bool :=
  None_bool (smallGraph n es) (topologicalSort (smallGraph n es))
def pbtFirstMatch (n : Nat) (es : List (Nat × Nat)) : Bool :=
  FirstMatch_bool (smallGraph n es) (topologicalSort (smallGraph n es))
def pbtNoSelfLoop (n : Nat) (es : List (Nat × Nat)) : Bool :=
  NoSelfLoop_bool (smallGraph n es) (topologicalSort (smallGraph n es))
def pbtNoTwoCycle (n : Nat) (es : List (Nat × Nat)) : Bool :=
  NoTwoCycle_bool (smallGraph n es) (topologicalSort (smallGraph n es))
def pbtAcyclic (n : Nat) (es : List (Nat × Nat)) : Bool :=
  Acyclic_bool (smallGraph n es) (topologicalSort (smallGraph n es))
def pbtEmpty (n : Nat) (es : List (Nat × Nat)) : Bool :=
  Empty_bool (smallGraph n es) (topologicalSort (smallGraph n es))
def pbtLexMin (n : Nat) (es : List (Nat × Nat)) : Bool :=
  LexMin_bool (smallGraph n es) (topologicalSort (smallGraph n es))
def pbtPost (n : Nat) (es : List (Nat × Nat)) : Bool :=
  Post_bool (smallGraph n es) (topologicalSort (smallGraph n es))

#eval Plausible.Testable.check (∀ (n : Nat) (es : List (Nat × Nat)), pbtPreChecked n es)
#eval Plausible.Testable.check (∀ (n : Nat) (es : List (Nat × Nat)), pbtSound n es)
#eval Plausible.Testable.check (∀ (n : Nat) (es : List (Nat × Nat)), pbtMember n es)
#eval Plausible.Testable.check (∀ (n : Nat) (es : List (Nat × Nat)), pbtPerm n es)
#eval Plausible.Testable.check (∀ (n : Nat) (es : List (Nat × Nat)), pbtSize n es)
#eval Plausible.Testable.check (∀ (n : Nat) (es : List (Nat × Nat)), pbtEdges n es)
#eval Plausible.Testable.check (∀ (n : Nat) (es : List (Nat × Nat)), pbtComplete n es)
#eval Plausible.Testable.check (∀ (n : Nat) (es : List (Nat × Nat)), pbtNone n es)
#eval Plausible.Testable.check (∀ (n : Nat) (es : List (Nat × Nat)), pbtFirstMatch n es)
#eval Plausible.Testable.check (∀ (n : Nat) (es : List (Nat × Nat)), pbtNoSelfLoop n es)
#eval Plausible.Testable.check (∀ (n : Nat) (es : List (Nat × Nat)), pbtNoTwoCycle n es)
#eval Plausible.Testable.check (∀ (n : Nat) (es : List (Nat × Nat)), pbtAcyclic n es)
#eval Plausible.Testable.check (∀ (n : Nat) (es : List (Nat × Nat)), pbtEmpty n es)
#eval Plausible.Testable.check (∀ (n : Nat) (es : List (Nat × Nat)), pbtLexMin n es)
#eval Plausible.Testable.check (∀ (n : Nat) (es : List (Nat × Nat)), pbtPost n es)
-- Randomized test over arbitrary (possibly malformed) adjacency lists: the result is always
-- a `some` only for well formed graphs, and then always passes the checker.
#eval Plausible.Testable.check (∀ (g : List (List Nat)),
  decide (g.length > 6) || (Sound_bool g (topologicalSort g) && PreChecked_bool g (topologicalSort g)))

/-!
## Correctness theorem
-/

/-- The post-condition holds for every input, unconditionally. -/
theorem Post_thm (graph : List (List Nat)) : Post_prop graph (topologicalSort graph) :=
  ⟨PreChecked_thm graph, Sound_thm graph, Member_thm graph, Perm_thm graph, Size_thm graph,
    Edges_thm graph,
    Complete_thm graph, None_thm graph, FirstMatch_thm graph, NoSelfLoop_thm graph,
    NoTwoCycle_thm graph, Acyclic_thm graph, Empty_thm graph⟩

/-- Correctness: `Pre -> Post`. -/
theorem correctness_thm (graph : List (List Nat)) (_h : Pre graph) :
    Post_prop graph (topologicalSort graph) :=
  Post_thm graph

/-!
## Imperative implementation

A single left-to-right scan over the candidate list with a mutable accumulator, written in
`Id.run do` notation.
-/

/-- One step of the imperative scan: remember the first candidate that passes the checker
and keep it afterwards. -/
def searchStep (graph : List (List Nat)) (best : Option (List Nat)) (cand : List Nat) :
    Option (List Nat) :=
  if best.isNone && isTopologicalOrder graph cand then some cand else best

/-- Imperative scan of a candidate list with a mutable accumulator. -/
def scanLoop (graph : List (List Nat)) (l : List (List Nat)) (best : Option (List Nat)) :
    Option (List Nat) := Id.run do
  let mut acc := best
  for cand in l do
    acc := searchStep graph acc cand
  return acc

/-- Imperative version of `topological_sort`: mutable state, one pass over the candidates. -/
def topologicalSortImp (graph : List (List Nat)) : Option (List Nat) :=
  if pre graph then scanLoop graph (candidates graph) none else none

/-!
## Imperative tests
-/

example : topologicalSortImp [[1], [2], []] = some [0, 1, 2] := by native_decide
#eval topologicalSortImp [[1], [2], []]
example : topologicalSortImp [[1, 2], [3], [3], []] = some [0, 1, 2, 3] := by native_decide
#eval topologicalSortImp [[1, 2], [3], [3], []]
example : topologicalSortImp [] = some [] := by native_decide
#eval topologicalSortImp ([] : List (List Nat))
example : topologicalSortImp [[], [], []] = some [0, 1, 2] := by native_decide
#eval topologicalSortImp [[], [], []]
example : topologicalSortImp [[2], [], []] = some [0, 1, 2] := by native_decide
#eval topologicalSortImp [[2], [], []]
example : topologicalSortImp [[1], [0]] = none := by native_decide
example : topologicalSortImp [[0]] = none := by native_decide
example : topologicalSortImp [[2]] = none := by native_decide
example : topologicalSortImp [[5], [0]] = none := by native_decide
#eval topologicalSortImp [[1], [0]]
#eval topologicalSortImp [[0]]
#eval topologicalSortImp [[2]]
theorem imp_check_g1 : topologicalSortImp [[1], [2], []] = some [0, 1, 2] := by decide
theorem imp_check_g3 : topologicalSortImp [] = some [] := by decide
theorem imp_check_g4 : topologicalSortImp [[], [], []] = some [0, 1, 2] := by decide
theorem imp_check_cycle : topologicalSortImp [[1], [0]] = none := by decide
theorem imp_check_selfLoop : topologicalSortImp [[0]] = none := by decide
theorem imp_check_malformed : topologicalSortImp [[2]] = none := by decide
-- The imperative version satisfies the same post-condition, via the equivalence theorem.
example : pbtGraphs.all (fun g => topologicalSortImp g == topologicalSort g) = true :=
  by native_decide
example : pbtGraphs.all (fun g => Post_bool g (topologicalSortImp g)) = true := by native_decide

/-!
## Equivalence of the functional and the imperative implementations
-/

/-- The imperative scan is the corresponding left fold. -/
theorem scanLoop_eq_foldl (graph : List (List Nat)) :
    ∀ (l : List (List Nat)) (best : Option (List Nat)),
      scanLoop graph l best = l.foldl (searchStep graph) best := by
  intro l
  induction l with
  | nil => intro best; simp [scanLoop]
  | cons c cs ih => intro best; simp [scanLoop]

/-- The fold keeps the first candidate that passes the checker, i.e. it computes `find?`. -/
theorem foldl_searchStep_find? (graph : List (List Nat)) :
    ∀ (l : List (List Nat)) (best : Option (List Nat)),
      l.foldl (searchStep graph) best =
        match best with
        | some a => some a
        | none => l.find? (isTopologicalOrder graph) := by
  intro l
  induction l with
  | nil => intro best; cases best <;> rfl
  | cons c cs ih =>
    intro best
    simp only [List.foldl_cons]
    cases best with
    | none =>
      by_cases hc : isTopologicalOrder graph c = true
      · simp [searchStep, hc, ih (some c)]
      · simp [searchStep, hc, ih none]
    | some a =>
      simp [searchStep, ih (some a)]

/-- Equivalence theorem: the imperative implementation computes the same result as the
functional one. -/
theorem equivalence_thm (graph : List (List Nat)) :
    topologicalSortImp graph = topologicalSort graph := by
  by_cases h : pre graph = true
  · simp [topologicalSortImp, topologicalSort, h, scanLoop_eq_foldl graph,
      foldl_searchStep_find? graph]
  · have hf : pre graph = false := Bool.eq_false_of_not_eq_true h
    simp [topologicalSortImp, topologicalSort, hf]

/-- The imperative implementation therefore satisfies the same post-condition. -/
theorem correctness_thm_imp (graph : List (List Nat)) (h : Pre graph) :
    Post_prop graph (topologicalSortImp graph) := by
  rw [equivalence_thm]
  exact correctness_thm graph h

end topological_sort
