import Mathlib

/-!
# Topological sorting for finite directed graphs

Formalisation of the Python program `topological_sort.py`.

The Python program represents a finite directed graph by an adjacency list
`graph : List[List[int]]`, where `graph[u]` lists the out-neighbours of the vertex `u`.
`topological_sort` brute-forces over **all** permutations of the vertices `0 .. n-1`
(in the lexicographic order produced by `itertools.permutations(range(n))`) and returns
the first permutation accepted by the executable checker `is_topological_order`.  It
returns `None` when

* the adjacency list is malformed (`pre` fails, i.e. some listed neighbour is not a
  vertex of `0 .. n-1`), or
* the graph contains a directed cycle, so that no permutation is a topological order.

The empty graph has the empty topological order, and disconnected DAGs still contain
every vertex exactly once.

## Modelling notes

* Graphs are `List (List Nat)`; the Python *runtime type* checks of `pre`
  (`isinstance(neighbors, list)`, `isinstance(v, int)`, e.g. the test input
  `[[1], "not a list"]`) are unrepresentable in the typed Lean model: every
  `List (List Nat)` already is an adjacency list of naturals.  What survives of `pre`
  and is modelled by `Pre` below is the range condition `0 <= v < n`; this is exactly
  what makes the Python test `candidate([[2]]) is None` hold.
* `Option (List Nat)` models `Optional[List[int]]`: `none` is Python's `None`.
* The candidate enumeration `lexPerms` is defined from scratch and lists the
  permutations of a duplicate-free list in lexicographic order, matching
  `itertools.permutations(range(n))`.  This is what makes the Python assertions
  `candidate([[1],[2],[]]) == [0,1,2]` and `candidate([[],[],[]]) == [0,1,2]`
  true as equalities, not merely up to "some topological order".
* `posOf v order` models the Python dictionary `position = {v: i for i, v in
  enumerate(order)}`; it is only consulted for vertices that occur in `order`
  (guaranteed by the permutation check), and returns `0` otherwise.
-/

namespace topological_sort

/-! ## 1. Functional implementation -/

/-- Position (index) of the vertex `v` in the ordering `order`. -/
def posOf (v : Nat) : List Nat → Nat
  | [] => 0
  | (x :: xs) => if x = v then 0 else posOf v xs + 1

/-- `row graph u` is the adjacency row `graph[u]` (`[]` if `u` is out of range). -/
def row : List (List Nat) → Nat → List Nat
  | [], _ => []
  | (ns :: _), 0 => ns
  | (_ :: rest), (u + 1) => row rest u

/-- Executable precondition, the Lean counterpart of the Python `pre`:
`graph` is an adjacency list over the vertices `0 .. graph.length - 1`. -/
def Pre (graph : List (List Nat)) : Bool :=
  graph.all fun ns => ns.all fun v => decide (v < graph.length)

/-- `edgesRespect order graph k` is `true` iff for every row index `u` of `graph` and every
out-neighbour `v` listed in that row, the vertex `k + u` occurs before `v` in `order`.
This is the `all(position[u] < position[v] ...)` conjunct of the Python checker. -/
def edgesRespect (order : List Nat) : List (List Nat) → Nat → Bool
  | [], _ => true
  | (ns :: rest), k =>
      (ns.all fun v => decide (posOf k order < posOf v order)) && edgesRespect order rest (k + 1)

/-- Executable checker, the Lean counterpart of the Python `is_topological_order`:
`order` is a permutation of the vertices and every edge goes forward. -/
def isTopologicalOrder (graph : List (List Nat)) (order : List Nat) : Bool :=
  Pre graph && (decide (order.Perm (List.range graph.length)) && edgesRespect order graph 0)

/-- First element of the list satisfying `p` (the Python `for candidate in permutations`
loop that `return`s the first accepted candidate). -/
def findFirst {α : Type} (p : α → Bool) : List α → Option α
  | [] => none
  | (a :: l) => if p a then some a else findFirst p l

/-- `lexPermsAux n l` lists the permutations of `l` in lexicographic order; `n` is an upper
bound for `l.length` that drives the recursion. -/
def lexPermsAux : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | (n + 1), l => List.flatMap (fun e => (lexPermsAux n (l.erase e)).map fun p => e :: p) l

/-- All permutations of `l`, in lexicographic order (as `itertools.permutations`). -/
def lexPerms (l : List Nat) : List (List Nat) := lexPermsAux l.length l

/-- All candidate orderings searched by the algorithm: the permutations of `0 .. n-1`. -/
def candidates (graph : List (List Nat)) : List (List Nat) :=
  lexPerms (List.range graph.length)

/-- The brute-force topological sort of the Python program. -/
def topologicalSort (graph : List (List Nat)) : Option (List Nat) :=
  if Pre graph then findFirst (isTopologicalOrder graph) (candidates graph) else none

/-! ## 2. Specification level (Prop) counterparts -/

/-- Propositional form of `edgesRespect`: every edge of `graph` goes forward in `order`. -/
def respectsEdges : List (List Nat) → List Nat → Nat → Prop
  | [], _, _ => True
  | (ns :: rest), order, k =>
      (∀ v ∈ ns, posOf k order < posOf v order) ∧ respectsEdges rest order (k + 1)

/-- `order` is a topological ordering of `graph`. -/
def IsTopOrder (graph : List (List Nat)) (order : List Nat) : Prop :=
  order.Perm (List.range graph.length) ∧ respectsEdges graph order 0

/-- `Reach graph u v`: there is a directed path with at least one edge from `u` to `v`. -/
inductive Reach (graph : List (List Nat)) : Nat → Nat → Prop
  | edge (u v : Nat) (h : v ∈ row graph u) : Reach graph u v
  | step (u v w : Nat) (h : v ∈ row graph u) (r : Reach graph v w) : Reach graph u w

/-! ## 3. Unit tests (the Lean counterpart of the Python `check` function) -/

#eval topologicalSort [[1], [2], []]
#eval topologicalSort [[1, 2], [3], [3], []]
#eval topologicalSort ([] : List (List Nat))
#eval topologicalSort [[], [], []]
#eval topologicalSort [[2], [], []]
#eval topologicalSort [[1], [0]]
#eval candidates [[1], [2], []]

/-- `g1 = [[1], [2], []]`: the chain `0 -> 1 -> 2` has the order `[0,1,2]`. -/
example : topologicalSort [[1], [2], []] = some [0, 1, 2] := by native_decide

example : isTopologicalOrder [[1], [2], []] [0, 1, 2] = true := by native_decide

/-- The checker rejects an ordering that is not compatible with the edges. -/
example : isTopologicalOrder [[1], [2], []] [1, 0, 2] = false := by native_decide

/-- The checker rejects an ordering that is not a permutation of the vertices. -/
example : isTopologicalOrder [[1], [2], []] [0, 1] = false := by native_decide

/-- `g2 = [[1,2],[3],[3],[]]`: the diamond DAG. -/
example : topologicalSort [[1, 2], [3], [3], []] = some [0, 1, 2, 3] := by native_decide

example : isTopologicalOrder [[1, 2], [3], [3], []] [0, 1, 2, 3] = true := by native_decide

/-- Every vertex occurs exactly once in the returned order. -/
example : (topologicalSort [[1, 2], [3], [3], []]).getD [] = [0, 1, 2, 3] := by native_decide

/-- `g3 = []`: the empty graph has the empty topological order. -/
example : topologicalSort ([] : List (List Nat)) = some [] := by native_decide

/-- `g4 = [[], [], []]`: three isolated vertices, lexicographically first order. -/
example : topologicalSort [[], [], []] = some [0, 1, 2] := by native_decide

/-- `g5 = [[2], [], []]`: the disconnected DAG with the single edge `0 -> 2`. -/
example : topologicalSort [[2], [], []] = some [0, 1, 2] := by native_decide

example : isTopologicalOrder [[2], [], []] [0, 1, 2] = true := by native_decide

/-- Python: `order5.index(0) < order5.index(2)`. -/
example : (topologicalSort [[2], [], []]).getD [] = [0, 1, 2] := by native_decide

example : posOf 0 [0, 1, 2] < posOf 2 [0, 1, 2] := by native_decide

/-- A two-cycle has no topological order. -/
example : topologicalSort [[1], [0]] = none := by native_decide

/-- A self-loop has no topological order. -/
example : topologicalSort [[0]] = none := by native_decide

/-- `[[2]]` is malformed: `2` is not a vertex of a one-vertex graph, so `Pre` fails. -/
example : Pre [[2]] = false := by native_decide

example : topologicalSort [[2]] = none := by native_decide

/-- The Python test `candidate([[1], "not a list"]) is None` checks a runtime *type* error,
which the typed Lean model cannot express; its typed analogue is a row mentioning a
non-vertex, which `Pre` rejects as well. -/
example : Pre [[1], [2]] = false := by native_decide

example : topologicalSort [[1], [2]] = none := by native_decide

/-- The candidate enumeration is lexicographic, exactly like
`itertools.permutations(range(3))`. -/
example : candidates [[1], [2], []] =
    [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]] := by native_decide

example : candidates ([] : List (List Nat)) = [[]] := by native_decide

/-- The Lean counterpart of the Python `check` function: it runs every assertion of the
Python test suite (the `"not a list"` case is replaced by its typed analogue, an adjacency
row mentioning a non-vertex) and is `true` exactly when all of them hold. -/
def check : Bool :=
  let g1 : List (List Nat) := [[1], [2], []]
  let g2 : List (List Nat) := [[1, 2], [3], [3], []]
  let g3 : List (List Nat) := []
  let g4 : List (List Nat) := [[], [], []]
  let g5 : List (List Nat) := [[2], [], []]
  (topologicalSort g1 == some [0, 1, 2]) &&
  (match topologicalSort g1 with
   | none => false
   | some o => isTopologicalOrder g1 o) &&
  (match topologicalSort g2 with
   | none => false
   | some o => isTopologicalOrder g2 o && decide (o.Perm [0, 1, 2, 3])) &&
  (topologicalSort g3 == some []) &&
  (topologicalSort g4 == some [0, 1, 2]) &&
  (match topologicalSort g5 with
   | none => false
   | some o => isTopologicalOrder g5 o && decide (posOf 0 o < posOf 2 o)) &&
  (topologicalSort [[1], [0]] == none) &&
  (topologicalSort [[0]] == none) &&
  (topologicalSort [[2]] == none) &&
  (Pre [[1], [2]] == false)

#eval check

example : check = true := by native_decide

/-! ## 4. Pre-condition -/

/-- The precondition as a proposition: every listed neighbour is a vertex. -/
def Pre_prop (graph : List (List Nat)) : Prop :=
  ∀ ns ∈ graph, ∀ v ∈ ns, v < graph.length

theorem Pre_true_iff (graph : List (List Nat)) : Pre graph = true ↔ Pre_prop graph := by
  simp only [Pre, Pre_prop, List.all_eq_true]
  constructor
  · intro h ns hns v hv
    simpa using (h ns hns v hv)
  · intro h ns hns v hv
    simp [h ns hns v hv]

/-! ## 5. Helper lemmas about the search -/

theorem findFirst_spec {α : Type} {p : α → Bool} : ∀ {l : List α} {a : α},
    findFirst p l = some a → p a = true ∧ a ∈ l := by
  intro l
  induction l with
  | nil => intro a h; simp [findFirst] at h
  | cons c cs ih =>
      intro a h
      cases hpc : p c
      · have h1 : findFirst p (c :: cs) = findFirst p cs := by simp [findFirst, hpc]
        rw [h1] at h
        have := ih h
        exact ⟨this.1, List.Mem.tail _ this.2⟩
      · have h1 : findFirst p (c :: cs) = some c := by simp [findFirst, hpc]
        rw [h1] at h
        have hca : c = a := Option.some.inj h
        rw [← hca]
        exact ⟨hpc, List.Mem.head _⟩

theorem findFirst_eq_none {α : Type} {p : α → Bool} : ∀ {l : List α},
    findFirst p l = none ↔ ∀ a ∈ l, p a = false := by
  intro l
  induction l with
  | nil => simp [findFirst]
  | cons c cs ih =>
      cases hpc : p c
      · have h1 : findFirst p (c :: cs) = findFirst p cs := by simp [findFirst, hpc]
        rw [h1, ih]
        constructor
        · intro h a ha
          simp only [List.mem_cons] at ha
          rcases ha with rfl | ha
          · exact hpc
          · exact h a ha
        · intro h a ha; exact h a (List.Mem.tail _ ha)
      · have h1 : findFirst p (c :: cs) = some c := by simp [findFirst, hpc]
        rw [h1]
        constructor
        · intro h; exact absurd h (by simp)
        · intro h; exact absurd (h c (List.Mem.head _)) (by simp [hpc])

theorem findFirst_isSome {α : Type} {p : α → Bool} : ∀ {l : List α},
    (∃ a ∈ l, p a = true) → ∃ b, findFirst p l = some b := by
  intro l
  induction l with
  | nil => simp
  | cons c cs ih =>
      intro h
      cases hpc : p c
      · have h1 : findFirst p (c :: cs) = findFirst p cs := by simp [findFirst, hpc]
        rw [h1]
        obtain ⟨a, ha, hpa⟩ := h
        have ha' : a ∈ cs := by
          simp only [List.mem_cons] at ha
          rcases ha with rfl | ha
          · exact absurd hpc (by simp [hpa])
          · exact ha
        exact ih ⟨a, ha', hpa⟩
      · exact ⟨c, by simp [findFirst, hpc]⟩

/-- The element returned by `findFirst` really is the *first* one satisfying `p`:
every candidate scanned before it fails `p`. -/
theorem findFirst_first {α : Type} {p : α → Bool} : ∀ {l : List α} {a : α},
    findFirst p l = some a →
      ∃ pre post, l = pre ++ (a :: post) ∧ ∀ b ∈ pre, p b = false := by
  intro l
  induction l with
  | nil => intro a h; simp [findFirst] at h
  | cons c cs ih =>
      intro a h
      cases hpc : p c
      · have h1 : findFirst p (c :: cs) = findFirst p cs := by simp [findFirst, hpc]
        rw [h1] at h
        obtain ⟨pre, post, hcs, hpre⟩ := ih h
        refine ⟨c :: pre, post, ?_, ?_⟩
        · simp [hcs]
        · intro b hb
          simp only [List.mem_cons] at hb
          rcases hb with rfl | hb
          · exact hpc
          · exact hpre b hb
      · have h1 : findFirst p (c :: cs) = some c := by simp [findFirst, hpc]
        rw [h1] at h
        have hca : c = a := Option.some.inj h
        exact ⟨[], cs, by simp [hca], by simp⟩

/-! ## 6. Helper lemmas about the permutation enumeration -/

theorem perm_cons_cancel {a : Nat} {l₁ l₂ : List Nat}
    (h : (a :: l₁).Perm (a :: l₂)) : l₁.Perm l₂ := by
  have := List.Perm.erase a h
  simpa using this

theorem mem_lexPermsAux {n : Nat} : ∀ (l m : List Nat), l.length ≤ n →
    m ∈ lexPermsAux n l → m.Perm l := by
  induction n with
  | zero =>
      intro l m hl hm
      cases l with
      | nil =>
          simp only [lexPermsAux, List.mem_singleton] at hm
          subst hm
          exact List.Perm.refl []
      | cons a l => exact absurd hl (by simp)
  | succ n ih =>
      intro l m hl hm
      simp only [lexPermsAux] at hm
      obtain ⟨e, he, hme⟩ := List.mem_flatMap.mp hm
      obtain ⟨q, hq, hqm⟩ := List.mem_map.mp hme
      have hlen : (l.erase e).length ≤ n := by
        rw [List.length_erase_of_mem he]
        omega
      have hperm : q.Perm (l.erase e) := ih (l.erase e) q hlen hq
      have h1 : (e :: q).Perm (e :: l.erase e) := List.Perm.cons e hperm
      have h2 : l.Perm (e :: l.erase e) := List.perm_cons_erase he
      rw [← hqm]
      exact List.Perm.trans h1 h2.symm

theorem lexPermsAux_mem {n : Nat} : ∀ (l : List Nat), l.length = n → l.Nodup →
    ∀ m, m.Perm l → m ∈ lexPermsAux n l := by
  induction n with
  | zero =>
      intro l hl hnd m hm
      have hnil : l = [] := List.length_eq_zero_iff.mp hl
      subst hnil
      have hm' : m = [] := List.Perm.eq_nil hm
      subst hm'
      simp [lexPermsAux]
  | succ n ih =>
      intro l hl hnd m hm
      have hmlen : m.length = n + 1 := by rw [List.Perm.length_eq hm, hl]
      obtain ⟨h, t, rfl⟩ : ∃ (h : Nat) (t : List Nat), m = h :: t := by
        cases m with
        | nil => exact absurd hmlen (by simp)
        | cons h t => exact ⟨h, t, rfl⟩
      have hhl : h ∈ l := (List.Perm.mem_iff hm).mp (List.Mem.head t)
      have hperm : (h :: t).Perm (h :: l.erase h) :=
        List.Perm.trans hm (List.perm_cons_erase hhl)
      have ht : t.Perm (l.erase h) := perm_cons_cancel hperm
      have hlen : (l.erase h).length = n := by
        rw [List.length_erase_of_mem hhl, hl]
        omega
      have hnd' : (l.erase h).Nodup :=
        (List.nodup_cons.mp ((List.Perm.nodup_iff (List.perm_cons_erase hhl)).mp hnd)).2
      have hmem : t ∈ lexPermsAux n (l.erase h) := ih (l.erase h) hlen hnd' t ht
      exact List.mem_flatMap.mpr ⟨h, hhl, List.mem_map.mpr ⟨t, hmem, rfl⟩⟩

/-- `lexPerms` enumerates exactly the permutations of a duplicate-free list. -/
theorem mem_lexPerms {l m : List Nat} (h : l.Nodup) : m ∈ lexPerms l ↔ m.Perm l := by
  simp only [lexPerms]
  exact ⟨fun hm => mem_lexPermsAux l m (Nat.le_refl _) hm,
         fun hm => lexPermsAux_mem l rfl h m hm⟩

/-- The list itself is the first permutation enumerated by `lexPermsAux`: the enumeration is
lexicographic, exactly like `itertools.permutations`. -/
theorem lexPermsAux_cons_head : ∀ (n : Nat) (l : List Nat), l.length = n →
    ∃ rest, lexPermsAux n l = l :: rest := by
  intro n
  induction n with
  | zero =>
      intro l hl
      have hnil : l = [] := List.length_eq_zero_iff.mp hl
      subst hnil
      exact ⟨[], by simp [lexPermsAux]⟩
  | succ n ih =>
      intro l hl
      cases l with
      | nil => simp at hl
      | cons a t =>
          have htl : t.length = n := by
            simp at hl
            omega
          obtain ⟨rest, hrest⟩ := ih t htl
          have hera : (a :: t).erase a = t := by simp
          have hflat : lexPermsAux (n + 1) (a :: t) =
              (lexPermsAux n ((a :: t).erase a)).map (fun p => a :: p) ++
                List.flatMap
                  (fun e => (lexPermsAux n ((a :: t).erase e)).map (fun p => e :: p)) t := rfl
          use (List.map (fun p => a :: p) rest) ++
                List.flatMap
                  (fun e => (lexPermsAux n ((a :: t).erase e)).map (fun p => e :: p)) t
          rw [hflat, hera, hrest]
          simp

theorem lexPerms_cons_head (l : List Nat) : ∃ rest, lexPerms l = l :: rest :=
  lexPermsAux_cons_head l.length l rfl

/-- The first candidate examined by the search is the identity ordering `0, 1, .., n-1`. -/
theorem candidates_cons (graph : List (List Nat)) :
    ∃ rest, candidates graph = List.range graph.length :: rest :=
  lexPerms_cons_head (List.range graph.length)

/-! ## 7. Bridging the executable checkers and their propositional forms -/

theorem edgesRespect_true_iff (order : List Nat) :
    ∀ (graph : List (List Nat)) (k : Nat),
      edgesRespect order graph k = true ↔ respectsEdges graph order k := by
  intro graph
  induction graph with
  | nil => intro k; simp [edgesRespect, respectsEdges]
  | cons ns rest ih =>
      intro k
      simp only [edgesRespect, respectsEdges, Bool.and_eq_true, List.all_eq_true, ih (k + 1)]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨fun v hv => by simpa using h1 v hv, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨fun v hv => by simp [h1 v hv], h2⟩

theorem isTopologicalOrder_true_iff (graph : List (List Nat)) (order : List Nat) :
    isTopologicalOrder graph order = true ↔ (Pre graph = true ∧ IsTopOrder graph order) := by
  constructor
  · intro h
    simp only [isTopologicalOrder, Bool.and_eq_true] at h
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨h1, ?_, (edgesRespect_true_iff order graph 0).mp h3⟩
    simpa using h2
  · rintro ⟨h1, h2⟩
    obtain ⟨hperm, hres⟩ := h2
    simp only [isTopologicalOrder, h1, Bool.true_and, Bool.and_eq_true]
    refine ⟨by simp [hperm], (edgesRespect_true_iff order graph 0).mpr hres⟩

theorem IsTopOrder_length {graph : List (List Nat)} {order : List Nat}
    (h : IsTopOrder graph order) : order.length = graph.length := by
  have h1 := List.Perm.length_eq h.1
  simp only [List.length_range] at h1
  exact h1

/-! ## 8. Positions along a directed path -/

theorem mem_row_imp : ∀ (graph : List (List Nat)) (u v : Nat),
    v ∈ row graph u → u < graph.length
  | [], u, v, h => absurd h (by simp [row])
  | (ns :: rest), 0, v, h => Nat.zero_lt_succ _
  | (ns :: rest), (u + 1), v, h => Nat.succ_lt_succ (mem_row_imp rest u v h)

theorem row_respects : ∀ (graph : List (List Nat)) (order : List Nat) (k u : Nat),
    respectsEdges graph order k → u < graph.length → ∀ v ∈ row graph u,
      posOf (k + u) order < posOf v order
  | [], order, k, u, hres, hu, v, hv => absurd hu (by simp)
  | (ns :: rest), order, k, 0, hres, hu, v, hv => by
      simpa using hres.1 v hv
  | (ns :: rest), order, k, (u + 1), hres, hu, v, hv => by
      have h := row_respects rest order (k + 1) u hres.2 (by simpa using hu) v hv
      have hkey : k + (u + 1) = k + 1 + u := by omega
      rw [hkey]
      exact h

/-- Along a directed path the positions in a topological order strictly increase. -/
theorem posOf_lt_of_Reach {graph : List (List Nat)} {u v : Nat}
    (h : Reach graph u v) :
    ∀ order, respectsEdges graph order 0 → posOf u order < posOf v order := by
  induction h with
  | edge u v hv =>
      intro order hres
      simpa using row_respects graph order 0 u hres (mem_row_imp graph u v hv) v hv
  | step u v w hv r ih =>
      intro order hres
      have h1 : posOf u order < posOf v order := by
        simpa using row_respects graph order 0 u hres (mem_row_imp graph u v hv) v hv
      exact Nat.lt_trans h1 (ih order hres)

/-- `posOf` on the identity ordering: vertex `u` sits at position `u`. -/
theorem posOf_succ_map (u : Nat) :
    ∀ (l : List Nat), posOf (u + 1) (l.map Nat.succ) = posOf u l := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih =>
      by_cases h : x = u
      · simp [posOf, List.map_cons, h]
      · have h2 : ¬(Nat.succ x = u + 1) := by
          intro h3; exact absurd (Nat.succ_inj.mp h3) h
        simp [posOf, List.map_cons, h, ih]

theorem posOf_range : ∀ (n u : Nat), u < n → posOf u (List.range n) = u := by
  intro n
  induction n with
  | zero => intro u hu; exact absurd hu (by simp)
  | succ n ih =>
      intro u hu
      rw [List.range_succ_eq_map]
      cases u with
      | zero => simp [posOf]
      | succ u =>
          have hne : ¬(0 = u + 1) := by simp
          have h1 : posOf u (List.range n) = u := ih u (by omega)
          have h2 : posOf (u + 1) ((List.range n).map Nat.succ) = posOf u (List.range n) :=
            posOf_succ_map u (List.range n)
          simp only [posOf, hne, if_false, h2, h1]

/-- Every vertex listed in a row occurs somewhere in the adjacency list. -/
theorem row_mem : ∀ (graph : List (List Nat)) (u v : Nat),
    v ∈ row graph u → ∃ ns ∈ graph, v ∈ ns
  | [], u, v, h => absurd h (by simp [row])
  | (ns :: rest), 0, v, h => ⟨ns, List.Mem.head _, h⟩
  | (ns :: rest), (u + 1), v, h =>
      match row_mem rest u v h with
      | ⟨ns', hns', hv⟩ => ⟨ns', List.Mem.tail _ hns', hv⟩

/-- If every edge of `graph` goes from a smaller index to a larger one (relative to the
offset `k`), then the identity ordering `List.range n` respects all edges. -/
theorem respectsEdges_range : ∀ (graph : List (List Nat)) (k n : Nat),
    k + graph.length = n →
    (∀ u < graph.length, ∀ v ∈ row graph u, k + u < v ∧ v < n) →
    respectsEdges graph (List.range n) k := by
  intro graph
  induction graph with
  | nil => intro k n hk H; exact trivial
  | cons ns rest ih =>
      intro k n hk H
      have hkl : (ns :: rest).length = rest.length + 1 := rfl
      rw [hkl] at hk
      have h1 : ∀ v ∈ ns, posOf k (List.range n) < posOf v (List.range n) := by
        intro v hv
        have Hv := H 0 (by simp) v hv
        have hk' : k < n := by omega
        rw [posOf_range n k hk', posOf_range n v Hv.2]
        simpa using Hv.1
      have h2 : respectsEdges rest (List.range n) (k + 1) :=
        ih (k + 1) n (by omega) (by
          intro u hu v hv
          have Hv := H (u + 1) (by simpa using hu) v hv
          exact ⟨by omega, Hv.2⟩)
      exact ⟨h1, h2⟩

/-! ## 9. Properties of the functional implementation -/

/-- Every `Option` is either `none` or `some a`. -/
theorem option_none_or_some {α : Type} (o : Option α) : o = none ∨ ∃ a, o = some a := by
  cases o with
  | none => exact Or.inl rfl
  | some a => exact Or.inr ⟨a, rfl⟩

/-- Malformed adjacency lists are rejected: the Python `if not pre(graph): return None`. -/
def malformed_prop (graph : List (List Nat)) : Prop :=
  Pre graph = false → topologicalSort graph = none

theorem malformed_thm (graph : List (List Nat)) : malformed_prop graph := by
  simp only [malformed_prop, topologicalSort]
  intro h
  simp [h]

/-- Soundness: whenever an order is returned it satisfies the topological-order checker,
i.e. it is a permutation of the vertices and every edge goes forward. -/
def soundness_prop (graph : List (List Nat)) : Prop :=
  ∀ order, topologicalSort graph = some order → IsTopOrder graph order

theorem soundness_thm (graph : List (List Nat)) : soundness_prop graph := by
  simp only [soundness_prop]
  intro order h
  simp only [topologicalSort] at h
  split at h
  · next _hpre =>
      obtain ⟨hchk, _⟩ := findFirst_spec h
      exact ((isTopologicalOrder_true_iff graph order).mp hchk).2
  · next _h => simp at h

/-- The returned order contains every vertex exactly once
(Python: "Disconnected DAGs include every vertex exactly once"). -/
def permutation_prop (graph : List (List Nat)) : Prop :=
  ∀ order, topologicalSort graph = some order →
    order.Perm (List.range graph.length) ∧ order.length = graph.length

theorem permutation_thm (graph : List (List Nat)) : permutation_prop graph := by
  simp only [permutation_prop]
  intro order h
  have htop := soundness_thm graph order h
  exact ⟨htop.1, IsTopOrder_length htop⟩

/-- Completeness: if some ordering of the vertices is topological, the exhaustive search
over all permutations finds one, so the result is not `None`. -/
def completeness_prop (graph : List (List Nat)) : Prop :=
  (∃ order, IsTopOrder graph order) → ∃ order, topologicalSort graph = some order

theorem completeness_thm (graph : List (List Nat)) (hpre : Pre graph = true) :
    completeness_prop graph := by
  simp only [completeness_prop]
  rintro ⟨order, hperm, hres⟩
  have hchk : isTopologicalOrder graph order = true :=
    (isTopologicalOrder_true_iff graph order).mpr ⟨hpre, hperm, hres⟩
  have hmem : order ∈ candidates graph := by
    simp only [candidates]
    exact (mem_lexPerms List.nodup_range).mpr hperm
  obtain ⟨b, hb⟩ := findFirst_isSome ⟨order, hmem, hchk⟩
  exact ⟨b, by simp [topologicalSort, hpre, hb]⟩

/-- `None` is returned exactly when no permutation of the vertices is a topological order
(Python: "Cycles return None because no topological order exists"). -/
def none_iff_prop (graph : List (List Nat)) : Prop :=
  topologicalSort graph = none ↔ ¬ ∃ order, IsTopOrder graph order

theorem none_iff_thm (graph : List (List Nat)) (hpre : Pre graph = true) :
    none_iff_prop graph := by
  simp only [none_iff_prop]
  constructor
  · intro hnone horder
    obtain ⟨order, ho⟩ := completeness_thm graph hpre horder
    rw [hnone] at ho
    simp at ho
  · intro h
    rcases option_none_or_some (topologicalSort graph) with hnone | ⟨order, ho⟩
    · exact hnone
    · exact absurd ⟨order, soundness_thm graph order ho⟩ h

/-- A graph that contains a directed cycle has no topological order, hence `None`
is returned.  `Reach graph u u` says that `u` lies on a directed cycle. -/
def cycle_prop (graph : List (List Nat)) : Prop :=
  (∃ u, Reach graph u u) → topologicalSort graph = none

theorem cycle_thm (graph : List (List Nat)) : cycle_prop graph := by
  simp only [cycle_prop]
  rintro ⟨u, hu⟩
  rcases option_none_or_some (topologicalSort graph) with h | ⟨order, ho⟩
  · exact h
  · have htop := soundness_thm graph order ho
    exact absurd (posOf_lt_of_Reach hu order htop.2) (Nat.lt_irrefl _)

/-- Converse of `cycle_thm`: if the search returns an ordering then the graph has no
directed cycle. -/
theorem isSome_imp_acyclic (graph : List (List Nat)) :
    (∃ order, topologicalSort graph = some order) → ¬ ∃ u, Reach graph u u := by
  rintro ⟨order, ho⟩ ⟨u, hu⟩
  have hnone := cycle_thm graph ⟨u, hu⟩
  rw [hnone] at ho
  simp at ho

/-- A self-loop is a cycle: Python `assert candidate([[0]]) is None`. -/
theorem selfLoop_none (graph : List (List Nat)) (u : Nat) (h : u ∈ row graph u) :
    topologicalSort graph = none :=
  cycle_thm graph ⟨u, Reach.edge u u h⟩

/-- A two-cycle is a cycle: Python `assert candidate([[1], [0]]) is None`. -/
theorem twoCycle_none (graph : List (List Nat)) (u v : Nat)
    (h1 : v ∈ row graph u) (h2 : u ∈ row graph v) :
    topologicalSort graph = none :=
  cycle_thm graph ⟨u, Reach.step u v u h1 (Reach.edge v u h2)⟩

theorem self_loop_example : topologicalSort [[0]] = none :=
  selfLoop_none [[0]] 0 (by simp [row])

theorem two_cycle_example : topologicalSort [[1], [0]] = none :=
  twoCycle_none [[1], [0]] 0 1 (by simp [row]) (by simp [row])

theorem malformed_example : Pre [[2]] = false := by decide

theorem malformed_example' : topologicalSort [[2]] = none :=
  malformed_thm [[2]] malformed_example

/-- The order returned is the *first* candidate, in the lexicographic enumeration of the
permutations, that passes the checker (Python: `return order` inside the `for candidate in
permutations(range(n))` loop). -/
def first_prop (graph : List (List Nat)) : Prop :=
  ∀ order, topologicalSort graph = some order →
    ∃ pre post, candidates graph = pre ++ (order :: post) ∧
      ∀ cand ∈ pre, isTopologicalOrder graph cand = false

theorem first_thm (graph : List (List Nat)) : first_prop graph := by
  simp only [first_prop]
  intro order h
  simp only [topologicalSort] at h
  split at h
  · next _hpre => exact findFirst_first h
  · next _h => simp at h

/-- If every edge points forward in the natural numbering `0 .. n-1`, then the identity
ordering `List.range n` passes the checker and, being the first candidate of the
lexicographic enumeration, is exactly what the search returns.  This is the theorem behind
the Python assertions `candidate([[1],[2],[]]) == [0,1,2]`,
`candidate([]) == []`, `candidate([[],[],[]]) == [0,1,2]` and the `g5` assertion
`order5.index(0) < order5.index(2)`. -/
theorem topologicalSort_range (graph : List (List Nat)) (hpre : Pre graph = true)
    (hfwd : ∀ u < graph.length, ∀ v ∈ row graph u, u < v) :
    topologicalSort graph = some (List.range graph.length) := by
  have hperm : (List.range graph.length).Perm (List.range graph.length) := List.Perm.refl _
  have hres : respectsEdges graph (List.range graph.length) 0 :=
    respectsEdges_range graph 0 graph.length (by simp) (by
      intro u hu v hv
      have hlt : v < graph.length := by
        obtain ⟨ns, hns, hv'⟩ := row_mem graph u v hv
        exact (Pre_true_iff graph).mp hpre ns hns v hv'
      exact ⟨by simpa using hfwd u hu v hv, hlt⟩)
  have hchk : isTopologicalOrder graph (List.range graph.length) = true :=
    (isTopologicalOrder_true_iff graph _).mpr ⟨hpre, hperm, hres⟩
  obtain ⟨rest, hrest⟩ := candidates_cons graph
  simp only [topologicalSort, hpre, ite_true, hrest, findFirst, hchk]

theorem empty_graph_result : topologicalSort ([] : List (List Nat)) = some [] :=
  topologicalSort_range [] (by decide) (by simp)

theorem no_edge_graph_result : topologicalSort [[], [], []] = some [0, 1, 2] :=
  topologicalSort_range [[], [], []] (by decide) (by
    intro u hu v hv
    have hu3 : u < 3 := by simpa using hu
    have hu' : u = 0 ∨ u = 1 ∨ u = 2 := by omega
    rcases hu' with rfl | rfl | rfl <;> simp [row] at hv)

theorem chain_graph_result : topologicalSort [[1], [2], []] = some [0, 1, 2] := by
  refine topologicalSort_range [[1], [2], []] (by decide) ?_
  intro u hu v hv
  have hu3 : u < 3 := by simpa using hu
  have hu' : u = 0 ∨ u = 1 ∨ u = 2 := by omega
  rcases hu' with rfl | rfl | rfl
  · simp [row] at hv
    rcases hv with rfl
    decide
  · simp [row] at hv
    rcases hv with rfl
    decide
  · simp [row] at hv

theorem single_edge_graph_result : topologicalSort [[2], [], []] = some [0, 1, 2] := by
  refine topologicalSort_range [[2], [], []] (by decide) ?_
  intro u hu v hv
  have hu3 : u < 3 := by simpa using hu
  have hu' : u = 0 ∨ u = 1 ∨ u = 2 := by omega
  rcases hu' with rfl | rfl | rfl
  · simp [row] at hv
    rcases hv with rfl
    decide
  · simp [row] at hv
  · simp [row] at hv

theorem diamond_graph_result : topologicalSort [[1, 2], [3], [3], []] = some [0, 1, 2, 3] := by
  refine topologicalSort_range [[1, 2], [3], [3], []] (by decide) ?_
  intro u hu v hv
  have hu4 : u < 4 := by simpa using hu
  have hu' : u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 := by omega
  rcases hu' with rfl | rfl | rfl | rfl
  · simp [row] at hv
    rcases hv with rfl | rfl <;> decide
  · simp [row] at hv
    rcases hv with rfl
    decide
  · simp [row] at hv
    rcases hv with rfl
    decide
  · simp [row] at hv

/-! ## 10. Post-condition and correctness -/

/-- Post-condition of `topologicalSort`: the answer is either a genuine topological order
of `graph` or `none`, `none` is returned exactly when no topological order exists, and a
returned order is one of the enumerated candidates. -/
def Post_prop (graph : List (List Nat)) (result : Option (List Nat)) : Prop :=
  (∀ order, result = some order → IsTopOrder graph order) ∧
  (result = none ↔ ¬ ∃ order, IsTopOrder graph order) ∧
  (∀ order, result = some order → order ∈ candidates graph)

/-! ## 11. Property-based tests

Every executable property stated above is tested on many inputs.

The bounded tests use `allGraphs n`, which enumerates *all* adjacency lists with `n` rows
whose entries range over `0 .. n`; since the entry `n` is out of range for an `n`-row
graph, both well-formed and malformed graphs occur.  For `n = 3` this is an exhaustive
scan of `16^3 = 4096` graphs, for `n = 2` of `8^2 = 64` graphs.
-/

/-- All sublists of `l`; used to enumerate the possible adjacency rows. -/
def allSublists : List Nat → List (List Nat)
  | [] => [[]]
  | (a :: l) => (allSublists l).map (a :: ·) ++ allSublists l

/-- All lists of `k` rows, every row drawn from `rows`. -/
def allGraphsAux : Nat → List (List Nat) → List (List (List Nat))
  | 0, _ => [[]]
  | (k + 1), rows =>
      List.flatMap (fun r => (allGraphsAux k rows).map fun g => r :: g) rows

/-- Every adjacency list with `n` rows over the vertices `0 .. n`. -/
def allGraphs (n : Nat) : List (List (List Nat)) :=
  allGraphsAux n (allSublists (List.range (n + 1)))

#eval (allGraphs 2).length
#eval (allGraphs 3).length

/-- Executable reachability: every vertex reachable from a vertex of `start` by a path of
at most `graph.length` edges. -/
def reachFrom (graph : List (List Nat)) (start : List Nat) : List Nat :=
  (List.range graph.length).foldl
    (fun acc _ => (acc ++ acc.flatMap (fun w => row graph w)).dedup) start

/-- Executable cycle test: some vertex is reachable from one of its own out-neighbours,
i.e. lies on a directed cycle. -/
def hasCycleB (graph : List (List Nat)) : Bool :=
  (List.range graph.length).any fun u => decide (u ∈ reachFrom graph (row graph u))

/-- A self-loop or a two-cycle, detected executably; used to test `cycle_prop`. -/
def hasSmallCycle (g : List (List Nat)) : Bool :=
  Pre g && (List.range g.length).any (fun u =>
    (row g u).any (fun v => decide (v = u) || (row g v).any (fun w => decide (w = u))))

-- PBT for `soundness_prop`: whenever an order is returned it passes the executable checker.
example : (allGraphs 3).all (fun g => match topologicalSort g with
    | none => true
    | some o => isTopologicalOrder g o) = true := by native_decide

-- PBT for `permutation_prop`: a returned order is a permutation of the vertices `0 .. n-1`.
example : (allGraphs 3).all (fun g => match topologicalSort g with
    | none => true
    | some o => decide (o.Perm (List.range g.length))) = true := by native_decide

-- PBT for `none_iff_prop` (and hence `completeness_prop`): `none` is returned exactly when
-- no candidate permutation passes the checker.
example : (allGraphs 3).all (fun g =>
    ((topologicalSort g).isNone == (candidates g).all (fun o => !isTopologicalOrder g o))) = true
  := by native_decide

-- PBT for `malformed_prop`: an adjacency list mentioning a non-vertex yields `none`
-- (equivalently: a graph that is *not* rejected by `Pre` may return an order, a graph that
-- is rejected always returns `none`).
example : (allGraphs 3).all (fun g => (Pre g) || (topologicalSort g).isNone) = true := by
  native_decide

-- PBT for `cycle_prop`: graphs with a self-loop or a two-cycle yield `none`.
example : (allGraphs 3).all (fun g => (!hasSmallCycle g) || (topologicalSort g).isNone) = true := by
  native_decide

-- PBT for `first_prop`: no candidate scanned before the returned one passes the checker.
example : (allGraphs 3).all (fun g => match topologicalSort g with
    | none => true
    | some o => ((candidates g).takeWhile (fun c => !(c == o))).all
      (fun c => !isTopologicalOrder g c)) = true := by native_decide

-- PBT for the checker itself: on candidates (which are permutations by construction) it
-- agrees with the conjunction of the precondition and the edge condition.
example : (allGraphs 2).all (fun g => (candidates g).all (fun o =>
    (isTopologicalOrder g o == (Pre g && edgesRespect o g 0)))) = true := by native_decide

-- PBT for `Pre`: it agrees with the row-wise formulation of the well-formedness condition
-- (the executable content of `Pre_prop`) on every small graph.
example : (allGraphs 3).all (fun g =>
    (Pre g == (List.range g.length).all (fun u =>
      (row g u).all (fun v => decide (v < g.length))))) = true := by native_decide

-- PBT for `edgesRespect`: it agrees with a direct scan over all pairs `(u, v)` of the rows.
example : (allGraphs 2).all (fun g => (candidates g).all (fun o =>
    (edgesRespect o g 0 == (List.range g.length).all (fun u =>
      (row g u).all (fun v => decide (posOf u o < posOf v o)))))) = true := by native_decide

-- PBT for the DAG characterisation of the Python docstring ("Cycles return None because
-- no topological order exists"): for a well-formed graph, `none` is returned *exactly*
-- when the graph has a directed cycle.  Exhaustive over all 4096 small adjacency lists.
example : (allGraphs 3).all (fun g =>
    (!Pre g) || ((hasCycleB g) == (topologicalSort g).isNone)) = true := by native_decide

-- PBT for `cycle_thm` with the executable cycle detector.
example : (allGraphs 3).all (fun g =>
    (!hasCycleB g) || (topologicalSort g).isNone) = true := by native_decide

-- PBT for `isSome_imp_acyclic`: a returned order witnesses acyclicity.
example : (allGraphs 3).all (fun g =>
    (topologicalSort g).isNone || (!hasCycleB g)) = true := by native_decide

/-! ### Randomized property-based tests (Plausible)

Plausible's sampler for `List (List Nat)` produces lists whose length grows with the test
number, so a size *precondition* would make it discard most samples.  Instead the tests
below are precondition-free: an unconstrained seed is turned into a small graph by
`sampleGraph`, and the property is stated about that graph.  The theorems proved above are
stated for *all* graphs, with no restriction.
-/

/-- Turns an arbitrary seed into a small graph: at most four rows, entries in `0 .. 4`
(so both well-formed and malformed graphs occur). -/
def sampleGraph (seed : List (List Nat)) : List (List Nat) :=
  (seed.take 4).map fun ns => ns.map fun v => v % 5

-- randomized PBT for `soundness_prop`
#eval Plausible.Testable.check (∀ (seed : List (List Nat)),
  (topologicalSort (sampleGraph seed)).isNone ||
    isTopologicalOrder (sampleGraph seed) ((topologicalSort (sampleGraph seed)).getD []))

-- randomized PBT for `permutation_prop`
#eval Plausible.Testable.check (∀ (seed : List (List Nat)),
  (topologicalSort (sampleGraph seed)).isNone ||
    decide (((topologicalSort (sampleGraph seed)).getD []).Perm
      (List.range (sampleGraph seed).length)))

-- randomized PBT for `malformed_prop`
#eval Plausible.Testable.check (∀ (seed : List (List Nat)),
  (Pre (sampleGraph seed)) || (topologicalSort (sampleGraph seed)).isNone)

-- randomized PBT for `none_iff_prop` / `completeness_prop`
#eval Plausible.Testable.check (∀ (seed : List (List Nat)),
  (topologicalSort (sampleGraph seed)).isNone ==
    (candidates (sampleGraph seed)).all fun o => !(isTopologicalOrder (sampleGraph seed) o))

-- randomized PBT for `first_prop`
#eval Plausible.Testable.check (∀ (seed : List (List Nat)),
  (topologicalSort (sampleGraph seed)).isNone ||
    ((candidates (sampleGraph seed)).takeWhile
      (fun c => !(c == (topologicalSort (sampleGraph seed)).getD []))).all
      fun c => !isTopologicalOrder (sampleGraph seed) c)

-- randomized PBT for `cycle_prop`: self-loops
#eval Plausible.Testable.check (∀ (seed : List (List Nat)) (u : Nat),
  !(decide (u ∈ row (sampleGraph seed) u)) || (topologicalSort (sampleGraph seed)).isNone)

-- randomized PBT for `cycle_prop`: self-loops and two-cycles
#eval Plausible.Testable.check (∀ (seed : List (List Nat)),
  !(hasSmallCycle (sampleGraph seed)) || (topologicalSort (sampleGraph seed)).isNone)

-- randomized PBT for the checker: it implies both of its conjuncts (cheap, no seed needed)
#eval Plausible.Testable.check (∀ (g : List (List Nat)) (o : List Nat),
  !(isTopologicalOrder g o) || (edgesRespect o g 0))

#eval Plausible.Testable.check (∀ (g : List (List Nat)) (o : List Nat),
  !(isTopologicalOrder g o) || (Pre g))

-- randomized PBT for the DAG characterisation
#eval Plausible.Testable.check (∀ (seed : List (List Nat)),
  (!Pre (sampleGraph seed)) ||
    ((hasCycleB (sampleGraph seed)) == (topologicalSort (sampleGraph seed)).isNone))

-- randomized PBT for `Pre`: it is implied by all vertices being in range
#eval Plausible.Testable.check (∀ (g : List (List Nat)),
  ((List.range g.length).all (fun u => (row g u).all (fun v => decide (v < g.length)))) ==
    (Pre g))

theorem correctness_thm (graph : List (List Nat)) (hpre : Pre graph = true) :
    Post_prop graph (topologicalSort graph) := by
  refine ⟨?_, ?_, ?_⟩
  · intro order ho
    exact soundness_thm graph order ho
  · exact none_iff_thm graph hpre
  · intro order ho
    have h1 : findFirst (isTopologicalOrder graph) (candidates graph) = some order := by
      simpa [topologicalSort, hpre] using ho
    exact (findFirst_spec h1).2

/-! ## 12. Imperative implementation (`Id.run do` with mutable state) -/

/-- A `for` loop over a list in the `Id` monad that only updates an accumulator is a left
fold. -/
theorem forIn_eq_foldl {α β : Type} (f : α → β → β) :
    ∀ (b : β) (l : List α),
      Id.run (forIn l b (fun x s => pure (ForInStep.yield (f x s)))) =
        l.foldl (fun s x => f x s) b := by
  intro b l
  induction l generalizing b with
  | nil => rfl
  | cons a l ih => simp

theorem foldl_and_all {α : Type} (g : α → Bool) :
    ∀ (b : Bool) (l : List α), l.foldl (fun ok x => ok && g x) b = (b && l.all g) := by
  intro b l
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
      have h1 : (a :: l).foldl (fun ok x => ok && g x) b =
          l.foldl (fun ok x => ok && g x) (b && g a) := rfl
      rw [h1, ih (b && g a)]
      show ((b && g a) && l.all g) = (b && (g a && l.all g))
      rw [Bool.and_assoc]

/-- One iteration of the imperative search: if nothing has been accepted yet and `cand`
passes the checker, store it in the mutable accumulator. -/
def searchStep (graph : List (List Nat)) (cand : List Nat)
    (best : Option (List Nat)) : Option (List Nat) :=
  Id.run do
    let mut best := best
    if best.isNone then
      if isTopologicalOrder graph cand then
        best := some cand
    return best

theorem searchStep_eq (graph : List (List Nat)) (cand : List Nat)
    (best : Option (List Nat)) :
    searchStep graph cand best =
      (if best.isNone && isTopologicalOrder graph cand then some cand else best) := by
  by_cases hb : best.isNone
  · by_cases hp : isTopologicalOrder graph cand
    · simp [searchStep, hb, hp]
    · simp [searchStep, hb, hp]
  · simp [searchStep, hb]

/-- The imperative scan of the candidate list, with a mutable accumulator. -/
def searchImp (graph : List (List Nat)) (cands : List (List Nat)) : Option (List Nat) :=
  Id.run do
    let mut best : Option (List Nat) := none
    for cand in cands do
      best := searchStep graph cand best
    return best

theorem searchImp_unfold (graph : List (List Nat)) (cands : List (List Nat)) :
    searchImp graph cands =
      Id.run (forIn cands none
        (fun cand best => pure (ForInStep.yield (searchStep graph cand best)))) := rfl

theorem foldl_searchStep (graph : List (List Nat)) :
    ∀ (b : Option (List Nat)) (l : List (List Nat)),
      l.foldl (fun s x => searchStep graph x s) b =
        (if b.isNone then findFirst (isTopologicalOrder graph) l else b) := by
  intro b l
  induction l generalizing b with
  | nil => simp [findFirst]
  | cons a l ih =>
      have h1 : (a :: l).foldl (fun s x => searchStep graph x s) b =
          l.foldl (fun s x => searchStep graph x s) (searchStep graph a b) := rfl
      rw [h1, ih (searchStep graph a b), searchStep_eq]
      by_cases hb : b.isNone
      · by_cases hp : isTopologicalOrder graph a
        · simp [hb, hp, findFirst]
        · simp [hb, hp, findFirst]
      · simp [hb]

theorem searchImp_eq (graph : List (List Nat)) (cands : List (List Nat)) :
    searchImp graph cands = findFirst (isTopologicalOrder graph) cands := by
  rw [searchImp_unfold, forIn_eq_foldl, foldl_searchStep]
  simp

/-- The imperative well-formedness scan with a mutable flag. -/
def preScan (n : Nat) (graph : List (List Nat)) : Bool :=
  Id.run do
    let mut ok := true
    for ns in graph do
      ok := ok && ns.all (fun v => decide (v < n))
    return ok

theorem preScan_unfold (n : Nat) (graph : List (List Nat)) :
    preScan n graph =
      Id.run (forIn graph true
        (fun (ns : List Nat) (ok : Bool) =>
          pure (ForInStep.yield (ok && ns.all (fun v => decide (v < n)))))) := rfl

theorem preScan_eq (n : Nat) (graph : List (List Nat)) :
    preScan n graph = graph.all (fun ns => ns.all (fun v => decide (v < n))) := by
  rw [preScan_unfold, forIn_eq_foldl, foldl_and_all]
  simp

/-- Imperative counterpart of `Pre`. -/
def preImp (graph : List (List Nat)) : Bool := preScan graph.length graph

theorem preImp_eq (graph : List (List Nat)) : preImp graph = Pre graph := by
  simp only [preImp, Pre]
  exact preScan_eq graph.length graph

/-- Imperative topological sort: check the adjacency list with a mutable flag, then walk
the candidate permutations with a mutable accumulator holding the first accepted order. -/
def topologicalSortImp (graph : List (List Nat)) : Option (List Nat) :=
  Id.run do
    let mut ok := preImp graph
    let mut best : Option (List Nat) := none
    if ok then
      for cand in lexPerms (List.range graph.length) do
        best := searchStep graph cand best
    return best

theorem topologicalSortImp_bridge (graph : List (List Nat)) :
    topologicalSortImp graph =
      (if preImp graph then searchImp graph (lexPerms (List.range graph.length))
       else none) := by
  by_cases h : preImp graph
  · simp [topologicalSortImp, searchImp, h]
  · simp [topologicalSortImp, h]

/-! ## 13. Imperative tests -/

#eval topologicalSortImp [[1], [2], []]
#eval topologicalSortImp [[1, 2], [3], [3], []]
#eval topologicalSortImp ([] : List (List Nat))
#eval topologicalSortImp [[1], [0]]
#eval preImp [[2]]

example : topologicalSortImp [[1], [2], []] = some [0, 1, 2] := by native_decide
example : topologicalSortImp [[1, 2], [3], [3], []] = some [0, 1, 2, 3] := by native_decide
example : topologicalSortImp ([] : List (List Nat)) = some [] := by native_decide
example : topologicalSortImp [[], [], []] = some [0, 1, 2] := by native_decide
example : topologicalSortImp [[2], [], []] = some [0, 1, 2] := by native_decide
example : topologicalSortImp [[1], [0]] = none := by native_decide
example : topologicalSortImp [[0]] = none := by native_decide
example : topologicalSortImp [[2]] = none := by native_decide
example : preImp [[1], [2], []] = true := by native_decide
example : preImp [[2]] = false := by native_decide
example : searchImp [[1], [2], []] (candidates [[1], [2], []]) = some [0, 1, 2] := by
  native_decide

-- Bounded PBT: the imperative and the functional implementation agree on all 4096 small
-- adjacency lists.
example : (allGraphs 3).all (fun g => (topologicalSortImp g == topologicalSort g)) = true := by
  native_decide

-- Randomized PBT for the functional/imperative equivalence.
#eval Plausible.Testable.check (∀ (seed : List (List Nat)),
  (topologicalSortImp (sampleGraph seed)) == (topologicalSort (sampleGraph seed)))

/-! ## 14. Equivalence of the functional and the imperative implementation -/

/-- The imperative implementation returns exactly what the functional one returns. -/
theorem topologicalSortImp_eq (graph : List (List Nat)) :
    topologicalSortImp graph = topologicalSort graph := by
  rw [topologicalSortImp_bridge, searchImp_eq, preImp_eq]
  simp [topologicalSort, candidates]

/-- The imperative implementation satisfies the same post-condition. -/
theorem correctness_thm_imp (graph : List (List Nat)) (hpre : preImp graph = true) :
    Post_prop graph (topologicalSortImp graph) := by
  rw [topologicalSortImp_eq]
  rw [preImp_eq] at hpre
  exact correctness_thm graph hpre

end topological_sort
