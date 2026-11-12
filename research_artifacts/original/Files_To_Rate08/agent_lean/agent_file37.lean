import Mathlib

/-!
# Exhaustive topological sorting

Translation of the Python adjacency-list program. `Value` retains dynamic type
errors (including a non-list outer object or row); `boolean` is accepted as an
integer, as it is by Python's `isinstance(v, int)`. All other Python objects are
represented by `other`: their payload is irrelevant to the program.

Orders contain natural-number vertex labels. Sorting all permutations by the
lexicographic order on lists gives the order of
`itertools.permutations(range(n))`, including `[[]]` when n = 0. The search is
exhaustive, not an efficient graph algorithm.
-/

namespace topological_sort

inductive Value where
  | integer : Int → Value
  | boolean : Bool → Value
  | list : List Value → Value
  | other : String → Value
  deriving Repr

def integerValue : Value → Option Int
  | .integer i => some i
  | .boolean b => some (if b then 1 else 0)
  | _ => none

def rows : Value → List Value
  | .list xs => xs
  | _ => []

def size (g : Value) : Nat := (rows g).length

def pre (g : Value) : Bool :=
  match g with
  | .list rs => rs.all fun r =>
      match r with
      | .list ns => ns.all fun v =>
          match integerValue v with
          | some i => decide (0 ≤ i ∧ i < (rs.length : Int))
          | none => false
      | _ => false
  | _ => false

/-- Only used after validation; defaults here do not make malformed inputs valid. -/
def neighbors (g : Value) (u : Nat) : List Nat :=
  (rows ((rows g)[u]?.getD (.other "missing"))).map
    (fun v => ((integerValue v).getD (-1)).toNat)

def edgesOK (g : Value) (order : List Nat) : Bool :=
  (List.range (size g)).all fun u =>
    (neighbors g u).all fun v => decide (order.idxOf u < order.idxOf v)

def is_topological_order (g : Value) (order : List Nat) : Bool :=
  pre g && decide (order.Perm (List.range (size g))) && edgesOK g order

def permutations (n : Nat) : List (List Nat) :=
  (List.range n).permutations.mergeSort (fun a b => decide (a ≤ b))

def topological_sort (g : Value) : Option (List Nat) :=
  if pre g then (permutations (size g)).find? (is_topological_order g) else none

/-- Injection of ordinary integer adjacency lists into the dynamic input type. -/
def graph (g : List (List Int)) : Value :=
  .list (g.map fun ns => .list (ns.map Value.integer))

-- Unit tests, including every case in the Python check function.
example : topological_sort (graph [[1], [2], []]) = some [0, 1, 2] := by native_decide
example : topological_sort (graph [[1, 2], [3], [3], []]) = some [0, 1, 2, 3] := by native_decide
example : is_topological_order (graph [[1, 2], [3], [3], []]) [0, 1, 2, 3] = true := by native_decide
example : topological_sort (graph []) = some [] := by native_decide
example : topological_sort (graph [[], [], []]) = some [0, 1, 2] := by native_decide
example : topological_sort (graph [[2], [], []]) = some [0, 1, 2] := by native_decide
example : topological_sort (graph [[1], [0]]) = none := by native_decide
example : topological_sort (graph [[0]]) = none := by native_decide
example : topological_sort (graph [[2]]) = none := by native_decide
example : topological_sort (.list [.list [.integer 1], .other "not a list"]) = none := by native_decide
example : topological_sort (graph [[-1]]) = none := by native_decide
example : topological_sort (.other "not a graph") = none := by native_decide
example : topological_sort (.list [.list [.other "not an integer"]]) = none := by native_decide
example : topological_sort (.list [.list [.boolean true], .list []]) = some [0, 1] := by native_decide
example : topological_sort (graph [[], [0]]) = some [1, 0] := by native_decide
example : is_topological_order (graph [[], []]) [0, 0] = false := by native_decide
#eval topological_sort (graph [[1, 2], [3], [3], []])
#eval topological_sort (graph [[1], [0]])

/-- Exactly the source's validity precondition, not a DAG assumption. -/
def Pre (g : Value) : Prop := pre g = true

/-- Mathematical, independent specification of a valid order. -/
def TopologicalOrder (g : Value) (o : List Nat) : Prop :=
  Pre g ∧ o.Perm (List.range (size g)) ∧
    ∀ u ∈ List.range (size g), ∀ v ∈ neighbors g u, o.idxOf u < o.idxOf v

def Edge (g : Value) (u v : Nat) : Prop :=
  u ∈ List.range (size g) ∧ v ∈ neighbors g u

def HasCycle (g : Value) : Prop := ∃ v, Relation.TransGen (Edge g) v v

def soundness_prop (g : Value) : Prop :=
  ∀ o, topological_sort g = some o → TopologicalOrder g o

def completeness_prop (g : Value) : Prop :=
  (topological_sort g = none) ↔ ¬ ∃ o, TopologicalOrder g o

def malformed_prop (g : Value) : Prop := ¬ Pre g → topological_sort g = none

def vertices_prop (g : Value) : Prop :=
  ∀ o, topological_sort g = some o →
    o.Nodup ∧ (∀ v, v ∈ o ↔ v < size g) ∧ o.length = size g

def edges_prop (g : Value) : Prop :=
  ∀ o, topological_sort g = some o →
    ∀ u v, Edge g u v → o.idxOf u < o.idxOf v

def cycle_prop (g : Value) : Prop := HasCycle g → topological_sort g = none

/-- Not just any valid result: every preceding permutation fails the checker. -/
def first_prop (g : Value) : Prop :=
  ∀ o, topological_sort g = some o →
    ∃ before after, permutations (size g) = before ++ o :: after ∧
      (∀ p ∈ before, ¬ TopologicalOrder g p)

def minimal_prop (g : Value) : Prop :=
  ∀ o, topological_sort g = some o → ∀ p, TopologicalOrder g p → o ≤ p

-- All theorems below use kernel-checked proofs, not compiled tests.
theorem checker_iff (g : Value) (o : List Nat) :
    is_topological_order g o = true ↔ TopologicalOrder g o := by
  simp [is_topological_order, edgesOK, TopologicalOrder, Pre, List.all_eq_true,
    and_assoc]

theorem pre_graph_thm (g : List (List Int)) :
    Pre (graph g) ↔ ∀ ns ∈ g, ∀ v ∈ ns, 0 ≤ v ∧ v < (g.length : Int) := by
  simp [Pre, graph, pre, integerValue, List.all_eq_true]

theorem mem_permutations (n : Nat) (o : List Nat) :
    o ∈ permutations n ↔ o.Perm (List.range n) := by
  simp [permutations, List.mem_permutations]

theorem permutations_sorted (n : Nat) :
    (permutations n).Pairwise (· ≤ ·) := by
  have h := List.sorted_mergeSort
    (le := fun a b : List Nat => decide (a ≤ b))
    (by intro a b c hab hbc; simpa using le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total a b)
    (List.range n).permutations
  simpa [permutations] using h

theorem soundness_thm (g : Value) : soundness_prop g := by
  intro o h
  unfold topological_sort at h
  split at h
  · exact (checker_iff g o).mp (List.find?_some h)
  · simp at h

theorem malformed_thm (g : Value) : malformed_prop g := by
  intro h
  change ¬ pre g = true at h
  simp [topological_sort, h]

theorem completeness_thm (g : Value) : completeness_prop g := by
  constructor
  · intro hn ⟨o, ho⟩
    have hp : pre g = true := ho.1
    have hf : (permutations (size g)).find? (is_topological_order g) = none := by
      simpa [topological_sort, hp] using hn
    exact (List.find?_eq_none.mp hf) o ((mem_permutations _ _).mpr ho.2.1)
      ((checker_iff g o).mpr ho)
  · intro h
    cases he : topological_sort g with
    | none => rfl
    | some o => exact False.elim (h ⟨o, soundness_thm g o he⟩)

theorem vertices_thm (g : Value) : vertices_prop g := by
  intro o h
  have hp := (soundness_thm g o h).2.1
  refine ⟨hp.nodup_iff.mpr List.nodup_range, ?_, ?_⟩
  · intro v
    exact hp.mem_iff.trans List.mem_range
  · simpa using hp.length_eq

theorem edges_thm (g : Value) : edges_prop g := by
  intro o h u v huv
  exact (soundness_thm g o h).2.2 u huv.1 v huv.2

theorem path_increases {g : Value} {o : List Nat} (ho : TopologicalOrder g o)
    {u v : Nat} (h : Relation.TransGen (Edge g) u v) : o.idxOf u < o.idxOf v := by
  induction h with
  | single h => exact ho.2.2 _ h.1 _ h.2
  | tail h e ih => exact lt_trans ih (ho.2.2 _ e.1 _ e.2)

theorem cycle_thm (g : Value) : cycle_prop g := by
  intro ⟨v, hv⟩
  apply (completeness_thm g).mpr
  rintro ⟨o, ho⟩
  exact (Nat.lt_irrefl _) (path_increases ho hv)

theorem first_thm (g : Value) : first_prop g := by
  intro o h
  have hp : pre g = true := (soundness_thm g o h).1
  have hf : (permutations (size g)).find? (is_topological_order g) = some o := by
    simpa [topological_sort, hp, Pre] using h
  obtain ⟨_, before, after, he, hb⟩ := List.find?_eq_some_iff_append.mp hf
  refine ⟨before, after, he, ?_⟩
  intro p hm ht
  have ht' := (checker_iff g p).mpr ht
  have := hb p hm
  simp [ht'] at this

/-- Generic fact: searching a sorted list returns its least successful element. -/
theorem find_le {xs : List (List Nat)} {test : List Nat → Bool} {o : List Nat}
    (hs : xs.Pairwise (· ≤ ·)) (hf : xs.find? test = some o) :
    ∀ p ∈ xs, test p = true → o ≤ p := by
  induction xs with
  | nil => simp at hf
  | cons a xs ih =>
    obtain ⟨ha, ht⟩ := List.pairwise_cons.mp hs
    by_cases hta : test a = true
    · have hoa : a = o := by simpa [List.find?, hta] using hf
      subst o
      intro p hp _
      rcases List.mem_cons.mp hp with rfl | hp
      · exact le_rfl
      · exact ha p hp
    · have hf' : xs.find? test = some o := by simpa [List.find?, hta] using hf
      intro p hp htp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact False.elim (hta htp)
      · exact ih ht hf' p hp htp

theorem minimal_thm (g : Value) : minimal_prop g := by
  intro o ho p hp
  have hg : pre g = true := (soundness_thm g o ho).1
  have hf : (permutations (size g)).find? (is_topological_order g) = some o := by
    simpa [topological_sort, hg, Pre] using ho
  exact find_le (permutations_sorted _) hf p
    ((mem_permutations _ _).mpr hp.2.1) ((checker_iff g p).mpr hp)

/-- A valid graph with zero vertices returns the empty order, not failure. -/
def empty_prop (g : Value) : Prop :=
  Pre g → size g = 0 → topological_sort g = some []

theorem empty_thm (g : Value) : empty_prop g := by
  intro hp hn
  change pre g = true at hp
  simp [topological_sort, hp, hn, permutations, is_topological_order, edgesOK]

theorem sorted_le_perm {l p : List Nat} (hs : l.Pairwise (· ≤ ·)) (hp : l.Perm p) :
    l ≤ p := by
  induction l generalizing p with
  | nil =>
    have h : p = [] := List.nil_perm.mp hp
    subst p
    exact le_rfl
  | cons a l ih =>
    cases p with
    | nil => simp at hp
    | cons b p =>
      by_cases hab : a = b
      · subst b
        exact List.cons_le_cons a (ih (List.pairwise_cons.mp hs).2 ((List.perm_cons a).mp hp))
      · have hb : b ∈ a :: l := hp.mem_iff.mpr (by simp)
        have hb' : b ∈ l := by simpa [Ne.symm hab] using hb
        have hle : a ≤ b := (List.pairwise_cons.mp hs).1 b hb'
        have hlt : a < b := by omega
        exact le_of_lt (show List.Lex (· < ·) (a :: l) (b :: p) from .rel hlt)

/-- Disconnected graphs with no edges use the first permutation, in ascending order. -/
def edgeless_prop (g : Value) : Prop :=
  Pre g → (∀ u ∈ List.range (size g), neighbors g u = []) →
    topological_sort g = some (List.range (size g))

theorem edgeless_thm (g : Value) : edgeless_prop g := by
  intro hg he
  have hid : TopologicalOrder g (List.range (size g)) := by
    refine ⟨hg, List.Perm.refl _, ?_⟩
    intro u hu v hv
    simp [he u hu] at hv
  cases h : topological_sort g with
  | none => exact False.elim ((completeness_thm g).mp h ⟨_, hid⟩)
  | some o =>
    have ho := soundness_thm g o h
    have heq : o = List.range (size g) := le_antisymm
      (minimal_thm g o h _ hid)
      (sorted_le_perm List.pairwise_le_range ho.2.1.symm)
    exact congrArg some heq

/-- The complete contract; validity is not strengthened to acyclicity. -/
def Post_prop (g : Value) : Prop :=
  soundness_prop g ∧ completeness_prop g ∧ malformed_prop g ∧
  vertices_prop g ∧ edges_prop g ∧ cycle_prop g ∧ first_prop g ∧
  minimal_prop g ∧ empty_prop g ∧ edgeless_prop g

/-! ## Exhaustive property-based tests

Every adjacency matrix on 0, 1, 2, or 3 vertices is included (531 graphs).
Additional inputs exercise duplicate edges, negative/out-of-range endpoints,
Boolean integers, and dynamic type errors. These are tests, not proof lemmas.
-/

def maskGraph (n mask : Nat) : Value :=
  graph ((List.range n).map fun u =>
    ((List.range n).filter fun v => (mask / 2 ^ (u * n + v)) % 2 == 1).map Int.ofNat)

def testGraphs : List Value :=
  ((List.range 4).flatMap fun n => (List.range (2 ^ (n * n))).map (maskGraph n)) ++
  [graph [[1, 1], []], graph [[], [0, 0]], graph [[1, 2], [3], [3], []],
   graph [[-1]], graph [[2]], graph [[1], [3]],
   .other "not a graph", .integer 0, .boolean false,
   .list [.list [.integer 1], .other "not a list"],
   .list [.list [.other "not an integer"]],
   .list [.list [.list []]], .list [.list [.boolean true], .list []],
   .list [.list [.boolean false]], .list [.list [.boolean true]]]

-- Executable form of soundness_prop.
def soundnessCheck (g : Value) : Bool :=
  match topological_sort g with
  | none => true
  | some o => is_topological_order g o

-- Executable form of completeness_prop, using the complete permutation universe.
def completenessCheck (g : Value) : Bool :=
  (topological_sort g == none) ==
    (!(permutations (size g)).any (is_topological_order g))

-- Executable form of malformed_prop.
def malformedCheck (g : Value) : Bool := pre g || (topological_sort g == none)

-- Executable form of vertices_prop (both inclusions, length, and no duplicates).
def verticesCheck (g : Value) : Bool :=
  match topological_sort g with
  | none => true
  | some o => decide o.Nodup && (o.length == size g) &&
      o.all (fun v => decide (v < size g)) && (List.range (size g)).all o.contains

-- Executable form of edges_prop.
def edgesCheck (g : Value) : Bool :=
  match topological_sort g with
  | none => true
  | some o => edgesOK g o

/-- Exact-length walks, explicitly restricted to the graph's vertex set. -/
def walkB (g : Value) : Nat → Nat → Nat → Bool
  | 0, u, v => u == v
  | k + 1, u, v => decide (u < size g) && (neighbors g u).any (fun w => walkB g k w v)

/-- A finite directed cycle has a closed subwalk of length between 1 and n. -/
def cycleB (g : Value) : Bool :=
  (List.range (size g)).any fun v =>
    (List.range (size g)).any fun k => walkB g (k + 1) v v

-- Executable form of cycle_prop via finite closed-walk enumeration.
def cycleCheck (g : Value) : Bool := !cycleB g || (topological_sort g == none)

-- Executable form of first_prop, inspecting the prefix before the returned order.
def firstCheck (g : Value) : Bool :=
  match topological_sort g with
  | none => true
  | some o => (permutations (size g)).contains o &&
      ((permutations (size g)).takeWhile (fun p => p != o)).all
        (fun p => !is_topological_order g p)

-- Executable form of minimal_prop in the lexicographic order used by Python.
def minimalCheck (g : Value) : Bool :=
  match topological_sort g with
  | none => true
  | some o => (permutations (size g)).all fun p =>
      !is_topological_order g p || decide (o ≤ p)

-- Executable form of empty_prop.
def emptyCheck (g : Value) : Bool :=
  !(pre g && (size g == 0)) || (topological_sort g == some [])

-- Executable form of edgeless_prop.
def edgelessCheck (g : Value) : Bool :=
  !(pre g && (List.range (size g)).all (fun u => (neighbors g u).isEmpty)) ||
    (topological_sort g == some (List.range (size g)))

-- Executable conjunction for Post_prop; tested on invalid inputs too.
def postCheck (g : Value) : Bool :=
  soundnessCheck g && completenessCheck g && malformedCheck g &&
  verticesCheck g && edgesCheck g && cycleCheck g && firstCheck g &&
  minimalCheck g && emptyCheck g && edgelessCheck g

example : testGraphs.all soundnessCheck = true := by native_decide
example : testGraphs.all completenessCheck = true := by native_decide
example : testGraphs.all malformedCheck = true := by native_decide
example : testGraphs.all verticesCheck = true := by native_decide
example : testGraphs.all edgesCheck = true := by native_decide
example : testGraphs.all cycleCheck = true := by native_decide
example : testGraphs.all firstCheck = true := by native_decide
example : testGraphs.all minimalCheck = true := by native_decide
example : testGraphs.all emptyCheck = true := by native_decide
example : testGraphs.all edgelessCheck = true := by native_decide
example : (List.range 8).all (fun n =>
    topological_sort (graph (List.replicate n [])) == some (List.range n)) = true := by native_decide
example : testGraphs.all postCheck = true := by native_decide
#eval (testGraphs.length, testGraphs.all postCheck)

/-- In fact each component was proved for all dynamic inputs, not just Pre. -/
theorem correctness_thm (g : Value) : Pre g → Post_prop g := by
  intro _
  exact ⟨soundness_thm g, completeness_thm g, malformed_thm g,
    vertices_thm g, edges_thm g, cycle_thm g, first_thm g, minimal_thm g, empty_thm g, edgeless_thm g⟩

/-! ## Imperative implementation

The mutable accumulator retains the first successful candidate. Subsequent
iterations do not replace it. The loop invariant below allows any initial state,
so its proof does not merely unfold a wrapper around the functional search.
-/

def searchImperative (test : List Nat → Bool) (xs : List (List Nat))
    (initial : Option (List Nat)) : Option (List Nat) := Id.run do
  let mut result := initial
  for x in xs do
    if result.isNone && test x then
      result := some x
  return result

def topological_sort_imperative (g : Value) : Option (List Nat) := Id.run do
  let mut result := none
  if pre g then
    result := searchImperative (is_topological_order g) (permutations (size g)) result
  return result

-- Imperative fixed tests and a bounded equivalence test over the entire suite.
example : topological_sort_imperative (graph [[1], [2], []]) = some [0, 1, 2] := by native_decide
example : topological_sort_imperative (graph [[1, 2], [3], [3], []]) = some [0, 1, 2, 3] := by native_decide
example : topological_sort_imperative (graph []) = some [] := by native_decide
example : topological_sort_imperative (graph [[], [], []]) = some [0, 1, 2] := by native_decide
example : topological_sort_imperative (graph [[2], [], []]) = some [0, 1, 2] := by native_decide
example : topological_sort_imperative (graph [[1], [0]]) = none := by native_decide
example : topological_sort_imperative (graph [[0]]) = none := by native_decide
example : topological_sort_imperative (graph [[2]]) = none := by native_decide
example : topological_sort_imperative (.list [.list [.integer 1], .other "not a list"]) = none := by native_decide
example : testGraphs.all (fun g => topological_sort g == topological_sort_imperative g) = true := by native_decide
#eval topological_sort_imperative (graph [[], [0]])

theorem searchImperative_eq (test : List Nat → Bool) (xs : List (List Nat))
    (initial : Option (List Nat)) :
    searchImperative test xs initial = initial.or (xs.find? test) := by
  induction xs generalizing initial with
  | nil => simp [searchImperative]
  | cons a xs ih =>
    cases initial with
    | none =>
      cases h : test a <;>
        simpa [searchImperative, List.forIn_cons, h, List.find?] using
          ih (if test a then some a else none)
    | some b =>
      simpa [searchImperative, List.forIn_cons, List.find?] using ih (some b)

/-- Unconditional extensional equivalence, including malformed and cyclic inputs. -/
theorem equivalence_thm (g : Value) :
    topological_sort g = topological_sort_imperative g := by
  cases h : pre g <;>
    simp [topological_sort, topological_sort_imperative, searchImperative_eq, h]

end topological_sort
