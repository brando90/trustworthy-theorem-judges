import Mathlib

/-!+# Exhaustive topological sorting

Translation of the Python adjacency-list program. `PyValue` retains malformed
outer values, malformed rows, noninteger neighbors, and negative integers.
Python Booleans are integers for `isinstance(v, int)`, so they decode as 0/1.
`other` represents any Python object that is neither a list nor an integer.
Integer values are unbounded; accepted vertices and returned positions use `Nat`.

The candidates are the permutations of `range n`, sorted lexicographically to
match `itertools.permutations(range(n))`. The checker tests both the permutation
condition and every directed edge. Duplicate edges are permitted.
-/

namespace topological_sort

inductive PyValue where
  | int : Int → PyValue
  | bool : Bool → PyValue
  | list : List PyValue → PyValue
  | other : String → PyValue
  deriving Repr

abbrev Graph := List (List Nat)

def ofGraph (g : List (List Int)) : PyValue :=
  .list (g.map fun row => .list (row.map PyValue.int))

def integer? : PyValue → Option Int
  | .int z => some z
  | .bool b => some (if b then 1 else 0)
  | _ => none

/-- Validation and normalization, including the runtime list checks. -/
def decodeGraph : PyValue → Option Graph
  | .list rows => rows.mapM fun row =>
      match row with
      | .list ns => ns.mapM fun value => do
          let z ← integer? value
          if 0 ≤ z ∧ z < (rows.length : Int) then
            some z.toNat
          else none
      | _ => none
  | _ => none

def pre (input : PyValue) : Bool := (decodeGraph input).isSome

def candidates (n : Nat) : List (List Nat) :=
  (List.range n).permutations.mergeSort (fun a b => decide (a ≤ b))

def edgesOK (g : Graph) (order : List Nat) : Bool :=
  (List.range g.length).all fun u =>
    (g[u]?.getD []).all fun v => decide (order.idxOf u < order.idxOf v)

def checkOrder (g : Graph) (order : List Nat) : Bool :=
  decide (order.Perm (List.range g.length)) && edgesOK g order

def is_topological_order (input : PyValue) (order : List Nat) : Bool :=
  match decodeGraph input with
  | none => false
  | some g => checkOrder g order

set_option linter.dupNamespace false in
def topological_sort (input : PyValue) : Option (List Nat) :=
  match decodeGraph input with
  | none => none
  | some g => (candidates g.length).find? (checkOrder g)

-- Unit tests: the examples from the Python check, and additional corner cases.
example : topological_sort (ofGraph [[1], [2], []]) = some [0, 1, 2] := by native_decide
example : is_topological_order (ofGraph [[1], [2], []]) [0, 1, 2] = true := by native_decide
example : topological_sort (ofGraph [[1, 2], [3], [3], []]) = some [0, 1, 2, 3] := by
  native_decide
example : topological_sort (ofGraph []) = some [] := by native_decide
example : topological_sort (ofGraph [[], [], []]) = some [0, 1, 2] := by native_decide
example : topological_sort (ofGraph [[2], [], []]) = some [0, 1, 2] := by native_decide
example : topological_sort (ofGraph [[1], [0]]) = none := by native_decide
example : topological_sort (ofGraph [[0]]) = none := by native_decide
example : topological_sort (ofGraph [[2]]) = none := by native_decide
example : topological_sort (.list [.list [.int 1], .other "not a list"]) = none := by
  native_decide
example : topological_sort (ofGraph [[-1]]) = none := by native_decide
example : topological_sort (.other "not an outer list") = none := by native_decide
example : topological_sort (.list [.list [.other "not an integer"]]) = none := by
  native_decide
example : topological_sort (ofGraph [[], [], [0]]) = some [1, 2, 0] := by native_decide
example : topological_sort (ofGraph [[1, 1], []]) = some [0, 1] := by native_decide
example : topological_sort (.list [.list [.bool true], .list []]) = some [0, 1] := by
  native_decide
example : is_topological_order (ofGraph [[], []]) [0, 0] = false := by native_decide
example : is_topological_order (ofGraph [[1], []]) [1, 0] = false := by native_decide

#eval topological_sort (ofGraph [[1, 2], [3], [3], []])
#eval topological_sort (ofGraph [[1], [0]])
#eval topological_sort (ofGraph [])

/-- Exactly Python's validation requirement, with no acyclicity assumption. -/
def Pre (input : PyValue) : Prop := pre input = true

/-- Mathematical meaning of an order on a normalized graph. -/
def GraphOrder (g : Graph) (order : List Nat) : Prop :=
  order.Perm (List.range g.length) ∧
    ∀ u ∈ List.range g.length, ∀ v ∈ g[u]?.getD [],
      order.idxOf u < order.idxOf v

/-- Malformed inputs have no valid topological order. -/
def ValidOrder (input : PyValue) (order : List Nat) : Prop :=
  ∃ g, decodeGraph input = some g ∧ GraphOrder g order

theorem checkOrder_iff (g : Graph) (order : List Nat) :
    checkOrder g order = true ↔ GraphOrder g order := by
  simp [checkOrder, edgesOK, GraphOrder, List.all_eq_true]

theorem checker_iff (input : PyValue) (order : List Nat) :
    is_topological_order input order = true ↔ ValidOrder input order := by
  cases h : decodeGraph input <;>
    simp [is_topological_order, ValidOrder, h, checkOrder_iff]

theorem mem_candidates (n : Nat) (order : List Nat) :
    order ∈ candidates n ↔ order.Perm (List.range n) := by
  rw [candidates, (List.mergeSort_perm _ _).mem_iff, List.mem_permutations]

def soundness_prop (input : PyValue) (result : Option (List Nat)) : Prop :=
  ∀ order, result = some order → ValidOrder input order

theorem soundness_thm (input : PyValue) :
    soundness_prop input (topological_sort input) := by
  intro order h
  cases hd : decodeGraph input with
  | none => simp [topological_sort, hd] at h
  | some g =>
      simp only [topological_sort, hd] at h
      exact ⟨g, hd, (checkOrder_iff g order).mp (List.find?_some h)⟩

/-- Every vertex occurs exactly once, also for disconnected graphs. -/
def vertices_prop (input : PyValue) (result : Option (List Nat)) : Prop :=
  ∀ order g, result = some order → decodeGraph input = some g →
    order.Nodup ∧ (∀ v, v ∈ order ↔ v < g.length) ∧ order.length = g.length

theorem vertices_thm (input : PyValue) :
    vertices_prop input (topological_sort input) := by
  intro order g h hd
  obtain ⟨g', hd', hp, _⟩ := soundness_thm input order h
  have hg : g' = g := Option.some.inj (hd'.symm.trans hd)
  subst g'
  exact ⟨hp.nodup_iff.mpr List.nodup_range,
    fun v => hp.mem_iff.trans List.mem_range, by simpa using hp.length_eq⟩

/-- Failure occurs exactly when no topological order exists. -/
def completeness_prop (input : PyValue) (result : Option (List Nat)) : Prop :=
  result = none ↔ ¬ ∃ order, ValidOrder input order

theorem completeness_thm (input : PyValue) :
    completeness_prop input (topological_sort input) := by
  unfold completeness_prop
  constructor
  · intro hn ⟨order, g, hd, ho⟩
    have hf : (candidates g.length).find? (checkOrder g) = none := by
      simpa [topological_sort, hd] using hn
    exact (List.find?_eq_none.mp hf order ((mem_candidates _ _).mpr ho.1))
      ((checkOrder_iff _ _).mpr ho)
  · intro h
    cases hr : topological_sort input with
    | none => rfl
    | some order => exact False.elim (h ⟨order, soundness_thm input order hr⟩)

/-- The first Python permutation is the lexicographically least valid order. -/
def first_order_prop (input : PyValue) (result : Option (List Nat)) : Prop :=
  ∀ order, result = some order → ∀ other, ValidOrder input other → order ≤ other

private theorem find?_least {xs : List (List Nat)} {p : List Nat → Bool}
    (hs : xs.Pairwise (· ≤ ·)) {order : List Nat}
    (hf : xs.find? p = some order) :
    ∀ other ∈ xs, p other = true → order ≤ other := by
  induction xs with
  | nil => simp at hf
  | cons a xs ih =>
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
      by_cases ha : p a = true
      · have heq : a = order := by simpa [ha] using hf
        subst a
        intro other hm _
        rcases List.mem_cons.mp hm with heq | hm
        · exact le_of_eq heq.symm
        · exact hhead other hm
      · have hf' : xs.find? p = some order := by simpa [ha] using hf
        intro other hm hp
        rcases List.mem_cons.mp hm with heq | hm
        · subst other; exact False.elim (ha hp)
        · exact ih htail hf' other hm hp

theorem first_order_thm (input : PyValue) :
    first_order_prop input (topological_sort input) := by
  intro order hf other ho
  obtain ⟨g, hd, hg⟩ := ho
  have hs : (candidates g.length).Pairwise (· ≤ ·) :=
    List.sorted_mergeSort' (· ≤ ·) _
  apply find?_least hs (by simpa [topological_sort, hd] using hf) other
  · exact (mem_candidates _ _).mpr hg.1
  · exact (checkOrder_iff _ _).mpr hg

def malformed_prop (input : PyValue) (result : Option (List Nat)) : Prop :=
  ¬ Pre input → result = none

theorem malformed_thm (input : PyValue) :
    malformed_prop input (topological_sort input) := by
  intro h
  cases hd : decodeGraph input with
  | none => simp [topological_sort, hd]
  | some g => exact False.elim (h (by simp [Pre, pre, hd]))

def empty_prop (input : PyValue) (result : Option (List Nat)) : Prop :=
  input = .list [] → result = some []

theorem empty_thm (input : PyValue) : empty_prop input (topological_sort input) := by
  rintro rfl
  native_decide

/-- A finite directed walk, with its final endpoint checked explicitly. -/
def walk (g : Graph) (u : Nat) : List Nat → Nat → Bool
  | [], target => u == target
  | v :: vs, target =>
      decide (u < g.length ∧ v ∈ g[u]?.getD []) && walk g v vs target

/-- Every nonempty closed directed walk forces failure; includes self-loops. -/
def cycles_prop (input : PyValue) (result : Option (List Nat)) : Prop :=
  ∀ g u vs, decodeGraph input = some g → vs ≠ [] →
    walk g u vs u = true → result = none

private theorem walk_increases {g : Graph} {order : List Nat} (ho : GraphOrder g order)
    (vs : List Nat) (u target : Nat) (hw : walk g u vs target = true) :
    (vs = [] ∧ u = target) ∨ order.idxOf u < order.idxOf target := by
  induction vs generalizing u with
  | nil => exact Or.inl ⟨rfl, by simpa [walk] using hw⟩
  | cons v vs ih =>
      simp only [walk, Bool.and_eq_true, decide_eq_true_eq] at hw
      obtain ⟨⟨hu, hv⟩, hw⟩ := hw
      have huv := ho.2 u (List.mem_range.mpr hu) v hv
      rcases ih v hw with ⟨_, rfl⟩ | hvt
      · exact Or.inr huv
      · exact Or.inr (lt_trans huv hvt)

theorem cycles_thm (input : PyValue) : cycles_prop input (topological_sort input) := by
  intro g u vs hd hn hw
  apply (completeness_thm input).mpr
  rintro ⟨order, g', hd', ho⟩
  have hg : g' = g := Option.some.inj (hd'.symm.trans hd)
  subst g'
  rcases walk_increases ho vs u u hw with ⟨he, _⟩ | hlt
  · exact hn he
  · exact (lt_irrefl _ hlt)

def Post_prop (input : PyValue) (result : Option (List Nat)) : Prop :=
  soundness_prop input result ∧ vertices_prop input result ∧
  completeness_prop input result ∧ first_order_prop input result ∧
  malformed_prop input result ∧ empty_prop input result ∧ cycles_prop input result

/-! Bounded property-based tests. All 531 directed simple graphs on at most
three vertices are enumerated, including self-loops. Extra inputs exercise
duplicate edges, Boolean vertices, and each kind of malformed input.
Every check below is an executable counterpart of the named proposition.
These tests do not serve as proofs of the universally quantified theorems. -/

def graphFromMask (n mask : Nat) : PyValue :=
  ofGraph ((List.range n).map fun u =>
    ((List.range n).filter fun v => (mask / 2 ^ (u * n + v)) % 2 == 1).map Int.ofNat)

def smallGraphs : List PyValue :=
  (List.range 4).flatMap fun n => (List.range (2 ^ (n * n))).map (graphFromMask n)

def testInputs : List PyValue := smallGraphs ++
  [.other "not a graph", .int 0, .bool false,
   .list [.other "not a row"], .list [.int 1],
   .list [.list [.other "not a vertex"]], .list [.list [.list []]],
   .list [.list [.int 1], .other "not a list"],
   ofGraph [[-1]], ofGraph [[2]], ofGraph [[1], [2]],
   ofGraph [[1, 1], []], ofGraph [[1, 1], [0]],
   .list [.list [.bool true], .list []],
   .list [.list [.bool false]], .list [.list [.bool true]],
   ofGraph [[1, 2], [3], [3], []], ofGraph [[], [], [], []]]

def soundnessCheck (input : PyValue) (result : Option (List Nat)) : Bool :=
  match result with
  | none => true
  | some order => is_topological_order input order

def verticesCheck (input : PyValue) (result : Option (List Nat)) : Bool :=
  match result, decodeGraph input with
  | some order, some g =>
      decide order.Nodup && (order.length == g.length) &&
        order.all (fun v => decide (v < g.length)) &&
        (List.range g.length).all (fun v => order.contains v)
  | _, _ => true

def completenessCheck (input : PyValue) (result : Option (List Nat)) : Bool :=
  let existsOrder := match decodeGraph input with
    | none => false
    | some g => (List.range g.length).permutations.any (checkOrder g)
  result.isNone == !existsOrder

def firstOrderCheck (input : PyValue) (result : Option (List Nat)) : Bool :=
  match result, decodeGraph input with
  | some order, some g => (List.range g.length).permutations.all fun other =>
      !checkOrder g other || decide (order ≤ other)
  | _, _ => true

def malformedCheck (input : PyValue) (result : Option (List Nat)) : Bool :=
  pre input || result.isNone

def emptyCheck (input : PyValue) (result : Option (List Nat)) : Bool :=
  match input with
  | .list [] => result == some []
  | _ => true

/-- All vertex sequences of a fixed length, for bounded cycle witnesses. -/
def words (n : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | k + 1 => (List.range n).flatMap fun v => (words n k).map (v :: ·)

def cyclesCheck (input : PyValue) (result : Option (List Nat)) : Bool :=
  match decodeGraph input with
  | none => true
  | some g => (List.range g.length).all fun u =>
      ((List.range g.length).flatMap fun k => words g.length (k + 1)).all fun vs =>
        !walk g u vs u || result.isNone

def postCheck (input : PyValue) (result : Option (List Nat)) : Bool :=
  soundnessCheck input result && verticesCheck input result &&
  completenessCheck input result && firstOrderCheck input result &&
  malformedCheck input result && emptyCheck input result && cyclesCheck input result

-- PBT for soundness_prop.
example : testInputs.all (fun g => soundnessCheck g (topological_sort g)) = true := by
  native_decide
-- PBT for vertices_prop: uniqueness, membership in both directions, and length.
example : testInputs.all (fun g => verticesCheck g (topological_sort g)) = true := by
  native_decide
-- PBT for completeness_prop, searching the unsorted permutations independently.
example : testInputs.all (fun g => completenessCheck g (topological_sort g)) = true := by
  native_decide
-- PBT for first_order_prop: compare against every valid permutation.
example : testInputs.all (fun g => firstOrderCheck g (topological_sort g)) = true := by
  native_decide
-- PBT for malformed_prop, including runtime type errors and invalid integers.
example : testInputs.all (fun g => malformedCheck g (topological_sort g)) = true := by
  native_decide
-- PBT for empty_prop (the empty input is included in this generated family).
example : testInputs.all (fun g => emptyCheck g (topological_sort g)) = true := by
  native_decide
-- PBT for cycles_prop: all closed walks of lengths 1 through n in each graph.
-- The theorem above quantifies over walks of arbitrary length.
example : testInputs.all (fun g => cyclesCheck g (topological_sort g)) = true := by
  native_decide
-- PBT for the complete Post_prop, including inputs that fail Pre.
example : testInputs.all (fun g => postCheck g (topological_sort g)) = true := by
  native_decide

#eval (smallGraphs.length, testInputs.all fun g => postCheck g (topological_sort g))

-- A randomized PBT of Post_prop supplements the exhaustive family with graphs
-- on up to four vertices. Modulo bounds keep the factorial search affordable.
#eval Plausible.Testable.check (∀ n mask : Nat,
  postCheck (graphFromMask (n % 5) mask)
    (topological_sort (graphFromMask (n % 5) mask)) = true)

theorem correctness (input : PyValue) (_h : Pre input) :
    Post_prop input (topological_sort input) := by
  exact ⟨soundness_thm input, vertices_thm input, completeness_thm input,
    first_order_thm input, malformed_thm input, empty_thm input, cycles_thm input⟩

/-- An imperative scan with mutable state. Once set, the first answer is kept. -/
def scanImperative (p : List Nat → Bool) (xs : List (List Nat))
    (initial : Option (List Nat) := none) : Option (List Nat) := Id.run do
  let mut result := initial
  for order in xs do
    if result.isNone && p order then
      result := some order
  return result

def topological_sort_imperative (input : PyValue) : Option (List Nat) := Id.run do
  let mut result : Option (List Nat) := none
  match decodeGraph input with
  | none => return none
  | some g =>
      for order in candidates g.length do
        if result.isNone && checkOrder g order then
          result := some order
      return result

example : topological_sort_imperative (ofGraph [[1], [2], []]) = some [0, 1, 2] := by
  native_decide
example : topological_sort_imperative (ofGraph []) = some [] := by native_decide
example : topological_sort_imperative (ofGraph [[], [], [0]]) = some [1, 2, 0] := by
  native_decide
example : topological_sort_imperative (ofGraph [[1], [0]]) = none := by native_decide
example : topological_sort_imperative (.list [.list [.int 1], .other "not a list"]) = none := by
  native_decide
example : testInputs.all (fun g => postCheck g (topological_sort_imperative g)) = true := by
  native_decide
example : testInputs.all (fun g => topological_sort g == topological_sort_imperative g) =
    true := by native_decide

#eval topological_sort_imperative (ofGraph [[1, 2], [3], [3], []])

private theorem scanImperative_eq (p : List Nat → Bool) (xs : List (List Nat))
    (initial : Option (List Nat)) :
    scanImperative p xs initial = initial.or (xs.find? p) := by
  induction xs generalizing initial with
  | nil => simp [scanImperative, List.forIn_nil]
  | cons a xs ih =>
      simp only [scanImperative, List.forIn_cons] at *
      cases initial with
      | none =>
          by_cases ha : p a = true <;> simp_all
      | some order => simp_all

theorem functional_eq_imperative (input : PyValue) :
    topological_sort input = topological_sort_imperative input := by
  cases hd : decodeGraph input with
  | none => simp [topological_sort, topological_sort_imperative, hd]
  | some g =>
      simp only [topological_sort, hd]
      have hi : topological_sort_imperative input =
          scanImperative (checkOrder g) (candidates g.length) none := by
        simp [topological_sort_imperative, scanImperative, hd]
      rw [hi, scanImperative_eq]
      rfl

end topological_sort
