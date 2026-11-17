import Mathlib

/-!
# Topological sorting

Lean 4 formalization of a Python topological sort on finite directed graphs
given as adjacency lists. Vertices of a graph `g` are `0, …, g.length - 1`,
and `g[u]` is the list of outgoing neighbors of `u`.

The Python implementation searches `itertools.permutations(range(n))`, which
emits permutations in lexicographic order, and returns the first permutation
that is a topological order. If the adjacency list is malformed or the graph
has a directed cycle, it returns `None`.

In Lean the dynamic checks `isinstance(..., list)` are enforced by the type
`List (List Nat)`. The check that remains is that every neighbor lies in
`0, …, n - 1`. Out-of-range neighbors, including the Python test `[[2]]`,
are malformed. The Python test `[[1], "not a list"]` is not a value of
`List (List Nat)`; `topologicalSortOrMalformed` models that failure.
-/

namespace topological_sort

/-! ## Order instances used by lexicographic list comparison -/

instance : Std.Irrefl (· < · : Nat → Nat → Prop) where
  irrefl a := Nat.lt_irrefl a

instance : Std.Asymm (· < · : Nat → Nat → Prop) where
  asymm _ _ := Nat.lt_asymm

instance : Std.Total (¬ · < · : Nat → Nat → Prop) where
  total a b := by
    cases Nat.le_total a b with
    | inl h => exact Or.inr (Nat.not_lt.mpr h)
    | inr h => exact Or.inl (Nat.not_lt.mpr h)

instance : Trans (¬ · < · : Nat → Nat → Prop) (¬ · < ·) (¬ · < ·) where
  trans {a b c} (h1 : ¬ a < b) (h2 : ¬ b < c) : ¬ a < c := by
    exact Nat.not_lt.mpr (Nat.le_trans (Nat.not_lt.mp h2) (Nat.not_lt.mp h1))

/-! ## Validation and the lexicographic permutation list -/

/-- Python `pre`: every neighbor index lies in `0 .. n - 1`. -/
def pre (g : List (List Nat)) : Bool :=
  g.all fun ns => ns.all fun v => decide (v < g.length)

/-- Boolean lexicographic order on lists, equivalent to `decide (a ≤ b)`. -/
def leB (a b : List Nat) : Bool :=
  decide (a ≤ b)

/-- Nondecreasing order on `Nat`, used to match Python `sorted`. -/
def natLeB (a b : Nat) : Bool :=
  decide (a ≤ b)

/-- All permutations of `0 .. n - 1` in nondecreasing lexicographic order. -/
def lexPerms (n : Nat) : List (List Nat) :=
  ((List.range n).permutations').mergeSort leB

/-- Outgoing edges point forward in `order`. -/
def edgesBefore (g : List (List Nat)) (order : List Nat) : Bool :=
  (List.range g.length).all fun u =>
    (g[u]?.getD []).all fun v => decide (order.idxOf u < order.idxOf v)

/-- Python `is_topological_order`. -/
def isTopologicalOrder (g : List (List Nat)) (order : List Nat) : Bool :=
  pre g && order.isPerm (List.range g.length) && edgesBefore g order

/-- Python `topological_sort`. -/
def topologicalSort (g : List (List Nat)) : Option (List Nat) :=
  if pre g then (lexPerms g.length).find? (isTopologicalOrder g) else none

/-- Model of a Python adjacency list that may contain a non-list entry. -/
def topologicalSortOrMalformed (g : List (Option (List Nat))) : Option (List Nat) :=
  match g.mapM id with
  | none => none
  | some g => topologicalSort g

/-! ## Unit tests

The fixed examples are the Python `check` suite. `native_decide` is used only
on closed `example` goals.
-/

#eval topologicalSort [[1], [2], []]
#eval topologicalSort [[1, 2], [3], [3], []]
#eval topologicalSort ([] : List (List Nat))
#eval topologicalSort [[], [], []]
#eval topologicalSort [[2], [], []]
#eval topologicalSort [[1], [0]]
#eval topologicalSort [[0]]
#eval topologicalSort [[2]]
#eval topologicalSort [[], [0]]
#eval topologicalSort [[], [], [1]]
#eval topologicalSortOrMalformed [some [1], none]

example : topologicalSort [[1], [2], []] = some [0, 1, 2] := by native_decide

example : isTopologicalOrder [[1], [2], []] [0, 1, 2] = true := by native_decide

example : topologicalSort [[1, 2], [3], [3], []] = some [0, 1, 2, 3] := by native_decide

example :
    match topologicalSort [[1, 2], [3], [3], []] with
    | some order =>
        isTopologicalOrder [[1, 2], [3], [3], []] order &&
          order.mergeSort natLeB == [0, 1, 2, 3]
    | none => false
  := by native_decide

example : topologicalSort ([] : List (List Nat)) = some [] := by native_decide

example : topologicalSort [[], [], []] = some [0, 1, 2] := by native_decide

example :
    match topologicalSort [[2], [], []] with
    | some order =>
        isTopologicalOrder [[2], [], []] order && order.idxOf 0 < order.idxOf 2
    | none => false
  := by native_decide

example : topologicalSort [[1], [0]] = none := by native_decide

example : topologicalSort [[0]] = none := by native_decide

example : topologicalSort [[2]] = none := by native_decide

example : topologicalSortOrMalformed [some [1], none] = none := by native_decide

example : topologicalSort [[], [0]] = some [1, 0] := by native_decide

example : topologicalSort [[], [], [1]] = some [0, 2, 1] := by native_decide

example : topologicalSort [[1, 1], []] = some [0, 1] := by native_decide

/-! ## Specification -/

/-- Adjacency list over vertices `0 .. n - 1`. -/
def Pre (g : List (List Nat)) : Prop :=
  ∀ ns, ns ∈ g → ∀ v, v ∈ ns → v < g.length

/-- A directed edge `u → v`. -/
structure HasEdge (g : List (List Nat)) (u v : Nat) : Prop where
  src : u < g.length
  mem : v ∈ g[u]

/-- A directed walk of positive length. -/
inductive Reach (g : List (List Nat)) : Nat → Nat → Prop
  | edge {u v : Nat} : HasEdge g u v → Reach g u v
  | cons {u v w : Nat} : HasEdge g u v → Reach g v w → Reach g u w

/-- The graph has a directed closed walk of positive length. -/
def HasCycle (g : List (List Nat)) : Prop :=
  ∃ u, Reach g u u

/-- `order` is a topological ordering of a valid adjacency list. -/
structure IsTopologicalOrder (g : List (List Nat)) (order : List Nat) : Prop where
  pre : Pre g
  perm : order ~ List.range g.length
  edges : ∀ u, (hu : u < g.length) → ∀ v, v ∈ g[u] → order.idxOf u < order.idxOf v

/-! ## Checker and permutation lemmas -/

theorem pre_iff (g : List (List Nat)) : pre g = true ↔ Pre g := by
  simp [pre, Pre, List.all_eq_true, decide_eq_true_eq]

theorem getD_getElem {g : List (List Nat)} {u : Nat} (hu : u < g.length) :
    g[u]?.getD [] = g[u] := by
  simp [List.getElem?_eq_getElem hu]

theorem edgesBefore_iff (g : List (List Nat)) (order : List Nat) :
    edgesBefore g order = true ↔
      ∀ u, (hu : u < g.length) → ∀ v, v ∈ g[u] → order.idxOf u < order.idxOf v := by
  constructor
  · intro h u hu v hv
    have hall := (List.all_eq_true.mp h) u (by simpa [List.mem_range] using hu)
    rw [getD_getElem hu, List.all_eq_true, decide_eq_true_eq] at hall
    exact hall v hv
  · intro h
    rw [List.all_eq_true]
    intro u hu
    rw [List.mem_range] at hu
    rw [getD_getElem hu, List.all_eq_true, decide_eq_true_eq]
    exact h u hu

theorem isTopologicalOrder_iff (g : List (List Nat)) (order : List Nat) :
    isTopologicalOrder g order = true ↔ IsTopologicalOrder g order := by
  simp only [isTopologicalOrder, Bool.and_eq_true, pre_iff, List.isPerm_iff, edgesBefore_iff]
  constructor
  · rintro ⟨hp, hperm, hedges⟩
    exact ⟨hp, hperm, hedges⟩
  · rintro ⟨hp, hperm, hedges⟩
    exact ⟨hp, hperm, hedges⟩

theorem leB_trans (a b c : List Nat) (hab : leB a b = true) (hbc : leB b c = true) :
    leB a c = true := by
  simp only [leB, decide_eq_true_eq] at *
  exact List.le_trans hab hbc

theorem leB_total (a b : List Nat) : (leB a b || leB b a) = true := by
  simp only [leB]
  cases List.le_total a b with
  | inl h => simp [h]
  | inr h => simp [h]

theorem lexPerms_pairwise (n : Nat) : (lexPerms n).Pairwise (fun a b => a ≤ b) := by
  have htrans : ∀ a b c : List Nat, leB a b → leB b c → leB a c := by
    intro a b c hab hbc
    exact leB_trans a b c hab hbc
  have htotal : ∀ a b : List Nat, leB a b || leB b a := by
    intro a b
    exact leB_total a b
  have hs := List.sorted_mergeSort htrans htotal (List.range n).permutations'
  simpa [lexPerms, leB, decide_eq_true_eq] using hs

theorem mem_lexPerms {n : Nat} {p : List Nat} :
    p ∈ lexPerms n ↔ p ~ List.range n := by
  simp [lexPerms, List.mem_mergeSort, List.mem_permutations']

theorem natLeB_trans (a b c : Nat) (hab : natLeB a b = true) (hbc : natLeB b c = true) :
    natLeB a c = true := by
  simp only [natLeB, decide_eq_true_eq] at *
  exact Nat.le_trans hab hbc

theorem natLeB_total (a b : Nat) : (natLeB a b || natLeB b a) = true := by
  simp only [natLeB]
  cases Nat.le_total a b with
  | inl h => simp [h]
  | inr h => simp [h]

theorem eq_of_pairwise_lt_mem {l₁ l₂ : List Nat}
    (h₁ : l₁.Pairwise (· < ·)) (h₂ : l₂.Pairwise (· < ·))
    (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons b _ =>
      have : b ∈ ([] : List Nat) := (hmem b).2 (by simp)
      simp at this
  | cons a l₁ ih =>
    cases l₂ with
    | nil =>
      have : a ∈ ([] : List Nat) := (hmem a).1 (by simp)
      simp at this
    | cons b l₂ =>
      have ha : a ∈ b :: l₂ := (hmem a).1 (by simp)
      have hb : b ∈ a :: l₁ := (hmem b).2 (by simp)
      have hmin₁ := List.rel_of_pairwise_cons h₁
      have hmin₂ := List.rel_of_pairwise_cons h₂
      cases List.mem_cons.1 ha with
      | inl heq =>
        subst heq
        congr 1
        apply ih (List.Pairwise.of_cons h₁) (List.Pairwise.of_cons h₂)
        intro x
        constructor
        · intro hx
          have hx' : x ∈ a :: l₂ := (hmem x).1 (List.mem_cons_of_mem _ hx)
          cases List.mem_cons.1 hx' with
          | inl hxa =>
            exact absurd (hmin₁ x hx) (by simp [hxa, Nat.lt_irrefl])
          | inr hx₂ => exact hx₂
        · intro hx
          have hx' : x ∈ a :: l₁ := (hmem x).2 (List.mem_cons_of_mem _ hx)
          cases List.mem_cons.1 hx' with
          | inl hxa =>
            exact absurd (hmin₂ x hx) (by simp [hxa, Nat.lt_irrefl])
          | inr hx₁ => exact hx₁
      | inr ha₂ =>
        cases List.mem_cons.1 hb with
        | inl heq =>
          subst heq
          exact absurd (hmin₂ a ha₂) (Nat.lt_irrefl _)
        | inr hb₂ =>
          exact Nat.lt_asymm (hmin₂ a ha₂) (hmin₁ b hb₂)

theorem eq_of_pairwise_lt_perm {l₁ l₂ : List Nat}
    (h₁ : l₁.Pairwise (· < ·)) (h₂ : l₂.Pairwise (· < ·)) (hp : l₁ ~ l₂) : l₁ = l₂ :=
  eq_of_pairwise_lt_mem h₁ h₂ (fun x => hp.mem_iff)

theorem pairwise_le_nodup_lt {l : List Nat}
    (hs : l.Pairwise (fun a b => natLeB a b = true)) (hd : l.Nodup) :
    l.Pairwise (· < ·) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.pairwise_cons] at hs
    rw [List.nodup_cons] at hd
    constructor
    · intro b hb
      have hle : a ≤ b := by simpa [natLeB, decide_eq_true_eq] using hs.1 b hb
      have hne : a ≠ b := by
        intro eq
        exact hd.1 (eq ▸ hb)
      exact Nat.lt_of_le_of_ne hle hne
    · exact ih hs.2 hd.2

theorem mergeSort_nat_pairwise (l : List Nat) :
    (l.mergeSort natLeB).Pairwise (fun a b => natLeB a b = true) := by
  have htrans : ∀ a b c : Nat, natLeB a b → natLeB b c → natLeB a c := by
    intro a b c hab hbc
    exact natLeB_trans a b c hab hbc
  have htotal : ∀ a b : Nat, natLeB a b || natLeB b a := by
    intro a b
    exact natLeB_total a b
  simpa [natLeB] using List.sorted_mergeSort htrans htotal l

theorem mergeSort_eq_range {order : List Nat} {n : Nat} (hp : order ~ List.range n) :
    order.mergeSort natLeB = List.range n := by
  have hperm : order.mergeSort natLeB ~ List.range n :=
    (List.mergeSort_perm order natLeB).trans hp
  have hnodup : (order.mergeSort natLeB).Nodup :=
    (hperm.nodup_iff).mpr List.nodup_range
  have hlt : (order.mergeSort natLeB).Pairwise (· < ·) :=
    pairwise_le_nodup_lt (mergeSort_nat_pairwise order) hnodup
  exact eq_of_pairwise_lt_perm hlt List.pairwise_lt_range hperm

/-- Python checks `sorted(order) == list(range(n))`, which is `isPerm`. -/
theorem isPerm_eq_sorted (order : List Nat) (n : Nat) :
    order.isPerm (List.range n) = (order.mergeSort natLeB == List.range n) := by
  cases h1 : order.isPerm (List.range n) <;> cases h2 : order.mergeSort natLeB == List.range n
  · rfl
  · simp only [beq_iff_eq] at h2
    have hp : order ~ List.range n := by
      have hperm := (List.mergeSort_perm order natLeB).symm
      simpa [h2] using hperm
    have := List.isPerm_iff.mpr hp
    simp [h1] at this
  · have hp : order ~ List.range n := List.isPerm_iff.mp (by simp [h1])
    have heq := mergeSort_eq_range hp
    simp [beq_iff_eq, heq] at h2
  · rfl

theorem find?_le_mem {l : List (List Nat)} {p : List Nat → Bool} {a : List Nat}
    (hs : l.Pairwise (fun x y => x ≤ y)) (hf : l.find? p = some a) :
    ∀ b, b ∈ l → p b = true → a ≤ b := by
  rw [List.find?_eq_some_iff_append] at hf
  rcases hf with ⟨_, as, bs, rfl, hall⟩
  intro b hb hpb
  have hpair : (as ++ a :: bs).Pairwise (fun x y => x ≤ y) := hs
  simp only [List.mem_append, List.mem_cons] at hb
  rcases hb with hbas | rfl | hbbs
  · have hnot : (!p b) = true := hall b hbas
    have : p b = false := by
      cases hp : p b <;> simp [hp, Bool.not_true, Bool.not_false] at hnot
    simp [hpb] at this
  · exact List.le_refl a
  · have hrel : ∀ x ∈ bs, a ≤ x := by
      induction as generalizing a bs with
      | nil =>
        simpa using List.rel_of_pairwise_cons hpair
      | cons y ys ih =>
        exact ih (List.Pairwise.of_cons hpair)
    exact hrel b hbbs

/-! ## Lexicographically least permutation of a range -/

theorem permutations'Aux_ne_nil (a : Nat) (l : List Nat) :
    List.permutations'Aux a l ≠ [] := by
  induction l <;> simp [List.permutations'Aux]

theorem permutations'_ne_nil : ∀ l : List Nat, l.permutations' ≠ []
  | [] => by simp [List.permutations']
  | a :: l => by
    intro h
    rw [List.permutations'] at h
    have hflat := List.flatMap_eq_nil_iff.mp h
    have hne : l.permutations' ≠ [] := permutations'_ne_nil l
    cases hp : l.permutations' with
    | nil => exact hne hp
    | cons p ps =>
      have hnil := hflat p (by simp [hp])
      exact permutations'Aux_ne_nil a p hnil

theorem lexPerms_ne_nil (n : Nat) : lexPerms n ≠ [] := by
  intro h
  have hlen := congrArg List.length h
  simp only [lexPerms, List.length_mergeSort, List.length_nil] at hlen
  exact permutations'_ne_nil (List.range n) (List.eq_nil_of_length_eq_zero hlen)

theorem range'_le_of_perm {start len : Nat} {p : List Nat}
    (hp : p ~ List.range' start len) : List.range' start len ≤ p := by
  induction len generalizing start p with
  | zero =>
    simp at hp
    subst hp
    exact List.le_refl _
  | succ len ih =>
    have hform : List.range' start (len + 1) = start :: List.range' (start + 1) len := by
      simp [List.range'_succ]
    rw [hform] at hp ⊢
    have hnodup : p.Nodup := (hp.nodup_iff).mpr (by simpa [hform] using (List.nodup_range' (s := start) (n := len + 1)))
    have hmem : start ∈ p := hp.mem_iff.mp (by simp)
    obtain ⟨as, bs, rfl⟩ := List.append_of_mem hmem
    have hsplit := (List.nodup_append.mp hnodup)
    have hstart_not_as : start ∉ as := by
      intro hin
      have hdis := hsplit.2.2 start hin start (by simp)
      exact hdis rfl
    have hstart_not_bs : start ∉ bs := by
      have hcons := (List.nodup_cons.mp hsplit.2.1)
      exact hcons.1
    cases as with
    | nil =>
      simp only [List.nil_append] at hp ⊢
      have htail : bs ~ List.range' (start + 1) len := (List.perm_cons start).mp hp
      have hle : List.range' (start + 1) len ≤ bs := ih htail
      rw [List.cons_le_cons_iff]
      exact Or.inr ⟨rfl, hle⟩
    | cons x xs =>
      have hxne : x ≠ start := by
        intro hxs
        exact hstart_not_as (by simp [hxs])
      have hxmem : x ∈ List.range' start (len + 1) := by
        have : x ∈ x :: xs ++ start :: bs := by simp
        exact hp.mem_iff.mpr this
      have hxge : start ≤ x := by
        have := (List.mem_range'.mp hxmem)
        simpa using this.1
      have hxlt : start < x := Nat.lt_of_le_of_ne hxge (Ne.symm hxne)
      have hlt : (start :: List.range' (start + 1) len) < (x :: xs ++ start :: bs) := by
        rw [List.cons_append]
        exact List.Lex.rel hxlt
      exact List.le_of_lt hlt

theorem range_le_of_perm {n : Nat} {p : List Nat} (hp : p ~ List.range n) :
    List.range n ≤ p := by
  simpa [List.range_eq_range'] using range'_le_of_perm (by simpa [List.range_eq_range'] using hp)

theorem lexPerms_head_eq_range (n : Nat) :
    lexPerms n = List.range n :: (lexPerms n).tail := by
  have hne := lexPerms_ne_nil n
  cases hlex : lexPerms n with
  | nil => exact absurd hlex hne
  | cons a t =>
    have ha_mem : a ∈ lexPerms n := by simp [hlex]
    have ha_perm : a ~ List.range n := mem_lexPerms.mp ha_mem
    have hle_range : a ≤ List.range n := by
      have hmemr : List.range n ∈ lexPerms n := mem_lexPerms.mpr (List.Perm.refl _)
      rw [hlex] at hmemr
      cases List.mem_cons.1 hmemr with
      | inl h =>
        simpa [h] using List.le_refl a
      | inr h =>
        have hsort := lexPerms_pairwise n
        rw [hlex] at hsort
        exact List.rel_of_pairwise_cons hsort h
    have hge_range : List.range n ≤ a := range_le_of_perm ha_perm
    have heq : a = List.range n := List.le_antisymm hle_range hge_range
    simp [hlex, heq, List.tail_cons]

/-! ## Reachability and cycles -/

theorem idx_lt_of_hasEdge {g : List (List Nat)} {order u v : Nat}
    (hT : IsTopologicalOrder g order) (hE : HasEdge g u v) :
    order.idxOf u < order.idxOf v :=
  hT.edges u hE.src v hE.mem

theorem idx_lt_of_reach {g : List (List Nat)} {order u v : Nat}
    (hT : IsTopologicalOrder g order) (hR : Reach g u v) :
    order.idxOf u < order.idxOf v := by
  induction hR with
  | edge e => exact idx_lt_of_hasEdge hT e
  | cons e _ ih => exact Nat.lt_trans (idx_lt_of_hasEdge hT e) ih

theorem no_cycle_of_topo {g : List (List Nat)} {order : List Nat}
    (hT : IsTopologicalOrder g order) : ¬ HasCycle g := by
  intro hC
  rcases hC with ⟨u, hR⟩
  have hlt := idx_lt_of_reach hT hR
  exact Nat.lt_irrefl _ hlt
