import Mathlib
namespace Agent

/-!
# Quick-find union-find

A translation of the Python component-label implementation. Python integers are
modelled by `Int`; the static types `List Int` and `Int` discharge Python's dynamic
type checks. Negative sizes create an empty list. Negative and out-of-range
indices return `none`, and invalid unions return the original list. Lists are
immutable values, so returning the same value implements Python's fresh copy.
The specifications include arbitrary (possibly ill-formed) integer label lists;
only preservation of the label invariant needs the invariant as a hypothesis.
-/

namespace union_find

abbrev Labels := List Int

def make_set (n : Int) : Labels := (List.range n.toNat).map Int.ofNat

def pre (labels : Labels) : Bool :=
  labels.all (fun r => decide (0 ≤ r ∧ r < (labels.length : Int)))

def find (labels : Labels) (x : Int) : Option Int :=
  if 0 ≤ x then labels[x.toNat]? else none

def connected (labels : Labels) (x y : Int) : Bool :=
  match find labels x, find labels y with
  | some rx, some ry => decide (rx = ry)
  | _, _ => false

def replace (rx ry rep : Int) : Int := if rep = ry then rx else rep

def union (labels : Labels) (x y : Int) : Labels :=
  match find labels x, find labels y with
  | some rx, some ry => labels.map (replace rx ry)
  | _, _ => labels

-- Boolean counterpart of Python's assertion-based candidate test harness.
def check (candidate : Labels → Int → Int → Labels) : Bool :=
  let uf0 := make_set 5
  let uf1 := candidate uf0 0 1
  let uf2 := candidate uf1 1 2
  let uf3 := candidate uf2 0 2
  (uf0 == [0, 1, 2, 3, 4]) && pre uf0 &&
  (find uf0 0 == some 0) && (find uf0 4 == some 4) && (find uf0 5 == none) &&
  !connected uf0 0 1 && connected uf0 2 2 &&
  (uf1 == [0, 0, 2, 3, 4]) && (uf1.length == uf0.length) &&
  connected uf1 0 1 && connected uf1 1 0 && !connected uf1 0 2 &&
  (uf2 == [0, 0, 0, 3, 4]) && connected uf2 0 2 && connected uf2 2 1 &&
  (uf3 == uf2) && (candidate uf2 10 2 == uf2) &&
  (candidate uf2 2 10 == uf2) && (candidate [] 0 1 == [])

-- Fixed tests: the Python check, plus negative indices and sizes.
example : check union = true := by native_decide
#eval if check union then "All tests passed." else "Tests failed."
example : make_set 5 = [0, 1, 2, 3, 4] := by native_decide
example : pre (make_set 5) = true := by native_decide
example : find (make_set 5) 0 = some 0 ∧ find (make_set 5) 4 = some 4 ∧
    find (make_set 5) 5 = none := by native_decide
example : connected (make_set 5) 0 1 = false ∧
    connected (make_set 5) 2 2 = true := by native_decide
example : union (make_set 5) 0 1 = [0, 0, 2, 3, 4] := by native_decide
example : let uf := union (make_set 5) 0 1
    uf.length = 5 ∧ connected uf 0 1 = true ∧ connected uf 1 0 = true ∧
    connected uf 0 2 = false := by native_decide
example : let uf := union (union (make_set 5) 0 1) 1 2
    uf = [0, 0, 0, 3, 4] ∧ connected uf 0 2 = true ∧
    connected uf 2 1 = true ∧ union uf 0 2 = uf ∧
    union uf 10 2 = uf ∧ union uf 2 10 = uf := by native_decide
example : union [] 0 1 = [] ∧ make_set (-4) = [] ∧
    find (make_set 5) (-1) = none ∧ union (make_set 5) (-1) 2 = make_set 5 := by
  native_decide
#eval union (union (make_set 5) 0 1) 1 2
#eval (find [] 0, pre [], connected [] 0 0)

-- The representation invariant (not a restriction on the operations' domain).
def Pre (labels : Labels) : Prop :=
  ∀ r ∈ labels, 0 ≤ r ∧ r < (labels.length : Int)

-- Lookup lemmas used throughout the specification.
theorem find_map (f : Int → Int) (labels : Labels) (x : Int) :
    find (labels.map f) x = (find labels x).map f := by
  simp only [find, List.getElem?_map]
  split <;> rfl

theorem find_none_iff (labels : Labels) (x : Int) :
    find labels x = none ↔ x < 0 ∨ (labels.length : Int) ≤ x := by
  unfold find
  split_ifs with hx
  · simp only [List.getElem?_eq_none_iff]
    omega
  · simp only [true_iff]
    omega

theorem find_some_mem {labels : Labels} {x r : Int}
    (h : find labels x = some r) : r ∈ labels := by
  unfold find at h
  split_ifs at h with hx
  · exact List.mem_of_getElem? h

def pre_spec_prop (labels : Labels) : Prop := pre labels = true ↔ Pre labels

theorem pre_spec_thm (labels : Labels) : pre_spec_prop labels := by
  simp [pre_spec_prop, pre, Pre]

def find_prop (labels : Labels) (x : Int) : Prop :=
  (find labels x = none ↔ x < 0 ∨ (labels.length : Int) ≤ x) ∧
  (∀ r, find labels x = some r → r ∈ labels)

theorem find_thm (labels : Labels) (x : Int) : find_prop labels x :=
  ⟨find_none_iff labels x, fun _ h => find_some_mem h⟩

theorem find_make_set (n x : Int) :
    find (make_set n) x = if 0 ≤ x ∧ x < n then some x else none := by
  simp only [find, make_set, List.getElem?_map]
  split_ifs <;> simp_all

def make_set_prop (n : Int) : Prop :=
  (make_set n).length = n.toNat ∧ Pre (make_set n) ∧
  (∀ x, find (make_set n) x = if 0 ≤ x ∧ x < n then some x else none)

theorem make_set_thm (n : Int) : make_set_prop n := by
  refine ⟨by simp [make_set], ?_, find_make_set n⟩
  intro r hr
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
  have hi' := List.mem_range.mp hi
  simp only [make_set, List.length_map, List.length_range]
  exact ⟨Int.natCast_nonneg i, by change (i : Int) < (n.toNat : Int); omega⟩

def union_length_prop (labels : Labels) (x y : Int) : Prop :=
  (union labels x y).length = labels.length

theorem union_length_thm (labels : Labels) (x y : Int) :
    union_length_prop labels x y := by
  unfold union_length_prop union
  split <;> simp

def union_invalid_prop (labels : Labels) (x y : Int) : Prop :=
  (x < 0 ∨ (labels.length : Int) ≤ x ∨ y < 0 ∨ (labels.length : Int) ≤ y) →
  union labels x y = labels

theorem union_invalid_thm (labels : Labels) (x y : Int) :
    union_invalid_prop labels x y := by
  intro h
  have h' : find labels x = none ∨ find labels y = none := by
    rw [find_none_iff, find_none_iff]
    tauto
  rcases h' with h' | h' <;> simp [union, h']

def union_relabel_prop (labels : Labels) (x y : Int) : Prop :=
  ∀ rx ry, find labels x = some rx → find labels y = some ry →
    ∀ z, find (union labels x y) z = (find labels z).map (replace rx ry)

theorem union_relabel_thm (labels : Labels) (x y : Int) :
    union_relabel_prop labels x y := by
  intro rx ry hx hy z
  simp [union, hx, hy, find_map]

def union_pre_prop (labels : Labels) (x y : Int) : Prop :=
  Pre labels → Pre (union labels x y)

theorem union_pre_thm (labels : Labels) (x y : Int) :
    union_pre_prop labels x y := by
  intro hp r hr
  have hl := union_length_thm labels x y
  unfold union_length_prop at hl
  rw [hl]
  unfold union at hr
  split at hr
  next rx ry hx hy =>
    obtain ⟨s, hs, hr⟩ := List.mem_map.mp hr
    rw [← hr]
    unfold replace
    split_ifs
    · exact hp rx (find_some_mem hx)
    · exact hp s hs
  next => exact hp r hr

def union_already_prop (labels : Labels) (x y : Int) : Prop :=
  connected labels x y = true → union labels x y = labels

theorem union_already_thm (labels : Labels) (x y : Int) :
    union_already_prop labels x y := by
  intro h
  unfold connected at h
  cases hx : find labels x <;> cases hy : find labels y <;> simp [hx, hy] at h
  rename_i rx ry
  subst ry
  simp only [union, hx, hy]
  have he : replace rx rx = id := by
    funext r
    simp only [replace, id_eq]
    split_ifs with h
    · exact h.symm
    · rfl
  simp [he]

-- Connectivity is an equivalence relation on the valid indices.
def connected_prop (labels : Labels) (x y z : Int) : Prop :=
  (connected labels x y = connected labels y x) ∧
  (connected labels x x = true ↔ 0 ≤ x ∧ x < (labels.length : Int)) ∧
  (connected labels x y = true → connected labels y z = true →
    connected labels x z = true)

theorem connected_thm (labels : Labels) (x y z : Int) :
    connected_prop labels x y z := by
  refine ⟨?_, ?_, ?_⟩
  · cases hx : find labels x <;> cases hy : find labels y <;>
      simp [connected, hx, hy, eq_comm]
  · have hn := find_none_iff labels x
    cases hx : find labels x <;> simp [connected, hx] at * <;> omega
  · cases hx : find labels x <;> cases hy : find labels y <;>
      cases hz : find labels z <;> simp [connected, hx, hy, hz]
    omega

def union_connected_prop (labels : Labels) (x y : Int) : Prop :=
  0 ≤ x → x < (labels.length : Int) →
  0 ≤ y → y < (labels.length : Int) → connected (union labels x y) x y = true

theorem union_connected_thm (labels : Labels) (x y : Int) :
    union_connected_prop labels x y := by
  intro hx0 hxl hy0 hyl
  have hx : find labels x ≠ none := by
    intro h
    have := (find_none_iff labels x).mp h
    omega
  have hy : find labels y ≠ none := by
    intro h
    have := (find_none_iff labels y).mp h
    omega
  cases hfx : find labels x <;> cases hfy : find labels y <;> try contradiction
  simp [connected, union, hfx, hfy, find_map, replace]

def union_idempotent_prop (labels : Labels) (x y : Int) : Prop :=
  union (union labels x y) x y = union labels x y

theorem union_idempotent_thm (labels : Labels) (x y : Int) :
    union_idempotent_prop labels x y := by
  unfold union_idempotent_prop
  by_cases hx : 0 ≤ x ∧ x < (labels.length : Int)
  · by_cases hy : 0 ≤ y ∧ y < (labels.length : Int)
    · exact union_already_thm _ x y (union_connected_thm labels x y hx.1 hx.2 hy.1 hy.2)
    · have he := union_invalid_thm labels x y (by omega)
      simp only [he]
  · have he := union_invalid_thm labels x y (by omega)
    simp only [he]

-- This exact partition formula includes invalid x/y/a/b and ill-formed labels.
-- It implies preservation of old connections and excludes unintended merges.
def union_partition_prop (labels : Labels) (x y a b : Int) : Prop :=
  connected (union labels x y) a b =
    (connected labels a b ||
      (connected labels a x && connected labels b y) ||
      (connected labels a y && connected labels b x))

theorem replace_eq_iff (rx ry a b : Int) :
    replace rx ry a = replace rx ry b ↔
      a = b ∨ (a = rx ∧ b = ry) ∨ (a = ry ∧ b = rx) := by
  unfold replace
  split_ifs <;> omega

theorem union_partition_thm (labels : Labels) (x y a b : Int) :
    union_partition_prop labels x y a b := by
  unfold union_partition_prop
  cases hx : find labels x <;> cases hy : find labels y <;>
    cases ha : find labels a <;> cases hb : find labels b <;>
    simp [union, connected, hx, hy, ha, hb, find_map,
      replace_eq_iff, Bool.or_assoc]

-- The union postcondition collects the representation and behavioral contracts.
def Post_prop (labels : Labels) (x y : Int) : Prop :=
  Pre (union labels x y) ∧
  union_length_prop labels x y ∧
  union_invalid_prop labels x y ∧
  union_relabel_prop labels x y ∧
  union_already_prop labels x y ∧
  union_connected_prop labels x y ∧
  union_idempotent_prop labels x y ∧
  (∀ a b, union_partition_prop labels x y a b)

/-! ## Property-based tests

These are exhaustive bounded tests, not proofs of the universal propositions.
The alphabet deliberately includes a negative representative and representatives
outside some lists' bounds. The integer indices include both negative and high
out-of-bounds cases. Quantifiers over queried indices are bounded only in these
tests, never in the specifications or theorems above.
-/

private def labelAlphabet : List Int := [-1, 0, 1, 2, 3]

private def listsOfLength : Nat → List Labels
  | 0 => [[]]
  | n + 1 => labelAlphabet.flatMap fun r => (listsOfLength n).map (r :: ·)

private def sampleLabels : List Labels :=
  (List.range 4).flatMap listsOfLength ++
  (List.range 8).map (fun n => make_set (n : Int)) ++
  [[0, 0, 2, 3, 4], [0, 0, 0, 3, 4], [4, 4, 4, 4, 4], [-9, 30, -9, 30]]

private def indices (labels : Labels) : List Int :=
  (List.range (labels.length + 3)).map (fun i => (i : Int) - 1)

private def all1 (p : Labels → Int → Bool) : Bool :=
  sampleLabels.all fun l => (indices l).all (p l)

private def all2 (p : Labels → Int → Int → Bool) : Bool :=
  sampleLabels.all fun l => (indices l).all fun x => (indices l).all (p l x)

private def all3 (p : Labels → Int → Int → Int → Bool) : Bool :=
  sampleLabels.all fun l => (indices l).all fun x =>
    (indices l).all fun y => (indices l).all (p l x y)

private def all4 (p : Labels → Int → Int → Int → Int → Bool) : Bool :=
  sampleLabels.all fun l => (indices l).all fun x => (indices l).all fun y =>
    (indices l).all fun a => (indices l).all (p l x y a)

private def valid (l : Labels) (x : Int) : Bool :=
  decide (0 ≤ x ∧ x < (l.length : Int))

-- PBT for pre_spec_prop: independently express the invariant by filtering.
example : sampleLabels.all (fun l =>
    pre l == (l.filter (fun r => decide (0 ≤ r ∧ r < (l.length : Int))) == l))
    = true := by native_decide

-- PBT for find_prop: bounds equivalence and membership of every returned label.
private def findCheck (l : Labels) (x : Int) : Bool :=
  ((find l x == none) == decide (x < 0 ∨ (l.length : Int) ≤ x)) &&
    (match find l x with | none => true | some r => l.contains r)
example : all1 findCheck = true := by native_decide

-- PBT for make_set_prop: negative sizes, length, invariant, and singleton lookups.
private def makeSetCheck (n : Int) : Bool :=
  let l := make_set n
  (l.length == n.toNat) && pre l &&
    (indices l).all (fun x => find l x ==
      (if 0 ≤ x ∧ x < n then some x else none))
example : ((List.range 24).map (fun i => (i : Int) - 5)).all makeSetCheck = true := by
  native_decide

-- PBT for connected_prop: symmetry, valid-index reflexivity, and transitivity.
private def connectedCheck (l : Labels) (x y z : Int) : Bool :=
  (connected l x y == connected l y x) &&
  (connected l x x == valid l x) &&
  (!(connected l x y && connected l y z) || connected l x z)
example : all3 connectedCheck = true := by native_decide

-- PBT for union_length_prop.
private def lengthCheck (l : Labels) (x y : Int) : Bool :=
  (union l x y).length == l.length
example : all2 lengthCheck = true := by native_decide

-- PBT for union_invalid_prop, including both invalid argument positions.
private def invalidCheck (l : Labels) (x y : Int) : Bool :=
  if !valid l x || !valid l y then union l x y == l else true
example : all2 invalidCheck = true := by native_decide

-- PBT for union_relabel_prop: all query indices, including invalid ones.
-- Looking up rx and ry enumerates the only possible witnesses of its premises.
private def relabelCheck (l : Labels) (x y : Int) : Bool :=
  match find l x, find l y with
  | some rx, some ry => (indices l).all fun z =>
      find (union l x y) z == (find l z).map (replace rx ry)
  | _, _ => true
example : all2 relabelCheck = true := by native_decide

-- PBT for union_pre_prop: only this check requires the input invariant.
private def invariantCheck (l : Labels) (x y : Int) : Bool :=
  !pre l || pre (union l x y)
example : all2 invariantCheck = true := by native_decide

-- PBT for union_already_prop.
private def alreadyCheck (l : Labels) (x y : Int) : Bool :=
  !connected l x y || union l x y == l
example : all2 alreadyCheck = true := by native_decide

-- PBT for union_connected_prop.
private def mergeCheck (l : Labels) (x y : Int) : Bool :=
  !(valid l x && valid l y) || connected (union l x y) x y
example : all2 mergeCheck = true := by native_decide

-- PBT for union_idempotent_prop (including invalid unions).
private def idempotentCheck (l : Labels) (x y : Int) : Bool :=
  union (union l x y) x y == union l x y
example : all2 idempotentCheck = true := by native_decide

-- PBT for union_partition_prop: exhaustive quadruples of indices.
private def partitionCheck (l : Labels) (x y a b : Int) : Bool :=
  connected (union l x y) a b ==
    (connected l a b || (connected l a x && connected l b y) ||
      (connected l a y && connected l b x))
example : all4 partitionCheck = true := by native_decide

-- PBT for Post_prop, under precisely the Pre hypothesis of correctness.
private def postCheck (l : Labels) (x y : Int) : Bool :=
  !pre l ||
    (pre (union l x y) && lengthCheck l x y && invalidCheck l x y &&
      relabelCheck l x y && alreadyCheck l x y && mergeCheck l x y &&
      idempotentCheck l x y &&
      (indices l).all (fun a => (indices l).all (partitionCheck l x y a)))
example : all2 postCheck = true := by native_decide
#eval (sampleLabels.length, all2 postCheck, all4 partitionCheck)

-- No testing oracle is used in this proof: it assembles the kernel-checked laws.
theorem correctness_thm (labels : Labels) (x y : Int) :
    Pre labels → Post_prop labels x y := by
  intro hp
  exact ⟨union_pre_thm labels x y hp, union_length_thm labels x y,
    union_invalid_thm labels x y, union_relabel_thm labels x y,
    union_already_thm labels x y, union_connected_thm labels x y,
    union_idempotent_thm labels x y, union_partition_thm labels x y⟩

/-! ## Imperative implementation

The mutable accumulator loop appends one rewritten label at a time. The loop
invariant below is generalized to every starting accumulator, which gives a
structural kernel proof rather than relying on evaluation of particular lists.
-/

def mapLoop (f : Int → Int) (labels acc : Labels) : Labels := Id.run do
  let mut out := acc
  for rep in labels do
    out := out ++ [f rep]
  return out

def unionImperative (labels : Labels) (x y : Int) : Labels := Id.run do
  let rx := find labels x
  let ry := find labels y
  let mut result := labels
  match rx, ry with
  | some rx, some ry =>
    result := mapLoop (fun rep => if rep = ry then rx else rep) labels []
  | _, _ => pure ()
  return result

-- Imperative fixed and bounded tests.
example : check unionImperative = true := by native_decide
#eval check unionImperative
example : unionImperative (make_set 5) 0 1 = [0, 0, 2, 3, 4] := by native_decide
example : let l := unionImperative (unionImperative (make_set 5) 0 1) 1 2
    l = [0, 0, 0, 3, 4] ∧ unionImperative l 0 2 = l ∧
    unionImperative l 10 2 = l ∧ unionImperative l 2 10 = l := by native_decide
example : unionImperative [] 0 1 = [] ∧
    unionImperative (make_set 5) (-1) 2 = make_set 5 := by native_decide
example : all2 (fun l x y => union l x y == unionImperative l x y) = true := by
  native_decide
#eval unionImperative (make_set 5) 0 1

-- Generalized accumulator invariant, proved by list induction.
theorem mapLoop_spec (f : Int → Int) (labels acc : Labels) :
    mapLoop f labels acc = acc ++ labels.map f := by
  induction labels generalizing acc with
  | nil => simp [mapLoop]
  | cons r rs ih =>
    have step : mapLoop f (r :: rs) acc = mapLoop f rs (acc ++ [f r]) := by
      simp [mapLoop]
    rw [step, ih]
    simp [List.append_assoc]

theorem equivalence_thm (labels : Labels) (x y : Int) :
    union labels x y = unionImperative labels x y := by
  cases hx : find labels x <;> cases hy : find labels y <;>
    simp [union, unionImperative, hx, hy, mapLoop_spec, replace]

end union_find
end Agent
