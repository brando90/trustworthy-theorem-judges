import Mathlib
namespace Agent

/-!
# A state-passing formalization of `collections.ChainMap`

Keys and values are arbitrary Lean types (with decidable key equality). Finite
ordered dictionaries are represented by association lists: the first binding
wins, updates retain a key's position, and deletion removes that key. Repeated
bindings are harmless alternative representations of the same dictionary.

Mapping objects live in an explicit heap. A ChainMap contains references, not
copies: writing through one view is observable through every other view of the
same object, including repeated references in a single chain. Allocation models
the fresh empty dictionary used by the empty constructor and `new_child()`.
`Option` represents absence; `Except` distinguishes the two Python KeyErrors.
The typed domain supplies the mapping protocol checked by `pre_init`; `Pre`
additionally expresses that the supplied object references have been allocated.
This is the finite dictionary model, not an interpreter for user-defined Python
mapping subclasses with effectful `__getitem__` or overridden `__missing__`.
-/

namespace CollectionsChainMap

abbrev Dict (K V : Type) := List (K × V)

variable {K V : Type} [DecidableEq K]

def dictLookup (k : K) : Dict K V → Option V
  | [] => none
  | (q, v) :: ds => if k = q then some v else dictLookup k ds

def dictSet (k : K) (v : V) : Dict K V → Dict K V
  | [] => [(k, v)]
  | (q, w) :: ds => if k = q then (q, v) :: ds else (q, w) :: dictSet k v ds

def dictErase (k : K) (d : Dict K V) : Dict K V :=
  d.filter (fun p => decide (p.1 ≠ k))

/-- Keep first occurrences, in insertion order. -/
def orderedUnique (xs : List K) : List K := xs.reverse.dedup.reverse

def dictKeys (d : Dict K V) : List K := orderedUnique (d.map Prod.fst)

structure Heap (K V : Type) where
  next : Nat
  read : Nat → Dict K V

def emptyHeap : Heap K V := ⟨0, fun _ => []⟩

def writeMap (h : Heap K V) (i : Nat) (d : Dict K V) : Heap K V :=
  ⟨h.next, fun j => if j = i then d else h.read j⟩

def allocate (h : Heap K V) (d : Dict K V) : Heap K V × Nat :=
  (⟨h.next + 1, fun j => if j = h.next then d else h.read j⟩, h.next)

structure ChainMap where
  first : Nat
  rest : List Nat
  deriving Repr, DecidableEq

def ChainMap.maps (c : ChainMap) : List Nat := c.first :: c.rest

def init (h : Heap K V) : List Nat → Heap K V × ChainMap
  | [] => let (h', i) := allocate h []; (h', ⟨i, []⟩)
  | i :: is => (h, ⟨i, is⟩)

def lookupMaps (h : Heap K V) : List Nat → K → Option V
  | [], _ => none
  | i :: is, k => match dictLookup k (h.read i) with
    | some v => some v
    | none => lookupMaps h is k

def lookup (h : Heap K V) (c : ChainMap) (k : K) : Option V :=
  lookupMaps h c.maps k

inductive KeyError (K : Type) where
  | missing (key : K)
  | notInFirst (key : K)
  deriving Repr, DecidableEq

def getItem (h : Heap K V) (c : ChainMap) (k : K) : Except (KeyError K) V :=
  match lookup h c k with
  | some v => .ok v
  | none => .error (.missing k)

def contains (h : Heap K V) (c : ChainMap) (k : K) : Bool :=
  c.maps.any (fun i => (dictLookup k (h.read i)).isSome)

def get (h : Heap K V) (c : ChainMap) (k : K) (default : Option V := none) : Option V :=
  if contains h c k then lookup h c k else default

/-- Reversed updates retain the first insertion position of each key. -/
def iter (h : Heap K V) (c : ChainMap) : List K :=
  orderedUnique (c.maps.reverse.flatMap (fun i => dictKeys (h.read i)))

def length (h : Heap K V) (c : ChainMap) : Nat := (iter h c).length

def newChild (h : Heap K V) (c : ChainMap) (m : Option Nat := none) : Heap K V × ChainMap :=
  match m with
  | some i => (h, ⟨i, c.maps⟩)
  | none => let (h', i) := allocate h []; (h', ⟨i, c.maps⟩)

def parents (h : Heap K V) (c : ChainMap) : Heap K V × ChainMap := init h c.rest

def setItem (h : Heap K V) (c : ChainMap) (k : K) (v : V) : Heap K V :=
  writeMap h c.first (dictSet k v (h.read c.first))

def delItem (h : Heap K V) (c : ChainMap) (k : K) : Except (KeyError K) (Heap K V) :=
  match dictLookup k (h.read c.first) with
  | none => .error (.notInFirst k)
  | some _ => .ok (writeMap h c.first (dictErase k (h.read c.first)))

/-! ## The source's unit tests, including observable aliasing -/

def d1 : Dict String Int := [("a", 1), ("b", 2)]
def d2 : Dict String Int := [("b", 3), ("c", 4)]
def demoHeap : Heap String Int :=
  ⟨2, fun i => if i = 0 then d1 else if i = 1 then d2 else []⟩
def cm : ChainMap := (init demoHeap [0, 1]).2
def written : Heap String Int := setItem demoHeap cm "c" 5

def sourceTests : Bool := Id.run do
  let mut ok := lookup demoHeap cm "a" == some 1 && lookup demoHeap cm "c" == some 4
  ok := ok && lookup demoHeap cm "b" == some 2
  ok := ok && dictLookup "c" (written.read 0) == some 5
  ok := ok && dictLookup "c" (written.read 1) == some 4
  let (h, i) := allocate written [("d", 6)]
  let (h2, cm2) := newChild h cm (some i)
  ok := ok && lookup h2 cm2 "a" == some 1 && lookup h2 cm2 "d" == some 6
  ok := ok && h2.read cm2.first == [("d", 6)]
  ok := ok && h2.read (cm2.rest.headD 99) == written.read 0
  let (hp, p) := parents written cm
  ok := ok && lookup hp p "b" == some 3 && !(contains hp p "a")
  return ok

example : sourceTests = true := by native_decide
example : iter demoHeap cm = ["b", "c", "a"] := by native_decide
example : length demoHeap cm = 3 := by native_decide
example : (match getItem demoHeap cm "z" with
  | .error (.missing "z") => true | _ => false) = true := by native_decide
example : get demoHeap cm "z" (some 9) = some 9 := by native_decide
example : (init (emptyHeap : Heap String Int) []).2.maps = [0] := by native_decide
example : (newChild demoHeap cm).2.maps = [2, 0, 1] := by native_decide
example : lookup (setItem demoHeap cm "a" 7) ⟨0, []⟩ "a" = some 7 := by native_decide
example : (match delItem demoHeap cm "c" with
  | .error (.notInFirst "c") => true | _ => false) = true := by native_decide
example : (match delItem demoHeap cm "b" with
  | .ok h => lookup h cm "b" == some 3 | _ => false) = true := by native_decide
#eval sourceTests
#eval (iter demoHeap cm, length demoHeap cm, getItem demoHeap cm "b")

/-! ## Preconditions and specifications -/

def Pre (h : Heap K V) (refs : List Nat) : Prop := ∀ i ∈ refs, i < h.next


/-! The following lemmas are kernel proofs, independent of the test evaluator. -/

lemma dictLookup_set_self (d : Dict K V) (k : K) (v : V) :
    dictLookup k (dictSet k v d) = some v := by
  induction d with
  | nil => simp [dictSet, dictLookup]
  | cons p ds ih =>
    rcases p with ⟨q, w⟩
    by_cases e : k = q <;> simp [dictSet, dictLookup, e, ih]

lemma dictLookup_set_other (d : Dict K V) (k q : K) (v : V) (ne : q ≠ k) :
    dictLookup q (dictSet k v d) = dictLookup q d := by
  induction d with
  | nil => simp [dictSet, dictLookup, ne]
  | cons p ds ih =>
    rcases p with ⟨a, w⟩
    by_cases e : k = a
    · subst a; simp [dictSet, dictLookup, ne]
    · by_cases f : q = a <;> simp [dictSet, dictLookup, e, f, ih]

lemma dictLookup_erase_self (d : Dict K V) (k : K) :
    dictLookup k (dictErase k d) = none := by
  induction d with
  | nil => rfl
  | cons p ds ih =>
    rcases p with ⟨q, w⟩
    by_cases e : q = k
    · subst q; simpa [dictErase] using ih
    · simpa [dictErase, e, dictLookup, Ne.symm e] using ih

lemma dictLookup_erase_other (d : Dict K V) (k q : K) (ne : q ≠ k) :
    dictLookup q (dictErase k d) = dictLookup q d := by
  induction d with
  | nil => rfl
  | cons p ds ih =>
    rcases p with ⟨a, w⟩
    by_cases e : a = k
    · subst a; simpa [dictErase, dictLookup, ne] using ih
    · by_cases f : q = a <;> simp [dictErase, dictLookup, e, f, dictErase] at ih ⊢ <;> exact ih

lemma mem_dictKeys (d : Dict K V) (k : K) :
    k ∈ dictKeys d ↔ (dictLookup k d).isSome = true := by
  simp only [dictKeys, orderedUnique, List.mem_reverse, List.mem_dedup]
  induction d with
  | nil => simp [dictLookup]
  | cons p ds ih =>
    rcases p with ⟨q, w⟩
    by_cases e : k = q <;> simp_all [dictLookup]

lemma lookupMaps_none (h : Heap K V) (ids : List Nat) (k : K) :
    lookupMaps h ids k = none ↔ ∀ i ∈ ids, dictLookup k (h.read i) = none := by
  induction ids with
  | nil => simp [lookupMaps]
  | cons i ids ih =>
    cases e : dictLookup k (h.read i) <;> simp [lookupMaps, e, ih]

lemma lookupMaps_append_misses (h : Heap K V) (xs ys : List Nat) (k : K)
    (miss : ∀ i ∈ xs, dictLookup k (h.read i) = none) :
    lookupMaps h (xs ++ ys) k = lookupMaps h ys k := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    simp only [List.cons_append, lookupMaps, miss i (by simp)]
    exact ih (fun j hj => miss j (by simp [hj]))

lemma lookupMaps_first (h : Heap K V) (ids : List Nat) (k : K) (v : V) :
    lookupMaps h ids k = some v ↔
      ∃ before i after, ids = before ++ i :: after ∧
        (∀ j ∈ before, dictLookup k (h.read j) = none) ∧
        dictLookup k (h.read i) = some v := by
  constructor
  · induction ids with
    | nil => simp [lookupMaps]
    | cons i ids ih =>
      intro hit
      cases e : dictLookup k (h.read i) with
      | none =>
        simp only [lookupMaps, e] at hit
        obtain ⟨before, j, after, heq, hm, hv⟩ := ih hit
        refine ⟨i :: before, j, after, by simp [heq], ?_, hv⟩
        intro a ha
        simp only [List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact e
        · exact hm a ha
      | some w =>
        simp only [lookupMaps, e, Option.some.injEq] at hit
        subst w
        exact ⟨[], i, ids, rfl, by simp, e⟩
  · rintro ⟨before, i, after, rfl, hm, hv⟩
    rw [lookupMaps_append_misses h before (i :: after) k hm]
    simp [lookupMaps, hv]

lemma any_lookup (h : Heap K V) (ids : List Nat) (k : K) :
    ids.any (fun i => (dictLookup k (h.read i)).isSome) = (lookupMaps h ids k).isSome := by
  induction ids with
  | nil => rfl
  | cons i ids ih => cases e : dictLookup k (h.read i) <;> simp [lookupMaps, e, ih]

lemma lookupMaps_congr (h g : Heap K V) (ids : List Nat) (k : K)
    (eqs : ∀ i ∈ ids, h.read i = g.read i) :
    lookupMaps h ids k = lookupMaps g ids k := by
  induction ids with
  | nil => rfl
  | cons i ids ih =>
    simp only [lookupMaps, eqs i (by simp)]
    cases dictLookup k (g.read i)
    · exact ih (fun j hj => eqs j (by simp [hj]))
    · rfl

/-- The constructor preserves nonempty arguments, but allocates a fresh empty
object on no arguments. It never constructs an empty list of mappings. -/
def init_prop (h : Heap K V) (ids : List Nat) : Prop :=
  let (g, c) := init h ids
  c.maps ≠ [] ∧
  (ids ≠ [] → g = h ∧ c.maps = ids) ∧
  (ids = [] → c.maps = [h.next] ∧ g.next = h.next + 1 ∧
    g.read h.next = [] ∧ ∀ i, i ≠ h.next → g.read i = h.read i)

theorem init_thm (h : Heap K V) (ids : List Nat) : init_prop h ids := by
  cases ids <;> simp (config := { contextual := true }) [init_prop, init, allocate, ChainMap.maps]

def valid_prop (h : Heap K V) (ids : List Nat) : Prop :=
  Pre h ids → Pre (init h ids).1 (init h ids).2.maps

theorem valid_thm (h : Heap K V) (ids : List Nat) : valid_prop h ids := by
  cases ids <;> simp [valid_prop, Pre, init, allocate, ChainMap.maps]

/-- A value is returned exactly at the first successful mapping lookup. -/
def lookup_prop (h : Heap K V) (c : ChainMap) (k : K) (v : V) : Prop :=
  lookup h c k = some v ↔ ∃ before i after, c.maps = before ++ i :: after ∧
    (∀ j ∈ before, dictLookup k (h.read j) = none) ∧ dictLookup k (h.read i) = some v

theorem lookup_thm (h : Heap K V) (c : ChainMap) (k : K) (v : V) :
    lookup_prop h c k v := lookupMaps_first h c.maps k v

def missing_prop (h : Heap K V) (c : ChainMap) (k : K) : Prop :=
  lookup h c k = none ↔ ∀ i ∈ c.maps, dictLookup k (h.read i) = none

theorem missing_thm (h : Heap K V) (c : ChainMap) (k : K) : missing_prop h c k :=
  lookupMaps_none h c.maps k

def shadow_prop (h : Heap K V) (c : ChainMap) (k : K) : Prop :=
  lookup h c k = (dictLookup k (h.read c.first)).or (lookupMaps h c.rest k)

theorem shadow_thm (h : Heap K V) (c : ChainMap) (k : K) : shadow_prop h c k := by
  cases e : dictLookup k (h.read c.first) <;>
    simp [shadow_prop, lookup, ChainMap.maps, lookupMaps, e]

def getItem_prop (h : Heap K V) (c : ChainMap) (k : K) : Prop :=
  (getItem h c k = .error (.missing k) ↔ lookup h c k = none) ∧
  ∀ v, getItem h c k = .ok v ↔ lookup h c k = some v

theorem getItem_thm (h : Heap K V) (c : ChainMap) (k : K) : getItem_prop h c k := by
  cases e : lookup h c k <;> simp [getItem_prop, getItem, e]

def contains_prop (h : Heap K V) (c : ChainMap) (k : K) : Prop :=
  contains h c k = (lookup h c k).isSome

theorem contains_thm (h : Heap K V) (c : ChainMap) (k : K) : contains_prop h c k :=
  any_lookup h c.maps k

def get_prop (h : Heap K V) (c : ChainMap) (k : K) (default : Option V) : Prop :=
  get h c k default = (lookup h c k).or default

theorem get_thm (h : Heap K V) (c : ChainMap) (k : K) (default : Option V) :
    get_prop h c k default := by
  have hc := contains_thm h c k
  unfold contains_prop at hc
  unfold get_prop get
  rw [hc]
  cases lookup h c k <;> rfl

def iter_prop (h : Heap K V) (c : ChainMap) (k : K) : Prop :=
  (iter h c).Nodup ∧ (k ∈ iter h c ↔ contains h c k = true)

theorem iter_thm (h : Heap K V) (c : ChainMap) (k : K) : iter_prop h c k := by
  constructor
  · unfold iter orderedUnique
    rw [List.nodup_reverse]
    exact List.nodup_dedup _
  · simp only [iter, orderedUnique, List.mem_reverse, List.mem_dedup, List.mem_flatMap, List.mem_reverse,
      mem_dictKeys, contains, List.any_eq_true]

def length_prop (h : Heap K V) (c : ChainMap) : Prop :=
  length h c = (c.maps.flatMap (fun i => dictKeys (h.read i))).toFinset.card

theorem length_thm (h : Heap K V) (c : ChainMap) : length_prop h c := by
  have hn : (iter h c).Nodup := by
    unfold iter orderedUnique
    rw [List.nodup_reverse]
    exact List.nodup_dedup _
  have he : (iter h c).toFinset = (c.maps.flatMap (fun i => dictKeys (h.read i))).toFinset := by
    ext k
    simp [iter, orderedUnique]
  unfold length_prop length
  rw [← List.toFinset_card_of_nodup hn, he]

/-- Writes update the first object only, retain all other keys, and are immediately
visible through the chain. The quantified object `i` includes unreferenced objects. -/
def set_prop (h : Heap K V) (c : ChainMap) (k q : K) (v : V) (i : Nat) : Prop :=
  let g := setItem h c k v
  g.next = h.next ∧ dictLookup k (g.read c.first) = some v ∧ lookup g c k = some v ∧
  (q ≠ k → dictLookup q (g.read c.first) = dictLookup q (h.read c.first)) ∧
  (i ≠ c.first → g.read i = h.read i)

theorem set_thm (h : Heap K V) (c : ChainMap) (k q : K) (v : V) (i : Nat) :
    set_prop h c k q v i := by
  simp (config := { contextual := true }) [set_prop, setItem, writeMap, lookup, ChainMap.maps, lookupMaps,
    dictLookup_set_self, dictLookup_set_other]

/-- A missing first-map key is an error even when a later mapping has the key.
After successful deletion, search resumes through the tail in the UPDATED heap:
this detail matters when the same object occurs more than once. -/
def delete_prop (h : Heap K V) (c : ChainMap) (k q : K) (i : Nat) : Prop :=
  match dictLookup k (h.read c.first) with
  | none => delItem h c k = .error (.notInFirst k)
  | some _ =>
    let g := writeMap h c.first (dictErase k (h.read c.first))
    delItem h c k = .ok g ∧ g.next = h.next ∧ dictLookup k (g.read c.first) = none ∧
    (q ≠ k → dictLookup q (g.read c.first) = dictLookup q (h.read c.first)) ∧
    (i ≠ c.first → g.read i = h.read i) ∧ lookup g c k = lookupMaps g c.rest k

theorem delete_thm (h : Heap K V) (c : ChainMap) (k q : K) (i : Nat) :
    delete_prop h c k q i := by
  cases e : dictLookup k (h.read c.first) <;>
    simp (config := { contextual := true }) [delete_prop, delItem, e, writeMap, dictLookup_erase_self,
      dictLookup_erase_other, lookup, ChainMap.maps, lookupMaps]

/-- The explicit-map case shares the object. The default case allocates, preserves
all old objects, and contributes no bindings. -/
def child_prop (h : Heap K V) (c : ChainMap) (m : Option Nat) (k : K) : Prop :=
  let (g, ch) := newChild h c m
  match m with
  | some i => g = h ∧ ch.maps = i :: c.maps ∧
      lookup g ch k = (dictLookup k (h.read i)).or (lookup h c k)
  | none => ch.maps = h.next :: c.maps ∧ g.next = h.next + 1 ∧ g.read h.next = [] ∧
      (∀ i, i < h.next → g.read i = h.read i) ∧
      (Pre h c.maps → lookup g ch k = lookup h c k)

theorem child_thm (h : Heap K V) (c : ChainMap) (m : Option Nat) (k : K) :
    child_prop h c m k := by
  cases m with
  | some i =>
    cases e : dictLookup k (h.read i) <;>
      simp [child_prop, newChild, ChainMap.maps, lookup, lookupMaps, e]
  | none =>
    let g := (allocate h ([] : Dict K V)).1
    change (h.next :: c.maps) = h.next :: c.maps ∧ g.next = h.next + 1 ∧
      g.read h.next = [] ∧ (∀ i, i < h.next → g.read i = h.read i) ∧
      (Pre h c.maps → lookupMaps g (h.next :: c.maps) k = lookupMaps h c.maps k)
    refine ⟨rfl, rfl, ?_, ?_, ?_⟩
    · simp [g, allocate]
    · intro i hi
      simp [g, allocate, Nat.ne_of_lt hi]
    · intro hp
      have hn : dictLookup k (g.read h.next) = none := by simp [g, allocate, dictLookup]
      rw [lookupMaps, hn]
      apply lookupMaps_congr
      intro i hi
      simp [g, allocate, Nat.ne_of_lt (hp i hi)]

def parents_prop (h : Heap K V) (c : ChainMap) (k : K) : Prop :=
  let (g, p) := parents h c
  match c.rest with
  | [] => p.maps = [h.next] ∧ g.next = h.next + 1 ∧ lookup g p k = none ∧
      ∀ i, i < h.next → g.read i = h.read i
  | i :: is => g = h ∧ p.maps = i :: is ∧ lookup g p k = lookupMaps h c.rest k

theorem parents_thm (h : Heap K V) (c : ChainMap) (k : K) : parents_prop h c k := by
  rcases c with ⟨i, ids⟩
  cases ids with
  | nil =>
    simp [parents_prop, parents, init, allocate, ChainMap.maps, lookup,
      lookupMaps, dictLookup]
    intro j hj he
    omega
  | cons j js => simp [parents_prop, parents, init, ChainMap.maps, lookup]

/-- Aliasing is observable, not just a statement about a copied list of maps. -/
def alias_prop (h : Heap K V) (writer observer : ChainMap) (k : K) (v : V) : Prop :=
  observer.first = writer.first → lookup (setItem h writer k v) observer k = some v

theorem alias_thm (h : Heap K V) (writer observer : ChainMap) (k : K) (v : V) :
    alias_prop h writer observer k v := by
  intro e
  simp [lookup, ChainMap.maps, lookupMaps, setItem, writeMap, e, dictLookup_set_self]

/-- Postcondition for construction, together with the full public method laws on
the resulting view. Keys, values, defaults, references and observers are unbounded. -/
def Post_prop (h : Heap K V) (ids : List Nat) : Prop :=
  let (g, c) := init h ids
  init_prop h ids ∧ valid_prop h ids ∧ Pre g c.maps ∧
  (∀ k v, lookup_prop g c k v) ∧ (∀ k, missing_prop g c k) ∧
  (∀ k, shadow_prop g c k) ∧ (∀ k, getItem_prop g c k) ∧
  (∀ k, contains_prop g c k) ∧ (∀ k d, get_prop g c k d) ∧
  (∀ k, iter_prop g c k) ∧ length_prop g c ∧
  (∀ k q v i, set_prop g c k q v i) ∧
  (∀ k q i, delete_prop g c k q i) ∧
  (∀ m k, child_prop g c m k) ∧ (∀ k, parents_prop g c k) ∧
  (∀ observer k v, alias_prop g c observer k v)


/-! ## Bounded property-based tests

Enumerate every dictionary of length at most two over {0,1} × {0,1}, every
pair of these objects, and every chain of length at most two over their refs.
This includes repeated keys and repeated OBJECTS. The empty heap is also tested.
Keys and values 2 exercise absence/new insertions. Heap equalities in the specs
are tested observationally at every allocated reference and some unallocated
ones; universal key/value statements use the stated finite bounds ONLY here.
The theorems above and below retain their unrestricted domains.
-/

def smallBindings : List (Nat × Nat) := [(0, 0), (0, 1), (1, 0), (1, 1)]
def smallDicts : List (Dict Nat Nat) :=
  [[]] ++ smallBindings.map (fun p => [p]) ++
    smallBindings.flatMap (fun p => smallBindings.map (fun q => [p, q]))
def smallHeaps : List (Heap Nat Nat) :=
  emptyHeap :: smallDicts.flatMap (fun a => smallDicts.map (fun b =>
    ⟨2, fun i => if i = 0 then a else if i = 1 then b else []⟩))
def smallRefs : List (List Nat) := [[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1]]
def keysToTest : List Nat := List.range 3

def pbtInputs (test : Heap Nat Nat → List Nat → Bool) : Bool :=
  smallHeaps.all (fun h => smallRefs.all (fun refs =>
    if refs.all (fun i => decide (i < h.next)) then test h refs else true))
def pbtViews (test : Heap Nat Nat → ChainMap → Bool) : Bool :=
  pbtInputs (fun h refs => let (g, c) := init h refs; test g c)

def checkInit (h : Heap Nat Nat) (refs : List Nat) : Bool :=
  let (g, c) := init h refs
  !c.maps.isEmpty &&
  if refs.isEmpty then
    c.maps == [h.next] && g.next == h.next + 1 && g.read h.next == [] &&
      (List.range 4).all (fun i => i == h.next || g.read i == h.read i)
  else c.maps == refs && g.next == h.next &&
    (List.range 4).all (fun i => g.read i == h.read i)

def checkValid (h : Heap Nat Nat) (refs : List Nat) : Bool :=
  let (g, c) := init h refs
  c.maps.all (fun i => decide (i < g.next))

/-- `take pos` is the executable prefix witness in `lookup_prop`. -/
def checkLookup (h : Heap Nat Nat) (c : ChainMap) : Bool :=
  keysToTest.all (fun k => keysToTest.all (fun v =>
    (lookup h c k == some v) == (c.maps.zipIdx.any (fun (i, pos) =>
      (c.maps.take pos).all (fun j => dictLookup k (h.read j) == none) &&
        dictLookup k (h.read i) == some v))))
def checkMissing (h : Heap Nat Nat) (c : ChainMap) : Bool :=
  keysToTest.all (fun k => (lookup h c k == none) ==
    c.maps.all (fun i => dictLookup k (h.read i) == none))
def checkShadow (h : Heap Nat Nat) (c : ChainMap) : Bool :=
  keysToTest.all (fun k => lookup h c k ==
    (dictLookup k (h.read c.first)).or (lookupMaps h c.rest k))
def checkGetItem (h : Heap Nat Nat) (c : ChainMap) : Bool :=
  keysToTest.all (fun k => match getItem h c k with
    | .error (.missing q) => k == q && lookup h c k == none
    | .error (.notInFirst _) => false
    | .ok v => lookup h c k == some v)
def checkContains (h : Heap Nat Nat) (c : ChainMap) : Bool :=
  keysToTest.all (fun k => contains h c k == (lookup h c k).isSome)
def checkGet (h : Heap Nat Nat) (c : ChainMap) : Bool :=
  keysToTest.all (fun k => [none, some 0, some 1, some 2].all (fun d =>
    get h c k d == (lookup h c k).or d))
def checkIter (h : Heap Nat Nat) (c : ChainMap) : Bool :=
  decide (iter h c |>.Nodup) && keysToTest.all (fun k =>
    (iter h c).contains k == contains h c k)
def checkLength (h : Heap Nat Nat) (c : ChainMap) : Bool :=
  length h c == (c.maps.flatMap (fun i => dictKeys (h.read i))).toFinset.card

def checkSet (h : Heap Nat Nat) (c : ChainMap) : Bool :=
  keysToTest.all (fun k => keysToTest.all (fun v =>
    let g := setItem h c k v
    g.next == h.next && dictLookup k (g.read c.first) == some v &&
      lookup g c k == some v &&
      keysToTest.all (fun q => q == k ||
        dictLookup q (g.read c.first) == dictLookup q (h.read c.first)) &&
      (List.range 4).all (fun i => i == c.first || g.read i == h.read i)))

def checkDelete (h : Heap Nat Nat) (c : ChainMap) : Bool :=
  keysToTest.all (fun k => match dictLookup k (h.read c.first), delItem h c k with
    | none, .error (.notInFirst q) => q == k
    | some _, .ok g =>
      g.next == h.next && g.read c.first == dictErase k (h.read c.first) &&
      dictLookup k (g.read c.first) == none &&
      keysToTest.all (fun q => q == k ||
        dictLookup q (g.read c.first) == dictLookup q (h.read c.first)) &&
      (List.range 4).all (fun i => i == c.first || g.read i == h.read i) &&
      lookup g c k == lookupMaps g c.rest k
    | _, _ => false)

def checkChild (h : Heap Nat Nat) (c : ChainMap) : Bool :=
  (none :: (List.range h.next).map some).all (fun m =>
    let (g, ch) := newChild h c m
    match m with
    | some i => ch.maps == i :: c.maps && g.next == h.next &&
      (List.range 4).all (fun j => g.read j == h.read j) &&
      keysToTest.all (fun k => lookup g ch k == (dictLookup k (h.read i)).or (lookup h c k))
    | none => ch.maps == h.next :: c.maps && g.next == h.next + 1 &&
      g.read h.next == [] && (List.range h.next).all (fun j => g.read j == h.read j) &&
      keysToTest.all (fun k => lookup g ch k == lookup h c k))

def checkParents (h : Heap Nat Nat) (c : ChainMap) : Bool :=
  let (g, p) := parents h c
  match c.rest with
  | [] => p.maps == [h.next] && g.next == h.next + 1 &&
    keysToTest.all (fun k => lookup g p k == none) &&
    (List.range h.next).all (fun i => g.read i == h.read i)
  | i :: is => p.maps == i :: is && g.next == h.next &&
    (List.range 4).all (fun j => g.read j == h.read j) &&
    keysToTest.all (fun k => lookup g p k == lookupMaps h c.rest k)

def checkAlias (h : Heap Nat Nat) (c : ChainMap) : Bool :=
  (List.range 4).all (fun i => smallRefs.all (fun refs =>
    keysToTest.all (fun k => keysToTest.all (fun v =>
      i != c.first || lookup (setItem h c k v) ⟨i, refs⟩ k == some v))))

-- One bounded PBT for EACH executable named property, without admitting proofs.
example : pbtInputs checkInit = true := by native_decide       -- init_prop
example : pbtInputs checkValid = true := by native_decide      -- valid_prop
example : pbtViews checkLookup = true := by native_decide      -- lookup_prop
example : pbtViews checkMissing = true := by native_decide     -- missing_prop
example : pbtViews checkShadow = true := by native_decide      -- shadow_prop
example : pbtViews checkGetItem = true := by native_decide     -- getItem_prop
example : pbtViews checkContains = true := by native_decide    -- contains_prop
example : pbtViews checkGet = true := by native_decide         -- get_prop
example : pbtViews checkIter = true := by native_decide        -- iter_prop
example : pbtViews checkLength = true := by native_decide      -- length_prop
example : pbtViews checkSet = true := by native_decide         -- set_prop
example : pbtViews checkDelete = true := by native_decide      -- delete_prop
example : pbtViews checkChild = true := by native_decide       -- child_prop
example : pbtViews checkParents = true := by native_decide     -- parents_prop
example : pbtViews checkAlias = true := by native_decide       -- alias_prop

def checkPost (h : Heap Nat Nat) (refs : List Nat) : Bool :=
  let (g, c) := init h refs
  checkInit h refs && checkValid h refs && checkLookup g c && checkMissing g c &&
  checkShadow g c && checkGetItem g c && checkContains g c && checkGet g c &&
  checkIter g c && checkLength g c && checkSet g c && checkDelete g c &&
  checkChild g c && checkParents g c && checkAlias g c

example : pbtInputs checkPost = true := by native_decide       -- Post_prop
#eval ("bounded postcondition", pbtInputs checkPost)

/-! ## Correctness: no test result is used in this proof -/

theorem correctness (h : Heap K V) (ids : List Nat) : Pre h ids → Post_prop h ids := by
  intro hp
  exact ⟨init_thm h ids, valid_thm h ids, valid_thm h ids hp,
    fun k v => lookup_thm _ _ k v, fun k => missing_thm _ _ k,
    fun k => shadow_thm _ _ k, fun k => getItem_thm _ _ k,
    fun k => contains_thm _ _ k, fun k d => get_thm _ _ k d,
    fun k => iter_thm _ _ k, length_thm _ _,
    fun k q v i => set_thm _ _ k q v i, fun k q i => delete_thm _ _ k q i,
    fun m k => child_thm _ _ m k, fun k => parents_thm _ _ k,
    fun observer k v => alias_thm _ _ observer k v⟩


/-! ## Imperative implementation

The recursive loops are structurally terminating versions of the Python loops.
Each `Id.run` block has local mutable state; the heap is returned explicitly so
that all existing view references continue to denote the same mapping objects.
-/

def initImp (h : Heap K V) (ids : List Nat) : Heap K V × ChainMap := Id.run do
  let mut heap := h
  let mut view : ChainMap := ⟨h.next, []⟩
  match ids with
  | [] => heap := (allocate heap []).1
  | i :: is => view := ⟨i, is⟩
  return (heap, view)

def scanImp (h : Heap K V) : List Nat → K → Option V
  | [], _ => Id.run do return none
  | i :: is, k => Id.run do
    let mut result := dictLookup k (h.read i)
    if result.isNone then
      result := scanImp h is k
    return result

def lookupImp (h : Heap K V) (c : ChainMap) (k : K) : Option V := Id.run do
  let mut result := none
  result := scanImp h c.maps k
  return result

def getItemImp (h : Heap K V) (c : ChainMap) (k : K) : Except (KeyError K) V := Id.run do
  let mut result : Except (KeyError K) V := .error (.missing k)
  match lookupImp h c k with
  | some v => result := .ok v
  | none => pure ()
  return result

def containsImp (h : Heap K V) (c : ChainMap) (k : K) : Bool := Id.run do
  let mut found := false
  found := (scanImp h c.maps k).isSome
  return found

def getImp (h : Heap K V) (c : ChainMap) (k : K) (default : Option V := none) : Option V := Id.run do
  let mut result := default
  if containsImp h c k then
    result := lookupImp h c k
  return result

/-- Mutable accumulation while traversing the reversed list of mapping objects. -/
def collectKeysImp (h : Heap K V) : List Nat → List K → List K
  | [], acc => Id.run do return acc
  | i :: is, acc => Id.run do
    let mut keys := acc
    keys := keys ++ dictKeys (h.read i)
    keys := collectKeysImp h is keys
    return keys

def iterImp (h : Heap K V) (c : ChainMap) : List K := Id.run do
  let mut keys := []
  keys := collectKeysImp h c.maps.reverse keys
  keys := orderedUnique keys
  return keys

def lengthImp (h : Heap K V) (c : ChainMap) : Nat := Id.run do
  let mut n := 0
  n := (iterImp h c).length
  return n

def newChildImp (h : Heap K V) (c : ChainMap) (m : Option Nat := none) : Heap K V × ChainMap := Id.run do
  let mut heap := h
  let mut view := c
  match m with
  | some i => view := ⟨i, c.maps⟩
  | none =>
    let (g, i) := allocate heap []
    heap := g
    view := ⟨i, c.maps⟩
  return (heap, view)

def parentsImp (h : Heap K V) (c : ChainMap) : Heap K V × ChainMap := Id.run do
  let mut refs := c.maps
  refs := refs.drop 1
  return initImp h refs

def setItemImp (h : Heap K V) (c : ChainMap) (k : K) (v : V) : Heap K V := Id.run do
  let mut heap := h
  let mut front := heap.read c.first
  front := dictSet k v front
  heap := writeMap heap c.first front
  return heap

def delItemImp (h : Heap K V) (c : ChainMap) (k : K) : Except (KeyError K) (Heap K V) := Id.run do
  let mut heap := h
  let mut front := heap.read c.first
  if (dictLookup k front).isSome then
    front := dictErase k front
    heap := writeMap heap c.first front
    return .ok heap
  else
    return .error (.notInFirst k)

/-! ## Imperative tests -/

def imperativeSourceTests : Bool := Id.run do
  let (h, c) := initImp demoHeap [0, 1]
  let mut heap := h
  let mut ok := lookupImp heap c "a" == some 1 && lookupImp heap c "c" == some 4
  ok := ok && lookupImp heap c "b" == some 2
  heap := setItemImp heap c "c" 5
  ok := ok && dictLookup "c" (heap.read 0) == some 5 && dictLookup "c" (heap.read 1) == some 4
  let (g, i) := allocate heap [("d", 6)]
  let (g2, ch) := newChildImp g c (some i)
  ok := ok && lookupImp g2 ch "a" == some 1 && lookupImp g2 ch "d" == some 6
  ok := ok && g2.read ch.first == [("d", 6)] && g2.read (ch.rest.headD 99) == heap.read 0
  let (gp, p) := parentsImp heap c
  ok := ok && lookupImp gp p "b" == some 3 && !(containsImp gp p "a")
  return ok

example : imperativeSourceTests = true := by native_decide
example : iterImp demoHeap cm = ["b", "c", "a"] := by native_decide
example : lengthImp demoHeap cm = 3 := by native_decide
example : getImp demoHeap cm "absent" (some 10) = some 10 := by native_decide
example : (match getItemImp demoHeap cm "absent" with
  | .error (.missing "absent") => true | _ => false) = true := by native_decide
example : (match delItemImp demoHeap cm "b" with
  | .ok h => lookupImp h cm "b" == some 3 | _ => false) = true := by native_decide
example : (match delItemImp demoHeap cm "c" with
  | .error (.notInFirst "c") => true | _ => false) = true := by native_decide
-- Repeated references: deleting the shared object must not reveal its old value.
example : (match delItemImp demoHeap ⟨0, [0, 1]⟩ "b" with
  | .ok h => lookupImp h ⟨0, [0, 1]⟩ "b" == some 3 | _ => false) = true := by native_decide
example : (parentsImp demoHeap ⟨0, []⟩).2.maps = [2] := by native_decide
example : (newChildImp demoHeap cm).2.maps = [2, 0, 1] := by native_decide
#eval imperativeSourceTests
#eval (iterImp demoHeap cm, lengthImp demoHeap cm)

/-! ## Kernel-checked equivalence of every public method -/

lemma scanImp_eq (h : Heap K V) (ids : List Nat) (k : K) :
    scanImp h ids k = lookupMaps h ids k := by
  induction ids with
  | nil => rfl
  | cons i ids ih =>
    cases e : dictLookup k (h.read i) <;> simp [scanImp, lookupMaps, e, ih]

lemma collectKeysImp_eq (h : Heap K V) (ids : List Nat) (acc : List K) :
    collectKeysImp h ids acc = acc ++ ids.flatMap (fun i => dictKeys (h.read i)) := by
  induction ids generalizing acc with
  | nil => simp [collectKeysImp]
  | cons i ids ih => simp [collectKeysImp, ih, List.append_assoc]

lemma initImp_eq (h : Heap K V) (ids : List Nat) : initImp h ids = init h ids := by
  cases ids <;> rfl

lemma lookupImp_eq (h : Heap K V) (c : ChainMap) (k : K) :
    lookupImp h c k = lookup h c k := scanImp_eq h c.maps k

lemma getItemImp_eq (h : Heap K V) (c : ChainMap) (k : K) :
    getItemImp h c k = getItem h c k := by
  simp only [getItemImp, lookupImp_eq, getItem]
  cases lookup h c k <;> rfl

lemma containsImp_eq (h : Heap K V) (c : ChainMap) (k : K) :
    containsImp h c k = contains h c k := by
  change (scanImp h c.maps k).isSome = contains h c k
  rw [scanImp_eq]
  exact (contains_thm h c k).symm

lemma getImp_eq (h : Heap K V) (c : ChainMap) (k : K) (d : Option V) :
    getImp h c k d = get h c k d := by
  cases hc : contains h c k <;> simp [getImp, get, containsImp_eq, lookupImp_eq, hc]

lemma iterImp_eq (h : Heap K V) (c : ChainMap) : iterImp h c = iter h c := by
  simp [iterImp, collectKeysImp_eq, iter]

lemma lengthImp_eq (h : Heap K V) (c : ChainMap) : lengthImp h c = length h c := by
  simp [lengthImp, length, iterImp_eq]

lemma newChildImp_eq (h : Heap K V) (c : ChainMap) (m : Option Nat) :
    newChildImp h c m = newChild h c m := by
  cases m <;> rfl

lemma parentsImp_eq (h : Heap K V) (c : ChainMap) : parentsImp h c = parents h c := by
  change initImp h c.rest = init h c.rest
  exact initImp_eq h c.rest

lemma setItemImp_eq (h : Heap K V) (c : ChainMap) (k : K) (v : V) :
    setItemImp h c k v = setItem h c k v := rfl

lemma delItemImp_eq (h : Heap K V) (c : ChainMap) (k : K) :
    delItemImp h c k = delItem h c k := by
  cases e : dictLookup k (h.read c.first) <;> simp [delItemImp, delItem, e]

/-- Equality includes the returned heaps themselves, not merely sampled lookups.
Consequently it also preserves every future operation through any shared view. -/
theorem equivalence_thm (h : Heap K V) (ids : List Nat) (c : ChainMap)
    (k : K) (v : V) (d : Option V) (m : Option Nat) :
    init h ids = initImp h ids ∧
    lookup h c k = lookupImp h c k ∧ getItem h c k = getItemImp h c k ∧
    contains h c k = containsImp h c k ∧ get h c k d = getImp h c k d ∧
    iter h c = iterImp h c ∧ length h c = lengthImp h c ∧
    newChild h c m = newChildImp h c m ∧ parents h c = parentsImp h c ∧
    setItem h c k v = setItemImp h c k v ∧ delItem h c k = delItemImp h c k := by
  simp only [initImp_eq, lookupImp_eq, getItemImp_eq, containsImp_eq, getImp_eq,
    iterImp_eq, lengthImp_eq, newChildImp_eq, parentsImp_eq, setItemImp_eq,
    delItemImp_eq, and_self]

#print axioms correctness
#print axioms equivalence_thm

end CollectionsChainMap
end Agent
