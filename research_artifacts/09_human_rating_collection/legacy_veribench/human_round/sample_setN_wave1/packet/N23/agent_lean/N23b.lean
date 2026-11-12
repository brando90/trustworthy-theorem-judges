import Mathlib

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 400000

/-!
# VeriBench 31 — `statistics.quantiles` (Python standard library)

Formalization of the Python program

```python
def quantiles(data, n=4, method='exclusive'):
    if n < 1: raise StatisticsError('n must be at least 1')
    data = sorted(data); ld = len(data)
    if ld < 2: raise StatisticsError('must have at least two data points')
    if method == 'inclusive':
        m = ld - 1
        for i in range(1, n):
            j, delta = divmod(i * m, n)
            result.append((data[j] * (n - delta) + data[j + 1] * delta) / n)
    if method == 'exclusive':
        m = ld + 1
        for i in range(1, n):
            j = i * m // n
            j = 1 if j < 1 else ld-1 if j > ld-1 else j
            delta = i*m - j*n
            result.append((data[j - 1] * (n - delta) + data[j] * delta) / n)
    raise ValueError(f'Unknown method: {method!r}')
```

## Numeric layers

* `Rat` is the **exact mathematical layer**: every index computation of the Python source is
  exact integer arithmetic (`//`, `divmod`, `-`) and the only inexact step in the source is the
  final division, which is exact in `Rat` (Python returns `Fraction`s exactly this way when the
  input consists of `int`/`Fraction`).  All properties, the pre/post-condition and the
  functional-imperative equivalence are stated and *proved* here.
* `FloatLayer` mirrors the IEEE-754 `float` behaviour of the Python source on concrete inputs;
  primitive `Float` arithmetic is opaque to the kernel, so that layer is exercised with `#eval`
  and `native_decide` unit tests (no general theorem is claimed about it).
* `RealLayer` re-states the exact cut points in `Real` through the canonical embedding
  `Rat → Real` (the `Real`-valued properties are the images of the proved `Rat` theorems).

The Python pre-condition `pre(data, n, method)` requires `data` to be a list/tuple (automatic for
`data : List Rat`), `len data ≥ 2`, `n ≥ 1` and `method ∈ {inclusive, exclusive}` (automatic for
`method : Method`; the string-level entry point `quantilesStr` models the `ValueError` raised for
an unknown method name).
-/

namespace StatisticsQuantiles

open List

/-! ## 1. The `method` argument -/

/-- The two admissible values of the Python `method` keyword argument. -/
inductive Method
  | exclusive
  | inclusive
  deriving DecidableEq, Repr, Inhabited

/-- Parsing of the Python string argument; `none` models `ValueError: Unknown method`. -/
def Method.ofString (s : String) : Option Method :=
  match s with
  | "exclusive" => some Method.exclusive
  | "inclusive" => some Method.inclusive
  | _ => none

/-! ## 2. `sorted(data)` -/

/-- Boolean comparator used by the merge sort that models Python's `sorted`. -/
def ratLe (a b : Rat) : Bool := decide (a ≤ b)

/-- `sorted(data)`. -/
def sortData (l : List Rat) : List Rat := l.mergeSort ratLe

lemma ratLe_true {a b : Rat} : ratLe a b = true ↔ a ≤ b := by simp [ratLe]

theorem sortData_length (l : List Rat) : (sortData l).length = l.length := List.length_mergeSort _

theorem sortData_pairwise (l : List Rat) : (sortData l).Pairwise (· ≤ ·) := by
  have tr : ∀ a b c : Rat, ratLe a b = true → ratLe b c = true → ratLe a c = true := by
    intro a b c h1 h2
    rw [ratLe_true] at h1 h2 ⊢
    exact le_trans h1 h2
  have tot : ∀ a b : Rat, (ratLe a b || ratLe b a) = true := by
    intro a b
    rw [Bool.or_eq_true, ratLe_true, ratLe_true]
    exact le_total a b
  refine (List.sorted_mergeSort tr tot l).imp ?_
  intro a b h
  exact ratLe_true.mp h

/-- Two sorted permutations of each other are equal. -/
lemma eq_of_pairwise_of_perm {l l' : List Rat} (h : l.Pairwise (· ≤ ·)) (h' : l'.Pairwise (· ≤ ·))
    (p : l.Perm l') : l = l' := by
  induction l generalizing l' with
  | nil =>
      have hM : (↑([] : List Rat) : Multiset Rat) = ↑l' := Multiset.coe_eq_coe.mpr p
      have hl' : l' = [] := (Multiset.coe_eq_zero l').mp (by simpa using hM.symm)
      subst hl'; rfl
  | cons a l ih =>
      obtain ⟨ha, hl⟩ := List.pairwise_cons.mp h
      have hM : (↑(a :: l) : Multiset Rat) = ↑l' := Multiset.coe_eq_coe.mpr p
      cases l' with
      | nil =>
          have hz : (↑(a :: l) : Multiset Rat) = 0 := hM
          simp at hz
      | cons b l'' =>
          obtain ⟨hb, hl''⟩ := List.pairwise_cons.mp h'
          have hM2 : ({a} : Multiset Rat) + ↑l = {b} + ↑l'' := by
            have := hM
            simp at this ⊢
            exact this
          have h1 : a ≤ b := by
            by_cases hmem : b ∈ l
            · exact ha b hmem
            · have hb' : b ∈ ({a} : Multiset Rat) + ↑l := by
                rw [hM2]
                exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton.mpr rfl))
              rw [Multiset.mem_add, Multiset.mem_singleton, Multiset.mem_coe] at hb'
              rcases hb' with e | e
              · exact le_of_eq e.symm
              · exact absurd e hmem
          have h2 : b ≤ a := by
            by_cases hmem : a ∈ l''
            · exact hb a hmem
            · have ha' : a ∈ ({b} : Multiset Rat) + ↑l'' := by
                rw [← hM2]
                exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton.mpr rfl))
              rw [Multiset.mem_add, Multiset.mem_singleton, Multiset.mem_coe] at ha'
              rcases ha' with e | e
              · exact le_of_eq e.symm
              · exact absurd e hmem
          have hab : a = b := le_antisymm h1 h2
          subst hab
          have hll : (↑l : Multiset Rat) = ↑l'' := add_left_cancel hM2
          exact congrArg (List.cons a) (ih hl hl'' (Multiset.coe_eq_coe.mp hll))

/-- `sorted` only depends on the multiset of the data (Python test 7: unsorted input). -/
theorem sortData_perm {l l' : List Rat} (h : l.Perm l') : sortData l = sortData l' :=
  eq_of_pairwise_of_perm (sortData_pairwise l) (sortData_pairwise l')
    (List.Perm.trans (List.mergeSort_perm l ratLe)
      (List.Perm.trans h (List.Perm.symm (List.mergeSort_perm l' ratLe))))

/-- Sorting an already sorted list is the identity. -/
theorem sortData_id {l : List Rat} (h : l.Pairwise (· ≤ ·)) : sortData l = l := by
  have p : sortData l ~ l := List.mergeSort_perm l ratLe
  exact eq_of_pairwise_of_perm (sortData_pairwise l) h p

/-! ## 3. List helpers -/

lemma getD_mem {α : Type} {l : List α} {i : Nat} (d : α) (h : i < l.length) : l.getD i d ∈ l := by
  induction l generalizing i with
  | nil => exact absurd h (by simp)
  | cons a l ih =>
    simp only [List.length_cons] at h
    cases i with
    | zero => rw [List.getD_cons_zero]; exact List.mem_cons_self
    | succ i =>
      rw [List.getD_cons_succ]
      exact List.mem_cons.mpr (Or.inr (ih (by omega)))

lemma Pairwise_getD_le {l : List Rat} (h : l.Pairwise (· ≤ ·)) {i j : Nat} (d : Rat)
    (hij : i ≤ j) (hj : j < l.length) : l.getD i d ≤ l.getD j d := by
  induction l generalizing i j with
  | nil => exact absurd hj (by simp)
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.pairwise_cons.mp h
    simp only [List.length_cons] at hj
    cases i with
    | zero =>
      cases j with
      | zero => simp
      | succ j =>
        rw [List.getD_cons_zero, List.getD_cons_succ]
        exact ha _ (getD_mem d (by omega))
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        rw [List.getD_cons_succ, List.getD_cons_succ]
        exact ih hl (by omega) (by omega)

lemma getD_map_of_lt {α β : Type} (f : α → β) {l : List α} {k : Nat} (b : β) (c : α)
    (hk : k < l.length) : (l.map f).getD k b = f (l.getD k c) := by
  induction l generalizing k with
  | nil => exact absurd hk (by simp)
  | cons a l ih =>
    simp only [List.length_cons] at hk
    cases k with
    | zero => simp [List.map]
    | succ k =>
      have := ih (by omega : k < l.length)
      simp only [List.map_cons, List.getD_cons_succ] at this ⊢
      exact this

/-- `Pairwise` for a monotone function applied to `List.range`. -/
lemma Pairwise_map_range {f : Nat → Rat} {m : Nat}
    (h : ∀ i j, i < j → j < m → f i ≤ f j) :
    ((List.range m).map f).Pairwise (· ≤ ·) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.pairwise_append]
    refine ⟨ih (fun i j hij hj => h i j hij (Nat.lt_succ_of_lt hj)), List.pairwise_singleton _ _, ?_⟩
    intro x hx y hy
    rw [List.mem_map] at hy; obtain ⟨j, hj, rfl⟩ := hy
    have hjm : j = m := by simpa using hj
    rw [List.mem_map] at hx; obtain ⟨i, hi, rfl⟩ := hx
    rw [List.mem_range] at hi
    exact h i j (by omega) (by omega)

/-! ## 4. Functional implementation (exact rational layer) -/

/-- `j = 1 if j < 1 else ld-1 if j > ld-1 else j` — the clamping of the exclusive method. -/
def clampJ (q ld : Nat) : Nat := if q < 1 then 1 else if ld - 1 < q then ld - 1 else q

/-- The clamp is `min (max q 1) (ld - 1)` whenever `2 ≤ ld`. -/
lemma clampJ_eq (q ld : Nat) (h : 2 ≤ ld) : clampJ q ld = min (max q 1) (ld - 1) := by
  unfold clampJ
  split_ifs with h1 h2 <;> omega

lemma clampJ_bounds {q ld : Nat} (h : 2 ≤ ld) : 1 ≤ clampJ q ld ∧ clampJ q ld ≤ ld - 1 := by
  rw [clampJ_eq q ld h]
  constructor <;> omega

lemma clampJ_mono {q₁ q₂ ld : Nat} (hld : 2 ≤ ld) (h : q₁ ≤ q₂) : clampJ q₁ ld ≤ clampJ q₂ ld := by
  rw [clampJ_eq q₁ ld hld, clampJ_eq q₂ ld hld]
  exact min_le_min (max_le_max h (le_refl 1)) (le_refl _)

/-- `j` of the *exclusive* method: `j = i * (ld+1) // n` clamped to `1 .. ld-1`. -/
def exclJ (s : List Rat) (n i : Nat) : Nat := clampJ (i * (s.length + 1) / n) s.length

/-- `delta = i*m - j*n` of the *exclusive* method (`m = ld + 1`), exact integer arithmetic.
It may be negative (the exclusive method extrapolates below `data[0]`). -/
def exclD (s : List Rat) (n i : Nat) : Int :=
  ((i * (s.length + 1) : Nat) : Int) - ((exclJ s n i * n : Nat) : Int)

/-- `(data[j-1] * (n - delta) + data[j] * delta) / n` — exclusive cut point. -/
def exclPoint (s : List Rat) (n i : Nat) : Rat :=
  (s.getD (exclJ s n i - 1) 0 * ((n : Rat) - (exclD s n i : Rat))
      + s.getD (exclJ s n i) 0 * (exclD s n i : Rat)) / (n : Rat)

/-- `j, delta = divmod(i * (ld-1), n)` of the *inclusive* method: the quotient. -/
def inclJ (s : List Rat) (n i : Nat) : Nat := i * (s.length - 1) / n

/-- The remainder `delta` of the *inclusive* method. -/
def inclD (s : List Rat) (n i : Nat) : Int :=
  ((i * (s.length - 1) : Nat) : Int) - ((inclJ s n i * n : Nat) : Int)

/-- `(data[j] * (n - delta) + data[j+1] * delta) / n` — inclusive cut point. -/
def inclPoint (s : List Rat) (n i : Nat) : Rat :=
  (s.getD (inclJ s n i) 0 * ((n : Rat) - (inclD s n i : Rat))
      + s.getD (inclJ s n i + 1) 0 * (inclD s n i : Rat)) / (n : Rat)

/-- The `i`-th cut point for the requested method. -/
def point (s : List Rat) (n i : Nat) (m : Method) : Rat :=
  match m with
  | Method.exclusive => exclPoint s n i
  | Method.inclusive => inclPoint s n i

/-- `result` of the Python source: the `n - 1` cut points for `i = 1, …, n-1`,
computed on the already sorted list `s`. -/
def cutPoints (s : List Rat) (n : Nat) (m : Method) : List Rat :=
  (List.range (n - 1)).map (fun k => point s n (k + 1) m)

/-- The pre-condition of the Python `pre` function: `data` has at least two points and `n ≥ 1`.
(The other two checks of `pre` — `isinstance(data, (list, tuple))` and
`method in ('inclusive','exclusive')` — are automatic for `data : List Rat` and `m : Method`.) -/
def Pre (data : List Rat) (n : Nat) (m : Method) : Prop :=
  2 ≤ data.length ∧ 1 ≤ n ∧ (m = Method.exclusive ∨ m = Method.inclusive)

/-- Every `Method` value is admissible (`method in ('inclusive','exclusive')`). -/
lemma method_valid (m : Method) : m = Method.exclusive ∨ m = Method.inclusive := by
  cases m <;> simp

lemma pre_mk {data : List Rat} {n : Nat} (h1 : 2 ≤ data.length) (h2 : 1 ≤ n) (m : Method) :
    Pre data n m := ⟨h1, h2, method_valid m⟩

lemma Pre.guard {data : List Rat} {n : Nat} {m : Method} (h : Pre data n m) :
    2 ≤ data.length ∧ 1 ≤ n := ⟨h.1, h.2.1⟩

/-- `benchmark_quantiles`: returns `none` where the Python source raises `StatisticsError`. -/
def quantiles (data : List Rat) (n : Nat) (m : Method) : Option (List Rat) :=
  if 2 ≤ data.length ∧ 1 ≤ n then some (cutPoints (sortData data) n m) else none

/-- The Python entry point with the method given as a string; `Except.error` models the raised
`StatisticsError` / `ValueError`. -/
def quantilesStr (data : List Rat) (n : Nat) (ms : String) : Except String (List Rat) :=
  match Method.ofString ms with
  | Option.none => Except.error ("Unknown method: " ++ ms)
  | Option.some m =>
      if 2 ≤ data.length ∧ 1 ≤ n then Except.ok (cutPoints (sortData data) n m)
      else Except.error "benchmark_quantiles requires at least 2 data points and n >= 1"

/-- Smallest and largest data value (of the sorted data). -/
def lo (data : List Rat) : Rat := (sortData data).getD 0 0
def hi (data : List Rat) : Rat := (sortData data).getD (data.length - 1) 0

/-- The median of the data (the single cut point produced for `n = 2`). -/
def median (data : List Rat) : Rat :=
  let s := sortData data
  let ld := s.length
  if ld % 2 = 0 then (s.getD (ld / 2 - 1) 0 + s.getD (ld / 2) 0) / 2 else s.getD (ld / 2) 0

/-! ## 5. Unit tests (ground truth taken from CPython's `statistics.quantiles`) -/

#eval quantiles [1, 2, 3, 4] 4 Method.exclusive
#eval quantiles [1, 2, 3, 4] 4 Method.inclusive
#eval quantiles [4, 1, 3, 2] 4 Method.exclusive
#eval quantiles (List.range 11) 10 Method.exclusive
#eval quantiles [1, 2, 3, 4, 5] 2 Method.exclusive
#eval quantiles [3/2, 5/2, 7/2, 9/2] 2 Method.inclusive
#eval quantiles [1] 4 Method.exclusive
#eval quantiles [1, 2] 0 Method.exclusive
#eval quantilesStr [1, 2, 3] 4 "invalid"

-- Python test 1: `quantiles([1,2,3,4]) == [1.25, 2.5, 3.75]`
example : quantiles [1, 2, 3, 4] 4 Method.exclusive = some [5/4, 5/2, 15/4] := by native_decide
-- Python test 4: inclusive quartiles of `[1,2,3,4]` are `[1.75, 2.5, 3.25]`
example : quantiles [1, 2, 3, 4] 4 Method.inclusive = some [7/4, 5/2, 13/4] := by native_decide
-- Python test 2: deciles of `range(11)`
example : quantiles (List.range 11) 10 Method.exclusive =
    some [1/5, 7/5, 13/5, 19/5, 5, 31/5, 37/5, 43/5, 49/5] := by native_decide
-- Python test 3: median for `n = 2`
example : quantiles [1, 2, 3, 4, 5] 2 Method.exclusive = some [3] := by native_decide
-- Python test 6: larger dataset
example : quantiles (List.range' 1 10) 4 Method.exclusive = some [11/4, 11/2, 33/4] := by native_decide
-- Python test 7: unsorted input is sorted internally
example : quantiles [4, 1, 3, 2] 4 Method.exclusive = quantiles [1, 2, 3, 4] 4 Method.exclusive := by
  native_decide
-- Python test 8: float data (modelled exactly as rationals)
example : quantiles [3/2, 5/2, 7/2, 9/2] 2 Method.exclusive = some [3] := by native_decide
-- Python test 9: error cases
example : quantiles [1] 4 Method.exclusive = none := by native_decide
example : quantiles [1, 2] 0 Method.exclusive = none := by native_decide
example : quantilesStr [1, 2, 3] 4 "invalid" = Except.error "Unknown method: invalid" := by
  simp [quantilesStr, Method.ofString]

example : (quantilesStr [1, 2, 3] 4 "inclusive").toOption = some [3/2, 2, 5/2] := by native_decide
example : (quantilesStr [1] 4 "exclusive").toOption = (none : Option (List Rat)) := by native_decide
example : (quantilesStr [1, 2, 3] 0 "exclusive").toOption = (none : Option (List Rat)) := by
  native_decide

theorem quartiles_doctest : quantiles [1, 2, 3, 4] 4 Method.exclusive = some [5/4, 5/2, 15/4] := by
  have hs : sortData ([1, 2, 3, 4] : List Rat) = [1, 2, 3, 4] := sortData_id (by decide)
  have hpre : 2 ≤ ([1, 2, 3, 4] : List Rat).length ∧ 1 ≤ 4 := by decide
  have hr : List.range (4 - 1) = [0, 1, 2] := by decide
  have e1 : point ([1, 2, 3, 4] : List Rat) 4 1 Method.exclusive = 5/4 := by
    simp [point, exclPoint, inclPoint, exclJ, inclJ, exclD, inclD, clampJ]
    norm_num
  have e2 : point ([1, 2, 3, 4] : List Rat) 4 2 Method.exclusive = 5/2 := by
    simp [point, exclPoint, inclPoint, exclJ, inclJ, exclD, inclD, clampJ]
    norm_num
  have e3 : point ([1, 2, 3, 4] : List Rat) 4 3 Method.exclusive = 15/4 := by
    simp [point, exclPoint, inclPoint, exclJ, inclJ, exclD, inclD, clampJ]
    norm_num
  rw [quantiles, if_pos hpre, hs, cutPoints, hr]
  simp [e1, e2, e3]

theorem quartiles_inclusive_doctest :
    quantiles [1, 2, 3, 4] 4 Method.inclusive = some [7/4, 5/2, 13/4] := by
  have hs : sortData ([1, 2, 3, 4] : List Rat) = [1, 2, 3, 4] := sortData_id (by decide)
  have hpre : 2 ≤ ([1, 2, 3, 4] : List Rat).length ∧ 1 ≤ 4 := by decide
  have hr : List.range (4 - 1) = [0, 1, 2] := by decide
  have e1 : point ([1, 2, 3, 4] : List Rat) 4 1 Method.inclusive = 7/4 := by
    simp [point, exclPoint, inclPoint, exclJ, inclJ, exclD, inclD, clampJ]
    norm_num
  have e2 : point ([1, 2, 3, 4] : List Rat) 4 2 Method.inclusive = 5/2 := by
    simp [point, exclPoint, inclPoint, exclJ, inclJ, exclD, inclD, clampJ]
    norm_num
  have e3 : point ([1, 2, 3, 4] : List Rat) 4 3 Method.inclusive = 13/4 := by
    simp [point, exclPoint, inclPoint, exclJ, inclJ, exclD, inclD, clampJ]
    norm_num
  rw [quantiles, if_pos hpre, hs, cutPoints, hr]
  simp [e1, e2, e3]

/-- Python test 7: the input is sorted internally, so the order does not matter. -/
theorem unsorted_doctest : quantiles [4, 1, 3, 2] 4 Method.exclusive = some [5/4, 5/2, 15/4] := by
  have hs : sortData ([4, 1, 3, 2] : List Rat) = [1, 2, 3, 4] := by
    rw [sortData_perm (by decide : ([4, 1, 3, 2] : List Rat).Perm [1, 2, 3, 4])]
    exact sortData_id (by decide)
  have hpre : 2 ≤ ([4, 1, 3, 2] : List Rat).length ∧ 1 ≤ 4 := by decide
  have hr : List.range (4 - 1) = [0, 1, 2] := by decide
  have e1 : point ([1, 2, 3, 4] : List Rat) 4 1 Method.exclusive = 5/4 := by
    simp [point, exclPoint, inclPoint, exclJ, inclJ, exclD, inclD, clampJ]
    norm_num
  have e2 : point ([1, 2, 3, 4] : List Rat) 4 2 Method.exclusive = 5/2 := by
    simp [point, exclPoint, inclPoint, exclJ, inclJ, exclD, inclD, clampJ]
    norm_num
  have e3 : point ([1, 2, 3, 4] : List Rat) 4 3 Method.exclusive = 15/4 := by
    simp [point, exclPoint, inclPoint, exclJ, inclJ, exclD, inclD, clampJ]
    norm_num
  rw [quantiles, if_pos hpre, hs, cutPoints, hr]
  simp [e1, e2, e3]

/-- The exclusive method extrapolates outside the data range for small samples:
`quantiles([1,2], n=4) == [0.75, 1.5, 2.25]`. -/
theorem extrapolation_doctest : quantiles [1, 2] 4 Method.exclusive = some [3/4, 3/2, 9/4] := by
  have hs : sortData ([1, 2] : List Rat) = [1, 2] := sortData_id (by decide)
  have hpre : 2 ≤ ([1, 2] : List Rat).length ∧ 1 ≤ 4 := by decide
  have hr : List.range (4 - 1) = [0, 1, 2] := by decide
  have e1 : point ([1, 2] : List Rat) 4 1 Method.exclusive = 3/4 := by
    simp [point, exclPoint, inclPoint, exclJ, inclJ, exclD, inclD, clampJ]
    norm_num
  have e2 : point ([1, 2] : List Rat) 4 2 Method.exclusive = 3/2 := by
    simp [point, exclPoint, inclPoint, exclJ, inclJ, exclD, inclD, clampJ]
    norm_num
  have e3 : point ([1, 2] : List Rat) 4 3 Method.exclusive = 9/4 := by
    simp [point, exclPoint, inclPoint, exclJ, inclJ, exclD, inclD, clampJ]
    norm_num
  rw [quantiles, if_pos hpre, hs, cutPoints, hr]
  simp [e1, e2, e3]

/-- `n = 1` produces no cut point at all. -/
theorem one_interval_doctest : quantiles [1, 2, 3] 1 Method.exclusive = some [] := by
  have hpre : 2 ≤ ([1, 2, 3] : List Rat).length ∧ 1 ≤ 1 := by decide
  rw [quantiles, if_pos hpre, cutPoints]
  rfl

/-! ## 6. Pre-condition -/

instance (data : List Rat) (n : Nat) (m : Method) : Decidable (Pre data n m) :=
  inferInstanceAs
    (Decidable (2 ≤ data.length ∧ 1 ≤ n ∧ (m = Method.exclusive ∨ m = Method.inclusive)))

/-- The Python `pre` function; the `isinstance(data, (list, tuple))` test is automatic for a
`List Rat`, and the method test is `Method.ofString ms ≠ none`. -/
def preStr (data : List Rat) (n : Nat) (ms : String) : Bool :=
  decide (2 ≤ data.length) && decide (1 ≤ n) && (Method.ofString ms).isSome

theorem preStr_sound (data : List Rat) (n : Nat) (ms : String) :
    preStr data n ms = true → 2 ≤ data.length ∧ 1 ≤ n := by
  intro h
  simp only [preStr, Bool.and_eq_true, decide_eq_true_iff] at h
  exact ⟨h.1.1, h.1.2⟩

theorem preStr_complete (data : List Rat) (n : Nat) (ms : String) (m : Method)
    (h : Pre data n m) (hms : Method.ofString ms = some m) : preStr data n ms = true := by
  simp only [preStr, Bool.and_eq_true, decide_eq_true_iff]
  exact ⟨⟨h.1, h.2.1⟩, by rw [hms]; rfl⟩

example : preStr [1, 2, 3] 4 "exclusive" = true := by decide
example : preStr [1, 2, 3] 4 "inclusive" = true := by decide
example : preStr [1] 4 "exclusive" = false := by decide
example : preStr [1, 2, 3] 0 "exclusive" = false := by decide
example : preStr [1, 2, 3] 4 "invalid" = false := by decide

theorem quantilesStr_invalid (data : List Rat) (n : Nat) :
    quantilesStr data n "invalid" = Except.error "Unknown method: invalid" := by
  simp [quantilesStr, Method.ofString]

theorem quantilesStr_exclusive (data : List Rat) (n : Nat) (h : Pre data n Method.exclusive) :
    quantilesStr data n "exclusive" = Except.ok (cutPoints (sortData data) n Method.exclusive) := by
  have hguard : 2 ≤ data.length ∧ 1 ≤ n := ⟨h.1, h.2.1⟩
  simp only [quantilesStr, Method.ofString]
  rw [if_pos hguard]

theorem quantilesStr_error (data : List Rat) (n : Nat)
    (h : ¬(2 ≤ data.length ∧ 1 ≤ n)) :
    quantilesStr data n "inclusive" =
      Except.error "benchmark_quantiles requires at least 2 data points and n >= 1" := by
  simp only [quantilesStr, Method.ofString, if_neg h]

/-! ## 7. Arithmetic of the index / delta computations -/

lemma exclJ_bounds (s : List Rat) (n i : Nat) (hld : 2 ≤ s.length) :
    1 ≤ exclJ s n i ∧ exclJ s n i ≤ s.length - 1 := clampJ_bounds hld

/-- The three possible outcomes of the clamping. -/
lemma exclJ_trichotomy (s : List Rat) (n i : Nat) :
    exclJ s n i = i * (s.length + 1) / n ∨
    (i * (s.length + 1) / n < 1 ∧ exclJ s n i = 1) ∨
    (s.length - 1 < i * (s.length + 1) / n ∧ exclJ s n i = s.length - 1) := by
  by_cases h1 : i * (s.length + 1) / n < 1
  · exact Or.inr (Or.inl ⟨h1, by simp [exclJ, clampJ, h1]⟩)
  · by_cases h2 : s.length - 1 < i * (s.length + 1) / n
    · exact Or.inr (Or.inr ⟨h2, by simp [exclJ, clampJ, h1, h2]⟩)
    · exact Or.inl (by simp [exclJ, clampJ, h1, h2])

lemma exclJ_mono (s : List Rat) (n : Nat) {i k : Nat} (hld : 2 ≤ s.length) (hik : i ≤ k) :
    exclJ s n i ≤ exclJ s n k :=
  clampJ_mono hld (Nat.div_le_div_right (Nat.mul_le_mul_right _ hik))

/-- Without clamping, `delta` is the remainder `i*m % n`. -/
lemma exclD_eq_mod (s : List Rat) {n i : Nat} (h : exclJ s n i = i * (s.length + 1) / n) :
    exclD s n i = (i * (s.length + 1) % n : Nat) := by
  have hle : i * (s.length + 1) / n * n ≤ i * (s.length + 1) := by
    rw [Nat.mul_comm]; exact Nat.mul_div_le _ _
  have hsub : i * (s.length + 1) - i * (s.length + 1) / n * n = i * (s.length + 1) % n := by
    have e : i * (s.length + 1) / n * n + i * (s.length + 1) % n = i * (s.length + 1) := by
      rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
    exact Nat.sub_eq_of_eq_add (e.symm.trans (Nat.add_comm _ _))
  simp only [exclD, h]
  rw [← Nat.cast_sub hle, hsub]

lemma exclD_nonneg (s : List Rat) {n i : Nat} (h : exclJ s n i = i * (s.length + 1) / n) :
    0 ≤ exclD s n i := by
  rw [exclD_eq_mod s h]
  exact Int.ofNat_le.mpr (Nat.zero_le _)

lemma exclD_lt (s : List Rat) {n i : Nat} (hn : 1 ≤ n)
    (h : exclJ s n i = i * (s.length + 1) / n) : exclD s n i < (n : Int) := by
  rw [exclD_eq_mod s h]
  exact_mod_cast Nat.mod_lt _ (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)

/-- Lower clamping (`j = 1`) makes `delta` negative: the exclusive method extrapolates. -/
lemma exclD_neg (s : List Rat) {n i : Nat} (hn : 1 ≤ n) (h : i * (s.length + 1) / n < 1) :
    exclJ s n i = 1 ∧ exclD s n i < 0 := by
  have hJ : exclJ s n i = 1 := by simp [exclJ, clampJ, h]
  have hA : i * (s.length + 1) < n := by
    have := (Nat.div_lt_iff_lt_mul (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)).mp h
    simpa using this
  have hA' : ((i * (s.length + 1) : Nat) : Int) < (n : Int) := Int.ofNat_lt.mpr hA
  refine ⟨hJ, ?_⟩
  simp only [exclD, hJ, Nat.one_mul]
  linarith

/-- Upper clamping (`j = ld - 1`) makes `delta ≥ n`: extrapolation above the last point. -/
lemma exclD_ge (s : List Rat) {n i : Nat} (hld : 2 ≤ s.length) (hn : 1 ≤ n)
    (h : s.length - 1 < i * (s.length + 1) / n) :
    exclJ s n i = s.length - 1 ∧ (n : Int) ≤ exclD s n i := by
  have hn1 : ¬(i * (s.length + 1) / n < 1) := by omega
  have hJ : exclJ s n i = s.length - 1 := by simp [exclJ, clampJ, hn1, h]
  have hq : s.length ≤ i * (s.length + 1) / n := by omega
  have hA : s.length * n ≤ i * (s.length + 1) := by
    have e1 : s.length * n ≤ (i * (s.length + 1) / n) * n := Nat.mul_le_mul_right n hq
    have e2 : (i * (s.length + 1) / n) * n ≤ i * (s.length + 1) := by
      rw [Nat.mul_comm]; exact Nat.mul_div_le _ _
    exact Nat.le_trans e1 e2
  have heq : s.length * n - (s.length - 1) * n = n := by
    have h1 : s.length - 1 + 1 = s.length := by omega
    have h2 : (s.length - 1 + 1) * n = (s.length - 1) * n + 1 * n := Nat.add_mul _ _ _
    rw [h1, Nat.one_mul] at h2
    omega
  have hle' : (s.length - 1) * n ≤ s.length * n := Nat.mul_le_mul_right n (by omega)
  have hA' : ((s.length * n : Nat) : Int) ≤ ((i * (s.length + 1) : Nat) : Int) :=
    Int.ofNat_le.mpr hA
  have h1 : (n : Int) = ((s.length * n : Nat) : Int) - (((s.length - 1) * n : Nat) : Int) := by
    rw [← Nat.cast_sub hle', heq]
  refine ⟨hJ, ?_⟩
  simp only [exclD, hJ]
  linarith

/-- Slope-intercept form of an exclusive cut point. -/
lemma exclPoint_eq (s : List Rat) (n i : Nat) (hn : 1 ≤ n) :
    exclPoint s n i = s.getD (exclJ s n i - 1) 0
        + ((exclD s n i : Rat) / (n : Rat))
          * (s.getD (exclJ s n i) 0 - s.getD (exclJ s n i - 1) 0) := by
  have hn0 : (n : Rat) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  simp only [exclPoint]
  field_simp [hn0]
  ring

lemma inclJ_le (s : List Rat) {n i : Nat} (hld : 2 ≤ s.length) (hn : 1 ≤ n)
    (hi : i ≤ n - 1) : inclJ s n i ≤ s.length - 2 := by
  have h1 : i * (s.length - 1) ≤ (n - 1) * (s.length - 1) := Nat.mul_le_mul_right _ hi
  have h2 : (n - 1) * (s.length - 1) < n * (s.length - 1) :=
    Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
  have h3 : i * (s.length - 1) / n < s.length - 1 :=
    Nat.div_lt_of_lt_mul (Nat.lt_of_le_of_lt h1 h2)
  simp only [inclJ]
  omega

lemma inclJ_mono (s : List Rat) (n : Nat) {i k : Nat} (hik : i ≤ k) :
    inclJ s n i ≤ inclJ s n k := Nat.div_le_div_right (Nat.mul_le_mul_right _ hik)

lemma inclD_eq_mod (s : List Rat) (n i : Nat) :
    inclD s n i = (i * (s.length - 1) % n : Nat) := by
  have hle : i * (s.length - 1) / n * n ≤ i * (s.length - 1) := by
    rw [Nat.mul_comm]; exact Nat.mul_div_le _ _
  have hsub : i * (s.length - 1) - i * (s.length - 1) / n * n = i * (s.length - 1) % n := by
    have e : i * (s.length - 1) / n * n + i * (s.length - 1) % n = i * (s.length - 1) := by
      rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
    exact Nat.sub_eq_of_eq_add (e.symm.trans (Nat.add_comm _ _))
  simp only [inclD, inclJ]
  rw [← Nat.cast_sub hle, hsub]

lemma inclD_bounds (s : List Rat) {n i : Nat} (hn : 1 ≤ n) :
    0 ≤ inclD s n i ∧ inclD s n i < (n : Int) := by
  have h1 : inclD s n i = (i * (s.length - 1) % n : Nat) := inclD_eq_mod s n i
  rw [h1]
  refine ⟨Int.ofNat_le.mpr (Nat.zero_le _), by
    exact_mod_cast Nat.mod_lt _ (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)⟩

/-- Slope-intercept form of an inclusive cut point. -/
lemma inclPoint_eq (s : List Rat) (n i : Nat) (hn : 1 ≤ n) :
    inclPoint s n i = s.getD (inclJ s n i) 0
        + ((inclD s n i : Rat) / (n : Rat))
          * (s.getD (inclJ s n i + 1) 0 - s.getD (inclJ s n i) 0) := by
  have hn0 : (n : Rat) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  simp only [inclPoint]
  field_simp [hn0]
  ring

/-! ## 8. Monotonicity of the cut points -/

lemma map_congr_range {m : Nat} {f g : Nat → Rat} (h : ∀ k, k < m → f k = g k) :
    (List.range m).map f = (List.range m).map g := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.map_append]
    rw [ih (fun k hk => h k (Nat.lt_succ_of_lt hk))]
    rw [List.map_cons, List.map_cons, List.map_nil, List.map_nil]
    rw [h m (by omega)]

/-- The exclusive cut points are non-decreasing in `i`: the interpolated positions
`i * (ld+1) / n` increase and the piecewise-linear interpolation of sorted data is monotone
(the clamped branches are the linear *extensions* of the first/last segment). -/
theorem exclPoint_mono (s : List Rat) (hs : s.Pairwise (· ≤ ·)) (hld : 2 ≤ s.length)
    (n : Nat) (hn : 1 ≤ n) {i k : Nat} (hi : 1 ≤ i) (hik : i ≤ k) (hk : k ≤ n - 1) :
    exclPoint s n i ≤ exclPoint s n k := by
  have hJi := exclJ_bounds s n i hld
  have hJk := exclJ_bounds s n k hld
  have hJmono : exclJ s n i ≤ exclJ s n k := exclJ_mono s n hld hik
  have hn0 : (0 : Rat) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hget : ∀ {p q : Nat}, p ≤ q → q < s.length → s.getD p 0 ≤ s.getD q 0 :=
    fun hpq hq => Pairwise_getD_le hs 0 hpq hq
  have hab : s.getD (exclJ s n i - 1) 0 ≤ s.getD (exclJ s n i) 0 := hget (by omega) (by omega)
  have hcd : s.getD (exclJ s n k - 1) 0 ≤ s.getD (exclJ s n k) 0 := hget (by omega) (by omega)
  by_cases hj : exclJ s n i = exclJ s n k
  · have hdI : exclD s n i ≤ exclD s n k := by
      have hmul : ((i * (s.length + 1) : Nat) : Int) ≤ ((k * (s.length + 1) : Nat) : Int) :=
        Int.ofNat_le.mpr (Nat.mul_le_mul_right _ hik)
      simp only [exclD]
      rw [hj]
      linarith
    have hd : (exclD s n i : Rat) / n ≤ (exclD s n k : Rat) / n :=
      div_le_div_of_nonneg_right (by exact_mod_cast hdI) (le_of_lt hn0)
    have hmul2 := mul_le_mul_of_nonneg_right hd
      (by linarith : 0 ≤ s.getD (exclJ s n i) 0 - s.getD (exclJ s n i - 1) 0)
    rw [exclPoint_eq s n i hn, exclPoint_eq s n k hn, ← hj]
    linarith
  · have hjlt : exclJ s n i < exclJ s n k := Nat.lt_of_le_of_ne hJmono hj
    have hmid : s.getD (exclJ s n i) 0 ≤ s.getD (exclJ s n k - 1) 0 := hget (by omega) (by omega)
    have hstep1 : exclPoint s n i ≤ s.getD (exclJ s n i) 0 := by
      rw [exclPoint_eq s n i hn]
      have hdle : (exclD s n i : Rat) / n ≤ 1 := by
        rw [div_le_one hn0]
        rcases exclJ_trichotomy s n i with h1 | ⟨hq, hJ1⟩ | ⟨hq, hJ1⟩
        · have hl := exclD_lt s hn h1
          exact_mod_cast (by linarith : exclD s n i ≤ (n : Int))
        · have hl := (exclD_neg s hn hq).2
          have hnn : (0 : Int) ≤ n := Int.ofNat_le.mpr (Nat.zero_le n)
          exact_mod_cast (by linarith : exclD s n i ≤ (n : Int))
        · exfalso
          omega
      have hmul2 := mul_le_mul_of_nonneg_right hdle
        (by linarith : 0 ≤ s.getD (exclJ s n i) 0 - s.getD (exclJ s n i - 1) 0)
      linarith
    have hstep3 : s.getD (exclJ s n k - 1) 0 ≤ exclPoint s n k := by
      rw [exclPoint_eq s n k hn]
      have hdge : 0 ≤ (exclD s n k : Rat) / n := by
        apply div_nonneg _ (le_of_lt hn0)
        rcases exclJ_trichotomy s n k with h1 | ⟨hq, hJ1⟩ | ⟨hq, hJ1⟩
        · exact_mod_cast exclD_nonneg s h1
        · exfalso
          omega
        · have hge := (exclD_ge s hld hn hq).2
          have hnn : (0 : Int) ≤ n := Int.ofNat_le.mpr (Nat.zero_le n)
          exact_mod_cast (by linarith : (0 : Int) ≤ exclD s n k)
      have hmul2 := mul_le_mul_of_nonneg_right hdge
        (by linarith : 0 ≤ s.getD (exclJ s n k) 0 - s.getD (exclJ s n k - 1) 0)
      linarith
    exact le_trans (le_trans hstep1 hmid) hstep3

/-- The inclusive cut points are non-decreasing in `i`. -/
theorem inclPoint_mono (s : List Rat) (hs : s.Pairwise (· ≤ ·)) (hld : 2 ≤ s.length)
    (n : Nat) (hn : 1 ≤ n) {i k : Nat} (hi : 1 ≤ i) (hik : i ≤ k) (hk : k ≤ n - 1) :
    inclPoint s n i ≤ inclPoint s n k := by
  have hJi := inclJ_le s hld hn (by omega : i ≤ n - 1)
  have hJk := inclJ_le s hld hn hk
  have hJmono : inclJ s n i ≤ inclJ s n k := inclJ_mono s n hik
  have hn0 : (0 : Rat) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hDi : 0 ≤ inclD s n i ∧ inclD s n i < (n : Int) := inclD_bounds s hn
  have hDk : 0 ≤ inclD s n k ∧ inclD s n k < (n : Int) := inclD_bounds s hn
  have hget : ∀ {p q : Nat}, p ≤ q → q < s.length → s.getD p 0 ≤ s.getD q 0 :=
    fun hpq hq => Pairwise_getD_le hs 0 hpq hq
  have hab : s.getD (inclJ s n i) 0 ≤ s.getD (inclJ s n i + 1) 0 := hget (by omega) (by omega)
  have hcd : s.getD (inclJ s n k) 0 ≤ s.getD (inclJ s n k + 1) 0 := hget (by omega) (by omega)
  by_cases hj : inclJ s n i = inclJ s n k
  · have hdI : inclD s n i ≤ inclD s n k := by
      have hmul : ((i * (s.length - 1) : Nat) : Int) ≤ ((k * (s.length - 1) : Nat) : Int) :=
        Int.ofNat_le.mpr (Nat.mul_le_mul_right _ hik)
      simp only [inclD]
      rw [hj]
      linarith
    have hd : (inclD s n i : Rat) / n ≤ (inclD s n k : Rat) / n :=
      div_le_div_of_nonneg_right (by exact_mod_cast hdI) (le_of_lt hn0)
    have hmul2 := mul_le_mul_of_nonneg_right hd
      (by linarith : 0 ≤ s.getD (inclJ s n i + 1) 0 - s.getD (inclJ s n i) 0)
    rw [inclPoint_eq s n i hn, inclPoint_eq s n k hn, ← hj]
    linarith
  · have hjlt : inclJ s n i < inclJ s n k := Nat.lt_of_le_of_ne hJmono hj
    have hstep1 : inclPoint s n i ≤ s.getD (inclJ s n i + 1) 0 := by
      rw [inclPoint_eq s n i hn]
      have hdle : (inclD s n i : Rat) / n ≤ 1 := by
        rw [div_le_one hn0]
        exact_mod_cast (by linarith : inclD s n i ≤ (n : Int))
      have hmul2 := mul_le_mul_of_nonneg_right hdle
        (by linarith : 0 ≤ s.getD (inclJ s n i + 1) 0 - s.getD (inclJ s n i) 0)
      linarith
    have hstep2 : s.getD (inclJ s n i + 1) 0 ≤ s.getD (inclJ s n k) 0 := hget (by omega) (by omega)
    have hstep3 : s.getD (inclJ s n k) 0 ≤ inclPoint s n k := by
      rw [inclPoint_eq s n k hn]
      have hdge : 0 ≤ (inclD s n k : Rat) / n :=
        div_nonneg (by exact_mod_cast hDk.1) (le_of_lt hn0)
      have hmul2 := mul_le_mul_of_nonneg_right hdge
        (by linarith : 0 ≤ s.getD (inclJ s n k + 1) 0 - s.getD (inclJ s n k) 0)
      linarith
    exact le_trans (le_trans hstep1 hstep2) hstep3

theorem cutPoints_length (s : List Rat) (n : Nat) (m : Method) :
    (cutPoints s n m).length = n - 1 := by simp [cutPoints]

theorem cutPoints_pairwise (s : List Rat) (hs : s.Pairwise (· ≤ ·)) (hld : 2 ≤ s.length)
    (n : Nat) (hn : 1 ≤ n) (m : Method) : (cutPoints s n m).Pairwise (· ≤ ·) := by
  refine Pairwise_map_range ?_
  intro i j hij hj
  cases m with
  | exclusive =>
      exact exclPoint_mono s hs hld n hn (by omega) (by omega) (by omega)
  | inclusive =>
      exact inclPoint_mono s hs hld n hn (by omega) (by omega) (by omega)

/-! ## 9. Inclusive cut points stay inside the data range -/

theorem inclPoint_bounds (s : List Rat) (hs : s.Pairwise (· ≤ ·)) (hld : 2 ≤ s.length)
    (n : Nat) (hn : 1 ≤ n) {i : Nat} (hi : 1 ≤ i) (hi' : i ≤ n - 1) :
    s.getD 0 0 ≤ inclPoint s n i ∧ inclPoint s n i ≤ s.getD (s.length - 1) 0 := by
  have hJ := inclJ_le s hld hn hi'
  have hD : 0 ≤ inclD s n i ∧ inclD s n i < (n : Int) := inclD_bounds s hn
  have hn0 : (0 : Rat) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have h1 : s.getD 0 0 ≤ s.getD (inclJ s n i) 0 := Pairwise_getD_le hs 0 (by omega) (by omega)
  have h2 : s.getD (inclJ s n i + 1) 0 ≤ s.getD (s.length - 1) 0 :=
    Pairwise_getD_le hs 0 (by omega) (by omega)
  have hab : s.getD (inclJ s n i) 0 ≤ s.getD (inclJ s n i + 1) 0 :=
    Pairwise_getD_le hs 0 (by omega) (by omega)
  have hd0 : 0 ≤ (inclD s n i : Rat) / n := div_nonneg (by exact_mod_cast hD.1) (le_of_lt hn0)
  have hd1 : (inclD s n i : Rat) / n ≤ 1 := by
    rw [div_le_one hn0]
    exact_mod_cast (by linarith : inclD s n i ≤ (n : Int))
  have hdiff : 0 ≤ s.getD (inclJ s n i + 1) 0 - s.getD (inclJ s n i) 0 := by linarith
  have hm0 : 0 ≤ (inclD s n i : Rat) / n * (s.getD (inclJ s n i + 1) 0 - s.getD (inclJ s n i) 0) :=
    mul_nonneg hd0 hdiff
  have hm1 : (inclD s n i : Rat) / n * (s.getD (inclJ s n i + 1) 0 - s.getD (inclJ s n i) 0)
      ≤ s.getD (inclJ s n i + 1) 0 - s.getD (inclJ s n i) 0 := by
    have := mul_le_mul_of_nonneg_right hd1 hdiff
    linarith
  rw [inclPoint_eq s n i hn]
  constructor <;> linarith

theorem cutPoints_incl_bounds (s : List Rat) (hs : s.Pairwise (· ≤ ·)) (hld : 2 ≤ s.length)
    (n : Nat) (hn : 1 ≤ n) :
    ∀ x ∈ cutPoints s n Method.inclusive, s.getD 0 0 ≤ x ∧ x ≤ s.getD (s.length - 1) 0 := by
  intro x hx
  rw [cutPoints, List.mem_map] at hx
  obtain ⟨k, hk, hxk⟩ := hx
  rw [List.mem_range] at hk
  subst hxk
  exact inclPoint_bounds s hs hld n hn (by omega) (by omega)

/-! ## 10. `n = 2`: both methods return the median -/

theorem cutPoints_two_median (s : List Rat) (hld : 2 ≤ s.length) (m : Method) :
    cutPoints s 2 m =
      [if s.length % 2 = 0 then (s.getD (s.length / 2 - 1) 0 + s.getD (s.length / 2) 0) / 2
       else s.getD (s.length / 2) 0] := by
  have hr : List.range (2 - 1) = [0] := by decide
  rw [cutPoints, hr, List.map_cons, List.map_nil]
  congr 1
  have h01 : (0 : Nat) + 1 = 1 := rfl
  rw [h01]
  rcases Nat.even_or_odd s.length with ⟨t, ht⟩ | ⟨t, ht⟩
  · have ht1 : 1 ≤ t := by omega
    have ht2 : s.length = 2 * t := by omega
    cases m with
    | exclusive =>
      have hJ : exclJ s 2 1 = t := by
        have h1 : 1 * (2 * t + 1) / 2 = t := by omega
        simp only [exclJ, clampJ, ht2, h1]
        split_ifs <;> omega
      have hD : exclD s 2 1 = 1 := by
        have e1 : 1 * (2 * t + 1) - t * 2 = 1 := by omega
        have e2 : t * 2 ≤ 1 * (2 * t + 1) := by omega
        simp only [exclD, hJ, ht2]
        rw [← Nat.cast_sub e2, e1]
        norm_num
      have hmod : (2 * t) % 2 = 0 := by omega
      have hdiv : 2 * t / 2 = t := by omega
      have htp : t - 1 + 1 = t := by omega
      simp only [point, exclPoint, hJ, hD, hmod, hdiv, ht2, if_pos hmod, htp]
      push_cast
      ring
    | inclusive =>
      have hJ : inclJ s 2 1 = t - 1 := by
        simp only [inclJ, ht2]
        omega
      have hD : inclD s 2 1 = 1 := by
        have e1 : 1 * (2 * t - 1) - (t - 1) * 2 = 1 := by omega
        have e2 : (t - 1) * 2 ≤ 1 * (2 * t - 1) := by omega
        simp only [inclD, hJ, ht2]
        rw [← Nat.cast_sub e2, e1]
        norm_num
      have hmod : (2 * t) % 2 = 0 := by omega
      have hdiv : 2 * t / 2 = t := by omega
      have htp : t - 1 + 1 = t := by omega
      simp only [point, inclPoint, hJ, hD, hmod, hdiv, ht2, if_pos hmod, htp]
      push_cast
      ring
  · have ht1 : 1 ≤ t := by omega
    cases m with
    | exclusive =>
      have hJ : exclJ s 2 1 = t + 1 := by
        have h1 : 1 * (2 * t + 1 + 1) / 2 = t + 1 := by omega
        simp only [exclJ, clampJ, ht, h1]
        split_ifs <;> omega
      have hD : exclD s 2 1 = 0 := by
        have e1 : 1 * (2 * t + 1 + 1) - (t + 1) * 2 = 0 := by omega
        have e2 : (t + 1) * 2 ≤ 1 * (2 * t + 1 + 1) := by omega
        simp only [exclD, hJ, ht]
        rw [← Nat.cast_sub e2, e1]
        norm_num
      have hne : ¬((2 * t + 1) % 2 = 0) := by omega
      have hdiv : (2 * t + 1) / 2 = t := by omega
      have htp : t + 1 - 1 = t := by omega
      simp only [point, exclPoint, hJ, hD, ht, hdiv, if_neg hne, htp]
      push_cast
      ring
    | inclusive =>
      have hJ : inclJ s 2 1 = t := by
        simp only [inclJ, ht]
        omega
      have hD : inclD s 2 1 = 0 := by
        have e1 : 1 * (2 * t + 1 - 1) - t * 2 = 0 := by omega
        have e2 : t * 2 ≤ 1 * (2 * t + 1 - 1) := by omega
        simp only [inclD, hJ, ht]
        rw [← Nat.cast_sub e2, e1]
        norm_num
      have hne : ¬((2 * t + 1) % 2 = 0) := by omega
      have hdiv : (2 * t + 1) / 2 = t := by omega
      simp only [point, inclPoint, hJ, hD, ht, hdiv, if_neg hne]
      push_cast
      ring

/-! ## 11. Translation equivariance of the interpolation -/

theorem sortData_map_add (l : List Rat) (c : Rat) :
    sortData (l.map (· + c)) = (sortData l).map (· + c) := by
  apply eq_of_pairwise_of_perm
  · exact sortData_pairwise _
  · exact List.Pairwise.map (· + c) (fun _ _ hx => add_le_add_right hx c) (sortData_pairwise l)
  · have p1 : sortData (l.map (· + c)) ~ l.map (· + c) := List.mergeSort_perm _ _
    have p2 : l.map (· + c) ~ (sortData l).map (· + c) :=
      List.Perm.map _ (List.Perm.symm (List.mergeSort_perm l ratLe))
    exact List.Perm.trans p1 p2

lemma exclPoint_shift (s : List Rat) (c : Rat) (n i : Nat) (hld : 2 ≤ s.length) (hn : 1 ≤ n) :
    exclPoint (s.map (· + c)) n i = exclPoint s n i + c := by
  have hlen : (s.map (· + c)).length = s.length := List.length_map _
  have hJ : exclJ (s.map (· + c)) n i = exclJ s n i := by simp [exclJ, hlen]
  have hD : exclD (s.map (· + c)) n i = exclD s n i := by simp [exclD, hJ, hlen]
  have hJb := exclJ_bounds s n i hld
  have h1 : exclJ s n i - 1 < s.length := by omega
  have h2 : exclJ s n i < s.length := by omega
  have hn0 : (n : Rat) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  simp only [exclPoint, hJ, hD, getD_map_of_lt (· + c) 0 0 h1, getD_map_of_lt (· + c) 0 0 h2]
  field_simp [hn0]
  ring

lemma inclPoint_shift (s : List Rat) (c : Rat) (n i : Nat) (hld : 2 ≤ s.length) (hn : 1 ≤ n)
    (hi : 1 ≤ i) (hi' : i ≤ n - 1) :
    inclPoint (s.map (· + c)) n i = inclPoint s n i + c := by
  have hlen : (s.map (· + c)).length = s.length := List.length_map _
  have hJ : inclJ (s.map (· + c)) n i = inclJ s n i := by simp [inclJ, hlen]
  have hD : inclD (s.map (· + c)) n i = inclD s n i := by simp [inclD, hJ, hlen]
  have hJb := inclJ_le s hld hn hi'
  have h1 : inclJ s n i < s.length := by omega
  have h2 : inclJ s n i + 1 < s.length := by omega
  have hn0 : (n : Rat) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  simp only [inclPoint, hJ, hD, getD_map_of_lt (· + c) 0 0 h1, getD_map_of_lt (· + c) 0 0 h2]
  field_simp [hn0]
  ring

theorem cutPoints_shift (s : List Rat) (c : Rat) (n : Nat) (hld : 2 ≤ s.length) (hn : 1 ≤ n)
    (m : Method) :
    cutPoints (s.map (· + c)) n m = (cutPoints s n m).map (· + c) := by
  have hcon : ∀ k, k < n - 1 →
      point (s.map (· + c)) n (k + 1) m = ((· + c) ∘ fun j => point s n (j + 1) m) k := by
    intro k hk
    simp only [Function.comp_apply]
    cases m with
    | exclusive => exact exclPoint_shift s c n (k + 1) hld hn
    | inclusive => exact inclPoint_shift s c n (k + 1) hld hn (by omega) (by omega)
  rw [cutPoints, cutPoints, List.map_map, map_congr_range hcon]

/-! ## 12. Properties of `benchmark_quantiles` -/

/-- The returned list has exactly `n - 1` cut points. -/
def length_prop (data : List Rat) (n : Nat) (m : Method) : Prop :=
  Pre data n m → (quantiles data n m).map List.length = some (n - 1)

/-- The cut points are non-decreasing (they separate *continuous* intervals). -/
def sorted_prop (data : List Rat) (n : Nat) (m : Method) : Prop :=
  Pre data n m → ∀ r, quantiles data n m = some r → r.Pairwise (· ≤ ·)

/-- For the inclusive method every cut point lies between the minimum and the maximum
of the data (the minimum is the 0th and the maximum the 100th percentile). -/
def bounds_prop (data : List Rat) (n : Nat) : Prop :=
  Pre data n Method.inclusive → ∀ r, quantiles data n Method.inclusive = some r →
    ∀ x ∈ r, lo data ≤ x ∧ x ≤ hi data

/-- For `n = 2` both methods return the median of the data. -/
def median_prop (data : List Rat) (m : Method) : Prop :=
  Pre data 2 m → quantiles data 2 m = some [median data]

/-- The result only depends on the multiset of the data: the input is sorted internally. -/
def perm_prop (data data' : List Rat) (n : Nat) (m : Method) : Prop :=
  Pre data n m → data.Perm data' → quantiles data n m = quantiles data' n m

/-- Translating every data point by `c` translates every cut point by `c`. -/
def shift_prop (data : List Rat) (c : Rat) (n : Nat) (m : Method) : Prop :=
  Pre data n m →
    quantiles (data.map (· + c)) n m = (quantiles data n m).map (List.map (· + c))

/-- Outside the pre-condition the Python function raises `StatisticsError`. -/
def error_prop (data : List Rat) (n : Nat) (m : Method) : Prop :=
  ¬ Pre data n m → quantiles data n m = none

/-! ## 13. The properties hold -/

theorem length_thm (data : List Rat) (n : Nat) (m : Method) : length_prop data n m := by
  intro h
  have hguard : 2 ≤ data.length ∧ 1 ≤ n := ⟨h.1, h.2.1⟩
  simp only [quantiles, if_pos hguard, Option.map_some, cutPoints_length]

theorem error_thm (data : List Rat) (n : Nat) (m : Method) : error_prop data n m := by
  intro h
  show (if 2 ≤ data.length ∧ 1 ≤ n then some (cutPoints (sortData data) n m) else none) = none
  rw [if_neg]
  exact fun hh => h (pre_mk hh.1 hh.2 m)

theorem sorted_thm (data : List Rat) (n : Nat) (m : Method) : sorted_prop data n m := by
  intro h r hr
  have hguard : 2 ≤ data.length ∧ 1 ≤ n := ⟨h.1, h.2.1⟩
  simp only [quantiles, if_pos hguard] at hr
  have hld : 2 ≤ (sortData data).length := by rw [sortData_length]; exact h.1
  injection hr with hr'
  subst hr'
  exact cutPoints_pairwise (sortData data) (sortData_pairwise data) hld n h.2.1 m

theorem bounds_thm (data : List Rat) (n : Nat) : bounds_prop data n := by
  intro h r hr x hx
  have hguard : 2 ≤ data.length ∧ 1 ≤ n := ⟨h.1, h.2.1⟩
  simp only [quantiles, if_pos hguard, lo, hi] at hr ⊢
  have hld : 2 ≤ (sortData data).length := by rw [sortData_length]; exact h.1
  injection hr with hr'
  subst hr'
  have hlen : (sortData data).length = data.length := sortData_length data
  rw [← hlen]
  exact cutPoints_incl_bounds (sortData data) (sortData_pairwise data) hld n h.2.1 x hx

theorem median_thm (data : List Rat) (m : Method) : median_prop data m := by
  intro h
  have hld : 2 ≤ (sortData data).length := by rw [sortData_length]; exact h.1
  have hpre : 2 ≤ data.length ∧ 1 ≤ 2 := ⟨h.1, by omega⟩
  have hcut : cutPoints (sortData data) 2 m = [median data] := by
    rw [cutPoints_two_median _ hld m]
    simp only [median]
  rw [quantiles, if_pos hpre, hcut]

theorem perm_thm (data data' : List Rat) (n : Nat) (m : Method) :
    perm_prop data data' n m := by
  intro h hp
  have h' : 2 ≤ data'.length ∧ 1 ≤ n := by
    refine ⟨?_, h.2.1⟩
    rw [← List.Perm.length_eq hp]
    exact h.1
  have hguard : 2 ≤ data.length ∧ 1 ≤ n := ⟨h.1, h.2.1⟩
  simp only [quantiles, if_pos hguard, if_pos h', sortData_perm hp]

theorem shift_thm (data : List Rat) (c : Rat) (n : Nat) (m : Method) :
    shift_prop data c n m := by
  intro h
  have hlen : (data.map (· + c)).length = data.length := List.length_map _
  have h2 : 2 ≤ (data.map (· + c)).length := by
    rw [hlen]
    exact h.1
  have hguard' : 2 ≤ (data.map (· + c)).length ∧ 1 ≤ n := ⟨h2, h.2.1⟩
  have hguard : 2 ≤ data.length ∧ 1 ≤ n := ⟨h.1, h.2.1⟩
  have hld : 2 ≤ (sortData data).length := by
    rw [sortData_length]
    exact h.1
  simp only [quantiles, if_pos hguard', if_pos hguard, sortData_map_add, Option.map_some]
  congr 1
  exact cutPoints_shift (sortData data) c n hld h.2.1 m

/-! ## 14. Post-condition and correctness -/

/-- The post-condition of `benchmark_quantiles`. -/
def Post_prop (data : List Rat) (n : Nat) (m : Method) (out : Option (List Rat)) : Prop :=
  (¬ Pre data n m → out = none) ∧
  (Pre data n m → out.map List.length = some (n - 1)) ∧
  (Pre data n m → ∀ r, out = some r → r.Pairwise (· ≤ ·)) ∧
  (Pre data n m → m = Method.inclusive → ∀ r, out = some r → ∀ x ∈ r, lo data ≤ x ∧ x ≤ hi data)

/-! ## 15. Property-based tests -/

def pbData : List (List Rat) :=
  [[1, 2], [1, 2, 3, 4], [4, 1, 3, 2], (List.range 11).map (↑), [3/2, 5/2, 7/2, 9/2],
   [-3, 0, 7, 7, 12], [5, 5, 5], [0, 1], [-5, -1, 0, 1, 5, 9, 9, 9, 12, 100],
   [10, -10], [1, 1000000, 3, 3, 3, 7], [0, 0, 0, 0, 0]]

def pbNs : List Nat := [1, 2, 3, 4, 5, 7, 10, 100]

def pbMethods : List Method := [Method.exclusive, Method.inclusive]

/-- executable Boolean form of `length_prop` -/
def checkLength (d : List Rat) (n : Nat) (m : Method) : Bool :=
  (quantiles d n m).map List.length == some (n - 1)

/-- executable Boolean form of `sorted_prop` -/
def checkSorted (d : List Rat) (n : Nat) (m : Method) : Bool :=
  match quantiles d n m with
  | none => true
  | some r => decide (r.Pairwise (· ≤ ·))

/-- executable Boolean form of `bounds_prop` -/
def checkBounds (d : List Rat) (n : Nat) : Bool :=
  match quantiles d n Method.inclusive with
  | none => true
  | some r => r.all (fun x => decide (lo d ≤ x) && decide (x ≤ hi d))

/-- executable Boolean form of `median_prop` -/
def checkMedian (d : List Rat) (m : Method) : Bool :=
  quantiles d 2 m == some [median d]

/-- executable Boolean form of `perm_prop` -/
def checkPerm (d d' : List Rat) (n : Nat) (m : Method) : Bool :=
  quantiles d n m == quantiles d' n m

/-- executable Boolean form of `shift_prop` -/
def checkShift (d : List Rat) (c : Rat) (n : Nat) (m : Method) : Bool :=
  quantiles (d.map (· + c)) n m == (quantiles d n m).map (List.map (· + c))

/-- executable Boolean form of `error_prop` -/
def checkError (d : List Rat) (n : Nat) (m : Method) : Bool :=
  quantiles d n m == none

/-- executable Boolean form of `Post_prop` -/
def checkPost (d : List Rat) (n : Nat) (m : Method) : Bool :=
  (decide (2 ≤ d.length) && decide (1 ≤ n) && checkLength d n m && checkSorted d n m
    && (decide (m = Method.inclusive) → checkBounds d n))
    || (!decide (2 ≤ d.length) || !decide (1 ≤ n))

-- bounded PBTs: exhaustive over a fixed family of samples, group sizes and methods
example : pbData.all (fun d => pbNs.all (fun n => pbMethods.all (fun m => checkLength d n m)))
    = true := by native_decide

example : pbData.all (fun d => pbNs.all (fun n => pbMethods.all (fun m => checkSorted d n m)))
    = true := by native_decide

example : pbData.all (fun d => pbNs.all (fun n => checkBounds d n)) = true := by native_decide

example : pbData.all (fun d => pbMethods.all (fun m => checkMedian d m)) = true := by native_decide

example : pbData.all (fun d => pbNs.all (fun n => pbMethods.all (fun m => checkPost d n m)))
    = true := by native_decide

example : pbData.all (fun d => pbNs.all (fun n => pbMethods.all (fun m =>
    checkShift d (7/3) n m))) = true := by native_decide

example : pbData.all (fun d => checkPerm d d.reverse 4 Method.exclusive) = true := by native_decide

example : pbData.all (fun d => pbNs.all (fun n => pbMethods.all (fun m =>
    checkError d n m == decide (¬(2 ≤ d.length ∧ 1 ≤ n))))) = true := by native_decide

-- randomized PBTs (Plausible); the statements are precondition-free so no sample is discarded
#eval Plausible.Testable.check (∀ xs : List Int,
  checkLength (xs.map (fun z => (z : Rat))) 4 Method.exclusive = decide (2 ≤ xs.length))

#eval Plausible.Testable.check (∀ xs : List Int,
  checkSorted (xs.map (fun z => (z : Rat))) 4 Method.exclusive = true)

#eval Plausible.Testable.check (∀ xs : List Int,
  checkSorted (xs.map (fun z => (z : Rat))) 5 Method.inclusive = true)

#eval Plausible.Testable.check (∀ xs : List Int,
  checkBounds (xs.map (fun z => (z : Rat))) 4 = true)

#eval Plausible.Testable.check (∀ xs : List Int,
  checkMedian (xs.map (fun z => (z : Rat))) Method.inclusive = decide (2 ≤ xs.length))

#eval Plausible.Testable.check (∀ (xs : List Int) (c : Int),
  checkShift (xs.map (fun z => (z : Rat))) (c : Rat) 4 Method.exclusive = true)

#eval Plausible.Testable.check (∀ xs : List Int,
  checkError (xs.map (fun z => (z : Rat))) 0 Method.exclusive = true)

#eval Plausible.Testable.check (∀ (xs : List Int) (n : Nat),
  checkPost (xs.map (fun z => (z : Rat))) n Method.inclusive = true)

-- PBT: the `Real`-valued image of these properties (`RealLayer` below) is not executable
-- (`Real` comparisons are not computable); it is tested through the `Rat` layer above.

/-! ## 15b. Correctness theorem: `Pre -> Post` -/

theorem quantiles_correct (data : List Rat) (n : Nat) (m : Method) :
    Post_prop data n m (quantiles data n m) :=
  ⟨error_thm data n m, length_thm data n m, sorted_thm data n m,
    fun h hm => by subst hm; exact bounds_thm data n h⟩

/-! ## 16. Imperative implementation (mutable state inside `Id.run do`) -/

/-- Imperative transcription of the Python function: guard clauses, an in-place sort, a mutable
accumulator and a `for` loop over `i = 1, …, n-1`. -/
def quantilesImp (data : List Rat) (n : Nat) (m : Method) : Option (List Rat) :=
  Id.run do
    let ld := data.length
    -- `if ld < 2: raise StatisticsError('must have at least two data points')`
    if ld < 2 then return none
    -- `if n < 1: raise StatisticsError('n must be at least 1')`
    if n < 1 then return none
    -- `data = sorted(data)`
    let s := sortData data
    -- `result = []`
    let mut acc : List Rat := []
    -- `for i in range(1, n)`
    for k in List.range (n - 1) do
      let i := k + 1
      -- `result.append(interpolated)` (prepend + final `reverse` is `append`)
      acc := point s n i m :: acc
    return some acc.reverse

#eval quantilesImp [1, 2, 3, 4] 4 Method.exclusive
#eval quantilesImp [1, 2, 3, 4] 4 Method.inclusive
#eval quantilesImp (List.range 11) 10 Method.exclusive
#eval quantilesImp [1] 4 Method.exclusive
#eval quantilesImp [1, 2] 0 Method.exclusive

example : quantilesImp [1, 2, 3, 4] 4 Method.exclusive = some [5/4, 5/2, 15/4] := by native_decide
example : quantilesImp [4, 1, 3, 2] 4 Method.inclusive = some [7/4, 5/2, 13/4] := by native_decide
example : quantilesImp (List.range 11) 10 Method.exclusive =
    some [1/5, 7/5, 13/5, 19/5, 5, 31/5, 37/5, 43/5, 49/5] := by native_decide
example : quantilesImp [1, 2] 4 Method.exclusive = some [3/4, 3/2, 9/4] := by native_decide
example : quantilesImp [1, 2, 3, 4, 5] 2 Method.inclusive = some [3] := by native_decide
example : quantilesImp [1] 4 Method.exclusive = none := by native_decide
example : quantilesImp [1, 2] 0 Method.exclusive = none := by native_decide

/-- The imperative program computes exactly what the functional specification computes. -/
theorem quantilesImp_eq (data : List Rat) (n : Nat) (m : Method) :
    quantilesImp data n m = quantiles data n m := by
  by_cases h1 : data.length < 2
  · have hn1 : ¬(2 ≤ data.length) := by omega
    simp [quantilesImp, quantiles, h1, hn1]
  · by_cases h2 : n < 1
    · have hn2 : ¬(1 ≤ n) := by omega
      simp [quantilesImp, quantiles, h1, h2, hn2]
    · have hg : 2 ≤ data.length ∧ 1 ≤ n := by omega
      have hloop : (Id.run do
            let mut acc : List Rat := []
            for k in List.range (n - 1) do
              acc := point (sortData data) n (k + 1) m :: acc
            return acc.reverse) =
          (List.range (n - 1)).map (fun k => point (sortData data) n (k + 1) m) := by simp
      simp [quantilesImp, quantiles, cutPoints, h1, h2, hg, hloop]

/-! ## 17. IEEE-754 `Float` layer

Primitive `Float` arithmetic is opaque to the kernel, so this layer is exercised with `#eval` and
`native_decide` ground tests against CPython's `float` output; the *proved* obligations live in
the exact `Rat` layer above (and in the `Real` layer below). -/

namespace FloatLayer

def sortDataF (l : List Float) : List Float := l.mergeSort (fun a b => decide (a ≤ b))

def exclPointF (s : List Float) (n i : Nat) : Float :=
  let ld := s.length
  let j := clampJ (i * (ld + 1) / n) ld
  let d := Float.ofNat (i * (ld + 1)) - Float.ofNat (j * n)
  (s.getD (j - 1) 0 * (Float.ofNat n - d) + s.getD j 0 * d) / Float.ofNat n

def inclPointF (s : List Float) (n i : Nat) : Float :=
  let ld := s.length
  let j := i * (ld - 1) / n
  let d := Float.ofNat (i * (ld - 1)) - Float.ofNat (j * n)
  (s.getD j 0 * (Float.ofNat n - d) + s.getD (j + 1) 0 * d) / Float.ofNat n

def pointF (s : List Float) (n i : Nat) (m : Method) : Float :=
  match m with
  | Method.exclusive => exclPointF s n i
  | Method.inclusive => inclPointF s n i

def cutPointsF (s : List Float) (n : Nat) (m : Method) : List Float :=
  (List.range (n - 1)).map (fun k => pointF s n (k + 1) m)

def quantilesF (data : List Float) (n : Nat) (m : Method) : Option (List Float) :=
  if 2 ≤ data.length ∧ 1 ≤ n then some (cutPointsF (sortDataF data) n m) else none

#eval quantilesF [1, 2, 3, 4] 4 Method.exclusive
#eval quantilesF [3, 1, 4, 1, 5, 9, 2, 6] 4 Method.inclusive

-- ground tests against CPython's `statistics.quantiles` on `float` data
-- (`Float` has no `DecidableEq`, so the tests use the `BEq` comparison)
example : (quantilesF [1, 2, 3, 4] 4 Method.exclusive == some [1.25, 2.5, 3.75]) = true := by
  native_decide
example : (quantilesF [1, 2, 3, 4] 4 Method.inclusive == some [1.75, 2.5, 3.25]) = true := by
  native_decide
example : (quantilesF [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 10 Method.exclusive ==
    some [0.2, 1.4, 2.6, 3.8, 5.0, 6.2, 7.4, 8.6, 9.8]) = true := by native_decide
example : (quantilesF [1, 2, 3, 4, 5] 2 Method.exclusive == some [3.0]) = true := by native_decide
example : (quantilesF [1.5, 2.5, 3.5, 4.5] 2 Method.exclusive == some [3.0]) = true := by
  native_decide
example : (quantilesF [4, 1, 3, 2] 4 Method.exclusive == some [1.25, 2.5, 3.75]) = true := by
  native_decide
example : (quantilesF [3, 1, 4, 1, 5, 9, 2, 6] 4 Method.exclusive ==
    some [1.25, 3.5, 5.75]) = true := by native_decide
example : (quantilesF [3, 1, 4, 1, 5, 9, 2, 6] 4 Method.inclusive ==
    some [1.75, 3.5, 5.25]) = true := by native_decide
example : (quantilesF [1, 2] 4 Method.exclusive == some [0.75, 1.5, 2.25]) = true := by
  native_decide
example : (quantilesF ((List.range' 1 10).map Float.ofNat) 4 Method.exclusive ==
    some [2.75, 5.5, 8.25]) = true := by native_decide
example : (quantilesF [1] 4 Method.exclusive == (none : Option (List Float))) = true := by
  native_decide
example : (quantilesF [1, 2] 0 Method.exclusive == (none : Option (List Float))) = true := by
  native_decide
example : (quantilesF [1, 2, 3, 4] 1 Method.exclusive == some []) = true := by native_decide

/-- Structural (kernel-checkable) facts about the `Float` layer. -/
theorem quantilesF_none (data : List Float) (n : Nat) (m : Method)
    (h : ¬(2 ≤ data.length ∧ 1 ≤ n)) : quantilesF data n m = none := by
  simp [quantilesF, if_neg h]

theorem quantilesF_some (data : List Float) (n : Nat) (m : Method)
    (h : 2 ≤ data.length ∧ 1 ≤ n) :
    quantilesF data n m = some (cutPointsF (sortDataF data) n m) := by
  simp [quantilesF, if_pos h]

theorem cutPointsF_length (data : List Float) (n : Nat) (m : Method) :
    (cutPointsF data n m).length = n - 1 := by simp [cutPointsF]

theorem quantilesF_length (data : List Float) (n : Nat) (m : Method)
    (h : 2 ≤ data.length ∧ 1 ≤ n) :
    (quantilesF data n m).map List.length = some (n - 1) := by
  simp [quantilesF_some data n m h, cutPointsF_length]

end FloatLayer

/-! ## 18. `Real` layer

The exact cut points viewed as real numbers through the canonical embedding `Rat → Real`.
`Real` comparisons are not computable, so this layer has no executable PBT of its own; the
executable tests of section 15 cover the same statements in the `Rat` layer. -/

namespace RealLayer

/-- The exact cut points viewed as real numbers through the canonical embedding `Rat → Real`. -/
noncomputable def quantilesReal (data : List Rat) (n : Nat) (m : Method) : Option (List Real) :=
  (quantiles data n m).map (List.map (((↑) : Rat → Real)))

theorem quantilesReal_doctest :
    quantilesReal [1, 2, 3, 4] 4 Method.exclusive =
      some (([5/4, 5/2, 15/4] : List Rat).map (((↑) : Rat → Real))) := by
  simp [quantilesReal, quartiles_doctest]

theorem quantilesReal_length (data : List Rat) (n : Nat) (m : Method) :
    Pre data n m → (quantilesReal data n m).map List.length = some (n - 1) := by
  intro h
  have h1 := length_thm data n m h
  have e : ∀ (x : Option (List Rat)),
      Option.map List.length (Option.map (List.map (((↑) : Rat → Real))) x)
        = Option.map List.length x := by
    intro x
    rcases x with _ | r
    · rfl
    · simp only [Option.map_some, List.length_map]
  rw [quantilesReal, e]
  exact h1

theorem quantilesReal_error (data : List Rat) (n : Nat) (m : Method) :
    ¬ Pre data n m → quantilesReal data n m = none := by
  intro h
  simp [quantilesReal, error_thm data n m h]

theorem quantilesReal_sorted (data : List Rat) (n : Nat) (m : Method) :
    Pre data n m → ∀ r, quantilesReal data n m = some r → r.Pairwise (· ≤ ·) := by
  intro h r hr
  have h1 := sorted_thm data n m h
  have hguard : 2 ≤ data.length ∧ 1 ≤ n := ⟨h.1, h.2.1⟩
  have hq : quantiles data n m = some (cutPoints (sortData data) n m) := by
    simp only [quantiles, if_pos hguard]
  rw [quantilesReal, hq, Option.map_some] at hr
  injection hr with hr2
  subst hr2
  exact List.Pairwise.map ((↑) : Rat → Real)
    (fun _ _ hx => by exact_mod_cast hx) (h1 _ hq)

theorem quantilesReal_bounds (data : List Rat) (n : Nat) :
    Pre data n Method.inclusive → ∀ r, quantilesReal data n Method.inclusive = some r →
      ∀ x ∈ r, (lo data : Real) ≤ x ∧ x ≤ (hi data : Real) := by
  intro h r hr x hx
  have h1 := bounds_thm data n h
  have hguard : 2 ≤ data.length ∧ 1 ≤ n := ⟨h.1, h.2.1⟩
  have hq : quantiles data n Method.inclusive = some (cutPoints (sortData data) n Method.inclusive) := by
    simp only [quantiles, if_pos hguard]
  rw [quantilesReal, hq, Option.map_some] at hr
  injection hr with hr2
  subst hr2
  rw [List.mem_map] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  have h2 := h1 _ hq y hy
  subst hxy
  exact ⟨by exact_mod_cast h2.1, by exact_mod_cast h2.2⟩

theorem quantilesReal_median (data : List Rat) (m : Method) :
    Pre data 2 m →
      quantilesReal data 2 m = some (([median data] : List Rat).map (((↑) : Rat → Real))) := by
  intro h
  simp [quantilesReal, median_thm data m h]

theorem quantilesReal_perm (data data' : List Rat) (n : Nat) (m : Method) :
    Pre data n m → data.Perm data' → quantilesReal data n m = quantilesReal data' n m := by
  intro h hp
  simp [quantilesReal, perm_thm data data' n m h hp]

end RealLayer


/-! ## 19. The interpolation formula and the classical group counts -/

/-- The mathematical content of "the cut points are linearly interpolated between data points":
when no clamping occurs, the exclusive cut point is the linear interpolation of the sorted data at
the rescaled position `i * (ld + 1) / n`, i.e. between `data[j-1]` and `data[j]` with weight
`i*(ld+1)/n - j`. -/
theorem exclPoint_interp (s : List Rat) (n i : Nat) (hn : 1 ≤ n)
    (h : exclJ s n i = i * (s.length + 1) / n) :
    exclPoint s n i = s.getD (exclJ s n i - 1) 0
      + (((i * (s.length + 1) : Nat) : Rat) / (n : Rat) - (exclJ s n i : Rat))
        * (s.getD (exclJ s n i) 0 - s.getD (exclJ s n i - 1) 0) := by
  have hn0 : (n : Rat) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  have hmod : exclD s n i = (i * (s.length + 1) % n : Nat) := exclD_eq_mod s h
  have hdiv : ((i * (s.length + 1) : Nat) : Rat) =
      ((i * (s.length + 1) / n : Nat) : Rat) * (n : Rat)
        + ((i * (s.length + 1) % n : Nat) : Rat) := by
    have e : i * (s.length + 1) / n * n + i * (s.length + 1) % n = i * (s.length + 1) := by
      rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
    have e2 : ((i * (s.length + 1) / n * n + i * (s.length + 1) % n : Nat) : Rat) =
        ((i * (s.length + 1) : Nat) : Rat) := congrArg (fun x : Nat => (x : Rat)) e
    rw [Nat.cast_add, Nat.cast_mul] at e2
    linarith
  have h2 : (((i * (s.length + 1) % n : Nat) : Int) : Rat) =
      ((i * (s.length + 1) : Nat) : Rat) - ((i * (s.length + 1) / n : Nat) : Rat) * (n : Rat) := by
    simp only [Int.cast_natCast]
    linarith [hdiv]
  have hkey : ((exclD s n i : Rat) / (n : Rat)) =
      ((i * (s.length + 1) : Nat) : Rat) / (n : Rat) - (exclJ s n i : Rat) := by
    rw [hmod, h, h2, sub_div, mul_div_assoc, div_self hn0, mul_one]
  rw [exclPoint_eq s n i hn, hkey]

/-- The same for the inclusive method: interpolation at the rescaled position `i * (ld - 1) / n`
between `data[j]` and `data[j+1]`. -/
theorem inclPoint_interp (s : List Rat) (n i : Nat) (hn : 1 ≤ n) :
    inclPoint s n i = s.getD (inclJ s n i) 0
      + (((i * (s.length - 1) : Nat) : Rat) / (n : Rat) - (inclJ s n i : Rat))
        * (s.getD (inclJ s n i + 1) 0 - s.getD (inclJ s n i) 0) := by
  have hn0 : (n : Rat) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  have hmod : inclD s n i = (i * (s.length - 1) % n : Nat) := inclD_eq_mod s n i
  have hdiv : ((i * (s.length - 1) : Nat) : Rat) =
      ((i * (s.length - 1) / n : Nat) : Rat) * (n : Rat)
        + ((i * (s.length - 1) % n : Nat) : Rat) := by
    have e : i * (s.length - 1) / n * n + i * (s.length - 1) % n = i * (s.length - 1) := by
      rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
    have e2 : ((i * (s.length - 1) / n * n + i * (s.length - 1) % n : Nat) : Rat) =
        ((i * (s.length - 1) : Nat) : Rat) := congrArg (fun x : Nat => (x : Rat)) e
    rw [Nat.cast_add, Nat.cast_mul] at e2
    linarith
  have h3 : (((i * (s.length - 1) % n : Nat) : Int) : Rat) =
      ((i * (s.length - 1) : Nat) : Rat) - ((i * (s.length - 1) / n : Nat) : Rat) * (n : Rat) := by
    simp only [Int.cast_natCast]
    linarith [hdiv]
  have hkey : ((inclD s n i : Rat) / (n : Rat)) =
      ((i * (s.length - 1) : Nat) : Rat) / (n : Rat) - (inclJ s n i : Rat) := by
    simp only [inclJ]
    rw [hmod, h3, sub_div, mul_div_assoc, div_self hn0, mul_one]
  rw [inclPoint_eq s n i hn, hkey]

/-- `n = 4` (the default): three quartiles. -/
theorem quartiles_length (data : List Rat) (m : Method) (h : Pre data 4 m) :
    (quantiles data 4 m).map List.length = some 3 := length_thm data 4 m h

/-- `n = 10`: nine deciles. -/
theorem deciles_length (data : List Rat) (m : Method) (h : Pre data 10 m) :
    (quantiles data 10 m).map List.length = some 9 := length_thm data 10 m h

/-- `n = 100`: the 99 cut points that separate the data into 100 equal sized groups. -/
theorem percentiles_length (data : List Rat) (m : Method) (h : Pre data 100 m) :
    (quantiles data 100 m).map List.length = some 99 := length_thm data 100 m h

end StatisticsQuantiles
