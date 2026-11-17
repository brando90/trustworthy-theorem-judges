import Mathlib

/-!
# VeriBench — Duplicate Characters

Translation of the Python function `duplicate_chars`.

```python
def duplicate_chars(s: str) -> str:
    if not isinstance(s, str):
        raise ValueError("Input must be a string")
    return ''.join(c * 2 for c in s)
```

Each Unicode code point of the input is written twice, in order.
The empty string is returned unchanged. A non-string input (modelled by
`none`, the Python test's `None`) raises `ValueError` with the message
`"Input must be a string"`.

`String.length` counts Unicode code points, matching Python 3 `len`.
-/

namespace «41_duplicate_chars»

/-- Character list produced by `''.join(c * 2 for c in cs)`. -/
def dupList (cs : List Char) : List Char :=
  cs.flatMap fun c => [c, c]

/-- Functional body of `duplicate_chars`: duplicate every code point. -/
def duplicate_chars (s : String) : String :=
  (dupList s.data).asString

/--
Python `pre`: `isinstance(s, str)`.

Lean's `String` type already guarantees this, so the Boolean guard is `true`
for every well-typed input. Non-strings are represented separately by
`duplicate_chars_checked`.
-/
def pre (_s : String) : Bool :=
  true

/--
Total model of the Python function, including the `ValueError` guard.

`none` stands for a non-string value such as `None`.
-/
def duplicate_chars_checked (inp : Option String) : Except String String :=
  match inp with
  | none => Except.error "Input must be a string"
  | some s =>
    if pre s then Except.ok (duplicate_chars s)
    else Except.error "Input must be a string"

/-! ## Unit tests -/

example : duplicate_chars "abc" = "aabbcc" := by native_decide

example : duplicate_chars "" = "" := by native_decide

example : duplicate_chars "!a " = "!!aa  " := by native_decide

example : duplicate_chars "é" = "éé" := by native_decide

example : duplicate_chars "a😀b" = "aa😀😀bb" := by native_decide

example : duplicate_chars "\n" = "\n\n" := by native_decide

example : duplicate_chars_checked none = Except.error "Input must be a string" := by
  rfl

example : duplicate_chars_checked (some "abc") = Except.ok "aabbcc" := by
  rfl

example :
    (match duplicate_chars_checked none with
      | Except.error msg => msg == "Input must be a string"
      | Except.ok _ => false) = true := by
  native_decide

example :
    (match duplicate_chars_checked (some "abc") with
      | Except.ok t => t == "aabbcc"
      | Except.error _ => false) = true := by
  native_decide

#eval duplicate_chars "abc"
#eval duplicate_chars ""
#eval duplicate_chars "!a "
#eval duplicate_chars "é"
#eval duplicate_chars_checked none
#eval duplicate_chars_checked (some "abc")

/-! ## Pre-condition -/

/-- The input is a string, i.e. Python `pre(s)` holds. -/
def Pre (s : String) : Prop :=
  pre s = true

/-! ## Auxiliary list lemmas -/

theorem length_eq_data_length (s : String) : s.length = s.data.length := by
  cases s
  simp

theorem dupList_nil : dupList [] = [] := by
  simp [dupList]

theorem dupList_cons (c : Char) (cs : List Char) :
    dupList (c :: cs) = c :: c :: dupList cs := by
  simp [dupList, List.flatMap_cons]

theorem dupList_length (cs : List Char) : (dupList cs).length = 2 * cs.length := by
  induction cs with
  | nil => simp [dupList]
  | cons c cs ih =>
    rw [dupList_cons]
    simp only [List.length_cons]
    rw [ih]
    omega

theorem dupList_append (xs ys : List Char) :
    dupList (xs ++ ys) = dupList xs ++ dupList ys := by
  simp [dupList, List.flatMap_append]

theorem data_eq (s : String) : (duplicate_chars s).data = dupList s.data := by
  simp [duplicate_chars, List.asString]

theorem dupList_get? (cs : List Char) (i : Nat) (hi : i < cs.length) :
    (dupList cs)[2 * i]? = cs[i]? ∧ (dupList cs)[2 * i + 1]? = cs[i]? := by
  induction cs generalizing i with
  | nil => simp at hi
  | cons c cs ih =>
    cases i with
    | zero =>
      simp [dupList_cons]
    | succ i =>
      have hi' : i < cs.length := Nat.lt_of_succ_lt_succ hi
      have ih' := ih i hi'
      have shift (k : Nat) (hk : 2 ≤ k) :
          (dupList (c :: cs))[k]? = (dupList cs)[k - 2]? := by
        simp only [dupList, List.flatMap_cons]
        rw [List.getElem?_append_right (l₁ := [c, c]) (by simpa using hk)]
        rfl
      have k0 : 2 ≤ 2 * (i + 1) := by omega
      have k1 : 2 ≤ 2 * (i + 1) + 1 := by omega
      have e0 : 2 * (i + 1) - 2 = 2 * i := by omega
      have e1 : 2 * (i + 1) + 1 - 2 = 2 * i + 1 := by omega
      constructor
      · rw [shift (2 * (i + 1)) k0, e0]
        simpa [List.getElem?_cons_succ] using ih'.1
      · rw [shift (2 * (i + 1) + 1) k1, e1]
        simpa [List.getElem?_cons_succ] using ih'.2

/-- Keep the first character of every adjacent pair. A trailing singleton is dropped. -/
def unpair : List Char → List Char
  | [] => []
  | c :: cs =>
    match cs with
    | [] => []
    | _ :: rest => c :: unpair rest

theorem unpair_dup_cons (c : Char) (cs : List Char) :
    unpair (c :: c :: cs) = c :: unpair cs :=
  rfl

theorem unpair_dupList (cs : List Char) : unpair (dupList cs) = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [dupList_cons, unpair_dup_cons, ih]

theorem dupList_count (c : Char) (cs : List Char) :
    (dupList cs).count c = 2 * cs.count c := by
  induction cs with
  | nil => simp [dupList]
  | cons x cs ih =>
    rw [dupList_cons, List.count_cons, List.count_cons, ih]
    by_cases h : x = c
    · simp [h]
      omega
    · simp [h]

theorem dupList_sublist (cs : List Char) : List.Sublist cs (dupList cs) := by
  induction cs with
  | nil =>
    rw [dupList_nil]
  | cons c cs ih =>
    rw [dupList_cons]
    exact List.Sublist.cons₂ c (List.Sublist.cons c ih)

theorem join_data (acc : String) (cs : List Char) :
    ((cs.map fun c => String.singleton c ++ String.singleton c).foldl
        (fun r t => r ++ t) acc).data
      = acc.data ++ dupList cs := by
  induction cs generalizing acc with
  | nil => simp [dupList]
  | cons c cs ih =>
    simp [List.map_cons, List.foldl_cons, dupList, List.flatMap_cons, ih,
      String.data_append, String.data_singleton, List.append_assoc]

/-! ## Properties -/

/-- The result's code points are the input's code points, each repeated twice. -/
def data_prop (s : String) : Prop :=
  (duplicate_chars s).data = s.data.flatMap fun c => [c, c]

theorem data_thm (s : String) : data_prop s := by
  simp [data_prop, data_eq, dupList]

/-- Python `len(duplicate_chars(s)) = 2 * len(s)`. -/
def length_prop (s : String) : Prop :=
  (duplicate_chars s).length = 2 * s.length

theorem length_thm (s : String) : length_prop s := by
  unfold length_prop
  rw [length_eq_data_length (duplicate_chars s), data_eq, dupList_length,
    length_eq_data_length]

/-- Documented edge case: the empty string is unchanged. -/
def empty_prop : Prop :=
  duplicate_chars "" = ""

theorem empty_thm : empty_prop := by
  simp [empty_prop, duplicate_chars, dupList, List.asString]

/-- The result is empty exactly when the input is empty. -/
def empty_iff_prop (s : String) : Prop :=
  duplicate_chars s = "" ↔ s = ""

theorem empty_iff_thm (s : String) : empty_iff_prop s := by
  unfold empty_iff_prop
  constructor
  · intro h
    have hlen : (duplicate_chars s).length = 0 := by
      simpa [String.length_empty] using congrArg String.length h
    rw [length_thm] at hlen
    have hz : s.length = 0 := by omega
    apply String.ext
    rw [length_eq_data_length] at hz
    exact List.eq_nil_of_length_eq_zero hz
  · intro h
    subst h
    exact empty_thm

/-- Duplication distributes over string concatenation. -/
def concat_prop (s t : String) : Prop :=
  duplicate_chars (s ++ t) = duplicate_chars s ++ duplicate_chars t

theorem concat_thm (s t : String) : concat_prop s t := by
  unfold concat_prop
  apply String.ext
  simp [data_eq, String.data_append, dupList_append]

/-- A one-character string is the Python expression `c * 2`. -/
def singleton_prop (c : Char) : Prop :=
  duplicate_chars (String.singleton c) = String.singleton c ++ String.singleton c

theorem singleton_thm (c : Char) : singleton_prop c := by
  unfold singleton_prop
  apply String.ext
  simp [data_eq, dupList, String.data_singleton, String.data_append]

/--
Positional reading of the duplicated string: the code point at index `i`
occupies both index `2 * i` and index `2 * i + 1` of the result.
-/
def index_prop (s : String) : Prop :=
  ∀ i, i < s.length →
    (duplicate_chars s).data[2 * i]? = s.data[i]? ∧
    (duplicate_chars s).data[2 * i + 1]? = s.data[i]?

theorem index_thm (s : String) : index_prop s := by
  intro i hi
  have hi' : i < s.data.length := by
    rwa [← length_eq_data_length]
  simpa [data_eq] using dupList_get? s.data i hi'

/-- The first code point of each duplicated pair rebuilds the input. -/
def recover_prop (s : String) : Prop :=
  unpair (duplicate_chars s).data = s.data

theorem recover_thm (s : String) : recover_prop s := by
  simp [recover_prop, data_eq, unpair_dupList]

/-- Every code point occurs twice as often in the result as in the input. -/
def count_prop (s : String) : Prop :=
  ∀ c : Char, (duplicate_chars s).data.count c = 2 * s.data.count c

theorem count_thm (s : String) : count_prop s := by
  intro c
  simpa [data_eq] using dupList_count c s.data

/--
`duplicate_chars` is `String.join` of the two-character strings `c * 2`,
the direct reading of `''.join(c * 2 for c in s)`.
-/
def join_form_prop (s : String) : Prop :=
  duplicate_chars s =
    String.join (s.data.map fun c => String.singleton c ++ String.singleton c)

theorem join_form_thm (s : String) : join_form_prop s := by
  unfold join_form_prop
  apply String.ext
  rw [data_eq, String.join, join_data]
  simp

/-- The input code points form a subsequence of the result (order is preserved). -/
def sublist_prop (s : String) : Prop :=
  List.Sublist s.data (duplicate_chars s).data

theorem sublist_thm (s : String) : sublist_prop s := by
  simp [sublist_prop, data_eq, dupList_sublist]

/-- The result uses exactly the code points that occur in the input. -/
def mem_prop (s : String) : Prop :=
  ∀ c : Char, c ∈ (duplicate_chars s).data ↔ c ∈ s.data

theorem mem_thm (s : String) : mem_prop s := by
  intro c
  rw [data_eq]
  simp only [dupList, List.mem_flatMap]
  constructor
  · rintro ⟨a, ha, hmem⟩
    have hc : c = a ∨ c = a := by
      simpa [List.mem_cons, List.mem_singleton] using hmem
    rcases hc with rfl | rfl <;> exact ha
  · intro ha
    exact ⟨c, ha, by simp⟩

/-- Python rejects a non-string with `ValueError("Input must be a string")`. -/
def nonstring_prop : Prop :=
  duplicate_chars_checked none = Except.error "Input must be a string"

theorem nonstring_thm : nonstring_prop := by
  simp [nonstring_prop, duplicate_chars_checked]

/-- On a real string the guard succeeds and returns `duplicate_chars`. -/
def checked_ok_prop (s : String) : Prop :=
  duplicate_chars_checked (some s) = Except.ok (duplicate_chars s)

theorem checked_ok_thm (s : String) : checked_ok_prop s := by
  simp [checked_ok_prop, duplicate_chars_checked, pre]

/-! ## Post-condition -/

/--
Full specification of one successful call: the output code-point list is the
input with each code point doubled, and the consequences of that fact
(length, indexing, recovery, counts, emptiness, the `join` form, subsequence
and membership). Concatenation is included universally in the second argument.
-/
def Post_prop (s : String) : Prop :=
  data_prop s ∧
  length_prop s ∧
  index_prop s ∧
  recover_prop s ∧
  count_prop s ∧
  empty_iff_prop s ∧
  join_form_prop s ∧
  sublist_prop s ∧
  mem_prop s ∧
  (∀ t : String, concat_prop s t)

/-! ## Property-based tests

Executable checks of every `_prop` and of `Post_prop`.
Random tests use Plausible. Bounded tests exhaust small inputs.
-/

/-- Boolean form of `index_prop`, checking every in-range index. -/
def indexOk (s : String) : Bool :=
  (List.range s.length).all fun i =>
    ((duplicate_chars s).data[2 * i]? == s.data[i]?) &&
    ((duplicate_chars s).data[2 * i + 1]? == s.data[i]?)

/-- Boolean form of `mem_prop`. -/
def memOk (s : String) : Bool :=
  s.data.all (fun c => (duplicate_chars s).data.elem c) &&
  (duplicate_chars s).data.all (fun c => s.data.elem c)

/--
Boolean form of the single-input conjuncts of `Post_prop`.
`count_prop` and `concat_prop` quantify over an extra character or string;
those conjuncts are checked by the Plausible tests below.
-/
def postOk (s : String) : Bool :=
  ((duplicate_chars s).data == s.data.flatMap fun c => [c, c]) &&
  ((duplicate_chars s).length == 2 * s.length) &&
  indexOk s &&
  (unpair (duplicate_chars s).data == s.data) &&
  ((duplicate_chars s == "") == (s == "")) &&
  (duplicate_chars s ==
    String.join (s.data.map fun c => String.singleton c ++ String.singleton c)) &&
  s.data.isSublist (duplicate_chars s).data &&
  memOk s

-- PBT: data_prop
#eval Plausible.Testable.check
  (∀ s : String, (duplicate_chars s).data = s.data.flatMap fun c => [c, c])

-- PBT: length_prop
#eval Plausible.Testable.check
  (∀ s : String, (duplicate_chars s).length = 2 * s.length)

-- PBT: empty_prop
example : (decide (duplicate_chars "" = "")) = true := by native_decide

-- PBT: empty_iff_prop
#eval Plausible.Testable.check
  (∀ s : String, duplicate_chars s = "" ↔ s = "")

-- PBT: concat_prop
#eval Plausible.Testable.check
  (∀ s t : String, duplicate_chars (s ++ t) = duplicate_chars s ++ duplicate_chars t)

example : (List.range 10).all (fun n =>
    (List.range 10).all (fun m =>
      let s := (List.replicate n 'a').asString
      let t := (List.replicate m 'b').asString
      duplicate_chars (s ++ t) == duplicate_chars s ++ duplicate_chars t)) = true := by
  native_decide

-- PBT: singleton_prop
#eval Plausible.Testable.check
  (∀ c : Char,
    duplicate_chars (String.singleton c) = String.singleton c ++ String.singleton c)

-- PBT: index_prop
#eval Plausible.Testable.check (∀ s : String, indexOk s = true)

example : (List.range 30).all (fun n =>
    indexOk (List.replicate n 'a').asString) = true := by
  native_decide

-- PBT: recover_prop
#eval Plausible.Testable.check
  (∀ s : String, unpair (duplicate_chars s).data = s.data)

-- PBT: count_prop
#eval Plausible.Testable.check
  (∀ s : String, ∀ c : Char, (duplicate_chars s).data.count c = 2 * s.data.count c)

-- PBT: join_form_prop
#eval Plausible.Testable.check
  (∀ s : String,
    duplicate_chars s =
      String.join (s.data.map fun c => String.singleton c ++ String.singleton c))

-- PBT: sublist_prop
#eval Plausible.Testable.check
  (∀ s : String, s.data.isSublist (duplicate_chars s).data = true)

-- PBT: mem_prop
#eval Plausible.Testable.check (∀ s : String, memOk s = true)

/-- Boolean observation of the `ValueError` branch. `Except` has no `BEq` here. -/
def nonstringOk : Bool :=
  match duplicate_chars_checked none with
  | Except.error msg => msg == "Input must be a string"
  | Except.ok _ => false

/-- Boolean observation of the successful guard. -/
def checkedOkBool (s : String) : Bool :=
  match duplicate_chars_checked (some s) with
  | Except.ok t => t == duplicate_chars s
  | Except.error _ => false

-- PBT: nonstring_prop
example : nonstringOk = true := by native_decide

-- PBT: checked_ok_prop
#eval Plausible.Testable.check (∀ s : String, checkedOkBool s = true)

example : (List.range 20).all (fun n =>
    checkedOkBool (List.replicate n 'z').asString) = true := by
  native_decide

-- PBT: Post_prop (single-input conjuncts, counts, and concatenation)
#eval Plausible.Testable.check
  (∀ s t : String, ∀ c : Char,
    postOk s = true ∧
    (duplicate_chars s).data.count c = 2 * s.data.count c ∧
    duplicate_chars (s ++ t) = duplicate_chars s ++ duplicate_chars t)

example : ["", "a", "abc", "!a ", " ", "é", "a😀b", "∀", "\n"].all postOk = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (s : String) (_h : Pre s) : Post_prop s :=
  ⟨data_thm s, length_thm s, index_thm s, recover_thm s, count_thm s,
   empty_iff_thm s, join_form_thm s, sublist_thm s, mem_thm s, fun t => concat_thm s t⟩

/-- The guard plus the string specification, for every Python-style input. -/
theorem checked_correctness_thm (inp : Option String) :
    (inp = none → duplicate_chars_checked inp = Except.error "Input must be a string") ∧
    (∀ s, inp = some s →
      duplicate_chars_checked inp = Except.ok (duplicate_chars s) ∧ Post_prop s) := by
  cases inp with
  | none =>
    constructor
    · intro _
      exact nonstring_thm
    · intro s hs
      cases hs
  | some s =>
    constructor
    · intro hs
      cases hs
    · intro s' hs
      cases hs
      exact ⟨checked_ok_thm s, correctness_thm s rfl⟩

/-! ## Imperative implementation -/

/--
Imperative duplicate: walk the code points, pushing each one twice into an
accumulator. This is the loop inside `''.join(c * 2 for c in s)`.
-/
def duplicate_chars_imp (s : String) : String :=
  Id.run do
    let mut acc : String := ""
    for c in s.data do
      acc := (acc.push c).push c
    return acc

/-! ## Imperative tests -/

example : duplicate_chars_imp "abc" = "aabbcc" := by native_decide

example : duplicate_chars_imp "" = "" := by native_decide

example : duplicate_chars_imp "!a " = "!!aa  " := by native_decide

example : duplicate_chars_imp "é" = "éé" := by native_decide

example : duplicate_chars_imp "a😀b" = "aa😀😀bb" := by native_decide

example : duplicate_chars "abc" = duplicate_chars_imp "abc" := by native_decide

example : duplicate_chars "" = duplicate_chars_imp "" := by native_decide

example : (List.range 30).all (fun n =>
    let s := (List.replicate n 'q').asString
    duplicate_chars s == duplicate_chars_imp s) = true := by
  native_decide

#eval duplicate_chars_imp "abc"
#eval duplicate_chars_imp ""
#eval duplicate_chars_imp "!a "

/-! ## Equivalence -/

theorem foldl_push (acc : String) (cs : List Char) :
    (cs.foldl (fun a c => (a.push c).push c) acc).data = acc.data ++ dupList cs := by
  induction cs generalizing acc with
  | nil => simp [dupList]
  | cons c cs ih =>
    simp [List.foldl_cons, dupList, List.flatMap_cons, ih, String.data_push, List.append_assoc]

theorem imp_eq_foldl (s : String) :
    duplicate_chars_imp s = s.data.foldl (fun acc c => (acc.push c).push c) "" := by
  simp [duplicate_chars_imp, Id.run, List.forIn_pure_yield_eq_foldl]
  rfl

/-- The functional implementation and the imperative loop agree on every string. -/
theorem equivalence_thm (s : String) : duplicate_chars s = duplicate_chars_imp s := by
  apply String.ext
  rw [imp_eq_foldl, foldl_push]
  simp [data_eq, dupList]

end «41_duplicate_chars»
