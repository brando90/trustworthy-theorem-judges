import Mathlib

/-!
# Levenshtein edit distance

A Lean 4 formalization of the Python program `edit_distance.py`, which computes the
Levenshtein edit distance (minimum number of single-element insertions, deletions and
substitutions) between two sequences.

The Python function accepts a `str` or a `list`; anything else violates the
pre-condition and raises `ValueError`.  We model this with a small `PyVal` universe of
Python values (strings, lists of elements, and non-sequences), a pre-condition `Pre`
selecting the sequence-shaped values, and the total front-end
`edit_distance : PyVal → PyVal → Option Nat`, which returns `none` exactly when `Pre`
fails (`none` models raising `ValueError`).

The mathematical core is `editDist : List α → List α → Nat`, the usual recursive
characterisation of the Levenshtein distance; it is exactly the recurrence that the
Python code evaluates in its DP table `dp`.  `editDistImp` is an imperative
`Id.run do` re-implementation with mutable state that keeps a single row of that table
alive, and `editDistImp_eq` proves that the two agree.
-/

namespace edit_distance

set_option linter.dupNamespace false

universe u
variable {α : Type u}

/-! ## Functional implementation -/

/-- Levenshtein edit distance between two lists.

`dp[i][j]` in the Python code is the distance between the length-`i` prefix of `s1` and
the length-`j` prefix of `s2`, and the recurrence used there (a `min` over deletion,
insertion and substitution) is exactly the one below. -/
def editDist [DecidableEq α] : List α → List α → Nat
  | [], t => t.length
  | s, [] => s.length
  | a :: s, b :: t =>
      if a = b then editDist s t
      else 1 + min (editDist s (b :: t)) (min (editDist (a :: s) t) (editDist s t))
termination_by s t => s.length + t.length

@[simp] theorem editDist_nil_left [DecidableEq α] (t : List α) :
    editDist ([] : List α) t = t.length := by
  rw [editDist]

@[simp] theorem editDist_nil_right [DecidableEq α] (s : List α) :
    editDist s ([] : List α) = s.length := by
  cases s with
  | nil => rw [editDist]
  | cons a s => rw [editDist]; simp

/-- The recursive step, matching the body of the Python double loop. -/
theorem editDist_cons_cons [DecidableEq α] (a : α) (s : List α) (b : α) (t : List α) :
    editDist (a :: s) (b :: t) =
      if a = b then editDist s t
      else 1 + min (editDist s (b :: t)) (min (editDist (a :: s) t) (editDist s t)) := by
  rw [editDist]

/-! ### Python's value universe and the total front-end -/

/-- Elements of the Python sequences occurring in the tests: characters (from `str`)
and integers (from `list`). -/
inductive Elem where
  | chr : Char → Elem
  | int : Int → Elem
deriving DecidableEq, Repr, Inhabited

/-- The Python values the program may be applied to.  `str` and `list` are the legal
("sequence") inputs; `int` stands for a non-sequence input such as `123`. -/
inductive PyVal where
  | str : String → PyVal
  | list : List Elem → PyVal
  | int : Int → PyVal
deriving DecidableEq, Repr, Inhabited

/-- `isinstance(v, (str, list))`. -/
def PyVal.isSeq : PyVal → Bool
  | .str _ => true
  | .list _ => true
  | .int _ => false

/-- Python's uniform view of an input: `list(s)` for a string, the list itself for a
list.  (Non-sequences are rejected by the pre-condition, so their value is irrelevant.) -/
def PyVal.toSeq : PyVal → List Elem
  | .str s => s.data.map Elem.chr
  | .list l => l
  | .int _ => []

/-- Total model of the Python function `edit_distance`.  `none` models `ValueError`. -/
def edit_distance (x y : PyVal) : Option Nat :=
  if x.isSeq && y.isSeq then some (editDist x.toSeq y.toSeq) else none

/-- Convenience wrapper for the string case. -/
def editDistStr (s t : String) : Nat := editDist s.data t.data

/-! ## Unit tests (mirroring the Python `check` function) -/

-- Basic functionality tests with strings
example : edit_distance (.str "hello") (.str "hello") = some 0 := by native_decide
example : edit_distance (.str "cat") (.str "bat") = some 1 := by native_decide
example : edit_distance (.str "cat") (.str "cats") = some 1 := by native_decide
example : edit_distance (.str "cats") (.str "cat") = some 1 := by native_decide
example : edit_distance (.str "cat") (.str "dog") = some 3 := by native_decide
example : edit_distance (.str "kitten") (.str "sitting") = some 3 := by native_decide

-- Edge cases
example : edit_distance (.str "") (.str "") = some 0 := by native_decide
example : edit_distance (.str "") (.str "abc") = some 3 := by native_decide
example : edit_distance (.str "ab") (.str "") = some 2 := by native_decide
example : edit_distance (.str "a") (.str "b") = some 1 := by native_decide

-- Tests with lists of integers
example : edit_distance (.list [.int 1, .int 2, .int 3]) (.list [.int 1, .int 2, .int 3])
    = some 0 := by native_decide
example : edit_distance (.list [.int 1, .int 2, .int 3]) (.list [.int 1, .int 4, .int 3])
    = some 1 := by native_decide
example : edit_distance (.list [.int 1, .int 2, .int 3, .int 4]) (.list [.int 1, .int 3, .int 4])
    = some 1 := by native_decide
example : edit_distance (.list [.int 1, .int 2, .int 3]) (.list [.int 4, .int 5, .int 6])
    = some 3 := by native_decide
example : edit_distance (.list [.int 1, .int 2, .int 3, .int 4, .int 5])
    (.list [.int 6, .int 7, .int 8]) = some 5 := by native_decide

-- Tests with character lists (`list("hello") == ['h','e','l','l','o']`)
example : edit_distance (.list [.chr 'h', .chr 'e', .chr 'l', .chr 'l', .chr 'o'])
    (.list [.chr 'h', .chr 'e', .chr 'l', .chr 'l', .chr 'o']) = some 0 := by native_decide
example : edit_distance (.list [.chr 'c', .chr 'a', .chr 't'])
    (.list [.chr 'b', .chr 'a', .chr 't']) = some 1 := by native_decide
example : edit_distance (.list [.chr 'c', .chr 'a', .chr 't'])
    (.list [.chr 'c', .chr 'a', .chr 't', .chr 's']) = some 1 := by native_decide
example : edit_distance (.list [.chr 'c', .chr 'a', .chr 't', .chr 's'])
    (.list [.chr 'c', .chr 'a', .chr 't']) = some 1 := by native_decide
-- a `str` and the corresponding list of characters behave identically
example : edit_distance (.str "cat") (.list [.chr 'b', .chr 'a', .chr 't']) = some 1 := by
  native_decide

-- Longer sequences
example : edit_distance (.str "intention") (.str "execution") = some 5 := by native_decide
example : edit_distance (.str "saturday") (.str "sunday") = some 3 := by native_decide

-- Same length, all different
example : edit_distance (.str "abc") (.str "def") = some 3 := by native_decide
example : edit_distance (.str "xyz") (.str "abc") = some 3 := by native_decide

-- One character strings
example : edit_distance (.str "a") (.str "a") = some 0 := by native_decide
example : edit_distance (.str "a") (.str "b") = some 1 := by native_decide
example : edit_distance (.str "a") (.str "") = some 1 := by native_decide
example : edit_distance (.str "") (.str "a") = some 1 := by native_decide

-- Repeated characters
example : edit_distance (.str "aaa") (.str "aa") = some 1 := by native_decide
example : edit_distance (.str "aa") (.str "aaa") = some 1 := by native_decide
example : edit_distance (.str "aaaa") (.str "bbbb") = some 4 := by native_decide

-- Negative test: `edit_distance(123, "abc")` raises `ValueError`
example : edit_distance (.int 123) (.str "abc") = none := by native_decide

#eval edit_distance (.str "kitten") (.str "sitting")
#eval edit_distance (.str "intention") (.str "execution")
#eval edit_distance (.int 123) (.str "abc")
#eval editDistStr "saturday" "sunday"

/-! ## Pre-condition -/

/-- `pre(s1, s2)` from the Python source: both inputs must be a `str` or a `list`. -/
def Pre (x y : PyVal) : Prop := x.isSeq = true ∧ y.isSeq = true

instance (x y : PyVal) : Decidable (Pre x y) := by
  unfold Pre; infer_instance

/-- The program raises `ValueError` (modelled by `none`) exactly when `Pre` fails. -/
theorem edit_distance_eq_none_iff (x y : PyVal) :
    edit_distance x y = none ↔ ¬ Pre x y := by
  simp [edit_distance, Pre]

/-- Under the pre-condition the program returns the edit distance of the sequence views
of its two arguments. -/
theorem edit_distance_eq_some (x y : PyVal) (h : Pre x y) :
    edit_distance x y = some (editDist x.toSeq y.toSeq) := by
  obtain ⟨hx, hy⟩ := h
  simp [edit_distance, hx, hy]

/-! ## Properties of the edit distance -/

/-- Property: the distance from a sequence to itself is `0`
(`edit_distance("hello", "hello") == 0`). -/
def self_prop [DecidableEq α] (s : List α) : Prop := editDist s s = 0

theorem self_thm [DecidableEq α] (s : List α) : self_prop s := by
  unfold self_prop
  induction s with
  | nil => simp
  | cons a s ih => rw [editDist_cons_cons]; simpa using ih

/-- Property: the distance from the empty sequence is the length of the other one
(`edit_distance("", "abc") == 3`, `edit_distance("ab", "") == 2`). -/
def nil_prop [DecidableEq α] (s : List α) : Prop :=
    editDist ([] : List α) s = s.length ∧ editDist s ([] : List α) = s.length

theorem nil_thm [DecidableEq α] (s : List α) : nil_prop s :=
  ⟨editDist_nil_left s, editDist_nil_right s⟩

/-- Property: the distance is `0` exactly for equal sequences. -/
def eq_zero_prop [DecidableEq α] (s t : List α) : Prop := editDist s t = 0 ↔ s = t

theorem eq_zero_thm [DecidableEq α] (s t : List α) : eq_zero_prop s t := by
  unfold eq_zero_prop
  constructor
  · induction s, t using editDist.induct with
    | case1 t => intro h; simp at h; simp [h]
    | case2 s h => intro h2; simpa using h2
    | case3 s b t ih => intro h; rw [editDist_cons_cons, if_pos rfl] at h; simp [ih h]
    | case4 a s b t hab ih1 ih2 ih3 =>
        intro h; rw [editDist_cons_cons, if_neg hab] at h; exfalso; omega
  · rintro rfl; exact self_thm s

theorem editDist_eq_zero [DecidableEq α] (s t : List α) : editDist s t = 0 ↔ s = t :=
  eq_zero_thm s t

/-- Property: the distance is symmetric. -/
def comm_prop [DecidableEq α] (s t : List α) : Prop := editDist s t = editDist t s

theorem comm_thm [DecidableEq α] (s t : List α) : comm_prop s t := by
  unfold comm_prop
  induction s, t using editDist.induct with
  | case1 t => simp
  | case2 s h => simp
  | case3 s b t ih =>
      rw [editDist_cons_cons, editDist_cons_cons, if_pos rfl, if_pos rfl]; exact ih
  | case4 a s b t hab ih1 ih2 ih3 =>
      rw [editDist_cons_cons, editDist_cons_cons, if_neg hab, if_neg (Ne.symm hab),
        ih1, ih2, ih3]
      omega

theorem editDist_comm [DecidableEq α] (s t : List α) : editDist s t = editDist t s :=
  comm_thm s t

/-- Property: the distance never exceeds the length of the longer sequence
(one can substitute the common part and insert/delete the rest). -/
def le_max_prop [DecidableEq α] (s t : List α) : Prop :=
    editDist s t ≤ max s.length t.length

theorem le_max_thm [DecidableEq α] (s t : List α) : le_max_prop s t := by
  unfold le_max_prop
  induction s, t using editDist.induct with
  | case1 t => simp
  | case2 s h => simp
  | case3 s b t ih =>
      rw [editDist_cons_cons, if_pos rfl]; simp only [List.length_cons]; omega
  | case4 a s b t hab ih1 ih2 ih3 =>
      rw [editDist_cons_cons, if_neg hab]; simp only [List.length_cons]; omega

theorem editDist_le_max [DecidableEq α] (s t : List α) :
    editDist s t ≤ max s.length t.length := le_max_thm s t

/-- Property: each single edit changes the length by at most one, so the difference of
the lengths is a lower bound for the distance. -/
def length_bound_prop [DecidableEq α] (s t : List α) : Prop :=
    s.length ≤ editDist s t + t.length

theorem length_bound_thm [DecidableEq α] (s t : List α) : length_bound_prop s t := by
  unfold length_bound_prop
  induction s, t using editDist.induct with
  | case1 t => simp
  | case2 s h => simp
  | case3 s b t ih =>
      rw [editDist_cons_cons, if_pos rfl]; simp only [List.length_cons]; omega
  | case4 a s b t hab ih1 ih2 ih3 =>
      rw [editDist_cons_cons, if_neg hab]; simp only [List.length_cons] at *; omega

theorem editDist_length_bound [DecidableEq α] (s t : List α) :
    s.length ≤ editDist s t + t.length := length_bound_thm s t

/-- Property: prefixing both sequences with the same element does not change the
distance (`edit_distance("cat", "cats") == edit_distance("at", "ats")`). -/
def cons_same_prop [DecidableEq α] (a : α) (s t : List α) : Prop :=
    editDist (a :: s) (a :: t) = editDist s t

theorem cons_same_thm [DecidableEq α] (a : α) (s t : List α) : cons_same_prop a s t := by
  unfold cons_same_prop
  rw [editDist_cons_cons, if_pos rfl]

/-- Property: a common prefix is irrelevant
(`edit_distance("cat", "cats") == edit_distance("", "s")`). -/
def prefix_prop [DecidableEq α] (u s t : List α) : Prop :=
    editDist (u ++ s) (u ++ t) = editDist s t

theorem prefix_thm [DecidableEq α] (u s t : List α) : prefix_prop u s t := by
  unfold prefix_prop
  induction u with
  | nil => simp
  | cons a u ih =>
      rw [List.cons_append, List.cons_append, editDist_cons_cons, if_pos rfl]; exact ih

/-! ## Post-condition and correctness -/

/-- Post-condition: on legal inputs the program returns the Levenshtein distance of the
two sequence views, which is `0` iff the sequences are equal, is bounded above by the
maximum of the two lengths, bounded below by the difference of the two lengths, and is
symmetric in its arguments. -/
def Post_prop (x y : PyVal) : Prop :=
    ∃ r : Nat, edit_distance x y = some r ∧
      r = editDist x.toSeq y.toSeq ∧
      (r = 0 ↔ x.toSeq = y.toSeq) ∧
      r ≤ max x.toSeq.length y.toSeq.length ∧
      x.toSeq.length ≤ r + y.toSeq.length ∧
      y.toSeq.length ≤ r + x.toSeq.length ∧
      edit_distance y x = some r

/-- **Correctness**: the pre-condition implies the post-condition. -/
theorem correctness (x y : PyVal) (h : Pre x y) : Post_prop x y := by
  obtain ⟨hx, hy⟩ := h
  refine ⟨editDist x.toSeq y.toSeq, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [edit_distance, hx, hy]
  · exact editDist_eq_zero _ _
  · exact editDist_le_max _ _
  · exact editDist_length_bound _ _
  · have h2 := editDist_length_bound y.toSeq x.toSeq
    rwa [editDist_comm y.toSeq x.toSeq] at h2
  · simp [edit_distance, hx, hy, editDist_comm y.toSeq x.toSeq]

/-- Outside the pre-condition the program signals an error (`ValueError`). -/
theorem correctness_neg (x y : PyVal) (h : ¬ Pre x y) : edit_distance x y = none :=
  (edit_distance_eq_none_iff x y).2 h

/-! ## Imperative implementation

A direct transcription of the Python dynamic program, keeping only one row of the table
alive.  Rows are indexed by *suffixes* instead of prefixes: after the outer loop has
consumed the last `k` elements of `s`, the mutable list `prev` holds

`prev = [d s' u₀, d s' u₁, …, d s' u_n]`, where `s' = s.drop (|s| - k)`

and `u_j` is the suffix of `t` of length `j`.  The inner loop extends the row one entry
at a time using the deletion / insertion / substitution minimum, exactly as the Python
inner loop fills `dp[i][j]`. -/

/-- One step of the inner loop as a pure function on the loop state
`(new row built so far, unconsumed part of the previous row)`. -/
def step [DecidableEq α] (a : α) (st : List Nat × List Nat) (b : α) : List Nat × List Nat :=
  let acc := st.1
  let rest := st.2
  let pPrev := rest.headD 0
  let rest' := rest.tail
  let pCur := rest'.headD 0
  let c := if a = b then pPrev else 1 + min pCur (min (acc.headD 0) pPrev)
  (c :: acc, rest')

/-- Imperative DP implementation with mutable state, mirroring the Python nested loops. -/
def editDistImp [DecidableEq α] (s t : List α) : Nat := Id.run do
  -- base row: the distance from the empty sequence to a suffix of `t` is its length
  let mut prev : List Nat := List.range (t.length + 1)
  for a in s.reverse do
    -- `st.1` accumulates the new row, `st.2` walks along the previous row
    let mut st : List Nat × List Nat := ([prev.headD 0 + 1], prev)
    for b in t.reverse do
      let acc := st.1
      let rest := st.2
      let pPrev := rest.headD 0            -- substitution:  dp[i-1][j-1]
      let rest' := rest.tail
      let pCur := rest'.headD 0            -- deletion:      dp[i-1][j]
      let c := if a = b then pPrev else 1 + min pCur (min (acc.headD 0) pPrev)
      st := (c :: acc, rest')              -- `acc.headD 0` is the insertion  dp[i][j-1]
    prev := st.1.reverse
  return prev.getLastD 0

/-- Imperative front-end, mirroring the Python function including its error case. -/
def edit_distanceImp (x y : PyVal) : Option Nat := Id.run do
  if !(x.isSeq && y.isSeq) then
    return none
  return some (editDistImp x.toSeq y.toSeq)

/-! ### Imperative tests -/

example : edit_distanceImp (.str "hello") (.str "hello") = some 0 := by native_decide
example : edit_distanceImp (.str "cat") (.str "bat") = some 1 := by native_decide
example : edit_distanceImp (.str "cat") (.str "cats") = some 1 := by native_decide
example : edit_distanceImp (.str "cats") (.str "cat") = some 1 := by native_decide
example : edit_distanceImp (.str "cat") (.str "dog") = some 3 := by native_decide
example : edit_distanceImp (.str "kitten") (.str "sitting") = some 3 := by native_decide
example : edit_distanceImp (.str "") (.str "") = some 0 := by native_decide
example : edit_distanceImp (.str "") (.str "abc") = some 3 := by native_decide
example : edit_distanceImp (.str "ab") (.str "") = some 2 := by native_decide
example : edit_distanceImp (.str "a") (.str "b") = some 1 := by native_decide
example : edit_distanceImp (.list [.int 1, .int 2, .int 3]) (.list [.int 1, .int 4, .int 3])
    = some 1 := by native_decide
example : edit_distanceImp (.list [.int 1, .int 2, .int 3, .int 4]) (.list [.int 1, .int 3, .int 4])
    = some 1 := by native_decide
example : edit_distanceImp (.list [.int 1, .int 2, .int 3, .int 4, .int 5])
    (.list [.int 6, .int 7, .int 8]) = some 5 := by native_decide
example : edit_distanceImp (.str "intention") (.str "execution") = some 5 := by native_decide
example : edit_distanceImp (.str "saturday") (.str "sunday") = some 3 := by native_decide
example : edit_distanceImp (.str "aaa") (.str "aa") = some 1 := by native_decide
example : edit_distanceImp (.str "aaaa") (.str "bbbb") = some 4 := by native_decide
example : edit_distanceImp (.int 123) (.str "abc") = none := by native_decide

#eval edit_distanceImp (.str "kitten") (.str "sitting")
#eval edit_distanceImp (.str "intention") (.str "execution")

/-! ## Equivalence of the functional and imperative implementations -/

/-- The lengths of the suffixes of `t`, shortest first, are `[0, 1, …, |t|]`. -/
theorem tails_reverse_map_length (t : List α) :
    (t.tails.reverse).map List.length = List.range (t.length + 1) := by
  induction t with
  | nil => simp
  | cons b t ih =>
      rw [List.tails_cons, List.reverse_cons, List.map_append, ih]
      simp [List.range_succ]

theorem map_tails_headD (f : List α → Nat) (t : List α) (d : Nat) :
    (t.tails.map f).headD d = f t := by
  cases t <;> simp

theorem tails_getLast? (t : List α) : t.tails.getLast? = some [] := by
  induction t with
  | nil => simp
  | cons b t ih =>
      rw [List.tails_cons]
      cases hh : t.tails with
      | nil =>
          have h2 := List.length_tails t
          rw [hh] at h2; simp at h2
      | cons u us => rw [List.getLast?_cons_cons, ← hh]; exact ih

theorem getLastD_reverse (l : List Nat) (d : Nat) : l.reverse.getLastD d = l.headD d := by
  cases l with
  | nil => simp
  | cons b l => simp [List.getLastD_eq_getLast?, List.getLast?_reverse]

/-- The inner loop: starting from the row for `s` (stored shortest-suffix-first, possibly
followed by unread entries `Q`) it produces the row for `a :: s` (stored
longest-suffix-first) together with the unconsumed tail of the old row. -/
theorem inner_loop [DecidableEq α] (a : α) (s : List α) :
    ∀ (t : List α) (Q : List Nat),
      List.foldr (fun b st => step a st b)
          ([s.length + 1], (t.tails.reverse.map (editDist s)) ++ Q) t
        = (t.tails.map (editDist (a :: s)), editDist s t :: Q) := by
  intro t
  induction t with
  | nil => intro Q; simp [step]
  | cons b t ih =>
      intro Q
      rw [List.tails_cons, List.reverse_cons, List.map_append, List.append_assoc]
      simp only [List.map_cons, List.map_nil, List.singleton_append, List.foldr_cons]
      rw [ih (editDist s (b :: t) :: Q)]
      simp only [step, List.headD_cons, List.tail_cons]
      rw [editDist_cons_cons, map_tails_headD]

/-- The outer loop maintains the row invariant: after processing the last `|s|` elements
of the first sequence, `prev` is the row of distances from `s` to the suffixes of `t`. -/
theorem outer_loop [DecidableEq α] (t : List α) :
    ∀ (s : List α),
      List.foldr
          (fun a prev => (List.foldl (step a) ([prev.headD 0 + 1], prev) t.reverse).1.reverse)
          (List.range (t.length + 1)) s
        = (t.tails.map (editDist s)).reverse := by
  intro s
  induction s with
  | nil =>
      rw [← tails_reverse_map_length t, ← List.map_reverse]
      simp
  | cons a s ih =>
      rw [List.foldr_cons, ih, List.foldl_reverse]
      have hhead : ((t.tails.map (editDist s)).reverse).headD 0 = s.length := by
        simp [tails_getLast?]
      rw [hhead]
      have h := inner_loop a s t []
      rw [List.map_reverse] at h
      simp only [List.append_nil] at h
      rw [h]

/-- The `do`-block reduces to the corresponding pair of folds. -/
theorem editDistImp_eq_fold [DecidableEq α] (s t : List α) :
    editDistImp s t =
      (List.foldr
        (fun a prev => (List.foldl (step a) ([prev.headD 0 + 1], prev) t.reverse).1.reverse)
        (List.range (t.length + 1)) s).getLastD 0 := by
  simp [editDistImp, Id.run, step, List.foldl_reverse]
  rfl

/-- **Equivalence theorem**: the imperative DP computes the functional specification. -/
theorem editDistImp_eq [DecidableEq α] (s t : List α) : editDistImp s t = editDist s t := by
  rw [editDistImp_eq_fold, outer_loop t s, getLastD_reverse, map_tails_headD]

/-- **Equivalence theorem** for the Python front-ends, error case included. -/
theorem edit_distanceImp_eq (x y : PyVal) : edit_distanceImp x y = edit_distance x y := by
  unfold edit_distanceImp edit_distance
  by_cases h : x.isSeq && y.isSeq <;> simp [Id.run, h, editDistImp_eq] <;> rfl

end edit_distance
