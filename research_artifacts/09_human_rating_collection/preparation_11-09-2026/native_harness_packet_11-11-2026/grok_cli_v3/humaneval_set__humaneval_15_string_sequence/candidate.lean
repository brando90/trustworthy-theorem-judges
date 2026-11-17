import Mathlib
import Batteries.Data.Nat.Digits

/-!
# HumanEval/15 — `string_sequence`

Python source (`humaneval_15_string_sequence.py`):

```python
def string_sequence(n: int) -> str:
    return ' '.join([str(x) for x in range(n + 1)])
```

`range(n + 1)` is `0, 1, …, n` when `n ≥ 0`, and is empty when `n < 0`.
`' '.join` of that list is the space-separated decimal rendering, and is `""`
when the list is empty. Natural-number rendering is the usual canonical
decimal (no leading zeros, except for `0` itself), matching Python `str` on
non-negative integers.
-/

namespace humaneval_15_string_sequence

/-- Space-separated decimals from `0` through `n` inclusive.
    Negative `n` yields the empty string, as Python `range(n + 1)` does. -/
def string_sequence (n : Int) : String :=
  if n < 0 then
    ""
  else
    " ".intercalate ((List.range (n.toNat + 1)).map toString)

/-! ## Unit tests -/

example : string_sequence 0 = "0" := by native_decide

example : string_sequence 3 = "0 1 2 3" := by native_decide

example : string_sequence 5 = "0 1 2 3 4 5" := by native_decide

example : string_sequence 10 = "0 1 2 3 4 5 6 7 8 9 10" := by native_decide

example : string_sequence (-1) = "" := by native_decide

example : string_sequence (-5) = "" := by native_decide

#eval string_sequence 0

#eval string_sequence 5

#eval string_sequence 10

#eval string_sequence (-1)

/-! ## Pre-condition

Python accepts every `int`. The empty-string branch covers negatives, so the
pre-condition does not restrict the domain. -/

def Pre (_n : Int) : Prop := True

/-! ## Auxiliary facts about decimal rendering and `String.intercalate` -/

theorem space_data : (" " : String).data = [' '] := rfl

theorem zero_string : ("0" : String) = String.mk ['0'] := rfl

theorem toString_data (n : Nat) : (toString n).data = Nat.toDigits 10 n := by
  simp [toString, Nat.repr, List.asString]

theorem toString_zero : toString (0 : Nat) = "0" := by
  simp [toString, Nat.repr, Nat.toDigits_zero, List.asString, zero_string]

theorem digitChar_val (d : Nat) (hd : d < 10) :
    (Nat.digitChar d).toNat - '0'.toNat = d := by
  interval_cases d <;> decide

theorem space_not_digit : ¬ (' '.isDigit) := by decide

theorem digitChar_eq_zero_iff (d : Nat) (hd : d < 10) :
    Nat.digitChar d = '0' ↔ d = 0 := by
  interval_cases d <;> simp [Nat.digitChar]

theorem toDigitsCore_suffix (b fuel n : Nat) (cs : List Char) :
    ∃ t, Nat.toDigitsCore b fuel n cs = t ++ cs := by
  induction fuel generalizing n cs with
  | zero =>
    exact ⟨[], by simp [Nat.toDigitsCore]⟩
  | succ fuel ih =>
    rw [Nat.toDigitsCore]
    split
    · exact ⟨[Nat.digitChar (n % b)], by simp⟩
    · obtain ⟨t, ht⟩ := ih (n / b) (Nat.digitChar (n % b) :: cs)
      refine ⟨t ++ [Nat.digitChar (n % b)], ?_⟩
      simpa [List.append_assoc] using ht

theorem toDigitsCore_pos_ne_nil (b fuel n : Nat) (hf : 0 < fuel) :
    Nat.toDigitsCore b fuel n [] ≠ [] := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    rw [Nat.toDigitsCore]
    split
    · simp
    · obtain ⟨t, ht⟩ := toDigitsCore_suffix b fuel (n / b) [Nat.digitChar (n % b)]
      rw [ht]
      simp

theorem toDigits_ne_nil (n : Nat) : Nat.toDigits 10 n ≠ [] := by
  simpa [Nat.toDigits] using toDigitsCore_pos_ne_nil 10 (n + 1) n (Nat.succ_pos n)

theorem toString_ne_empty (k : Nat) : toString k ≠ "" := by
  intro h
  have := congrArg String.data h
  rw [toString_data] at this
  exact toDigits_ne_nil k this

theorem toString_no_space (n : Nat) : ' ' ∉ (toString n).data := by
  rw [toString_data]
  intro h
  exact space_not_digit (Nat.isDigit_of_mem_toDigits (b := 10) (by decide) (by decide) h)

theorem toString_isNat (k : Nat) : (toString k).isNat = true := by
  rw [String.isNat]
  have hempty : (toString k).isEmpty = false := by
    rw [Bool.eq_false_iff]
    intro h
    exact toString_ne_empty k ((String.isEmpty_iff _).mp h)
  have hall : (toString k).all (·.isDigit) = true := by
    rw [String.all_eq, toString_data, List.all_eq_true]
    intro c hc
    exact Nat.isDigit_of_mem_toDigits (b := 10) (by decide) (by decide) hc
  simp [hempty, hall]

theorem foldl_toDigits (n : Nat) :
    (Nat.toDigits 10 n).foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0 = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n < 10
    · rw [Nat.toDigits_of_lt_base hn, List.foldl_cons, List.foldl_nil, Nat.zero_mul, Nat.zero_add]
      exact digitChar_val n hn
    · have hpos : 0 < n := by omega
      have hdiv_pos : 0 < n / 10 := by omega
      have hdiv_lt : n / 10 < n := Nat.div_lt_self hpos (by decide)
      have hmod : n % 10 < 10 := Nat.mod_lt _ (by decide)
      have happend :=
        Nat.toDigits_append_toDigits (b := 10) (n := n / 10) (d := n % 10)
          (by decide) hdiv_pos hmod
      have heq : 10 * (n / 10) + n % 10 = n := Nat.div_add_mod n 10
      rw [heq] at happend
      rw [← happend, List.foldl_append, ih (n / 10) hdiv_lt, Nat.toDigits_of_lt_base hmod,
        List.foldl_cons, List.foldl_nil, digitChar_val (n % 10) hmod]
      simpa [Nat.mul_comm] using Nat.div_add_mod n 10

theorem toDigits_head_ne_zero (n : Nat) (hn : 0 < n) :
    (Nat.toDigits 10 n).head? ≠ some '0' := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hhead
    by_cases hlt : n < 10
    · rw [Nat.toDigits_of_lt_base hlt, List.head?_cons] at hhead
      have hz : n = 0 := (digitChar_eq_zero_iff n hlt).mp (Option.some.inj hhead)
      omega
    · have hdiv_pos : 0 < n / 10 := by omega
      have hdiv_lt : n / 10 < n := Nat.div_lt_self (by omega) (by decide)
      have hmod : n % 10 < 10 := Nat.mod_lt _ (by decide)
      have happend :=
        Nat.toDigits_append_toDigits (b := 10) (n := n / 10) (d := n % 10)
          (by decide) hdiv_pos hmod
      have heq : 10 * (n / 10) + n % 10 = n := Nat.div_add_mod n 10
      rw [heq] at happend
      have hne : Nat.toDigits 10 (n / 10) ≠ [] := toDigits_ne_nil _
      rw [← happend, List.head?_append] at hhead
      cases hL : Nat.toDigits 10 (n / 10) with
      | nil => exact hne hL
      | cons c cs =>
        rw [hL] at hhead
        simp at hhead
        have ih' := ih (n / 10) hdiv_lt hdiv_pos
        rw [hL, List.head?_cons] at ih'
        exact ih' (congrArg some hhead)

theorem intercalate_go_data (acc sep : String) (bs : List String) :
    (String.intercalate.go acc sep bs).data =
      acc.data ++ (bs.map fun b => sep.data ++ b.data).flatten := by
  induction bs generalizing acc with
  | nil =>
    simp [String.intercalate.go, List.flatten_nil, List.append_nil]
  | cons b bs ih =>
    simp only [String.intercalate.go, ih, List.map_cons, List.flatten_cons]
    simp [String.data_append, List.append_assoc]

theorem flatten_intersperse_cons (sep a : List Char) (xs : List (List Char)) :
    (List.intersperse sep (a :: xs)).flatten =
      a ++ (xs.map fun b => sep ++ b).flatten := by
  induction xs generalizing a with
  | nil =>
    simp
  | cons b bs ih =>
    rw [List.intersperse_cons₂, List.flatten_cons, List.flatten_cons, ih]
    simp [List.append_assoc]

theorem data_intercalate (sep : String) (ss : List String) :
    (sep.intercalate ss).data = List.intercalate sep.data (ss.map String.data) := by
  cases ss with
  | nil =>
    simp [String.intercalate, List.intercalate]
  | cons a as =>
    have hgo : sep.intercalate (a :: as) = String.intercalate.go a sep as := rfl
    rw [hgo, intercalate_go_data, List.intercalate, List.map_cons, flatten_intersperse_cons]
    simp only [List.map_map]
    apply congrArg (fun t => a.data ++ t)
    apply congrArg List.flatten
    apply congrArg (fun f => as.map f)
    funext b
    rfl

theorem intercalate_go_append_singleton (acc sep : String) (as : List String) (x : String) :
    String.intercalate.go acc sep (as ++ [x]) =
      String.intercalate.go acc sep as ++ sep ++ x := by
  induction as generalizing acc with
  | nil =>
    simp [String.intercalate.go]
  | cons a as ih =>
    simp [String.intercalate.go, ih]

theorem intercalate_append_singleton (sep : String) (xs : List String) (x : String)
    (hne : xs ≠ []) :
    sep.intercalate (xs ++ [x]) = sep.intercalate xs ++ sep ++ x := by
  cases xs with
  | nil => exact (hne rfl).elim
  | cons a as =>
    have h1 : sep.intercalate (a :: (as ++ [x])) = String.intercalate.go a sep (as ++ [x]) := rfl
    have h2 : sep.intercalate (a :: as) = String.intercalate.go a sep as := rfl
    simpa [h1, h2, List.cons_append] using intercalate_go_append_singleton a sep as x

theorem map_singleton_flatten {α β : Type} (f : α → β) (xs : List α) :
    (xs.map (fun x => [f x])).flatten = xs.map f := by
  simpa [List.flatMap] using (List.map_eq_flatMap (f := f) (l := xs)).symm

theorem sum_append_nat (l₁ l₂ : List Nat) : (l₁ ++ l₂).sum = l₁.sum + l₂.sum := by
  induction l₁ with
  | nil => simp
  | cons a l ih => simp [ih, Nat.add_assoc]

theorem string_sequence_ofNat (n : Nat) :
    string_sequence (n : Int) =
      " ".intercalate ((List.range (n + 1)).map toString) := by
  have h : ¬ ((n : Int) < 0) := not_lt.mpr (Int.natCast_nonneg n)
  unfold string_sequence
  rw [if_neg h]
  simp [Int.toNat_natCast]

theorem string_sequence_eq_of_toNat (n : Int) (hn : 0 ≤ n) :
    string_sequence n = string_sequence (n.toNat : Int) := by
  have h1 : ¬ n < 0 := not_lt.mpr hn
  have h2 : ¬ ((n.toNat : Int) < 0) := not_lt.mpr (Int.natCast_nonneg _)
  unfold string_sequence
  rw [if_neg h1, if_neg h2, Int.toNat_natCast]

/-! ## Properties -/

/-- Negative inputs produce the empty string (`range(n + 1)` is empty). -/
def negative_empty_prop (n : Int) : Prop :=
  n < 0 → string_sequence n = ""

theorem negative_empty_thm (n : Int) : negative_empty_prop n := by
  intro hn
  unfold string_sequence
  rw [if_pos hn]

/-- Direct reading of the Python one-liner on the non-negative branch. -/
def join_range_prop (n : Int) : Prop :=
  0 ≤ n →
    string_sequence n =
      " ".intercalate ((List.range (n.toNat + 1)).map toString)

theorem join_range_thm (n : Int) : join_range_prop n := by
  intro hn
  rw [string_sequence_eq_of_toNat n hn]
  exact string_sequence_ofNat n.toNat

/-- Base value required by the docstring: `string_sequence(0) == '0'`. -/
def zero_prop : Prop :=
  string_sequence 0 = "0"

theorem zero_thm : zero_prop := by
  show string_sequence (0 : Int) = "0"
  unfold string_sequence
  rw [if_neg (by decide : ¬ ((0 : Int) < 0))]
  have h0 : (0 : Int).toNat = 0 := by decide
  rw [h0, List.range_one, List.map_cons, List.map_nil, toString_zero]
  rfl

/-- Appending the next integer adds one space and that integer's decimal. -/
def succ_prop (n : Nat) : Prop :=
  string_sequence ((n : Int) + 1) =
    string_sequence (n : Int) ++ " " ++ toString (n + 1)

theorem succ_thm (n : Nat) : succ_prop n := by
  show string_sequence ((n : Int) + 1) =
    string_sequence (n : Int) ++ " " ++ toString (n + 1)
  have hleft : string_sequence ((n : Int) + 1) =
      " ".intercalate ((List.range ((n + 1) + 1)).map toString) := by
    have hnn : 0 ≤ (n : Int) + 1 := by omega
    rw [string_sequence_eq_of_toNat _ hnn]
    have ht : ((n : Int) + 1).toNat = n + 1 := Int.toNat_natCast_add_one
    rw [ht]
    exact string_sequence_ofNat (n + 1)
  rw [hleft, string_sequence_ofNat]
  have hrange : List.range (n + 1 + 1) = List.range (n + 1) ++ [n + 1] := by
    exact List.range_succ (n := n + 1)
  rw [hrange, List.map_append, List.map_singleton]
  have hne : (List.range (n + 1)).map toString ≠ [] := by
    simp [List.map_eq_nil_iff, List.range_eq_nil]
  exact intercalate_append_singleton " " ((List.range (n + 1)).map toString)
    (toString (n + 1)) hne

/-- Splitting the result on spaces recovers `str(0), …, str(n)`. -/
def tokens_prop (n : Int) : Prop :=
  0 ≤ n →
    (string_sequence n).split (· == ' ') = (List.range (n.toNat + 1)).map toString

theorem tokens_ofNat (n : Nat) :
    (string_sequence (n : Int)).split (· == ' ') = (List.range (n + 1)).map toString := by
  rw [string_sequence_ofNat]
  let ss : List String := (List.range (n + 1)).map toString
  have hne : ss.map String.data ≠ [] := by
    dsimp [ss]
    simp [List.map_eq_nil_iff, List.range_eq_nil]
  have hnospace : ∀ l ∈ ss.map String.data, ' ' ∉ l := by
    intro l hl
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hl
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hs
    exact toString_no_space k
  have hsplit :
      (([' '] : List Char).intercalate (ss.map String.data)).splitOn ' ' =
        ss.map String.data :=
    List.splitOn_intercalate (ss.map String.data) ' ' hnospace hne
  have hdata :
      (" ".intercalate ss).data = [' '].intercalate (ss.map String.data) := by
    simpa [space_data] using data_intercalate " " ss
  calc
    (" ".intercalate ss).split (· == ' ')
        = ((" ".intercalate ss).data.splitOnP (· == ' ')).map String.mk := by
          simpa using String.split_of_valid (" ".intercalate ss) (· == ' ')
    _ = (([' '].intercalate (ss.map String.data)).splitOn ' ').map String.mk := by
          rw [hdata]
          rfl
    _ = (ss.map String.data).map String.mk := by rw [hsplit]
    _ = ss := by
          simp only [List.map_map]
          have hid : String.mk ∘ String.data = id := by
            funext s
            rfl
          simp [hid, List.map_id]

theorem tokens_thm (n : Int) : tokens_prop n := by
  intro hn
  rw [string_sequence_eq_of_toNat n hn]
  exact tokens_ofNat n.toNat

/-- There are exactly `n + 1` space-separated fields when `n ≥ 0`. -/
def token_count_prop (n : Int) : Prop :=
  0 ≤ n → ((string_sequence n).split (· == ' ')).length = n.toNat + 1

theorem token_count_thm (n : Int) : token_count_prop n := by
  intro hn
  rw [tokens_thm n hn, List.length_map, List.length_range]

/-- The field at index `k` is the decimal of `k`. -/
def nth_token_prop (n : Int) : Prop :=
  0 ≤ n → ∀ k, k ≤ n.toNat →
    ((string_sequence n).split (· == ' '))[k]? = some (toString k)

theorem nth_token_thm (n : Int) : nth_token_prop n := by
  intro hn k hk
  rw [tokens_thm n hn]
  have hk' : k < n.toNat + 1 := Nat.lt_succ_of_le hk
  have hlen : k < (List.range (n.toNat + 1)).length := by simpa using hk'
  rw [List.getElem?_map, List.getElem?_range (by simpa [List.length_range] using hk')]
  rfl

/-- The result begins with `"0"` whenever `n ≥ 0`. -/
def starts_with_zero_prop (n : Int) : Prop :=
  0 ≤ n → ∃ t : String, string_sequence n = "0" ++ t

theorem starts_with_zero_ofNat (n : Nat) :
    ∃ t : String, string_sequence (n : Int) = "0" ++ t := by
  induction n with
  | zero =>
    refine ⟨"", ?_⟩
    have h : string_sequence (0 : Int) = "0" := zero_thm
    simp [h]
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t ++ " " ++ toString (n + 1), ?_⟩
    rw [show string_sequence ((n + 1 : Nat) : Int) = string_sequence ((n : Int) + 1) by rfl,
      succ_thm, ht]
    simp [String.append_assoc]

theorem starts_with_zero_thm (n : Int) : starts_with_zero_prop n := by
  intro hn
  rw [string_sequence_eq_of_toNat n hn]
  exact starts_with_zero_ofNat n.toNat

/-- The result ends with the decimal representation of `n` when `n ≥ 0`. -/
def ends_with_last_prop (n : Int) : Prop :=
  0 ≤ n → ∃ t : String, string_sequence n = t ++ toString n.toNat

theorem ends_with_last_ofNat (n : Nat) :
    ∃ t : String, string_sequence (n : Int) = t ++ toString n := by
  cases n with
  | zero =>
    refine ⟨"", ?_⟩
    have h : string_sequence (0 : Int) = "0" := zero_thm
    simp [h, toString_zero]
  | succ n =>
    refine ⟨string_sequence (n : Int) ++ " ", ?_⟩
    rw [show string_sequence ((n + 1 : Nat) : Int) = string_sequence ((n : Int) + 1) by rfl,
      succ_thm, String.append_assoc]

theorem ends_with_last_thm (n : Int) : ends_with_last_prop n := by
  intro hn
  rw [string_sequence_eq_of_toNat n hn]
  exact ends_with_last_ofNat n.toNat

/-- Exactly `n` space characters separate the `n + 1` numerals. -/
def space_count_prop (n : Int) : Prop :=
  0 ≤ n → (string_sequence n).data.count ' ' = n.toNat

theorem count_toString_space (k : Nat) : (toString k).data.count ' ' = 0 :=
  List.count_eq_zero_of_not_mem (toString_no_space k)

theorem space_count_ofNat (n : Nat) :
    (string_sequence (n : Int)).data.count ' ' = n := by
  induction n with
  | zero =>
    have h : string_sequence (0 : Nat) = "0" := by
      rw [string_sequence_ofNat, List.range_one, List.map_cons, List.map_nil, toString_zero]
      rfl
    rw [h, zero_string]
    decide
  | succ n ih =>
    rw [show string_sequence ((n + 1 : Nat) : Int) = string_sequence ((n : Int) + 1) by rfl,
      succ_thm, String.data_append, String.data_append, List.count_append, List.count_append, ih,
      count_toString_space]
    have hc : (" " : String).data.count ' ' = 1 := by
      rw [space_data]
      decide
    rw [hc]

theorem space_count_thm (n : Int) : space_count_prop n := by
  intro hn
  rw [string_sequence_eq_of_toNat n hn]
  exact space_count_ofNat n.toNat

/-- Character length is the sum of the numeral lengths plus one space per gap. -/
def length_prop (n : Int) : Prop :=
  0 ≤ n →
    (string_sequence n).length =
      ((List.range (n.toNat + 1)).map (fun k => (toString k).length)).sum + n.toNat

theorem length_ofNat (n : Nat) :
    (string_sequence (n : Int)).length =
      ((List.range (n + 1)).map (fun k => (toString k).length)).sum + n := by
  induction n with
  | zero =>
    have h : string_sequence (0 : Nat) = "0" := by
      rw [string_sequence_ofNat, List.range_one, List.map_cons, List.map_nil, toString_zero]
      rfl
    rw [h, List.range_one]
    simp [toString_zero, zero_string]
  | succ n ih =>
    rw [show string_sequence ((n + 1 : Nat) : Int) = string_sequence ((n : Int) + 1) by rfl,
      succ_thm, String.length_append, String.length_append, ih]
    have hspace : (" " : String).length = 1 := by
      simpa [space_data] using String.length_mk [' ']
    have hsum :
        ((List.range (n + 1 + 1)).map (fun k => (toString k).length)).sum =
          ((List.range (n + 1)).map (fun k => (toString k).length)).sum +
            (toString (n + 1)).length := by
      have hrange : List.range (n + 1 + 1) = List.range (n + 1) ++ [n + 1] :=
        List.range_succ (n := n + 1)
      rw [hrange, List.map_append, sum_append_nat]
      simp
    rw [hspace, hsum]
    omega

theorem length_thm (n : Int) : length_prop n := by
  intro hn
  rw [string_sequence_eq_of_toNat n hn]
  exact length_ofNat n.toNat

/-- A non-negative input never yields the empty string. -/
def nonempty_prop (n : Int) : Prop :=
  0 ≤ n → string_sequence n ≠ ""

theorem nonempty_thm (n : Int) : nonempty_prop n := by
  intro hn hempty
  obtain ⟨t, ht⟩ := starts_with_zero_thm n hn
  rw [ht] at hempty
  have hd := congrArg String.data hempty
  simp [String.data_append, zero_string] at hd

/-- No field is empty, so the string has no leading, trailing, or doubled spaces. -/
def tokens_nonempty_prop (n : Int) : Prop :=
  0 ≤ n → ∀ t ∈ (string_sequence n).split (· == ' '), t ≠ ""

theorem tokens_nonempty_thm (n : Int) : tokens_nonempty_prop n := by
  intro hn t ht
  rw [tokens_thm n hn] at ht
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp ht
  exact toString_ne_empty k

/-- `str` and `int` are inverses on the numerals the function prints. -/
def repr_roundtrip_prop (k : Nat) : Prop :=
  String.toNat? (toString k) = some k

theorem repr_roundtrip_thm (k : Nat) : repr_roundtrip_prop k := by
  show String.toNat? (toString k) = some k
  rw [String.toNat?, toString_isNat, String.foldl_eq, toString_data, foldl_toDigits]
  simp

/-- Decimals of positive integers have no leading zero. `0` is rendered `"0"`. -/
def no_leading_zero_prop (k : Nat) : Prop :=
  k = 0 ∨ (toString k).data.head? ≠ some '0'

theorem no_leading_zero_thm (k : Nat) : no_leading_zero_prop k := by
  unfold no_leading_zero_prop
  by_cases hk : k = 0
  · exact Or.inl hk
  · refine Or.inr ?_
    rw [toString_data]
    exact toDigits_head_ne_zero k (Nat.pos_of_ne_zero hk)

/-- Every character of a numeral is a decimal digit. -/
def digits_only_prop (k : Nat) : Prop :=
  ∀ c ∈ (toString k).data, c.isDigit

theorem digits_only_thm (k : Nat) : digits_only_prop k := by
  unfold digits_only_prop
  rw [toString_data]
  intro c hc
  exact Nat.isDigit_of_mem_toDigits (b := 10) (by decide) (by decide) hc

/-- Each output field parses back to its index. -/
def token_roundtrip_prop (n : Int) : Prop :=
  0 ≤ n → ∀ k, k ≤ n.toNat →
    ((string_sequence n).split (· == ' '))[k]?.bind String.toNat? = some k

theorem token_roundtrip_thm (n : Int) : token_roundtrip_prop n := by
  intro hn k hk
  rw [nth_token_thm n hn k hk]
  have hr : String.toNat? (toString k) = some k := repr_roundtrip_thm k
  simp [hr]

/-- The printed numerals are pairwise distinct. -/
def distinct_tokens_prop (n : Int) : Prop :=
  0 ≤ n → ((string_sequence n).split (· == ' ')).Nodup

theorem toString_injective : Function.Injective (toString : Nat → String) := by
  intro a b h
  have ha : String.toNat? (toString a) = some a := repr_roundtrip_thm a
  have hb : String.toNat? (toString b) = some b := repr_roundtrip_thm b
  rw [h] at ha
  exact Option.some.inj (ha.symm.trans hb)

theorem distinct_tokens_thm (n : Int) : distinct_tokens_prop n := by
  intro hn
  rw [tokens_thm n hn]
  exact List.Nodup.map toString_injective (List.nodup_range (n := n.toNat + 1))

/-- Extending the upper bound only appends a suffix. -/
def extends_prop (a b : Nat) : Prop :=
  a ≤ b → ∃ t : String, string_sequence (b : Int) = string_sequence (a : Int) ++ t

theorem extends_thm (a b : Nat) : extends_prop a b := by
  intro hab
  induction b with
  | zero =>
    have ha : a = 0 := Nat.eq_zero_of_le_zero hab
    subst ha
    exact ⟨"", by simp⟩
  | succ b ih =>
    by_cases hle : a ≤ b
    · obtain ⟨t, ht⟩ := ih hle
      refine ⟨t ++ " " ++ toString (b + 1), ?_⟩
      rw [show string_sequence ((b + 1 : Nat) : Int) = string_sequence ((b : Int) + 1) by rfl,
        succ_thm, ht]
      simp [String.append_assoc]
    · have ha : a = b + 1 := by omega
      subst ha
      exact ⟨"", by simp⟩

/-- A strictly larger upper bound appends a space and then further numerals. -/
def strict_extends_prop (a b : Nat) : Prop :=
  a < b → ∃ t : String, string_sequence (b : Int) = string_sequence (a : Int) ++ " " ++ t

theorem strict_extends_thm (a b : Nat) : strict_extends_prop a b := by
  intro hab
  have hsucc : a + 1 ≤ b := Nat.succ_le_of_lt hab
  obtain ⟨t, ht⟩ := extends_thm (a + 1) b hsucc
  refine ⟨toString (a + 1) ++ t, ?_⟩
  rw [ht]
  rw [show string_sequence ((a + 1 : Nat) : Int) = string_sequence ((a : Int) + 1) by rfl,
    succ_thm, String.append_assoc]

/-! ## Post-condition -/

def Post_prop (n : Int) : Prop :=
  negative_empty_prop n ∧
  join_range_prop n ∧
  tokens_prop n ∧
  token_count_prop n ∧
  nth_token_prop n ∧
  starts_with_zero_prop n ∧
  ends_with_last_prop n ∧
  space_count_prop n ∧
  length_prop n ∧
  nonempty_prop n ∧
  tokens_nonempty_prop n ∧
  token_roundtrip_prop n ∧
  distinct_tokens_prop n

/-! ## Property-based tests

Executable checks of each stated property. A passing check is evidence, not a proof.
-/

-- negative_empty_prop
#eval Plausible.Testable.check (∀ k : Nat, string_sequence (-(k : Int) - 1) = "")

example : ((List.range 40).map (fun k => -(k : Int) - 1)).all (fun n => string_sequence n == "")
    = true := by native_decide

-- join_range_prop
#eval Plausible.Testable.check
  (∀ n : Nat,
    string_sequence (n : Int) =
      " ".intercalate ((List.range (n + 1)).map toString))

example : (List.range 30).all (fun n =>
    string_sequence (n : Int) ==
      " ".intercalate ((List.range (n + 1)).map toString)) = true := by native_decide

-- zero_prop
example : (List.range 1).all (fun _ => string_sequence 0 == "0") = true := by native_decide

-- succ_prop
#eval Plausible.Testable.check
  (∀ n : Nat,
    string_sequence ((n : Int) + 1) =
      string_sequence (n : Int) ++ " " ++ toString (n + 1))

example : (List.range 30).all (fun n =>
    string_sequence ((n : Int) + 1) ==
      string_sequence (n : Int) ++ " " ++ toString (n + 1)) = true := by native_decide

-- tokens_prop
#eval Plausible.Testable.check
  (∀ n : Nat,
    (string_sequence (n : Int)).split (· == ' ') = (List.range (n + 1)).map toString)

example : (List.range 30).all (fun n =>
    (string_sequence (n : Int)).split (· == ' ') == (List.range (n + 1)).map toString)
    = true := by native_decide

-- token_count_prop
#eval Plausible.Testable.check
  (∀ n : Nat, ((string_sequence (n : Int)).split (· == ' ')).length = n + 1)

example : (List.range 40).all (fun n =>
    ((string_sequence (n : Int)).split (· == ' ')).length == n + 1) = true := by native_decide

-- nth_token_prop
#eval Plausible.Testable.check
  (∀ n : Nat,
    (List.range (n + 1)).all (fun k =>
      ((string_sequence (n : Int)).split (· == ' '))[k]? == some (toString k)))

example : (List.range 25).all (fun n =>
    (List.range (n + 1)).all (fun k =>
      ((string_sequence (n : Int)).split (· == ' '))[k]? == some (toString k))) = true := by
  native_decide

-- starts_with_zero_prop
#eval Plausible.Testable.check
  (∀ n : Nat, (string_sequence (n : Int)).startsWith "0" = true)

example : (List.range 40).all (fun n => (string_sequence (n : Int)).startsWith "0") = true := by
  native_decide

-- ends_with_last_prop
#eval Plausible.Testable.check
  (∀ n : Nat, (string_sequence (n : Int)).endsWith (toString n) = true)

example : (List.range 40).all (fun n =>
    (string_sequence (n : Int)).endsWith (toString n)) = true := by native_decide

-- space_count_prop
#eval Plausible.Testable.check
  (∀ n : Nat, (string_sequence (n : Int)).data.count ' ' = n)

example : (List.range 40).all (fun n =>
    (string_sequence (n : Int)).data.count ' ' == n) = true := by native_decide

-- length_prop
#eval Plausible.Testable.check
  (∀ n : Nat,
    (string_sequence (n : Int)).length =
      ((List.range (n + 1)).map (fun k => (toString k).length)).sum + n)

example : (List.range 30).all (fun n =>
    (string_sequence (n : Int)).length ==
      ((List.range (n + 1)).map (fun k => (toString k).length)).sum + n) = true := by
  native_decide

-- nonempty_prop
#eval Plausible.Testable.check (∀ n : Nat, string_sequence (n : Int) ≠ "")

example : (List.range 40).all (fun n => !(string_sequence (n : Int)).isEmpty) = true := by
  native_decide

-- tokens_nonempty_prop
#eval Plausible.Testable.check
  (∀ n : Nat, ((string_sequence (n : Int)).split (· == ' ')).all (· ≠ ""))

example : (List.range 30).all (fun n =>
    ((string_sequence (n : Int)).split (· == ' ')).all (· ≠ "")) = true := by native_decide

-- repr_roundtrip_prop
#eval Plausible.Testable.check (∀ k : Nat, String.toNat? (toString k) = some k)

example : (List.range 60).all (fun k => (toString k).toNat? == some k) = true := by native_decide

-- no_leading_zero_prop
#eval Plausible.Testable.check
  (∀ k : Nat, k = 0 ∨ (toString k).data.head? ≠ some '0')

example : (List.range 60).all (fun k => k == 0 || (toString k).data.head? != some '0') = true := by
  native_decide

-- digits_only_prop
#eval Plausible.Testable.check (∀ k : Nat, (toString k).all Char.isDigit = true)

example : (List.range 60).all (fun k => (toString k).all Char.isDigit) = true := by native_decide

-- token_roundtrip_prop
#eval Plausible.Testable.check
  (∀ n : Nat,
    (List.range (n + 1)).all (fun k =>
      ((string_sequence (n : Int)).split (· == ' '))[k]?.bind String.toNat? == some k))

example : (List.range 25).all (fun n =>
    (List.range (n + 1)).all (fun k =>
      ((string_sequence (n : Int)).split (· == ' '))[k]?.bind String.toNat? == some k)) = true := by
  native_decide

-- distinct_tokens_prop
#eval Plausible.Testable.check
  (∀ n : Nat, ((string_sequence (n : Int)).split (· == ' ')).Nodup)

example : (List.range 30).all (fun n =>
    decide (((string_sequence (n : Int)).split (· == ' ')).Nodup)) = true := by native_decide

-- extends_prop
#eval Plausible.Testable.check
  (∀ a b : Nat, a ≤ b → (string_sequence (a : Int)).isPrefixOf (string_sequence (b : Int)) = true)

example : ((List.range 15).product (List.range 15)).all (fun p =>
    p.1 > p.2 || (string_sequence (p.1 : Int)).isPrefixOf (string_sequence (p.2 : Int))) = true := by
  native_decide

-- strict_extends_prop
#eval Plausible.Testable.check
  (∀ a d : Nat,
    (string_sequence ((a + d + 1 : Nat) : Int)).startsWith
      (string_sequence (a : Int) ++ " ") = true)

example : ((List.range 15).product (List.range 15)).all (fun p =>
    p.1 ≥ p.2 ||
      (string_sequence (p.2 : Int)).startsWith (string_sequence (p.1 : Int) ++ " ")) = true := by
  native_decide

-- Post_prop, on both signs of `Int`
private def postBool (n : Int) : Bool :=
  if n < 0 then
    string_sequence n == ""
  else
    let tokens := (string_sequence n).split (· == ' ')
    let nums := (List.range (n.toNat + 1)).map toString
    tokens == nums &&
      tokens.length == n.toNat + 1 &&
      (List.range (n.toNat + 1)).all (fun k => tokens[k]? == some (toString k)) &&
      (string_sequence n).startsWith "0" &&
      (string_sequence n).endsWith (toString n.toNat) &&
      (string_sequence n).data.count ' ' == n.toNat &&
      (string_sequence n).length ==
        (nums.map (fun s => s.length)).sum + n.toNat &&
      !(string_sequence n).isEmpty &&
      tokens.all (· ≠ "") &&
      (List.range (n.toNat + 1)).all (fun k => tokens[k]?.bind String.toNat? == some k) &&
      decide tokens.Nodup

#eval Plausible.Testable.check (∀ n : Int, postBool n = true)

example : ((List.range 41).map (fun k => (k : Int) - 20)).all postBool = true := by native_decide

/-! ## Correctness -/

theorem correctness_thm (n : Int) (_h : Pre n) : Post_prop n :=
  ⟨negative_empty_thm n, join_range_thm n, tokens_thm n, token_count_thm n, nth_token_thm n,
    starts_with_zero_thm n, ends_with_last_thm n, space_count_thm n, length_thm n,
    nonempty_thm n, tokens_nonempty_thm n, token_roundtrip_thm n, distinct_tokens_thm n⟩

/-! ## Imperative implementation

Mutable list accumulation of `str(x)` for `x` in `range(n + 1)`, then `' '.join`.
This is the loop form of the Python list comprehension. -/

def string_sequenceImp (n : Int) : String :=
  Id.run do
    if n < 0 then
      return ""
    let mut parts : List String := []
    for x in List.range (n.toNat + 1) do
      parts := parts ++ [toString x]
    return " ".intercalate parts

/-! ## Imperative tests -/

example : string_sequenceImp 0 = "0" := by native_decide

example : string_sequenceImp 3 = "0 1 2 3" := by native_decide

example : string_sequenceImp 5 = "0 1 2 3 4 5" := by native_decide

example : string_sequenceImp 10 = "0 1 2 3 4 5 6 7 8 9 10" := by native_decide

example : string_sequenceImp (-1) = "" := by native_decide

example : string_sequenceImp (-8) = "" := by native_decide

#eval string_sequenceImp 0

#eval string_sequenceImp 5

#eval string_sequenceImp 10

#eval string_sequenceImp (-1)

/-! ## Equivalence -/

theorem equivalence_thm (n : Int) : string_sequence n = string_sequenceImp n := by
  by_cases hn : n < 0
  · simp [string_sequence, string_sequenceImp, hn]
  · simp [string_sequence, string_sequenceImp, hn, map_singleton_flatten]

end humaneval_15_string_sequence
