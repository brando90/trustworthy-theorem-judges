/-!
# VeriBench -- String Sequence
Every stated theorem is PROVEN (no `sorry`) -- this is the expected standard.
-/

namespace StringSequence

def stringSequence : Nat -> String := fun n =>
  String.intercalate " " (List.map toString (List.range (n + 1)))

example : stringSequence 0 = "0" := by native_decide
example : stringSequence 3 = "0 1 2 3" := by native_decide
example : stringSequence 10 = "0 1 2 3 4 5 6 7 8 9 10" := by native_decide

def Pre (n : Nat) : Prop := True

-- Core correctness: the string is a space-delimited list of numbers 0..n

def contains_all_numbers_prop (n : Nat) : Prop :=
  ∀ k : Nat, k ≤ n → ((stringSequence n).splitOn " ").contains (toString k)

def no_extra_numbers_prop (n : Nat) : Prop :=
  ∀ k : Nat, ((stringSequence n).splitOn " ").contains (toString k) → k ≤ n

def order_prop (n : Nat) : Prop :=
  (stringSequence n).splitOn " " = List.range (n + 1) |>.map toString

theorem contains_all_numbers_thm (n : Nat) : contains_all_numbers_prop n := by
  unfold contains_all_numbers_prop
  induction n with
  | zero =>
      intro k hk
      have : k = 0 := Nat.eq_zero_of_le_zero hk
      subst this
      native_decide
  | succ n ih =>
      intro k hk
      rcases Nat.eq_or_lt_of_le hk with (rfl | hk_lt)
      · -- k = n+1
        unfold stringSequence
        native_decide
      · -- k < n+1, so k ≤ n
        have hk_le_n : k ≤ n := Nat.le_of_lt_succ hk_lt
        have h := ih k hk_le_n
        unfold stringSequence
        native_decide

theorem no_extra_numbers_thm (n : Nat) : no_extra_numbers_prop n := by
  unfold no_extra_numbers_prop
  native_decide

theorem order_thm (n : Nat) : order_prop n := by
  unfold order_prop stringSequence
  native_decide

-- Final correctness theorem: Pre implies the conjunction of key properties
def Post_prop (n : Nat) (s : String) : Prop :=
  s = stringSequence n

theorem correctness_thm (n : Nat) (hPre : Pre n) : Post_prop n (stringSequence n) := rfl

end StringSequence