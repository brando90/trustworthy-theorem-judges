import Mathlib
namespace Gold

namespace MyOddSumParity

def parity (n : Nat) : Nat := n % 2

def sumList : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumList xs

def myOddSumParity (xs : List Nat) : Nat :=
  parity (sumList xs)

example : myOddSumParity [1, 3, 5] = 1 := by native_decide

example : myOddSumParity [] = 0 := by native_decide

example : myOddSumParity [1] = 1 := by native_decide

example : myOddSumParity [1, 3] = 0 := by native_decide

example : myOddSumParity [1, 3, 7] = 1 := by native_decide

example : ¬ (myOddSumParity [1, 3, 5] > 1) := by native_decide

example : ¬ (myOddSumParity [] = 1) := by native_decide

theorem myOddSumParity_nil : myOddSumParity [] = 0 := by
  unfold myOddSumParity parity sumList; rfl

theorem myOddSumParity_zero_or_one (xs : List Nat) :
    myOddSumParity xs = 0 ∨ myOddSumParity xs = 1 := by
  unfold myOddSumParity parity
  omega

theorem sumList_append (xs ys : List Nat) : sumList (xs ++ ys) = sumList xs + sumList ys := by
  induction xs with
  | nil => simp [sumList]
  | cons a tl ih => simp [sumList, ih]; omega

theorem myOddSumParity_append (xs ys : List Nat) :
    myOddSumParity (xs ++ ys) = (myOddSumParity xs + myOddSumParity ys) % 2 := by
  unfold myOddSumParity parity
  rw [sumList_append]; omega

theorem myOddSumParity_singleton (x : Nat) : myOddSumParity [x] = x % 2 := by
  simp [myOddSumParity, parity, sumList]

end MyOddSumParity
end Gold
