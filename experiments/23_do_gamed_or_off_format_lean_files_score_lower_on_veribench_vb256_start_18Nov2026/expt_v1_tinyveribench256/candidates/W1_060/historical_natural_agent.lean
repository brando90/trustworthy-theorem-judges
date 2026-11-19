import Mathlib
namespace Agent

/-!
# Product of all elements in a non-empty list of integers

Lean 4 formalization of the Python program `product_of_list`.

The Python function requires a non-empty `List[int]` (checked by `pre`); on a
valid input it starts with `result = 1` and multiplies in every element from
left to right, returning the accumulated product.  Violating the precondition
raises `ValueError`, which we model by the precondition predicate `Pre`.

Contents:
* `productOfList` — functional (fold based) implementation.
* Unit tests mirroring the Python doctests / `check`.
* `Pre` — the precondition (`len(xs) > 0`).
* Property propositions + proved theorems, combined into `Post_prop`.
* `correctness_thm : Pre xs → Post_prop xs`.
* `productOfListImp` — imperative implementation with `Id.run do` and a
  mutable accumulator, mirroring the Python loop, plus its equivalence proof.
-/

namespace ProductOfList

/-! ## Functional implementation -/

/-- `result = 1; for x in xs: result *= x` as a left fold. -/
def productOfList (xs : List Int) : Int :=
  xs.foldl (· * ·) 1

/-! ## Unit tests (functional) -/

example : productOfList [2, 3, 4] = 24 := by native_decide
example : productOfList [5] = 5 := by native_decide
example : productOfList [1, 1, 1] = 1 := by native_decide
example : productOfList [-2, 3] = -6 := by native_decide
example : productOfList [7, 0, 9] = 0 := by native_decide

#eval productOfList [2, 3, 4]   -- 24
#eval productOfList [5]         -- 5
#eval productOfList [1, 1, 1]   -- 1

/-! ## Precondition -/

/-- Python's `pre`: the argument must be a non-empty list of integers.
`List Int` already enforces "list of integers", so only non-emptiness remains. -/
def Pre (xs : List Int) : Prop := xs ≠ []

/-! ## Properties -/

/-- Key characterization: the fold computes the mathematical product. -/
theorem productOfList_eq_prod (xs : List Int) : productOfList xs = xs.prod := by
  unfold productOfList
  rw [List.prod_eq_foldl]

/-- The result is the mathematical product of the list. -/
def prod_spec_prop (xs : List Int) : Prop :=
  productOfList xs = xs.prod

theorem prod_spec_thm (xs : List Int) : prod_spec_prop xs :=
  productOfList_eq_prod xs

/-- The loop accumulator behaves like `foldl` from an arbitrary start value:
starting from `a` just scales the result by `a`. -/
theorem foldl_mul_eq (xs : List Int) (a : Int) :
    xs.foldl (· * ·) a = a * productOfList xs := by
  unfold productOfList
  induction xs generalizing a with
  | nil => simp
  | cons y ys ih =>
    rw [List.foldl_cons, List.foldl_cons, ih (a * y), ih (1 * y), one_mul, mul_assoc]

/-- Peeling off the head: `product (x :: xs) = x * product xs`. -/
def cons_prop (x : Int) (xs : List Int) : Prop :=
  productOfList (x :: xs) = x * productOfList xs

theorem cons_thm (x : Int) (xs : List Int) : cons_prop x xs := by
  unfold cons_prop
  rw [productOfList_eq_prod, productOfList_eq_prod, List.prod_cons]

/-- A single-element list returns that element (Python: `product_of_list([5]) == 5`). -/
def singleton_prop (x : Int) : Prop := productOfList [x] = x

theorem singleton_thm (x : Int) : singleton_prop x := by
  simp [singleton_prop, productOfList]

/-- Products split over concatenation. -/
def append_prop (xs ys : List Int) : Prop :=
  productOfList (xs ++ ys) = productOfList xs * productOfList ys

theorem append_thm (xs ys : List Int) : append_prop xs ys := by
  unfold append_prop
  rw [productOfList_eq_prod, productOfList_eq_prod, productOfList_eq_prod,
    List.prod_append]

/-- Every element of the list divides the product. -/
def dvd_prop (xs : List Int) : Prop :=
  ∀ x ∈ xs, x ∣ productOfList xs

theorem dvd_thm (xs : List Int) : dvd_prop xs := by
  intro x hx
  rw [productOfList_eq_prod]
  exact List.dvd_prod hx

/-- A zero anywhere in the list forces a zero product. -/
def zero_mem_prop (xs : List Int) : Prop :=
  (0 : Int) ∈ xs → productOfList xs = 0

theorem zero_mem_thm (xs : List Int) : zero_mem_prop xs := by
  intro h
  rw [productOfList_eq_prod]
  exact List.prod_eq_zero h

/-- If every element is nonzero, so is the product. -/
def ne_zero_prop (xs : List Int) : Prop :=
  (∀ x ∈ xs, x ≠ 0) → productOfList xs ≠ 0

theorem ne_zero_thm (xs : List Int) : ne_zero_prop xs := by
  intro h
  rw [productOfList_eq_prod]
  exact List.prod_ne_zero (fun hm => h 0 hm rfl)

/-- On a valid (non-empty) input the result is the head times the product of the tail,
i.e. the loop really consumed the whole list starting from `1`. -/
def head_tail_prop (xs : List Int) : Prop :=
  xs ≠ [] → productOfList xs = xs.head! * productOfList xs.tail

theorem head_tail_thm (xs : List Int) : head_tail_prop xs := by
  intro h
  cases xs with
  | nil => exact absurd rfl h
  | cons y ys => simpa [List.head!] using cons_thm y ys

/-! ## Postcondition -/

/-- The full postcondition: the conjunction of all specified properties. -/
def Post_prop (xs : List Int) : Prop :=
  prod_spec_prop xs ∧
  dvd_prop xs ∧
  zero_mem_prop xs ∧
  ne_zero_prop xs ∧
  head_tail_prop xs ∧
  (∀ x : Int, productOfList [x] = x) ∧
  (∀ x : Int, ∀ ys : List Int, productOfList (x :: ys) = x * productOfList ys)

/-- Correctness: whenever the Python precondition holds, the postcondition holds. -/
theorem correctness_thm (xs : List Int) (_h : Pre xs) : Post_prop xs := by
  refine ⟨prod_spec_thm xs, dvd_thm xs, zero_mem_thm xs, ne_zero_thm xs,
    head_tail_thm xs, fun x => singleton_thm x, fun x ys => cons_thm x ys⟩

/-! ## Imperative implementation -/

/-- Direct transcription of the Python loop with a mutable accumulator. -/
def productOfListImp (xs : List Int) : Int := Id.run do
  let mut result : Int := 1
  for x in xs do
    result := result * x
  return result

/-! ## Unit tests (imperative) -/

example : productOfListImp [2, 3, 4] = 24 := by native_decide
example : productOfListImp [5] = 5 := by native_decide
example : productOfListImp [1, 1, 1] = 1 := by native_decide
example : productOfListImp [-2, 3] = -6 := by native_decide

#eval productOfListImp [2, 3, 4]   -- 24
#eval productOfListImp [5]         -- 5
#eval productOfListImp [1, 1, 1]   -- 1

/-! ## Equivalence of the two implementations -/

theorem imp_foldl (xs : List Int) (a : Int) :
    (Id.run do
      let mut result : Int := a
      for x in xs do
        result := result * x
      return result) = xs.foldl (· * ·) a := by
  induction xs generalizing a with
  | nil => rfl
  | cons y ys ih => simpa [Id.run] using ih (a * y)

/-- The functional and imperative implementations agree everywhere. -/
theorem equiv_thm (xs : List Int) : productOfList xs = productOfListImp xs := by
  rw [productOfListImp, productOfList, imp_foldl xs 1]

end ProductOfList
end Agent
