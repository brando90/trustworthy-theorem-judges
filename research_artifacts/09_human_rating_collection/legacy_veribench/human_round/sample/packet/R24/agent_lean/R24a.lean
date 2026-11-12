import Mathlib

/-!
# Duplicate every character of a string

This file formalizes the Python `duplicate_chars` program.  Lean's static type
system represents the Python precondition by requiring the input to be a
`String`.  The functional and imperative implementations both replace every
input character `c` by the pair `[c, c]`.
-/

namespace DuplicateChars

def duplicateList : List Char → List Char
  | [] => []
  | c :: cs => c :: c :: duplicateList cs

def duplicateChars (s : String) : String :=
  String.mk (duplicateList s.toList)

example : duplicateChars "abc" = "aabbcc" := by native_decide
example : duplicateChars "" = "" := by native_decide
example : duplicateChars "!a " = "!!aa  " := by native_decide

#eval duplicateChars "abc"
#eval duplicateChars ""
#eval duplicateChars "!a "

def Pre (_s : String) : Prop := True

def duplicates_in_order_prop (s : String) : Prop :=
  (duplicateChars s).toList = s.toList.flatMap (fun c => [c, c])

theorem duplicateList_eq_flatMap (xs : List Char) :
    duplicateList xs = xs.flatMap (fun c => [c, c]) := by
  induction xs with
  | nil => rfl
  | cons c cs ih => simp [duplicateList, ih]

theorem duplicates_in_order_thm (s : String) :
    duplicates_in_order_prop s := by
  simp [duplicates_in_order_prop, duplicateChars, duplicateList_eq_flatMap]

def length_doubles_prop (s : String) : Prop :=
  (duplicateChars s).length = 2 * s.length

theorem duplicateList_length (xs : List Char) :
    (duplicateList xs).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons c cs ih => simp [duplicateList, ih, Nat.mul_add]

theorem length_doubles_thm (s : String) : length_doubles_prop s := by
  simp [length_doubles_prop, duplicateChars, duplicateList_length]

def empty_input_prop : Prop := duplicateChars "" = ""

theorem empty_input_thm : empty_input_prop := by
  rfl

def Post_prop (s : String) : Prop :=
  duplicates_in_order_prop s ∧ length_doubles_prop s ∧
    (s = "" → duplicateChars s = "")

theorem duplicateChars_correct (s : String) : Pre s → Post_prop s := by
  intro _
  refine ⟨duplicates_in_order_thm s, length_doubles_thm s, ?_⟩
  intro hs
  subst s
  exact empty_input_thm

def duplicateCharsImperative (s : String) : String := Id.run do
  let mut result : List Char := []
  for c in s.toList do
    result := result ++ [c, c]
  return String.mk result

example : duplicateCharsImperative "abc" = "aabbcc" := by native_decide
example : duplicateCharsImperative "" = "" := by native_decide
example : duplicateCharsImperative "!a " = "!!aa  " := by native_decide

#eval duplicateCharsImperative "abc"
#eval duplicateCharsImperative ""
#eval duplicateCharsImperative "!a "

theorem foldl_append_duplicateList (xs acc : List Char) :
    xs.foldl (fun out c => out ++ [c, c]) acc = acc ++ duplicateList xs := by
  induction xs generalizing acc with
  | nil => simp [duplicateList]
  | cons c cs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp [duplicateList, List.append_assoc]

theorem functional_eq_imperative (s : String) :
    duplicateChars s = duplicateCharsImperative s := by
  simp [duplicateChars, duplicateCharsImperative, duplicateList_eq_flatMap,
    List.flatMap]

end DuplicateChars
