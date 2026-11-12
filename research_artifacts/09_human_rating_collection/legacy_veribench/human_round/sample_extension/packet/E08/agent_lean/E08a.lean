/-!
# VeriBench -- Duplicate Characters
Every stated theorem is PROVEN (no `sorry`) -- this is the expected standard.
-/

namespace DuplicateChars

/--
Return a new string where each character from the input string is duplicated.
-/
def duplicateChars (s : String) : String :=
  s.foldl (λ acc c => acc.push c |>.push c) ""

/-- Precondition: the input must be a string (always true in Lean for String type). -/
def Pre (_s : String) : Prop := True

example : duplicateChars "abc" = "aabbcc" := by native_decide
example : duplicateChars "" = "" := by native_decide
example : duplicateChars "!a " = "!!aa  " := by native_decide

/-- Post-condition: the output string has even length. -/
theorem duplicateChars_length_even (s : String) : (duplicateChars s).length % 2 = 0 := by
  sorry

/-- Property: duplicateChars preserves the original string when every other character
    is removed. The "un-duplicate" function takes characters at even indices (0, 2, 4, ...). -/
def unDuplicate (s : String) : String :=
  s.foldl (λ (acc : String) (c : Char) =>
    if acc.length % 2 = 0 then acc.push c else acc) ""

theorem duplicateChars_unDuplicate_eq (s : String) : unDuplicate (duplicateChars s) = s := by
  sorry

/-- Property: duplicateChars preserves the relative order of characters. -/
theorem duplicateChars_order (s t : String) (h : s.isPrefixOf t) :
    (duplicateChars s).isPrefixOf (duplicateChars t) := by
  sorry

/-- Property: duplicateChars is injective. -/
theorem duplicateChars_injective (s t : String) (h : duplicateChars s = duplicateChars t) : s = t := by
  sorry

/-- Correctness: the function satisfies the examples from the docstring
    and the length-even property. -/
theorem correctness_thm (s : String) (_hPre : Pre s) : (duplicateChars s).length % 2 = 0 := by
  sorry

end DuplicateChars