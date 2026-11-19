import Mathlib
namespace Agent

/-!
# HumanEval/27 — `flip_case`

Translation of the Python program

```python
def flip_case(string: str) -> str:
    """ For a given string, flip lowercase characters to uppercase and uppercase to lowercase. """
    return string.swapcase()
```

into Lean 4.

The file contains

* a functional implementation (`flipCase`, built on the character-level `flipChar`),
* unit tests mirroring the Python `check` function,
* a pre-condition, a collection of properties with proofs, a post-condition and the
  correctness theorem `Pre → Post`,
* an imperative implementation using `Id.run do` with a mutable accumulator, and
* the equivalence theorem between the functional and the imperative versions.

`String.swapcase` in Python operates on the full Unicode case mapping; as is customary for the
VeriBench translations (and matching Lean's `Char.toUpper` / `Char.toLower`) the ASCII case
mapping is used here, which agrees with Python on all inputs of the test suite.
-/

namespace humaneval_27_flip_case

/-! ## Implementation -/

/-- Flip the case of a single character: lowercase ↦ uppercase, uppercase ↦ lowercase,
every other character is left untouched. -/
def flipChar (c : Char) : Char :=
  if c.isLower then c.toUpper else if c.isUpper then c.toLower else c

/-- `flipCase s` is the Lean counterpart of Python's `s.swapcase()`. -/
def flipCase (s : String) : String := ⟨s.data.map flipChar⟩

/-! ## Unit tests (mirroring the Python `check` function) -/

example : flipCase "" = "" := by native_decide
example : flipCase "Hello" = "hELLO" := by native_decide
example : flipCase "Hello!" = "hELLO!" := by native_decide
example : flipCase "These violent delights have violent ends" =
    "tHESE VIOLENT DELIGHTS HAVE VIOLENT ENDS" := by native_decide

#eval flipCase "Hello"
#eval flipCase "Hello!"
#eval flipCase "These violent delights have violent ends"

/-! ## Character-level auxiliary lemmas -/

lemma isLower_iff (c : Char) : c.isLower = true ↔ (97 ≤ c.toNat ∧ c.toNat ≤ 122) := by
  simp only [Char.isLower, Bool.and_eq_true, decide_eq_true_eq]; exact Iff.rfl

lemma isUpper_iff (c : Char) : c.isUpper = true ↔ (65 ≤ c.toNat ∧ c.toNat ≤ 90) := by
  simp only [Char.isUpper, Bool.and_eq_true, decide_eq_true_eq]; exact Iff.rfl

lemma toNat_ofNat_small (n : ℕ) (h : n < 0xd800) : (Char.ofNat n).toNat = n := by
  rw [Char.toNat_ofNat, if_pos (Or.inl h)]

lemma toNat_toUpper (c : Char) (h : c.isLower = true) : c.toUpper.toNat = c.toNat - 32 := by
  rw [isLower_iff] at h
  show (if c.toNat ≥ 97 ∧ c.toNat ≤ 122 then Char.ofNat (c.toNat - 32) else c).toNat = _
  rw [if_pos ⟨h.1, h.2⟩]
  exact toNat_ofNat_small _ (by omega)

lemma toNat_toLower (c : Char) (h : c.isUpper = true) : c.toLower.toNat = c.toNat + 32 := by
  rw [isUpper_iff] at h
  show (if c.toNat ≥ 65 ∧ c.toNat ≤ 90 then Char.ofNat (c.toNat + 32) else c).toNat = _
  rw [if_pos ⟨h.1, h.2⟩]
  exact toNat_ofNat_small _ (by omega)

/-- Upper-casing a lowercase letter yields an uppercase letter. -/
lemma isUpper_toUpper (c : Char) (h : c.isLower = true) : c.toUpper.isUpper = true := by
  rw [isUpper_iff, toNat_toUpper c h]
  rw [isLower_iff] at h
  omega

/-- Lower-casing an uppercase letter yields a lowercase letter. -/
lemma isLower_toLower (c : Char) (h : c.isUpper = true) : c.toLower.isLower = true := by
  rw [isLower_iff, toNat_toLower c h]
  rw [isUpper_iff] at h
  omega

lemma toLower_toUpper (c : Char) (h : c.isLower = true) : c.toUpper.toLower = c := by
  have hn := toNat_toUpper c h
  rw [isLower_iff] at h
  have hu := (isUpper_iff _).1 (isUpper_toUpper c (by rw [isLower_iff]; exact h))
  show (if c.toUpper.toNat ≥ 65 ∧ c.toUpper.toNat ≤ 90 then Char.ofNat (c.toUpper.toNat + 32)
        else c.toUpper) = c
  rw [if_pos ⟨hu.1, hu.2⟩, hn]
  have h32 : c.toNat - 32 + 32 = c.toNat := by omega
  rw [h32, Char.ofNat_toNat]

lemma toUpper_toLower (c : Char) (h : c.isUpper = true) : c.toLower.toUpper = c := by
  have hn := toNat_toLower c h
  rw [isUpper_iff] at h
  have hu := (isLower_iff _).1 (isLower_toLower c (by rw [isUpper_iff]; exact h))
  show (if c.toLower.toNat ≥ 97 ∧ c.toLower.toNat ≤ 122 then Char.ofNat (c.toLower.toNat - 32)
        else c.toLower) = c
  rw [if_pos ⟨hu.1, hu.2⟩, hn]
  have h32 : c.toNat + 32 - 32 = c.toNat := by omega
  rw [h32, Char.ofNat_toNat]

/-- `flipChar` is an involution. -/
lemma flipChar_flipChar (c : Char) : flipChar (flipChar c) = c := by
  unfold flipChar
  by_cases hL : c.isLower = true
  · rw [if_pos hL]
    have hn := toNat_toUpper c hL
    have hL' := (isLower_iff c).1 hL
    have h1 : ¬ (c.toUpper.isLower = true) := by rw [isLower_iff, hn]; omega
    have h2 : c.toUpper.isUpper = true := by rw [isUpper_iff, hn]; omega
    rw [if_neg h1, if_pos h2, toLower_toUpper c hL]
  · rw [if_neg hL]
    by_cases hU : c.isUpper = true
    · rw [if_pos hU]
      have hn := toNat_toLower c hU
      have hU' := (isUpper_iff c).1 hU
      have h1 : c.toLower.isLower = true := by rw [isLower_iff, hn]; omega
      rw [if_pos h1, toUpper_toLower c hU]
    · rw [if_neg hU, if_neg hL, if_neg hU]

/-! ## Pre-condition -/

/-- `flip_case` is total in Python: every string is an admissible input. -/
def Pre (_s : String) : Prop := True

/-! ## Properties -/

/-- The result has the same length as the input. -/
def length_prop (s : String) : Prop := (flipCase s).length = s.length

theorem length_thm (s : String) : length_prop s := by
  show (s.data.map flipChar).length = s.data.length
  exact List.length_map _

/-- Position-wise specification: the `i`-th character of the result is `flipChar` applied to the
`i`-th character of the input (and the result has no extra positions). -/
def pointwise_prop (s : String) : Prop :=
  ∀ i : ℕ, (flipCase s).data[i]? = (s.data[i]?).map flipChar

theorem pointwise_thm (s : String) : pointwise_prop s := by
  intro i
  simp [flipCase]

/-- The defining case analysis of `swapcase`: lowercase letters become uppercase, uppercase
letters become lowercase, all other characters are copied verbatim. -/
def swapcase_prop (s : String) : Prop :=
  ∀ (i : ℕ) (c : Char), s.data[i]? = some c →
    (c.isLower = true → (flipCase s).data[i]? = some c.toUpper) ∧
    (c.isUpper = true → (flipCase s).data[i]? = some c.toLower) ∧
    (c.isLower = false → c.isUpper = false → (flipCase s).data[i]? = some c)

theorem swapcase_thm (s : String) : swapcase_prop s := by
  intro i c hc
  have hp : (flipCase s).data[i]? = some (flipChar c) := by
    have := pointwise_thm s i
    rw [this, hc]; rfl
  refine ⟨fun hl => ?_, fun hu => ?_, fun hl hu => ?_⟩
  · rw [hp, flipChar, if_pos hl]
  · by_cases hl : c.isLower = true
    · -- a character cannot be both lowercase and uppercase
      rw [isLower_iff] at hl
      rw [isUpper_iff] at hu
      omega
    · rw [hp, flipChar, if_neg hl, if_pos hu]
  · rw [hp, flipChar, if_neg (by simp [hl]), if_neg (by simp [hu])]

/-- Flipping the case twice gives back the original string. -/
def involutive_prop (s : String) : Prop := flipCase (flipCase s) = s

theorem involutive_thm (s : String) : involutive_prop s := by
  simp only [involutive_prop, flipCase, List.map_map, Function.comp_def, flipChar_flipChar,
    List.map_id_fun', id_eq]

/-- Edge case from the Python test suite: the empty string is mapped to the empty string. -/
def empty_prop : Prop := flipCase "" = ""

theorem empty_thm : empty_prop := by
  unfold empty_prop
  native_decide

/-! ## Post-condition -/

/-- The post-condition is the conjunction of all the properties above. -/
def Post_prop (s : String) : Prop :=
  length_prop s ∧ pointwise_prop s ∧ swapcase_prop s ∧ involutive_prop s

/-! ## Correctness -/

theorem correctness (s : String) (_h : Pre s) : Post_prop s :=
  ⟨length_thm s, pointwise_thm s, swapcase_thm s, involutive_thm s⟩

/-! ## Imperative implementation -/

/-- Imperative version: walk over the characters of `s`, pushing the flipped character onto a
mutable accumulator. -/
def flipCaseImp (s : String) : String := Id.run do
  let mut acc : String := ""
  for c in s.data do
    acc := acc.push (flipChar c)
  return acc

/-! ## Imperative unit tests -/

example : flipCaseImp "" = "" := by native_decide
example : flipCaseImp "Hello" = "hELLO" := by native_decide
example : flipCaseImp "Hello!" = "hELLO!" := by native_decide
example : flipCaseImp "These violent delights have violent ends" =
    "tHESE VIOLENT DELIGHTS HAVE VIOLENT ENDS" := by native_decide

#eval flipCaseImp "Hello"
#eval flipCaseImp "Hello!"
#eval flipCaseImp "These violent delights have violent ends"

/-! ## Equivalence of the functional and the imperative implementation -/

lemma foldl_push (l : List Char) (acc : String) :
    l.foldl (fun a c => a.push (flipChar c)) acc = ⟨acc.data ++ l.map flipChar⟩ := by
  induction l generalizing acc with
  | nil => simp
  | cons c t ih =>
    simp only [List.foldl_cons, List.map_cons, ih]
    cases acc
    simp [String.push]

lemma flipCaseImp_eq_foldl (s : String) :
    flipCaseImp s = s.data.foldl (fun a c => a.push (flipChar c)) "" := by
  simp [flipCaseImp, Id.run]; rfl

theorem flipCase_eq_flipCaseImp (s : String) : flipCase s = flipCaseImp s := by
  rw [flipCaseImp_eq_foldl, foldl_push]
  rfl

end humaneval_27_flip_case
end Agent
