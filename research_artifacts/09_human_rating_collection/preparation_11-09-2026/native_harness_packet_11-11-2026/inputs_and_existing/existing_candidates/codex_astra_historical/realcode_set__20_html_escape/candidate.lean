import Mathlib

/-!
Formalization of Python's `html.escape` and its checked benchmark wrapper.
The functional and imperative implementations perform the replacements in source
order, starting with ampersands. An independent characterwise specification states
the exact result, including the optional treatment of quotes and Unicode characters.

`Input.nonString` represents any Python object that is not a string: all such objects
have the same observable behavior here. `Except.error "expected str object"` models
the wrapper's TypeError. Lean strings model sequences of Unicode scalar values.
-/

namespace HtmlEscape

/-- A single-character `str.replace`: replacement text is not scanned again. -/
def replaceChar (s : String) (needle : Char) (replacement : String) : String :=
  String.mk (s.toList.flatMap fun c => if c = needle then replacement.toList else [c])

/-- The five passes of the Python implementation, with the same default flag. -/
def escape (s : String) (quote : Bool := true) : String :=
  let s := replaceChar s '&' "&amp;"
  let s := replaceChar s '<' "&lt;"
  let s := replaceChar s '>' "&gt;"
  if quote then
    let s := replaceChar s '"' "&quot;"
    replaceChar s '\'' "&#x27;"
  else s

inductive Input where
  | str (value : String)
  | nonString
  deriving Repr, DecidableEq

deriving instance DecidableEq for Except

def benchmark_escape (input : Input) (quote : Bool := true) : Except String String :=
  match input with
  | .str s => .ok (escape s quote)
  | .nonString => .error "expected str object"

/-- Independent specification of the output contributed by one input character. -/
def encodeChar (quote : Bool) (c : Char) : List Char :=
  if c = '&' then "&amp;".toList
  else if c = '<' then "&lt;".toList
  else if c = '>' then "&gt;".toList
  else if quote then
    if c = '"' then "&quot;".toList
    else if c = '\'' then "&#x27;".toList
    else [c]
  else [c]

/-- Characters which need no escaping for the given quote flag. -/
def Ordinary (quote : Bool) (c : Char) : Prop :=
  c ≠ '&' ∧ c ≠ '<' ∧ c ≠ '>' ∧ (quote = true → c ≠ '"' ∧ c ≠ '\'')

instance (quote : Bool) (c : Char) : Decidable (Ordinary quote c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ (_ → _ ∧ _)))

-- Unit tests, including the four checks in the Python source.
example : escape "<b>\"&'</b>" = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by
  native_decide
example : escape "" = "" := by native_decide
example : escape "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by
  native_decide
example : escape "&<" = "&amp;&lt;" := by native_decide
example : escape "&amp;" = "&amp;amp;" := by native_decide
example : escape "é🙂\n\t" = "é🙂\n\t" := by native_decide
example : benchmark_escape (.str "\"'") = .ok "&quot;&#x27;" := by native_decide
example : benchmark_escape .nonString = .error "expected str object" := by native_decide

#eval escape "<b>\"&'</b>"
#eval escape "<b>\"&'</b>" false
#eval benchmark_escape .nonString

/-- Exactly the Python precondition: the input is a string. -/
def Pre (input : Input) : Prop :=
  match input with
  | .str _ => True
  | .nonString => False

private theorem replaceChar_append (s t : String) (c : Char) (r : String) :
    replaceChar (s ++ t) c r = replaceChar s c r ++ replaceChar t c r := by
  cases s
  cases t
  simp [replaceChar, String.toList, List.flatMap_append]
  rfl

private theorem escape_append (s t : String) (quote : Bool) :
    escape (s ++ t) quote = escape s quote ++ escape t quote := by
  cases quote <;> simp [escape, replaceChar_append]

private theorem escape_singleton (c : Char) (quote : Bool) :
    escape (String.mk [c]) quote = String.mk (encodeChar quote c) := by
  by_cases ha : c = '&'
  · subst c; cases quote <;> decide
  by_cases hl : c = '<'
  · subst c; cases quote <;> decide
  by_cases hg : c = '>'
  · subst c; cases quote <;> decide
  by_cases hd : c = '"'
  · subst c; cases quote <;> decide
  by_cases hs : c = '\''
  · subst c; cases quote <;> decide
  cases quote <;> simp [escape, replaceChar, encodeChar, String.toList, ha, hl, hg, hd, hs]

/-- Every character expands exactly once according to the HTML entity table. -/
def characterwise_prop (s : String) (quote : Bool) : Prop :=
  escape s quote = String.mk (s.toList.flatMap (encodeChar quote))

theorem characterwise_thm (s : String) (quote : Bool) : characterwise_prop s quote := by
  rcases s with ⟨cs⟩
  unfold characterwise_prop
  induction cs with
  | nil => cases quote <;> rfl
  | cons c cs ih =>
    change escape (String.mk [c] ++ String.mk cs) quote = _
    rw [escape_append, escape_singleton, ih]
    rfl

/-- Escaping respects concatenation, so no entity depends on a neighboring character. -/
def append_prop (s t : String) (quote : Bool) : Prop :=
  escape (s ++ t) quote = escape s quote ++ escape t quote

theorem append_thm (s t : String) (quote : Bool) : append_prop s t quote :=
  escape_append s t quote

/-- Output contains no raw angle brackets, and no raw quotes when enabled. -/
def safeOutput_prop (s : String) (quote : Bool) : Prop :=
  ∀ c ∈ (escape s quote).toList,
    c ≠ '<' ∧ c ≠ '>' ∧ (quote = true → c ≠ '"' ∧ c ≠ '\'')

private theorem encodeChar_safe (c d : Char) (quote : Bool)
    (h : d ∈ encodeChar quote c) :
    d ≠ '<' ∧ d ≠ '>' ∧ (quote = true → d ≠ '"' ∧ d ≠ '\'') := by
  unfold encodeChar at h
  split_ifs at h <;> simp_all [String.toList] <;> aesop

theorem safeOutput_thm (s : String) (quote : Bool) : safeOutput_prop s quote := by
  intro c hc
  rw [characterwise_thm s quote] at hc
  obtain ⟨d, _, hd⟩ := List.mem_flatMap.mp hc
  exact encodeChar_safe d c quote hd

/-- Strings without enabled special characters are preserved exactly. -/
def unchanged_prop (s : String) (quote : Bool) : Prop :=
  (∀ c ∈ s.toList, Ordinary quote c) → escape s quote = s

private theorem encodeChar_ordinary (c : Char) (quote : Bool) (h : Ordinary quote c) :
    encodeChar quote c = [c] := by
  rcases h with ⟨ha, hl, hg, hq⟩
  cases quote <;> simp_all [encodeChar]

theorem unchanged_thm (s : String) (quote : Bool) : unchanged_prop s quote := by
  intro h
  rw [characterwise_thm s quote]
  have he : s.toList.flatMap (encodeChar quote) = s.toList := by
    calc
      _ = s.toList.flatMap (fun c => [c]) :=
        List.flatMap_congr (fun c hc => encodeChar_ordinary c quote (h c hc))
      _ = s.toList := by simp
  rw [he]
  rfl

/-- Exact increase in the number of Unicode characters, including both quote types. -/
def length_prop (s : String) (quote : Bool) : Prop :=
  (escape s quote).length = s.length +
    4 * s.toList.count '&' + 3 * s.toList.count '<' + 3 * s.toList.count '>' +
    (if quote then 5 * (s.toList.count '"' + s.toList.count '\'') else 0)

private theorem encodeChar_length (c : Char) (quote : Bool) :
    (encodeChar quote c).length = 1 +
      (if c = '&' then 4 else 0) + (if c = '<' then 3 else 0) +
      (if c = '>' then 3 else 0) +
      (if quote then (if c = '"' then 5 else 0) + (if c = '\'' then 5 else 0) else 0) := by
  unfold encodeChar
  split_ifs <;> simp_all [String.toList]

theorem length_thm (s : String) (quote : Bool) : length_prop s quote := by
  unfold length_prop
  rw [characterwise_thm s quote]
  rcases s with ⟨cs⟩
  change (cs.flatMap (encodeChar quote)).length = _
  simp only [String.length, String.toList]
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.length_append, encodeChar_length,
      List.length_cons, List.count_cons]
    rw [ih]
    cases quote <;> simp only [Bool.false_eq_true, if_false, if_true, beq_iff_eq] <;>
      split_ifs <;> omega

/-- With `quote=false`, the two quote characters retain their original counts. -/
def quotesPreserved_prop (s : String) : Prop :=
  (escape s false).toList.count '"' = s.toList.count '"' ∧
  (escape s false).toList.count '\'' = s.toList.count '\''

private theorem encodeChar_quote_counts (c : Char) :
    (encodeChar false c).count '"' = [c].count '"' ∧
    (encodeChar false c).count '\'' = [c].count '\'' := by
  unfold encodeChar
  split_ifs <;> simp_all [String.toList]

theorem quotesPreserved_thm (s : String) : quotesPreserved_prop s := by
  unfold quotesPreserved_prop
  rw [characterwise_thm s false]
  rcases s with ⟨cs⟩
  change (cs.flatMap (encodeChar false)).count '"' = cs.count '"' ∧
    (cs.flatMap (encodeChar false)).count '\'' = cs.count '\''
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simpa only [List.flatMap_cons, List.count_append, List.count_cons,
      List.count_nil, Nat.zero_add, Nat.add_comm] using
      And.intro (congrArg₂ (· + ·) (encodeChar_quote_counts c).1 ih.1)
        (congrArg₂ (· + ·) (encodeChar_quote_counts c).2 ih.2)

/-- The wrapper accepts every string and rejects every non-string with TypeError. -/
def boundary_prop (input : Input) (quote : Bool) : Prop :=
  match input with
  | .str s => benchmark_escape input quote = .ok (escape s quote)
  | .nonString => benchmark_escape input quote = .error "expected str object"

theorem boundary_thm (input : Input) (quote : Bool) : boundary_prop input quote := by
  cases input <;> rfl

/-- Successful calls satisfy the exact specification and its safety/preservation laws. -/
def Post_prop (input : Input) (quote : Bool) : Prop :=
  match input with
  | .str s =>
    boundary_prop input quote ∧ characterwise_prop s quote ∧ safeOutput_prop s quote ∧
    unchanged_prop s quote ∧ length_prop s quote ∧ quotesPreserved_prop s
  | .nonString => False

-- Executable decision procedures let the PBTs check the propositions themselves.
-- These procedures compute from the definitions; they do not use the proofs above.
instance (s : String) (quote : Bool) : Decidable (characterwise_prop s quote) := by
  unfold characterwise_prop
  infer_instance

instance (s t : String) (quote : Bool) : Decidable (append_prop s t quote) := by
  unfold append_prop
  infer_instance

instance (s : String) (quote : Bool) : Decidable (safeOutput_prop s quote) := by
  unfold safeOutput_prop
  infer_instance

instance (s : String) (quote : Bool) : Decidable (unchanged_prop s quote) := by
  unfold unchanged_prop
  infer_instance

instance (s : String) (quote : Bool) : Decidable (length_prop s quote) := by
  unfold length_prop
  infer_instance

instance (s : String) : Decidable (quotesPreserved_prop s) := by
  unfold quotesPreserved_prop
  infer_instance

instance (input : Input) (quote : Bool) : Decidable (boundary_prop input quote) := by
  cases input <;> unfold boundary_prop <;> infer_instance

instance (input : Input) (quote : Bool) : Decidable (Post_prop input quote) := by
  cases input <;> unfold Post_prop <;> infer_instance

-- Randomized PBTs: one for each executable property and for the postcondition.
#eval Plausible.Testable.check
  (∀ (s : String) (quote : Bool), decide (characterwise_prop s quote) = true)
#eval Plausible.Testable.check
  (∀ (s t : String) (quote : Bool), decide (append_prop s t quote) = true)
#eval Plausible.Testable.check
  (∀ (s : String) (quote : Bool), decide (safeOutput_prop s quote) = true)
#eval Plausible.Testable.check
  (∀ (s : String) (quote : Bool), decide (unchanged_prop s quote) = true)
#eval Plausible.Testable.check
  (∀ (s : String) (quote : Bool), decide (length_prop s quote) = true)
#eval Plausible.Testable.check
  (∀ s : String, decide (quotesPreserved_prop s) = true)
-- Both observable input classes are tested, without needing an Input sampler.
#eval Plausible.Testable.check
  (∀ (s : String) (quote : Bool),
    (decide (boundary_prop (.str s) quote) && decide (boundary_prop .nonString quote)) = true)
-- `Input.str s` generates exactly the admissible inputs of Pre, with no discarded samples.
#eval Plausible.Testable.check
  (∀ (s : String) (quote : Bool), decide (Post_prop (.str s) quote) = true)

/-- A focused alphabet containing all triggers, entity fragments, whitespace and Unicode. -/
def testAlphabet : List Char := ['&', '<', '>', '"', '\'', 'a', ';', '#', ' ', '\n', 'é', '🙂']

/-- Exhaustively enumerate every word of length at most n over an alphabet. -/
def wordsUpTo (alphabet : List Char) : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 => [] :: alphabet.flatMap (fun c => (wordsUpTo alphabet n).map (c :: ·))

def testStrings : List String := (wordsUpTo testAlphabet 3).map String.mk

-- Bounded PBTs: 1 + 12 + 12² + 12³ = 1,885 strings, using both quote flags.
-- Each named property is checked separately, as well as their postcondition conjunction.
example : testStrings.all (fun s => [false, true].all
    (fun quote => decide (characterwise_prop s quote))) = true := by native_decide
example : testStrings.all (fun s => [false, true].all
    (fun quote => decide (safeOutput_prop s quote))) = true := by native_decide
example : testStrings.all (fun s => [false, true].all
    (fun quote => decide (unchanged_prop s quote))) = true := by native_decide
example : testStrings.all (fun s => [false, true].all
    (fun quote => decide (length_prop s quote))) = true := by native_decide
example : testStrings.all (fun s => decide (quotesPreserved_prop s)) = true := by native_decide
example : (Input.nonString :: testStrings.map Input.str).all (fun input => [false, true].all
    (fun quote => decide (boundary_prop input quote))) = true := by native_decide
example : testStrings.all (fun s => [false, true].all
    (fun quote => decide (Post_prop (.str s) quote))) = true := by native_decide

-- Concatenation: all pairs of words of length at most two, in both modes.
example : ((wordsUpTo testAlphabet 2).map String.mk).all (fun s =>
    ((wordsUpTo testAlphabet 2).map String.mk).all (fun t =>
      [false, true].all (fun quote => decide (append_prop s t quote)))) = true := by
  native_decide

-- A non-vacuous preservation PBT: every generated character is ordinary in both modes.
example : ((wordsUpTo ['a', 'é', '🙂', ' ', '\n', ';'] 4).map String.mk).all (fun s =>
    [false, true].all (fun quote => decide (escape s quote = s))) = true := by
  native_decide

/-- Every input satisfying the original type check meets the complete postcondition. -/
theorem correctness (input : Input) (quote : Bool) : Pre input → Post_prop input quote := by
  cases input with
  | str s =>
    intro _
    exact ⟨boundary_thm (.str s) quote, characterwise_thm s quote,
      safeOutput_thm s quote, unchanged_thm s quote, length_thm s quote,
      quotesPreserved_thm s⟩
  | nonString =>
    intro h
    exact False.elim h

/-- Direct imperative translation of the Python assignments and conditional. -/
def escapeImperative (s : String) (quote : Bool := true) : String := Id.run do
  let mut result := s
  result := replaceChar result '&' "&amp;"
  result := replaceChar result '<' "&lt;"
  result := replaceChar result '>' "&gt;"
  if quote then
    result := replaceChar result '"' "&quot;"
    result := replaceChar result '\'' "&#x27;"
  return result

def benchmark_escapeImperative (input : Input) (quote : Bool := true) : Except String String :=
  match input with
  | .str s => .ok (escapeImperative s quote)
  | .nonString => .error "expected str object"

-- Imperative unit tests and property-based comparison with the functional definition.
example : escapeImperative "<b>\"&'</b>" = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by
  native_decide
example : escapeImperative "" = "" := by native_decide
example : escapeImperative "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by
  native_decide
example : escapeImperative "&<" = "&amp;&lt;" := by native_decide
example : benchmark_escapeImperative .nonString = .error "expected str object" := by
  native_decide

#eval escapeImperative "<b>\"&'</b>"
#eval escapeImperative "<b>\"&'</b>" false
#eval Plausible.Testable.check
  (∀ (s : String) (quote : Bool), escape s quote = escapeImperative s quote)
example : testStrings.all (fun s => [false, true].all
    (fun quote => decide (escape s quote = escapeImperative s quote))) = true := by
  native_decide

/-- Equality holds for all strings and both flags, without a restricted precondition. -/
theorem functional_imperative_thm (s : String) (quote : Bool) :
    escape s quote = escapeImperative s quote := by
  cases quote <;> rfl

/-- The checked wrappers agree on successful results and on type errors. -/
theorem benchmark_equivalence_thm (input : Input) (quote : Bool) :
    benchmark_escape input quote = benchmark_escapeImperative input quote := by
  cases input with
  | str s => exact congrArg Except.ok (functional_imperative_thm s quote)
  | nonString => rfl

end HtmlEscape
