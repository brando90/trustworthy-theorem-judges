import Mathlib

/-!
# HTML escaping (Python `html.escape`)

Lean 4 translation of Python's `html.escape`.  The Python function replaces the
characters `&`, `<` and `>` (and, when the flag `quote` is set, also `"` and `'`) by
their HTML-safe entity references `&amp;`, `&lt;`, `&gt;`, `&quot;` and `&#x27;`.

Python performs five successive `str.replace` calls, starting with `&` so that the
`&` introduced by later replacements is never escaped again.  Since the replacement
texts contain no `<`, `>`, `"` or `'`, this sequential process is the same as a single
left-to-right pass that translates every character independently, which is how the
functional model below is stated.

The file contains
* the functional implementation `escape` (and the wrapper `benchmarkEscape`),
* unit tests mirroring the Python `check` function,
* the pre-condition `Pre`, properties, the post-condition `Post_prop`,
  property-based tests, and the correctness theorem,
* an imperative implementation `escapeImp` and the equivalence theorem.
-/

namespace «20_html_escape»

/-! ## Functional implementation -/

/-- Replacement text for a single character.  `&`, `<` and `>` are always replaced;
`"` and `'` only when `quote = true`; every other character is kept unchanged. -/
def escapeChar (quote : Bool) (c : Char) : String :=
  if c = '&' then "&amp;"
  else if c = '<' then "&lt;"
  else if c = '>' then "&gt;"
  else if quote = true ∧ c = '"' then "&quot;"
  else if quote = true ∧ c = '\'' then "&#x27;"
  else String.singleton c

/-- Escape a list of characters from left to right. -/
def escapeList (quote : Bool) : List Char → List Char
  | [] => []
  | c :: cs => (escapeChar quote c).toList ++ escapeList quote cs

/-- `escape s quote` is Python's `html.escape(s, quote)` (default `quote = True`). -/
def escape (s : String) (quote : Bool := true) : String :=
  String.mk (escapeList quote s.toList)

/-- Python's `benchmark_escape`: it raises `TypeError` unless the input is a `str`.
In Lean the argument type `String` already guarantees the pre-condition, so this is
simply `escape`. -/
def benchmarkEscape (s : String) (quote : Bool := true) : String := escape s quote

/-- Literal transcription of the Python code with five successive `String.replace` calls
(`&` first, so that the `&` introduced by later replacements is not escaped again).  It is
used only in tests, to check that the character-wise model `escape` agrees with Python's
sequential replacement semantics. -/
def escapeSeq (s : String) (quote : Bool := true) : String :=
  let s₁ := s.replace "&" "&amp;"
  let s₂ := s₁.replace "<" "&lt;"
  let s₃ := s₂.replace ">" "&gt;"
  if quote then
    let s₄ := s₃.replace "\"" "&quot;"
    s₄.replace "'" "&#x27;"
  else s₃

/-! ## Unit tests (the Python `check` function) -/

-- 1. quote = true (default)
example : escape "<b>\"&'</b>" = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by native_decide
example : escape "" = "" := by native_decide
-- 2. quote = false: `"` and `'` remain untouched
example : escape "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by native_decide
-- 3. order check: no double escaping
example : escape "&<" = "&amp;&lt;" := by native_decide
-- the wrapper behaves identically
example : benchmarkEscape "<b>\"&'</b>" = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by native_decide
example : benchmarkEscape "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by native_decide

-- the sequential-`replace` transcription gives the same results
example : escapeSeq "<b>\"&'</b>" = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by native_decide
example : escapeSeq "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by native_decide
example : escapeSeq "&<" = "&amp;&lt;" := by native_decide

#eval escape "<b>\"&'</b>"
#eval escape "<b>\"&'</b>" false
#eval escape "&<"
#eval escape ""

/-! ## Pre-condition -/

/-- Pre-condition (`pre_escape`): the input must be a string.  The Lean type `String`
already guarantees this, hence the predicate is trivially true for all inputs. -/
def Pre (_s : String) (_quote : Bool) : Prop := True

/-! ## Auxiliary predicates -/

/-- The characters that `escape` rewrites (for the given value of `quote`). -/
def special (quote : Bool) (c : Char) : Prop :=
  c = '&' ∨ c = '<' ∨ c = '>' ∨ (quote = true ∧ (c = '"' ∨ c = '\''))

instance (quote : Bool) (c : Char) : Decidable (special quote c) := by
  unfold special; infer_instance

/-- Characters that must never appear in the escaped output: `<`, `>` and, when `quote`
is set, the quotation marks `"` and `'`. -/
def forbidden (quote : Bool) (c : Char) : Prop :=
  c = '<' ∨ c = '>' ∨ (quote = true ∧ (c = '"' ∨ c = '\''))

instance (quote : Bool) (c : Char) : Decidable (forbidden quote c) := by
  unfold forbidden; infer_instance

/-- Inverse of `escape` on lists of characters: decode the five entity references
produced by `escapeChar` (a stray `&` not starting a known entity is kept). -/
def unescapeList : List Char → List Char
  | [] => []
  | c :: rest =>
    if c = '&' then
      if rest.take 4 = ['a', 'm', 'p', ';'] then '&' :: unescapeList (rest.drop 4)
      else if rest.take 3 = ['l', 't', ';'] then '<' :: unescapeList (rest.drop 3)
      else if rest.take 3 = ['g', 't', ';'] then '>' :: unescapeList (rest.drop 3)
      else if rest.take 5 = ['q', 'u', 'o', 't', ';'] then '"' :: unescapeList (rest.drop 5)
      else if rest.take 5 = ['#', 'x', '2', '7', ';'] then '\'' :: unescapeList (rest.drop 5)
      else '&' :: unescapeList rest
    else c :: unescapeList rest
termination_by l => l.length
decreasing_by all_goals simp_wf; all_goals omega

/-- Inverse of `escape` (used to state that escaping is lossless). -/
def unescape (s : String) : String := String.mk (unescapeList s.toList)

example : unescape "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" = "<b>\"&'</b>" := by native_decide
#eval unescape "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;"

/-! ## Lemmas about `String` -/

theorem mk_toList (s : String) : String.mk s.toList = s := rfl

theorem append_mk_append (acc : String) (l₁ l₂ : List Char) :
    acc ++ String.mk (l₁ ++ l₂) = (acc ++ String.mk l₁) ++ String.mk l₂ := by
  rw [String.append_assoc]; rfl

theorem push_eq_append_singleton (s : String) (c : Char) :
    s.push c = s ++ String.singleton c := rfl

theorem singleton_toList (c : Char) : (String.singleton c).toList = [c] := rfl

/-! ## Lemmas about `escapeChar` -/

theorem escapeChar_of_not_special (quote : Bool) (c : Char) (hc : ¬ special quote c) :
    escapeChar quote c = String.singleton c := by
  unfold escapeChar
  split_ifs with h1 h2 h3 h4 h5
  · exact absurd (Or.inl h1) hc
  · exact absurd (Or.inr (Or.inl h2)) hc
  · exact absurd (Or.inr (Or.inr (Or.inl h3))) hc
  · exact absurd (Or.inr (Or.inr (Or.inr ⟨h4.1, Or.inl h4.2⟩))) hc
  · exact absurd (Or.inr (Or.inr (Or.inr ⟨h5.1, Or.inr h5.2⟩))) hc
  · rfl

theorem entity_safe (quote : Bool) :
    ∀ e ∈ ["&amp;", "&lt;", "&gt;", "&quot;", "&#x27;"], ∀ d ∈ e.toList, ¬ forbidden quote d := by
  cases quote <;> decide

theorem escapeChar_safe (quote : Bool) (c d : Char) (hd : d ∈ (escapeChar quote c).toList) :
    ¬ forbidden quote d := by
  unfold escapeChar at hd
  split_ifs at hd with h1 h2 h3 h4 h5
  · exact entity_safe quote "&amp;" (by decide) d hd
  · exact entity_safe quote "&lt;" (by decide) d hd
  · exact entity_safe quote "&gt;" (by decide) d hd
  · exact entity_safe quote "&quot;" (by decide) d hd
  · exact entity_safe quote "&#x27;" (by decide) d hd
  · rw [singleton_toList, List.mem_singleton] at hd
    subst hd
    unfold forbidden
    rintro (h | h | ⟨hq, h | h⟩)
    · exact h2 h
    · exact h3 h
    · exact h4 ⟨hq, h⟩
    · exact h5 ⟨hq, h⟩

theorem escapeChar_length (quote : Bool) (c : Char) :
    1 ≤ (escapeChar quote c).toList.length ∧ (escapeChar quote c).toList.length ≤ 6 := by
  unfold escapeChar
  split_ifs
  · decide
  · decide
  · decide
  · decide
  · decide
  · rw [singleton_toList]; simp

theorem escapeChar_count_amp_of_special (quote : Bool) (c : Char) (hc : special quote c) :
    (escapeChar quote c).toList.count '&' = 1 := by
  rcases hc with rfl | rfl | rfl | ⟨hq, rfl | rfl⟩ <;> simp [escapeChar, *]

theorem escapeChar_count_amp_of_not_special (quote : Bool) (c : Char) (hc : ¬ special quote c) :
    (escapeChar quote c).toList.count '&' = 0 := by
  rw [escapeChar_of_not_special quote c hc, singleton_toList]
  have hne : c ≠ '&' := fun h => hc (Or.inl h)
  simp [hne]

theorem escapeChar_count_quote_false (c q : Char) (hq : q = '"' ∨ q = '\'') :
    (escapeChar false c).toList.count q = [c].count q := by
  unfold escapeChar
  split_ifs with h1 h2 h3 h4 h5
  · subst h1; rcases hq with rfl | rfl <;> decide
  · subst h2; rcases hq with rfl | rfl <;> decide
  · subst h3; rcases hq with rfl | rfl <;> decide
  · simp at h4
  · simp at h5
  · rfl

theorem escapeChar_quote_irrelevant (c : Char) (hc : c ≠ '"' ∧ c ≠ '\'') :
    escapeChar true c = escapeChar false c := by
  unfold escapeChar
  simp [hc.1, hc.2]

/-! ## Lemmas about `escapeList` -/

theorem escapeList_append (quote : Bool) (l₁ l₂ : List Char) :
    escapeList quote (l₁ ++ l₂) = escapeList quote l₁ ++ escapeList quote l₂ := by
  induction l₁ with
  | nil => simp [escapeList]
  | cons c cs ih => simp [escapeList, ih]

theorem escapeList_eq_flatMap (quote : Bool) (l : List Char) :
    escapeList quote l = l.flatMap (fun c => (escapeChar quote c).toList) := by
  induction l with
  | nil => simp [escapeList]
  | cons c cs ih => simp [escapeList, List.flatMap_cons, ih]

theorem escapeList_safe (quote : Bool) (l : List Char) :
    ∀ d ∈ escapeList quote l, ¬ forbidden quote d := by
  induction l with
  | nil => simp [escapeList]
  | cons c cs ih =>
    intro d hd
    simp only [escapeList, List.mem_append] at hd
    rcases hd with hd | hd
    · exact escapeChar_safe quote c d hd
    · exact ih d hd

theorem escapeList_length (quote : Bool) (l : List Char) :
    l.length ≤ (escapeList quote l).length ∧ (escapeList quote l).length ≤ 6 * l.length := by
  induction l with
  | nil => simp [escapeList]
  | cons c cs ih =>
    have hc := escapeChar_length quote c
    simp only [escapeList, List.length_append, List.length_cons]
    omega

theorem escapeList_of_not_special (quote : Bool) (l : List Char)
    (h : ∀ c ∈ l, ¬ special quote c) : escapeList quote l = l := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    have hc : ¬ special quote c := h c (List.mem_cons_self ..)
    have hcs : ∀ c ∈ cs, ¬ special quote c := fun d hd => h d (List.mem_cons_of_mem c hd)
    simp only [escapeList, escapeChar_of_not_special quote c hc, singleton_toList, ih hcs,
      List.singleton_append]

theorem escapeList_count_amp (quote : Bool) (l : List Char) :
    (escapeList quote l).count '&' = l.countP (fun c => decide (special quote c)) := by
  induction l with
  | nil => simp [escapeList]
  | cons c cs ih =>
    simp only [escapeList, List.count_append, List.countP_cons, ih]
    by_cases hc : special quote c
    · rw [escapeChar_count_amp_of_special quote c hc]; simp [hc]; omega
    · rw [escapeChar_count_amp_of_not_special quote c hc]; simp [hc]

theorem escapeList_count_quote_false (l : List Char) (q : Char) (hq : q = '"' ∨ q = '\'') :
    (escapeList false l).count q = l.count q := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    rw [escapeList, List.count_append, escapeChar_count_quote_false c q hq, ih,
      ← List.count_append, List.singleton_append]

theorem escapeList_quote_irrelevant (l : List Char) (h : ∀ c ∈ l, c ≠ '"' ∧ c ≠ '\'') :
    escapeList true l = escapeList false l := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    have hc := h c (List.mem_cons_self ..)
    have hcs : ∀ c ∈ cs, c ≠ '"' ∧ c ≠ '\'' := fun d hd => h d (List.mem_cons_of_mem c hd)
    simp only [escapeList, escapeChar_quote_irrelevant c hc, ih hcs]

/-! ## Lemmas about `unescapeList` -/

theorem unescapeList_cons_of_ne (c : Char) (l : List Char) (h : c ≠ '&') :
    unescapeList (c :: l) = c :: unescapeList l := by
  rw [unescapeList, if_neg h]

theorem unescapeList_amp (l : List Char) :
    unescapeList ('&' :: 'a' :: 'm' :: 'p' :: ';' :: l) = '&' :: unescapeList l := by
  rw [unescapeList]; simp

theorem unescapeList_lt (l : List Char) :
    unescapeList ('&' :: 'l' :: 't' :: ';' :: l) = '<' :: unescapeList l := by
  rw [unescapeList]; simp

theorem unescapeList_gt (l : List Char) :
    unescapeList ('&' :: 'g' :: 't' :: ';' :: l) = '>' :: unescapeList l := by
  rw [unescapeList]; simp

theorem unescapeList_quot (l : List Char) :
    unescapeList ('&' :: 'q' :: 'u' :: 'o' :: 't' :: ';' :: l) = '"' :: unescapeList l := by
  rw [unescapeList]; simp

theorem unescapeList_x27 (l : List Char) :
    unescapeList ('&' :: '#' :: 'x' :: '2' :: '7' :: ';' :: l) = '\'' :: unescapeList l := by
  rw [unescapeList]; simp

/-- Decoding undoes escaping. -/
theorem unescapeList_escapeList (quote : Bool) (l : List Char) :
    unescapeList (escapeList quote l) = l := by
  induction l with
  | nil => simp [escapeList, unescapeList]
  | cons c cs ih =>
    simp only [escapeList]
    unfold escapeChar
    split_ifs with h1 h2 h3 h4 h5
    · subst h1
      rw [show "&amp;".toList = ['&', 'a', 'm', 'p', ';'] from rfl]
      simp [unescapeList_amp, ih]
    · subst h2
      rw [show "&lt;".toList = ['&', 'l', 't', ';'] from rfl]
      simp [unescapeList_lt, ih]
    · subst h3
      rw [show "&gt;".toList = ['&', 'g', 't', ';'] from rfl]
      simp [unescapeList_gt, ih]
    · obtain ⟨_, rfl⟩ := h4
      rw [show "&quot;".toList = ['&', 'q', 'u', 'o', 't', ';'] from rfl]
      simp [unescapeList_quot, ih]
    · obtain ⟨_, rfl⟩ := h5
      rw [show "&#x27;".toList = ['&', '#', 'x', '2', '7', ';'] from rfl]
      simp [unescapeList_x27, ih]
    · rw [singleton_toList, List.singleton_append, unescapeList_cons_of_ne c _ h1, ih]

/-! ## Properties and theorems -/

/-- Character-wise specification: the output is the concatenation of the replacement
texts of the input characters, in order. -/
def escape_spec_prop (s : String) (quote : Bool) (r : String) : Prop :=
  r.toList = s.toList.flatMap (fun c => (escapeChar quote c).toList)

theorem escape_spec_thm (s : String) (quote : Bool) :
    escape_spec_prop s quote (escape s quote) := by
  unfold escape_spec_prop escape
  exact escapeList_eq_flatMap quote s.toList

/-- The empty string is mapped to the empty string. -/
def escape_empty_prop : Prop := ∀ quote : Bool, escape "" quote = ""

theorem escape_empty_thm : escape_empty_prop := fun _ => rfl

/-- Escaping is a homomorphism for concatenation (it works character by character). -/
def escape_append_prop : Prop :=
  ∀ (s t : String) (quote : Bool), escape (s ++ t) quote = escape s quote ++ escape t quote

theorem escape_append_thm : escape_append_prop := by
  intro s t quote
  show String.mk (escapeList quote (s ++ t).data) =
    String.mk (escapeList quote s.data) ++ String.mk (escapeList quote t.data)
  rw [String.data_append, escapeList_append]
  rfl

/-- Safety: the output never contains `<` or `>`, nor `"` or `'` when `quote = true`. -/
def escape_safe_prop (quote : Bool) (r : String) : Prop :=
  ∀ c ∈ r.toList, ¬ forbidden quote c

theorem escape_safe_thm (s : String) (quote : Bool) : escape_safe_prop quote (escape s quote) :=
  escapeList_safe quote s.toList

/-- Length bounds: the output is at least as long as the input and at most 6 times
longer (the longest replacements, `&quot;` and `&#x27;`, have 6 characters). -/
def escape_length_prop (s : String) (r : String) : Prop :=
  s.length ≤ r.length ∧ r.length ≤ 6 * s.length

theorem escape_length_thm (s : String) (quote : Bool) : escape_length_prop s (escape s quote) :=
  escapeList_length quote s.toList

/-- Strings without special characters are returned unchanged. -/
def escape_no_special_prop : Prop :=
  ∀ (s : String) (quote : Bool), (∀ c ∈ s.toList, ¬ special quote c) → escape s quote = s

theorem escape_no_special_thm : escape_no_special_prop := by
  intro s quote h
  show String.mk (escapeList quote s.toList) = s
  rw [escapeList_of_not_special quote s.toList h]
  rfl

/-- Order matters / no double escaping: every `&` of the output comes from exactly one
special input character, i.e. the number of `&` in the output equals the number of
special characters of the input. -/
def escape_amp_count_prop (s : String) (quote : Bool) (r : String) : Prop :=
  r.toList.count '&' = s.toList.countP (fun c => decide (special quote c))

theorem escape_amp_count_thm (s : String) (quote : Bool) :
    escape_amp_count_prop s quote (escape s quote) :=
  escapeList_count_amp quote s.toList

/-- With `quote = false` the quotation marks `"` and `'` are left untouched: their
numbers of occurrences are preserved. -/
def escape_quote_false_prop (s : String) (quote : Bool) (r : String) : Prop :=
  quote = false →
    r.toList.count '"' = s.toList.count '"' ∧ r.toList.count '\'' = s.toList.count '\''

theorem escape_quote_false_thm (s : String) (quote : Bool) :
    escape_quote_false_prop s quote (escape s quote) := by
  intro hq
  subst hq
  exact ⟨escapeList_count_quote_false s.toList '"' (Or.inl rfl),
    escapeList_count_quote_false s.toList '\'' (Or.inr rfl)⟩

/-- The `quote` flag only matters for strings containing `"` or `'`. -/
def escape_quote_irrelevant_prop : Prop :=
  ∀ s : String, (∀ c ∈ s.toList, c ≠ '"' ∧ c ≠ '\'') → escape s true = escape s false

theorem escape_quote_irrelevant_thm : escape_quote_irrelevant_prop := by
  intro s h
  show String.mk (escapeList true s.toList) = String.mk (escapeList false s.toList)
  rw [escapeList_quote_irrelevant s.toList h]

/-- Escaping is lossless: `unescape` recovers the input. -/
def escape_roundtrip_prop (s : String) (r : String) : Prop :=
  unescape r = s

theorem escape_roundtrip_thm (s : String) (quote : Bool) :
    escape_roundtrip_prop s (escape s quote) := by
  show String.mk (unescapeList (escapeList quote s.toList)) = s
  rw [unescapeList_escapeList]
  rfl

/-- Escaping is injective (for a fixed `quote`). -/
def escape_injective_prop : Prop :=
  ∀ (s t : String) (quote : Bool), escape s quote = escape t quote → s = t

theorem escape_injective_thm : escape_injective_prop := by
  intro s t quote h
  have hs := escape_roundtrip_thm s quote
  have ht := escape_roundtrip_thm t quote
  unfold escape_roundtrip_prop at hs ht
  rw [← hs, ← ht, h]

/-! ## Post-condition -/

/-- Post-condition for `escape s quote = r`. -/
def Post_prop (s : String) (quote : Bool) (r : String) : Prop :=
  escape_spec_prop s quote r ∧
  escape_safe_prop quote r ∧
  escape_length_prop s r ∧
  escape_amp_count_prop s quote r ∧
  escape_quote_false_prop s quote r ∧
  escape_roundtrip_prop s r

/-! ## Property-based tests -/

/-- An alphabet rich in special characters, used to generate test strings. -/
def pbtAlphabet : List Char := ['&', '<', '>', '"', '\'', 'a', ';', ' ']

/-- Build a test string from a list of indices into `pbtAlphabet`. -/
def pbtString (l : List (Fin 8)) : String :=
  String.mk (l.map fun i => pbtAlphabet.getD i.val 'x')

/-- All words of a given length over `pbtAlphabet`. -/
def wordsOfLength : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 => (wordsOfLength n).flatMap fun w => pbtAlphabet.map (· :: w)

/-- All words of length at most 3 over `pbtAlphabet` (585 words). -/
def smallWords : List (List Char) :=
  wordsOfLength 0 ++ wordsOfLength 1 ++ wordsOfLength 2 ++ wordsOfLength 3

/-- A few hand-picked strings. -/
def pbtSamples : List String :=
  ["", "&", "<", ">", "\"", "'", "&amp;", "&lt;", "<b>\"&'</b>", "&<", "a&b<c>d\"e'f",
   "&&&", "<<>>", "plain text", "'''", "\"\"", "&#x27;", "&quot;&quot;"]

-- escape_spec_prop (random and bounded)
#eval Plausible.Testable.check (∀ (s : String) (q : Bool),
  (escape s q).toList = s.toList.flatMap (fun c => (escapeChar q c).toList))
#eval Plausible.Testable.check (∀ (l : List (Fin 8)) (q : Bool),
  (escape (pbtString l) q).toList =
    (pbtString l).toList.flatMap (fun c => (escapeChar q c).toList))
example : smallWords.all (fun w => decide (∀ q : Bool,
    (escape (String.mk w) q).toList = w.flatMap (fun c => (escapeChar q c).toList))) = true := by
  native_decide

-- the character-wise model agrees with the sequential-`replace` transcription of the
-- Python code (random and bounded)
#eval Plausible.Testable.check (∀ (s : String) (q : Bool), escapeSeq s q = escape s q)
#eval Plausible.Testable.check (∀ (l : List (Fin 8)) (q : Bool),
  escapeSeq (pbtString l) q = escape (pbtString l) q)
example : smallWords.all (fun w => decide (∀ q : Bool,
    escapeSeq (String.mk w) q = escape (String.mk w) q)) = true := by
  native_decide
example : pbtSamples.all (fun s => decide (∀ q : Bool, escapeSeq s q = escape s q)) = true := by
  native_decide

-- escape_empty_prop
example : (∀ q : Bool, escape "" q = "") := by decide

-- escape_append_prop
#eval Plausible.Testable.check (∀ (s t : String) (q : Bool),
  escape (s ++ t) q = escape s q ++ escape t q)
#eval Plausible.Testable.check (∀ (l₁ l₂ : List (Fin 8)) (q : Bool),
  escape (pbtString l₁ ++ pbtString l₂) q = escape (pbtString l₁) q ++ escape (pbtString l₂) q)

-- escape_safe_prop
#eval Plausible.Testable.check (∀ (s : String) (q : Bool),
  (escape s q).toList.all (fun c => !decide (forbidden q c)) = true)
#eval Plausible.Testable.check (∀ (l : List (Fin 8)) (q : Bool),
  (escape (pbtString l) q).toList.all (fun c => !decide (forbidden q c)) = true)
example : smallWords.all (fun w => decide (∀ q : Bool,
    ∀ c ∈ (escape (String.mk w) q).toList, ¬ forbidden q c)) = true := by
  native_decide

-- escape_length_prop
#eval Plausible.Testable.check (∀ (s : String) (q : Bool),
  s.length ≤ (escape s q).length ∧ (escape s q).length ≤ 6 * s.length)
#eval Plausible.Testable.check (∀ (l : List (Fin 8)) (q : Bool),
  (pbtString l).length ≤ (escape (pbtString l) q).length ∧
    (escape (pbtString l) q).length ≤ 6 * (pbtString l).length)

-- escape_no_special_prop
#eval Plausible.Testable.check (∀ (s : String) (q : Bool),
  s.toList.all (fun c => !decide (special q c)) = true → escape s q = s)
example : smallWords.all (fun w => decide (∀ q : Bool,
    (∀ c ∈ w, ¬ special q c) → escape (String.mk w) q = String.mk w)) = true := by
  native_decide

-- escape_amp_count_prop
#eval Plausible.Testable.check (∀ (s : String) (q : Bool),
  (escape s q).toList.count '&' = s.toList.countP (fun c => decide (special q c)))
#eval Plausible.Testable.check (∀ (l : List (Fin 8)) (q : Bool),
  (escape (pbtString l) q).toList.count '&' =
    (pbtString l).toList.countP (fun c => decide (special q c)))
example : smallWords.all (fun w => decide (∀ q : Bool,
    (escape (String.mk w) q).toList.count '&' =
      w.countP (fun c => decide (special q c)))) = true := by
  native_decide

-- escape_quote_false_prop
#eval Plausible.Testable.check (∀ (s : String),
  (escape s false).toList.count '"' = s.toList.count '"' ∧
    (escape s false).toList.count '\'' = s.toList.count '\'')
#eval Plausible.Testable.check (∀ (l : List (Fin 8)),
  (escape (pbtString l) false).toList.count '"' = (pbtString l).toList.count '"' ∧
    (escape (pbtString l) false).toList.count '\'' = (pbtString l).toList.count '\'')
example : smallWords.all (fun w => decide (
    (escape (String.mk w) false).toList.count '"' = w.count '"' ∧
    (escape (String.mk w) false).toList.count '\'' = w.count '\'')) = true := by
  native_decide

-- escape_quote_irrelevant_prop
#eval Plausible.Testable.check (∀ (s : String),
  s.toList.all (fun c => c != '"' && c != '\'') = true → escape s true = escape s false)
example : smallWords.all (fun w => decide (
    (∀ c ∈ w, c ≠ '"' ∧ c ≠ '\'') →
      escape (String.mk w) true = escape (String.mk w) false)) = true := by
  native_decide

-- escape_roundtrip_prop
#eval Plausible.Testable.check (∀ (s : String) (q : Bool), unescape (escape s q) = s)
#eval Plausible.Testable.check (∀ (l : List (Fin 8)) (q : Bool),
  unescape (escape (pbtString l) q) = pbtString l)
example : smallWords.all (fun w => decide (∀ q : Bool,
    unescape (escape (String.mk w) q) = String.mk w)) = true := by
  native_decide
example : pbtSamples.all (fun s => decide (∀ q : Bool, unescape (escape s q) = s)) = true := by
  native_decide

-- escape_injective_prop (stated as a decidable equivalence, so that no guard is needed)
#eval Plausible.Testable.check (∀ (s t : String) (q : Bool), (escape s q = escape t q ↔ s = t))
#eval Plausible.Testable.check (∀ (l₁ l₂ : List (Fin 8)) (q : Bool),
  (escape (pbtString l₁) q = escape (pbtString l₂) q ↔ pbtString l₁ = pbtString l₂))

-- Post_prop (all conjuncts at once, in executable form)
#eval Plausible.Testable.check (∀ (l : List (Fin 8)) (q : Bool),
  (escape (pbtString l) q).toList =
      (pbtString l).toList.flatMap (fun c => (escapeChar q c).toList) ∧
  (escape (pbtString l) q).toList.all (fun c => !decide (forbidden q c)) = true ∧
  ((pbtString l).length ≤ (escape (pbtString l) q).length ∧
    (escape (pbtString l) q).length ≤ 6 * (pbtString l).length) ∧
  (escape (pbtString l) q).toList.count '&' =
      (pbtString l).toList.countP (fun c => decide (special q c)) ∧
  (q = false → (escape (pbtString l) q).toList.count '"' = (pbtString l).toList.count '"' ∧
      (escape (pbtString l) q).toList.count '\'' = (pbtString l).toList.count '\'') ∧
  unescape (escape (pbtString l) q) = pbtString l)
example : pbtSamples.all (fun s => decide (∀ q : Bool,
    (escape s q).toList = s.toList.flatMap (fun c => (escapeChar q c).toList) ∧
    (∀ c ∈ (escape s q).toList, ¬ forbidden q c) ∧
    (s.length ≤ (escape s q).length ∧ (escape s q).length ≤ 6 * s.length) ∧
    (escape s q).toList.count '&' = s.toList.countP (fun c => decide (special q c)) ∧
    (q = false → (escape s q).toList.count '"' = s.toList.count '"' ∧
      (escape s q).toList.count '\'' = s.toList.count '\'') ∧
    unescape (escape s q) = s)) = true := by
  native_decide

/-! ## Correctness theorem -/

theorem escape_correct (s : String) (quote : Bool) (_h : Pre s quote) :
    Post_prop s quote (escape s quote) :=
  ⟨escape_spec_thm s quote, escape_safe_thm s quote, escape_length_thm s quote,
    escape_amp_count_thm s quote, escape_quote_false_thm s quote, escape_roundtrip_thm s quote⟩

/-! ## Imperative implementation -/

/-- Imperative version: scan the characters left to right, appending the replacement
text of each one to a mutable output buffer (mirrors the Python branching). -/
def escapeImp (s : String) (quote : Bool := true) : String := Id.run do
  let mut out : String := ""
  for c in s.toList do
    if c = '&' then
      out := out ++ "&amp;"
    else if c = '<' then
      out := out ++ "&lt;"
    else if c = '>' then
      out := out ++ "&gt;"
    else if quote ∧ c = '"' then
      out := out ++ "&quot;"
    else if quote ∧ c = '\'' then
      out := out ++ "&#x27;"
    else
      out := out.push c
  return out

/-! ## Imperative tests -/

example : escapeImp "<b>\"&'</b>" = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by native_decide
example : escapeImp "" = "" := by native_decide
example : escapeImp "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by native_decide
example : escapeImp "&<" = "&amp;&lt;" := by native_decide

#eval escapeImp "<b>\"&'</b>"
#eval escapeImp "<b>\"&'</b>" false

#eval Plausible.Testable.check (∀ (s : String) (q : Bool), escapeImp s q = escape s q)
#eval Plausible.Testable.check (∀ (l : List (Fin 8)) (q : Bool),
  escapeImp (pbtString l) q = escape (pbtString l) q)
example : smallWords.all (fun w => decide (∀ q : Bool,
    escapeImp (String.mk w) q = escape (String.mk w) q)) = true := by
  native_decide

/-! ## Equivalence theorem -/

/-- The loop of `escapeImp`, started with buffer `acc`, appends the escaped list. -/
theorem escapeImp_loop (quote : Bool) (l : List Char) (acc : String) :
    (Id.run do
      let mut out : String := acc
      for c in l do
        if c = '&' then
          out := out ++ "&amp;"
        else if c = '<' then
          out := out ++ "&lt;"
        else if c = '>' then
          out := out ++ "&gt;"
        else if quote ∧ c = '"' then
          out := out ++ "&quot;"
        else if quote ∧ c = '\'' then
          out := out ++ "&#x27;"
        else
          out := out.push c
      return out) = acc ++ String.mk (escapeList quote l) := by
  induction l generalizing acc with
  | nil => simp [escapeList]
  | cons c cs ih =>
    simp only [List.forIn_cons] at ih ⊢
    simp at ih ⊢
    split_ifs with h1 h2 h3 h4 h5 <;> simp only [Id.run_pure] <;>
      rw [ih, escapeList, append_mk_append, mk_toList] <;>
      simp [escapeChar, push_eq_append_singleton, *]

/-- The imperative implementation agrees with the functional one. -/
theorem escapeImp_eq_escape (s : String) (quote : Bool) : escapeImp s quote = escape s quote := by
  unfold escapeImp
  refine (escapeImp_loop quote s.toList "").trans ?_
  rfl

end «20_html_escape»
