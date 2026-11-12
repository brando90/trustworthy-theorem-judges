import Mathlib

/-!
# HTML escaping (`html.escape`)

Lean 4 formalization of Python's `html.escape`:

```python
def escape(s, quote=True):
    s = s.replace("&", "&amp;")      # order matters: `&` first, to avoid double escaping
    s = s.replace("<", "&lt;")
    s = s.replace(">", "&gt;")
    if quote:
        s = s.replace('"', "&quot;")
        s = s.replace('\'', "&#x27;")
    return s
```

`benchmark_escape` first checks that the input is a `str` (`pre_escape`) and then calls
`escape`.  In Lean the input type `String` makes the precondition trivially true.

The implementation mirrors the Python program literally: a sequence of single-character
replacements (`replaceChar` is `str.replace` for a one-character pattern).  The properties
proved below include

* `escape` is a single left-to-right pass, i.e. no character introduced by an earlier
  replacement is touched by a later one (`escape_single_pass`);
* the result contains no `<`, `>` (nor `"`, `'` when `quote`) characters (`escape_safe`);
* every `&` of the result starts an entity, and the escaping is lossless: a decoder
  `unescape` recovers the input (`unescape_escape`), hence `escape` is injective;
* an exact length formula, a homomorphism law for `++`, the characterisation of the fixed
  points (`escape s = s` iff `s` has no special character), and the relation between the two
  values of `quote`.

An imperative version (`escapeImp`, `Id.run do` with a mutable string and `for` loops) is
proved equal to the functional one.
-/

namespace «20_html_escape»

/-! ## Functional implementation -/

/-- Python `s.replace(t, r)` for a single-character pattern `t`, on lists of characters:
every occurrence of `t` is replaced by the characters `r`. -/
def replaceChar (t : Char) (r : List Char) : List Char → List Char
  | [] => []
  | c :: cs => (if c = t then r else [c]) ++ replaceChar t r cs

/-- The body of Python's `escape`, on lists of characters: the five replacements, in the
order of the Python program (`&` first). -/
def escapeList (quote : Bool) (l : List Char) : List Char :=
  let s1 := replaceChar '&' "&amp;".toList l
  let s2 := replaceChar '<' "&lt;".toList s1
  let s3 := replaceChar '>' "&gt;".toList s2
  if quote then
    let s4 := replaceChar '"' "&quot;".toList s3
    replaceChar '\'' "&#x27;".toList s4
  else s3

/-- Python `html.escape(s, quote=True)`. -/
def escape (s : String) (quote : Bool := true) : String :=
  ⟨escapeList quote s.toList⟩

/-- Python `benchmark_escape`: the `isinstance(s, str)` check is enforced by the type. -/
def benchmark_escape (s : String) (quote : Bool := true) : String :=
  escape s quote

/-- The HTML-safe sequence a single character is turned into (the single-pass view of the
sequential replacements). -/
def escapeChar (quote : Bool) (c : Char) : List Char :=
  if c = '&' then "&amp;".toList
  else if c = '<' then "&lt;".toList
  else if c = '>' then "&gt;".toList
  else if quote ∧ c = '"' then "&quot;".toList
  else if quote ∧ c = '\'' then "&#x27;".toList
  else [c]

/-- The characters that `escape s quote` must eliminate. -/
def isSpecial (quote : Bool) (c : Char) : Bool :=
  c == '&' || c == '<' || c == '>' || (quote && (c == '"' || c == '\''))

/-- Try to read one of the five entities produced by `escape` (the part after the `&`),
returning the decoded character and the number of characters consumed. -/
def readEntity : List Char → Option (Char × Nat)
  | 'a' :: 'm' :: 'p' :: ';' :: _ => some ('&', 4)
  | 'l' :: 't' :: ';' :: _ => some ('<', 3)
  | 'g' :: 't' :: ';' :: _ => some ('>', 3)
  | 'q' :: 'u' :: 'o' :: 't' :: ';' :: _ => some ('"', 5)
  | '#' :: 'x' :: '2' :: '7' :: ';' :: _ => some ('\'', 5)
  | _ => none

/-- Decoder for the five entities produced by `escape`; other characters are copied. -/
def unescapeList : List Char → List Char
  | [] => []
  | c :: rest =>
    if c = '&' then
      match readEntity rest with
      | some (d, n) => d :: unescapeList (rest.drop n)
      | none => c :: unescapeList rest
    else c :: unescapeList rest
termination_by l => l.length
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- Decoder on strings: `unescape (escape s quote) = s`. -/
def unescape (s : String) : String :=
  ⟨unescapeList s.toList⟩

/-! ## Unit tests (the Python `check` function) -/

-- 1. quote = True (default)
example : escape "<b>\"&'</b>" = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by native_decide
example : escape "" = "" := by native_decide
-- 2. quote = False: `"` and `'` remain untouched
example : escape "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by native_decide
-- 3. order check
example : escape "&<" = "&amp;&lt;" := by native_decide
-- `benchmark_escape` is `escape`
example : benchmark_escape "<b>\"&'</b>" = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by native_decide
example : benchmark_escape "&<" true = "&amp;&lt;" := by native_decide
-- no double escaping: an already escaped text is escaped again only at its `&`
example : escape "&amp;" = "&amp;amp;" := by native_decide
-- replacing `&` last (the wrong order) would double-escape
example :
    (⟨replaceChar '&' "&amp;".toList (replaceChar '<' "&lt;".toList "<".toList)⟩ : String)
      = "&amp;lt;" := by native_decide
-- the decoder inverts the examples above
example : unescape "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" = "<b>\"&'</b>" := by native_decide
example : unescape (escape "&amp;") = "&amp;" := by native_decide

#eval escape "<b>\"&'</b>"
#eval escape "<b>\"&'</b>" false
#eval escape "&<"
#eval escape ""
#eval unescape (escape "<b>\"&'</b>")

/-! ## Pre-condition -/

/-- Python `pre_escape`: the input must be a `str`.  This is guaranteed by the type
`String`, so the precondition holds for every input. -/
def Pre (_s : String) (_quote : Bool) : Prop := True

/-! ## Basic lemmas -/

@[simp] theorem replaceChar_nil (t : Char) (r : List Char) : replaceChar t r [] = [] := rfl

@[simp] theorem replaceChar_cons (t : Char) (r : List Char) (c : Char) (cs : List Char) :
    replaceChar t r (c :: cs) = (if c = t then r else [c]) ++ replaceChar t r cs := rfl

theorem replaceChar_append (t : Char) (r : List Char) (l₁ l₂ : List Char) :
    replaceChar t r (l₁ ++ l₂) = replaceChar t r l₁ ++ replaceChar t r l₂ := by
  induction l₁ with
  | nil => simp
  | cons c cs ih => simp [ih]

theorem replaceChar_eq_flatMap (t : Char) (r : List Char) (l : List Char) :
    replaceChar t r l = l.flatMap (fun c => if c = t then r else [c]) := by
  induction l with
  | nil => simp
  | cons c cs ih => simp [ih]

/-- `replaceChar` does nothing on a list that does not contain the pattern. -/
theorem replaceChar_of_not_mem (t : Char) (r : List Char) (l : List Char) (h : t ∉ l) :
    replaceChar t r l = l := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.mem_cons, not_or] at h
    simp [Ne.symm h.1, ih h.2]

@[simp] theorem escapeList_nil (quote : Bool) : escapeList quote [] = [] := by
  cases quote <;> rfl

theorem escapeList_append (quote : Bool) (l₁ l₂ : List Char) :
    escapeList quote (l₁ ++ l₂) = escapeList quote l₁ ++ escapeList quote l₂ := by
  unfold escapeList
  cases quote <;> simp [replaceChar_append]

theorem escapeList_singleton (quote : Bool) (c : Char) :
    escapeList quote [c] = escapeChar quote c := by
  unfold escapeList escapeChar
  by_cases h1 : c = '&'
  · subst h1; cases quote <;> decide
  by_cases h2 : c = '<'
  · subst h2; cases quote <;> decide
  by_cases h3 : c = '>'
  · subst h3; cases quote <;> decide
  by_cases h4 : c = '"'
  · subst h4; cases quote <;> decide
  by_cases h5 : c = '\''
  · subst h5; cases quote <;> decide
  cases quote <;> simp [h1, h2, h3, h4, h5]

theorem escapeList_cons (quote : Bool) (c : Char) (cs : List Char) :
    escapeList quote (c :: cs) = escapeChar quote c ++ escapeList quote cs := by
  rw [← List.singleton_append, escapeList_append, escapeList_singleton]

theorem escapeList_eq_flatMap (quote : Bool) (l : List Char) :
    escapeList quote l = l.flatMap (escapeChar quote) := by
  induction l with
  | nil => simp
  | cons c cs ih => rw [escapeList_cons, ih, List.flatMap_cons]

theorem escape_toList (s : String) (quote : Bool) :
    (escape s quote).toList = escapeList quote s.toList := rfl


/-- Case analysis on the escape sequence of a character. -/
theorem escapeChar_cases {P : List Char → Prop} (quote : Bool) (c : Char)
    (hamp : c = '&' → P "&amp;".toList)
    (hlt : c = '<' → P "&lt;".toList)
    (hgt : c = '>' → P "&gt;".toList)
    (hquot : quote = true → c = '"' → P "&quot;".toList)
    (hapos : quote = true → c = '\'' → P "&#x27;".toList)
    (hother : isSpecial quote c = false → P [c]) :
    P (escapeChar quote c) := by
  unfold escapeChar
  split_ifs with h1 h2 h3 h4 h5
  · exact hamp h1
  · exact hlt h2
  · exact hgt h3
  · exact hquot h4.1 h4.2
  · exact hapos h5.1 h5.2
  · apply hother
    cases quote <;> simp_all [isSpecial]

theorem escapeChar_of_not_special (quote : Bool) (c : Char) (h : isSpecial quote c = false) :
    escapeChar quote c = [c] := by
  refine escapeChar_cases quote c (P := fun L => L = [c]) ?_ ?_ ?_ ?_ ?_ ?_
  · rintro rfl; simp [isSpecial] at h
  · rintro rfl; simp [isSpecial] at h
  · rintro rfl; simp [isSpecial] at h
  · rintro rfl rfl; simp [isSpecial] at h
  · rintro rfl rfl; simp [isSpecial] at h
  · intro _; rfl

theorem escapeChar_safe (quote : Bool) (c : Char) :
    ∀ d ∈ escapeChar quote c, d ≠ '<' ∧ d ≠ '>' ∧ (quote = true → d ≠ '"' ∧ d ≠ '\'') := by
  refine escapeChar_cases quote c
    (P := fun L => ∀ d ∈ L, d ≠ '<' ∧ d ≠ '>' ∧ (quote = true → d ≠ '"' ∧ d ≠ '\'')) ?_ ?_ ?_ ?_ ?_ ?_
  · intro _; cases quote <;> decide
  · intro _; cases quote <;> decide
  · intro _; cases quote <;> decide
  · rintro rfl _; decide
  · rintro rfl _; decide
  · intro h d hd
    simp only [List.mem_singleton] at hd
    subst hd
    cases quote <;> simp_all [isSpecial]

theorem escapeChar_count_amp (quote : Bool) (c : Char) :
    (escapeChar quote c).count '&' = if isSpecial quote c then 1 else 0 := by
  refine escapeChar_cases quote c
    (P := fun L => L.count '&' = if isSpecial quote c then 1 else 0) ?_ ?_ ?_ ?_ ?_ ?_
  · rintro rfl; cases quote <;> decide
  · rintro rfl; cases quote <;> decide
  · rintro rfl; cases quote <;> decide
  · rintro rfl rfl; decide
  · rintro rfl rfl; decide
  · intro h
    have h' : c ≠ '&' := by
      rintro rfl; simp [isSpecial] at h
    simp [h, h']

theorem escapeChar_length (quote : Bool) (c : Char) :
    (escapeChar quote c).length =
      1 + (if c = '&' then 4 else 0) + (if c = '<' then 3 else 0) + (if c = '>' then 3 else 0)
        + (if quote ∧ c = '"' then 5 else 0) + (if quote ∧ c = '\'' then 5 else 0) := by
  unfold escapeChar
  by_cases h1 : c = '&'
  · subst h1; cases quote <;> decide
  by_cases h2 : c = '<'
  · subst h2; cases quote <;> decide
  by_cases h3 : c = '>'
  · subst h3; cases quote <;> decide
  by_cases h4 : c = '"'
  · subst h4; cases quote <;> decide
  by_cases h5 : c = '\''
  · subst h5; cases quote <;> decide
  simp [h1, h2, h3, h4, h5]

theorem escapeChar_false_count_quot (c : Char) :
    (escapeChar false c).count '"' = [c].count '"' := by
  refine escapeChar_cases false c (P := fun L => L.count '"' = [c].count '"') ?_ ?_ ?_ ?_ ?_ ?_
  · rintro rfl; decide
  · rintro rfl; decide
  · rintro rfl; decide
  · intro h; exact absurd h Bool.false_ne_true
  · intro h; exact absurd h Bool.false_ne_true
  · intro _; rfl

theorem escapeChar_false_count_apos (c : Char) :
    (escapeChar false c).count '\'' = [c].count '\'' := by
  refine escapeChar_cases false c (P := fun L => L.count '\'' = [c].count '\'') ?_ ?_ ?_ ?_ ?_ ?_
  · rintro rfl; decide
  · rintro rfl; decide
  · rintro rfl; decide
  · intro h; exact absurd h Bool.false_ne_true
  · intro h; exact absurd h Bool.false_ne_true
  · intro _; rfl

/-! ### Lemmas about the whole list -/

theorem escapeList_safe (quote : Bool) (l : List Char) :
    ∀ d ∈ escapeList quote l, d ≠ '<' ∧ d ≠ '>' ∧ (quote = true → d ≠ '"' ∧ d ≠ '\'') := by
  induction l with
  | nil => simp
  | cons c cs ih =>
    rw [escapeList_cons]
    intro d hd
    rcases List.mem_append.1 hd with h | h
    · exact escapeChar_safe quote c d h
    · exact ih d h

theorem escapeList_count_amp (quote : Bool) (l : List Char) :
    (escapeList quote l).count '&' = l.countP (isSpecial quote) := by
  induction l with
  | nil => simp
  | cons c cs ih =>
    rw [escapeList_cons, List.count_append, escapeChar_count_amp, ih, List.countP_cons]
    omega

theorem escapeList_length (quote : Bool) (l : List Char) :
    (escapeList quote l).length =
      l.length + 4 * l.count '&' + 3 * l.count '<' + 3 * l.count '>'
        + (if quote then 5 * (l.count '"' + l.count '\'') else 0) := by
  induction l with
  | nil => simp
  | cons c cs ih =>
    rw [escapeList_cons, List.length_append, escapeChar_length, ih]
    simp only [List.length_cons, List.count_cons, beq_iff_eq]
    cases quote
    · simp only [Bool.false_eq_true, false_and, if_false]
      split_ifs <;> omega
    · simp only [true_and, if_true]
      split_ifs <;> omega

theorem escapeList_of_not_special (quote : Bool) (l : List Char)
    (h : ∀ c ∈ l, isSpecial quote c = false) : escapeList quote l = l := by
  induction l with
  | nil => simp
  | cons c cs ih =>
    rw [escapeList_cons, escapeChar_of_not_special quote c (h c (by simp)),
      ih (fun d hd => h d (by simp [hd]))]
    rfl

theorem escapeList_length_ge (quote : Bool) (l : List Char) :
    l.length ≤ (escapeList quote l).length := by
  rw [escapeList_length]
  omega

theorem escapeList_eq_self_iff (quote : Bool) (l : List Char) :
    escapeList quote l = l ↔ ∀ c ∈ l, isSpecial quote c = false := by
  refine ⟨fun h c hc => ?_, escapeList_of_not_special quote l⟩
  have hlen := escapeList_length quote l
  rw [h] at hlen
  have h1 : l.count '&' = 0 := by omega
  have h2 : l.count '<' = 0 := by omega
  have h3 : l.count '>' = 0 := by omega
  rw [List.count_eq_zero] at h1 h2 h3
  have hc1 : c ≠ '&' := fun e => h1 (e ▸ hc)
  have hc2 : c ≠ '<' := fun e => h2 (e ▸ hc)
  have hc3 : c ≠ '>' := fun e => h3 (e ▸ hc)
  cases quote with
  | false => simp [isSpecial, hc1, hc2, hc3]
  | true =>
    have h4 : l.count '"' = 0 := by simp at hlen; omega
    have h5 : l.count '\'' = 0 := by simp at hlen; omega
    rw [List.count_eq_zero] at h4 h5
    have hc4 : c ≠ '"' := fun e => h4 (e ▸ hc)
    have hc5 : c ≠ '\'' := fun e => h5 (e ▸ hc)
    simp [isSpecial, hc1, hc2, hc3, hc4, hc5]

theorem escapeList_true (l : List Char) :
    escapeList true l =
      replaceChar '\'' "&#x27;".toList (replaceChar '"' "&quot;".toList (escapeList false l)) := rfl

theorem escapeList_false_count_quot (l : List Char) :
    (escapeList false l).count '"' = l.count '"' := by
  induction l with
  | nil => simp
  | cons c cs ih =>
    rw [escapeList_cons, List.count_append, escapeChar_false_count_quot, ih, ← List.count_append,
      List.singleton_append]

theorem escapeList_false_count_apos (l : List Char) :
    (escapeList false l).count '\'' = l.count '\'' := by
  induction l with
  | nil => simp
  | cons c cs ih =>
    rw [escapeList_cons, List.count_append, escapeChar_false_count_apos, ih, ← List.count_append,
      List.singleton_append]

/-! ### The decoder inverts `escapeList` -/

theorem unescapeList_nil : unescapeList [] = [] := by
  rw [unescapeList]

theorem unescapeList_cons_of_ne (c : Char) (h : c ≠ '&') (rest : List Char) :
    unescapeList (c :: rest) = c :: unescapeList rest := by
  rw [unescapeList, if_neg h]

theorem unescapeList_amp (X : List Char) :
    unescapeList ("&amp;".toList ++ X) = '&' :: unescapeList X := by
  rw [show "&amp;".toList ++ X = '&' :: 'a' :: 'm' :: 'p' :: ';' :: X from rfl, unescapeList, if_pos rfl]
  rfl

theorem unescapeList_lt (X : List Char) :
    unescapeList ("&lt;".toList ++ X) = '<' :: unescapeList X := by
  rw [show "&lt;".toList ++ X = '&' :: 'l' :: 't' :: ';' :: X from rfl, unescapeList, if_pos rfl]
  rfl

theorem unescapeList_gt (X : List Char) :
    unescapeList ("&gt;".toList ++ X) = '>' :: unescapeList X := by
  rw [show "&gt;".toList ++ X = '&' :: 'g' :: 't' :: ';' :: X from rfl, unescapeList, if_pos rfl]
  rfl

theorem unescapeList_quot (X : List Char) :
    unescapeList ("&quot;".toList ++ X) = '"' :: unescapeList X := by
  rw [show "&quot;".toList ++ X = '&' :: 'q' :: 'u' :: 'o' :: 't' :: ';' :: X from rfl, unescapeList,
    if_pos rfl]
  rfl

theorem unescapeList_apos (X : List Char) :
    unescapeList ("&#x27;".toList ++ X) = '\'' :: unescapeList X := by
  rw [show "&#x27;".toList ++ X = '&' :: '#' :: 'x' :: '2' :: '7' :: ';' :: X from rfl, unescapeList,
    if_pos rfl]
  rfl

theorem unescapeList_escapeList (quote : Bool) (l : List Char) :
    unescapeList (escapeList quote l) = l := by
  induction l with
  | nil => rw [escapeList_nil, unescapeList_nil]
  | cons c cs ih =>
    rw [escapeList_cons]
    refine escapeChar_cases quote c
      (P := fun L => unescapeList (L ++ escapeList quote cs) = c :: cs) ?_ ?_ ?_ ?_ ?_ ?_
    · rintro rfl; show unescapeList _ = _; rw [unescapeList_amp, ih]
    · rintro rfl; show unescapeList _ = _; rw [unescapeList_lt, ih]
    · rintro rfl; show unescapeList _ = _; rw [unescapeList_gt, ih]
    · rintro rfl rfl; show unescapeList _ = _; rw [unescapeList_quot, ih]
    · rintro rfl rfl; show unescapeList _ = _; rw [unescapeList_apos, ih]
    · intro h
      have hc : c ≠ '&' := by
        rintro rfl; simp [isSpecial] at h
      show unescapeList _ = _
      rw [List.singleton_append, unescapeList_cons_of_ne c hc, ih]

theorem escapeList_injective (quote : Bool) {l₁ l₂ : List Char}
    (h : escapeList quote l₁ = escapeList quote l₂) : l₁ = l₂ := by
  have := congrArg unescapeList h
  rwa [unescapeList_escapeList, unescapeList_escapeList] at this


/-! ## Properties of `escape` (on strings) -/

/-- Escaping the empty string gives the empty string. -/
def escape_empty_prop : Prop := ∀ quote : Bool, escape "" quote = ""

theorem escape_empty_thm : escape_empty_prop := by
  intro quote
  apply String.ext
  exact escapeList_nil quote

/-- `escape` is a homomorphism for concatenation. -/
def escape_append_prop : Prop :=
  ∀ (s t : String) (quote : Bool), escape (s ++ t) quote = escape s quote ++ escape t quote

theorem escape_append_thm : escape_append_prop := by
  intro s t quote
  apply String.ext
  show escapeList quote (s ++ t).data = (escape s quote ++ escape t quote).data
  rw [String.data_append, String.data_append, escapeList_append]
  rfl

/-- Single pass: although the Python program performs five successive `replace` calls, the
`&` of an inserted entity is never re-escaped (because `&` is replaced first), and no inserted
character is touched by a later replacement.  The result is simply every character of the
input replaced by its escape sequence. -/
def escape_single_pass_prop : Prop :=
  ∀ (s : String) (quote : Bool), (escape s quote).toList = s.toList.flatMap (escapeChar quote)

theorem escape_single_pass_thm : escape_single_pass_prop := by
  intro s quote
  exact escapeList_eq_flatMap quote s.toList

/-- HTML safety: the result never contains `<` or `>`, and when `quote` is set it contains
neither `"` nor `'`. -/
def escape_safe_prop : Prop :=
  ∀ (s : String) (quote : Bool), ∀ c ∈ (escape s quote).toList,
    c ≠ '<' ∧ c ≠ '>' ∧ (quote = true → c ≠ '"' ∧ c ≠ '\'')

theorem escape_safe_thm : escape_safe_prop := by
  intro s quote
  exact escapeList_safe quote s.toList

/-- Every `&` of the result is the start of an entity produced for one special character of
the input: the number of `&` in the result equals the number of special characters of `s`. -/
def escape_amp_count_prop : Prop :=
  ∀ (s : String) (quote : Bool),
    (escape s quote).toList.count '&' = s.toList.countP (isSpecial quote)

theorem escape_amp_count_thm : escape_amp_count_prop := by
  intro s quote
  exact escapeList_count_amp quote s.toList

/-- Lossless: decoding the five entities gives the input back. -/
def unescape_escape_prop : Prop := ∀ (s : String) (quote : Bool), unescape (escape s quote) = s

theorem unescape_escape_thm : unescape_escape_prop := by
  intro s quote
  apply String.ext
  exact unescapeList_escapeList quote s.toList

/-- `escape` is injective (different inputs have different escaped forms). -/
def escape_injective_prop : Prop :=
  ∀ quote : Bool, Function.Injective (fun s : String => escape s quote)

theorem escape_injective_thm : escape_injective_prop := by
  intro quote s t h
  apply String.ext
  exact escapeList_injective quote (congrArg String.data h)

/-- Exact length of the result: `&` grows by 4, `<` and `>` by 3, and when `quote` is set
`"` and `'` grow by 5. -/
def escape_length_prop : Prop :=
  ∀ (s : String) (quote : Bool),
    (escape s quote).length =
      s.length + 4 * s.toList.count '&' + 3 * s.toList.count '<' + 3 * s.toList.count '>'
        + (if quote then 5 * (s.toList.count '"' + s.toList.count '\'') else 0)

theorem escape_length_thm : escape_length_prop := by
  intro s quote
  exact escapeList_length quote s.toList

/-- Escaping never shortens a string. -/
def escape_length_ge_prop : Prop := ∀ (s : String) (quote : Bool), s.length ≤ (escape s quote).length

theorem escape_length_ge_thm : escape_length_ge_prop := by
  intro s quote
  exact escapeList_length_ge quote s.toList

/-- `escape` leaves `s` unchanged exactly when `s` contains no special character. -/
def escape_fixed_iff_prop : Prop :=
  ∀ (s : String) (quote : Bool), escape s quote = s ↔ ∀ c ∈ s.toList, isSpecial quote c = false

theorem escape_fixed_iff_thm : escape_fixed_iff_prop := by
  intro s quote
  rw [← escapeList_eq_self_iff quote s.toList, String.ext_iff]
  rfl

/-- `quote = true` is `quote = false` followed by the two quotation-mark replacements. -/
def escape_quote_prop : Prop :=
  ∀ s : String, escape s true =
    ⟨replaceChar '\'' "&#x27;".toList (replaceChar '"' "&quot;".toList (escape s false).toList)⟩

theorem escape_quote_thm : escape_quote_prop := by
  intro s
  rfl

/-- With `quote = false` the quotation marks are left untouched. -/
def escape_noquote_prop : Prop :=
  ∀ s : String, (escape s false).toList.count '"' = s.toList.count '"' ∧
    (escape s false).toList.count '\'' = s.toList.count '\''

theorem escape_noquote_thm : escape_noquote_prop := by
  intro s
  exact ⟨escapeList_false_count_quot s.toList, escapeList_false_count_apos s.toList⟩

/-- `benchmark_escape` is `escape` (the type check always succeeds on a `String`). -/
def benchmark_escape_prop : Prop := ∀ (s : String) (quote : Bool), benchmark_escape s quote = escape s quote

theorem benchmark_escape_thm : benchmark_escape_prop := by
  intro s quote
  rfl

/-! ## Post-condition -/

/-- Post-condition for `r = escape s quote`. -/
def Post_prop (s : String) (quote : Bool) (r : String) : Prop :=
  r.toList = s.toList.flatMap (escapeChar quote) ∧
  (∀ c ∈ r.toList, c ≠ '<' ∧ c ≠ '>' ∧ (quote = true → c ≠ '"' ∧ c ≠ '\'')) ∧
  r.toList.count '&' = s.toList.countP (isSpecial quote) ∧
  unescape r = s ∧
  r.length = s.length + 4 * s.toList.count '&' + 3 * s.toList.count '<' + 3 * s.toList.count '>'
    + (if quote then 5 * (s.toList.count '"' + s.toList.count '\'') else 0) ∧
  (r = s ↔ ∀ c ∈ s.toList, isSpecial quote c = false) ∧
  (quote = false → r.toList.count '"' = s.toList.count '"' ∧ r.toList.count '\'' = s.toList.count '\'')

/-! ## Property-based tests -/

/-- Executable form of `Post_prop`. -/
def postCheck (s : String) (quote : Bool) (r : String) : Bool :=
  (r.toList == s.toList.flatMap (escapeChar quote)) &&
  r.toList.all (fun c => c != '<' && c != '>' && (!quote || (c != '"' && c != '\''))) &&
  (r.toList.count '&' == s.toList.countP (isSpecial quote)) &&
  (unescape r == s) &&
  (r.length == s.length + 4 * s.toList.count '&' + 3 * s.toList.count '<' + 3 * s.toList.count '>'
    + (if quote then 5 * (s.toList.count '"' + s.toList.count '\'') else 0)) &&
  ((r == s) == s.toList.all (fun c => !isSpecial quote c)) &&
  (quote || (r.toList.count '"' == s.toList.count '"' && r.toList.count '\'' == s.toList.count '\''))

/-- Python's `escape` transcribed with Lean's own `String.replace`; used only as a test oracle
for the hand-rolled `replaceChar`. -/
def escapeOracle (s : String) (quote : Bool := true) : String :=
  let s := s.replace "&" "&amp;"
  let s := s.replace "<" "&lt;"
  let s := s.replace ">" "&gt;"
  if quote then (s.replace "\"" "&quot;").replace "'" "&#x27;" else s

/-- Test alphabet: the five special characters and the characters occurring in the entities. -/
def testAlphabet : List Char :=
  ['&', '<', '>', '"', '\'', 'a', 'm', 'p', ';', 'l', 't', 'g', 'q', 'u', 'o', '#', 'x', '2', '7', 'b', ' ']

/-- Strings over `testAlphabet`, for random testing with `Plausible`. -/
def ofIdx (l : List (Fin 21)) : String := ⟨l.map fun i => testAlphabet.getD i.val ' '⟩

/-- All words of length `n` over `alphabet`. -/
def words (alphabet : List Char) : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 => (words alphabet n).flatMap fun w => alphabet.map fun c => c :: w

/-- All strings of length `< 5` over the special characters, `a` and `;` (2801 strings). -/
def smallWords : List String :=
  ((List.range 5).flatMap (words ['&', '<', '>', '"', '\'', 'a', ';'])).map String.mk

example : smallWords.length = 2801 := by native_decide

-- escape_empty_prop
example : [true, false].all (fun q => escape "" q == "") = true := by native_decide
-- escape_append_prop
#eval Plausible.Testable.check
  (∀ (s t : String) (q : Bool), escape (s ++ t) q = escape s q ++ escape t q)
#eval Plausible.Testable.check
  (∀ (l m : List (Fin 21)) (q : Bool), escape (ofIdx l ++ ofIdx m) q = escape (ofIdx l) q ++ escape (ofIdx m) q)
example : smallWords.all (fun s => smallWords.take 60 |>.all fun t => [true, false].all fun q =>
    escape (s ++ t) q == escape s q ++ escape t q) = true := by native_decide
-- escape_single_pass_prop
#eval Plausible.Testable.check
  (∀ (s : String) (q : Bool), (escape s q).toList = s.toList.flatMap (escapeChar q))
#eval Plausible.Testable.check
  (∀ (l : List (Fin 21)) (q : Bool), (escape (ofIdx l) q).toList = (ofIdx l).toList.flatMap (escapeChar q))
example : smallWords.all (fun s => [true, false].all fun q =>
    (escape s q).toList == s.toList.flatMap (escapeChar q)) = true := by native_decide
-- escape_safe_prop
#eval Plausible.Testable.check
  (∀ (l : List (Fin 21)) (q : Bool), (escape (ofIdx l) q).toList.all
    (fun c => c != '<' && c != '>' && (!q || (c != '"' && c != '\''))) = true)
example : smallWords.all (fun s => [true, false].all fun q => (escape s q).toList.all
    (fun c => c != '<' && c != '>' && (!q || (c != '"' && c != '\'')))) = true := by native_decide
-- escape_amp_count_prop
#eval Plausible.Testable.check
  (∀ (l : List (Fin 21)) (q : Bool), (escape (ofIdx l) q).toList.count '&' = (ofIdx l).toList.countP (isSpecial q))
example : smallWords.all (fun s => [true, false].all fun q =>
    (escape s q).toList.count '&' == s.toList.countP (isSpecial q)) = true := by native_decide
-- unescape_escape_prop
#eval Plausible.Testable.check (∀ (s : String) (q : Bool), unescape (escape s q) = s)
#eval Plausible.Testable.check (∀ (l : List (Fin 21)) (q : Bool), unescape (escape (ofIdx l) q) = ofIdx l)
example : smallWords.all (fun s => [true, false].all fun q => unescape (escape s q) == s) = true := by
  native_decide
-- escape_injective_prop
#eval Plausible.Testable.check
  (∀ (l m : List (Fin 21)) (q : Bool), escape (ofIdx l) q = escape (ofIdx m) q → ofIdx l = ofIdx m)
example : smallWords.all (fun s => smallWords.all fun t => [true, false].all fun q =>
    (escape s q == escape t q) == (s == t)) = true := by native_decide
-- escape_length_prop
#eval Plausible.Testable.check
  (∀ (l : List (Fin 21)) (q : Bool), (escape (ofIdx l) q).length =
    (ofIdx l).length + 4 * (ofIdx l).toList.count '&' + 3 * (ofIdx l).toList.count '<'
      + 3 * (ofIdx l).toList.count '>'
      + (if q then 5 * ((ofIdx l).toList.count '"' + (ofIdx l).toList.count '\'') else 0))
example : smallWords.all (fun s => [true, false].all fun q => (escape s q).length ==
    s.length + 4 * s.toList.count '&' + 3 * s.toList.count '<' + 3 * s.toList.count '>'
      + (if q then 5 * (s.toList.count '"' + s.toList.count '\'') else 0)) = true := by native_decide
-- escape_length_ge_prop
#eval Plausible.Testable.check (∀ (s : String) (q : Bool), s.length ≤ (escape s q).length)
example : smallWords.all (fun s => [true, false].all fun q => decide (s.length ≤ (escape s q).length)) = true := by
  native_decide
-- escape_fixed_iff_prop
#eval Plausible.Testable.check
  (∀ (l : List (Fin 21)) (q : Bool), (escape (ofIdx l) q == ofIdx l) = (ofIdx l).toList.all (fun c => !isSpecial q c))
example : smallWords.all (fun s => [true, false].all fun q =>
    (escape s q == s) == s.toList.all (fun c => !isSpecial q c)) = true := by native_decide
-- escape_quote_prop
#eval Plausible.Testable.check (∀ (l : List (Fin 21)), escape (ofIdx l) true =
  ⟨replaceChar '\'' "&#x27;".toList (replaceChar '"' "&quot;".toList (escape (ofIdx l) false).toList)⟩)
example : smallWords.all (fun s => escape s true ==
    ⟨replaceChar '\'' "&#x27;".toList (replaceChar '"' "&quot;".toList (escape s false).toList)⟩) = true := by
  native_decide
-- escape_noquote_prop
#eval Plausible.Testable.check (∀ (l : List (Fin 21)),
  (escape (ofIdx l) false).toList.count '"' = (ofIdx l).toList.count '"' ∧
  (escape (ofIdx l) false).toList.count '\'' = (ofIdx l).toList.count '\'')
example : smallWords.all (fun s => (escape s false).toList.count '"' == s.toList.count '"' &&
    (escape s false).toList.count '\'' == s.toList.count '\'') = true := by native_decide
-- benchmark_escape_prop
#eval Plausible.Testable.check (∀ (s : String) (q : Bool), benchmark_escape s q = escape s q)
-- Post_prop (executable form `postCheck`)
#eval Plausible.Testable.check (∀ (s : String) (q : Bool), postCheck s q (escape s q) = true)
#eval Plausible.Testable.check (∀ (l : List (Fin 21)) (q : Bool), postCheck (ofIdx l) q (escape (ofIdx l) q) = true)
example : smallWords.all (fun s => [true, false].all fun q => postCheck s q (escape s q)) = true := by
  native_decide
-- Agreement with Lean's built-in `String.replace` (evidence that `replaceChar` is `str.replace`).
#eval Plausible.Testable.check (∀ (s : String) (q : Bool), escape s q = escapeOracle s q)
#eval Plausible.Testable.check (∀ (l : List (Fin 21)) (q : Bool), escape (ofIdx l) q = escapeOracle (ofIdx l) q)
example : smallWords.all (fun s => [true, false].all fun q => escape s q == escapeOracle s q) = true := by
  native_decide

/-! ## Correctness: `Pre → Post` -/

theorem correctness (s : String) (quote : Bool) (_h : Pre s quote) : Post_prop s quote (escape s quote) :=
  ⟨escape_single_pass_thm s quote, escape_safe_thm s quote, escape_amp_count_thm s quote,
    unescape_escape_thm s quote, escape_length_thm s quote, escape_fixed_iff_thm s quote,
    fun hq => hq ▸ escape_noquote_thm s⟩

/-! ## Imperative implementation -/

/-- Python `s.replace(t, r)` for a one-character pattern `t`, written as a loop that appends
to a mutable buffer. -/
def replaceCharImp (t : Char) (r : String) (s : String) : String := Id.run do
  let mut out : String := ""
  for c in s.toList do
    if c = t then
      out := out ++ r
    else
      out := out.push c
  return out

/-- Imperative transcription of Python's `escape`: the variable `s` is reassigned five times. -/
def escapeImp (s : String) (quote : Bool := true) : String := Id.run do
  let mut r := s
  r := replaceCharImp '&' "&amp;" r
  r := replaceCharImp '<' "&lt;" r
  r := replaceCharImp '>' "&gt;" r
  if quote then
    r := replaceCharImp '"' "&quot;" r
    r := replaceCharImp '\'' "&#x27;" r
  return r

/-- A second imperative version: a single pass over the input, appending each character's
escape sequence to a mutable buffer. -/
def escapeLoop (s : String) (quote : Bool := true) : String := Id.run do
  let mut out : String := ""
  for c in s.toList do
    out := out ++ ⟨escapeChar quote c⟩
  return out

/-! ### Imperative tests -/

example : escapeImp "<b>\"&'</b>" = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by native_decide
example : escapeImp "" = "" := by native_decide
example : escapeImp "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by native_decide
example : escapeImp "&<" = "&amp;&lt;" := by native_decide
example : escapeLoop "<b>\"&'</b>" = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by native_decide
example : escapeLoop "" = "" := by native_decide
example : escapeLoop "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by native_decide
example : escapeLoop "&<" = "&amp;&lt;" := by native_decide
example : replaceCharImp 'a' "xyz" "banana" = "bxyznxyznxyz" := by native_decide

#eval escapeImp "<b>\"&'</b>"
#eval escapeImp "<b>\"&'</b>" false
#eval escapeLoop "<b>\"&'</b>"

#eval Plausible.Testable.check (∀ (s : String) (q : Bool), escapeImp s q = escape s q)
#eval Plausible.Testable.check (∀ (l : List (Fin 21)) (q : Bool), escapeImp (ofIdx l) q = escape (ofIdx l) q)
#eval Plausible.Testable.check (∀ (l : List (Fin 21)) (q : Bool), escapeLoop (ofIdx l) q = escape (ofIdx l) q)
example : smallWords.all (fun s => [true, false].all fun q =>
    escapeImp s q == escape s q && escapeLoop s q == escape s q) = true := by native_decide

/-! ### Equivalence: functional = imperative -/

theorem replaceCharImp_loop (t : Char) (r : String) (l : List Char) (acc : String) :
    (forIn (m := Id) l acc (fun c out =>
        if c = t then (pure (ForInStep.yield (out ++ r)) : Id (ForInStep String))
        else pure (ForInStep.yield (out.push c)))) = acc ++ (⟨replaceChar t r.toList l⟩ : String) := by
  induction l generalizing acc with
  | nil =>
    simp only [List.forIn_nil, replaceChar]
    exact (String.append_empty acc).symm
  | cons c cs ih =>
    rw [List.forIn_cons]
    by_cases h : c = t
    · simp only [if_pos h, pure_bind, ih]
      apply String.ext
      simp [String.data_append, replaceChar, h]
    · simp only [if_neg h, pure_bind, ih]
      apply String.ext
      simp [String.data_append, String.data_push, replaceChar, h]

theorem replaceCharImp_eq (t : Char) (r : String) (s : String) :
    replaceCharImp t r s = ⟨replaceChar t r.toList s.toList⟩ := by
  show (forIn (m := Id) s.toList "" (fun c out =>
        if c = t then (pure (ForInStep.yield (out ++ r)) : Id (ForInStep String))
        else pure (ForInStep.yield (out.push c)))) = _
  rw [replaceCharImp_loop]
  exact String.empty_append _

/-- The imperative transcription computes `escape`. -/
theorem escapeImp_eq_escape (s : String) (quote : Bool) : escapeImp s quote = escape s quote := by
  cases quote
  · show replaceCharImp '>' "&gt;" (replaceCharImp '<' "&lt;" (replaceCharImp '&' "&amp;" s)) = _
    simp only [replaceCharImp_eq]
    rfl
  · show replaceCharImp '\'' "&#x27;" (replaceCharImp '"' "&quot;"
      (replaceCharImp '>' "&gt;" (replaceCharImp '<' "&lt;" (replaceCharImp '&' "&amp;" s)))) = _
    simp only [replaceCharImp_eq]
    rfl

theorem escapeLoop_loop (quote : Bool) (l : List Char) (acc : String) :
    (forIn (m := Id) l acc (fun c out =>
        (pure (ForInStep.yield (out ++ ⟨escapeChar quote c⟩)) : Id (ForInStep String)))) =
      acc ++ (⟨escapeList quote l⟩ : String) := by
  induction l generalizing acc with
  | nil =>
    simp only [List.forIn_nil, escapeList_nil]
    exact (String.append_empty acc).symm
  | cons c cs ih =>
    rw [List.forIn_cons]
    simp only [pure_bind, ih]
    apply String.ext
    simp [String.data_append, escapeList_cons]

/-- The single-pass imperative version computes `escape` as well. -/
theorem escapeLoop_eq_escape (s : String) (quote : Bool) : escapeLoop s quote = escape s quote := by
  show (forIn (m := Id) s.toList "" (fun c out =>
        (pure (ForInStep.yield (out ++ ⟨escapeChar quote c⟩)) : Id (ForInStep String)))) = _
  rw [escapeLoop_loop]
  exact String.empty_append _

/-- Both imperative versions agree. -/
theorem escapeImp_eq_escapeLoop (s : String) (quote : Bool) : escapeImp s quote = escapeLoop s quote := by
  rw [escapeImp_eq_escape, escapeLoop_eq_escape]

end «20_html_escape»
