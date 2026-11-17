import Mathlib

/-!
# HTML-Safe String Escaping (`20_html_escape`)

Lean 4 formalization of Python's `html.escape(s, quote=True)` function.

Given an input string `s` and an optional boolean flag `quote` (defaulting to `true`),
`escape` replaces the special HTML characters `'&'`, `'<'`, and `'>'` with their
corresponding HTML-safe entity sequences `"&amp;"`, `"&lt;"`, and `"&gt;"`.
When `quote` is `true`, double quotes (`'"'`) and single quotes (`'\''`) are also
translated to `"&quot;"` and `"&#x27;"` respectively.

Crucially, `'&'` is replaced first so that the ampersands introduced by subsequent
replacements are never double-escaped. We formalize both the sequential 5-step
replacement implementation from Python and the single-pass/imperative implementations,
and prove their exact equivalence and comprehensive safety/structural properties.
-/

namespace «20_html_escape»

/-! ## 4. Implementation (Functional Definition) -/

/-- Pre-condition check corresponding to Python's `pre_escape(s)`. -/
def pre_escape (_s : String) : Bool := true

/-- Replace every occurrence of character `target` in `s` with `replacement`. -/
def replaceChar (s : String) (target : Char) (replacement : String) : String :=
  String.mk (s.data.flatMap (fun c => if c == target then replacement.data else [c]))

/--
Replace special characters `"&"`, `"<"` and `">"` with HTML-safe sequences.
If the optional flag `quote` is `true` (the default), both double quote (`"\""`)
and single quote (`"'"`) characters are also translated.
Order matters: `"&"` is replaced first to avoid double-escaping.
-/
def escape (s : String) (quote : Bool := true) : String :=
  let s := replaceChar s '&' "&amp;"
  let s := replaceChar s '<' "&lt;"
  let s := replaceChar s '>' "&gt;"
  if quote then
    let s := replaceChar s '"' "&quot;"
    replaceChar s '\'' "&#x27;"
  else
    s

/-- Main entry point matching Python's `benchmark_escape(s, quote=True)`. -/
def benchmark_escape (s : String) (quote : Bool := true) : String :=
  escape s quote

/-- Single-character HTML escape sequence as a `List Char`. -/
def escapeChar (c : Char) (quote : Bool := true) : List Char :=
  if c == '&' then "&amp;".data
  else if c == '<' then "&lt;".data
  else if c == '>' then "&gt;".data
  else if quote && c == '"' then "&quot;".data
  else if quote && c == '\'' then "&#x27;".data
  else [c]

/-- Predicate identifying whether a character `c` is escaped under flag `quote`. -/
def isSpecialChar (c : Char) (quote : Bool := true) : Bool :=
  c == '&' || c == '<' || c == '>' || (quote && (c == '"' || c == '\''))

/-- Executable test suite matching Python's `check` function. -/
def check (escape_candidate : String → Bool → String) : Bool :=
  escape_candidate "<b>\"&'</b>" true == "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" &&
  escape_candidate "" true == "" &&
  escape_candidate "<b>\"&'</b>" false == "&lt;b&gt;\"&amp;'&lt;/b&gt;" &&
  escape_candidate "&<" true == "&amp;&lt;"

/-! ## 5. Unit Tests -/

-- 1. Quote=True (Default)
example : escape "<b>\"&'</b>" = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by native_decide
example : escape "" = "" := by native_decide

-- 2. Quote=False (" and ' remain untouched)
example : escape "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by native_decide
example : escape "" false = "" := by native_decide

-- 3. Order check (& must be first to avoid double-escaping)
example : escape "&<" = "&amp;&lt;" := by native_decide
example : escape "&lt;" = "&amp;lt;" := by native_decide
example : escape "<>\"'&" true = "&lt;&gt;&quot;&#x27;&amp;" := by native_decide
example : escape "<>\"'&" false = "&lt;&gt;\"'&amp;" := by native_decide
example : escape "hello world" true = "hello world" := by native_decide

-- 4. Full benchmark check suite
example : check (fun s q => benchmark_escape s q) = true := by native_decide

#eval escape "<b>\"&'</b>"
#eval escape ""
#eval escape "<b>\"&'</b>" false
#eval escape "&<"
#eval check (fun s q => benchmark_escape s q)

/-! ## 6. Pre-condition Predicate -/

/-- Pre-condition for `escape`: holds for all valid `String` and `Bool` inputs. -/
def Pre (s : String) (_quote : Bool := true) : Prop :=
  pre_escape s = true

/-! ## 7. Property Propositions and Theorems -/

/-! ### Helper Lemmas on `String` and `escapeChar` -/

@[simp]
lemma string_length_eq_data_length (s : String) : s.length = s.data.length := by
  cases s; rfl

@[simp]
lemma escape_data (s : String) (quote : Bool) :
    (escape s quote).data = s.data.flatMap (fun c => escapeChar c quote) := by
  cases quote
  · simp only [escape, replaceChar, Bool.false_eq_true, ↓reduceIte, List.flatMap_assoc]
    congr 1; funext c
    by_cases h1 : c = '&' <;> simp [h1, escapeChar]
    by_cases h2 : c = '<' <;> simp [h2]
  · simp only [escape, replaceChar, ↓reduceIte, List.flatMap_assoc]
    congr 1; funext c
    by_cases h1 : c = '&' <;> simp [h1, escapeChar]
    by_cases h2 : c = '<' <;> simp [h2]
    by_cases h3 : c = '>' <;> simp [h3]
    by_cases h4 : c = '"' <;> simp [h4]

lemma escapeChar_ne_nil (c : Char) (quote : Bool) : escapeChar c quote ≠ [] := by
  unfold escapeChar
  by_cases h1 : c = '&' <;> simp [h1]
  by_cases h2 : c = '<' <;> simp [h2]
  by_cases h3 : c = '>' <;> simp [h3]
  cases quote <;> simp
  by_cases h4 : c = '"' <;> simp [h4]
  by_cases h5 : c = '\'' <;> simp [h5]

lemma escapeChar_length (c : Char) (quote : Bool) :
    (escapeChar c quote).length =
      1 + 4 * (if c == '&' then 1 else 0) + 3 * (if c == '<' then 1 else 0) +
        3 * (if c == '>' then 1 else 0) +
        (if quote then 5 * (if c == '"' then 1 else 0) + 5 * (if c == '\'' then 1 else 0) else 0) := by
  unfold escapeChar
  by_cases h1 : c = '&' <;> simp [h1]
  by_cases h2 : c = '<' <;> simp [h2]
  by_cases h3 : c = '>' <;> simp [h3]
  cases quote <;> simp
  by_cases h4 : c = '"' <;> simp [h4]
  by_cases h5 : c = '\'' <;> simp [h5]

lemma escapeChar_length_bounds (c : Char) (quote : Bool) :
    1 ≤ (escapeChar c quote).length ∧
    (escapeChar c quote).length ≤ (if quote then 6 else 5) := by
  have h := escapeChar_length c quote
  cases quote <;>
  by_cases h1 : c = '&' <;>
  by_cases h2 : c = '<' <;>
  by_cases h3 : c = '>' <;>
  by_cases h4 : c = '"' <;>
  by_cases h5 : c = '\'' <;>
  simp_all

lemma escapeChar_count_amp (c : Char) (quote : Bool) :
    (escapeChar c quote).count '&' =
      (if c == '&' then 1 else 0) + (if c == '<' then 1 else 0) + (if c == '>' then 1 else 0) +
        (if quote then (if c == '"' then 1 else 0) + (if c == '\'' then 1 else 0) else 0) := by
  unfold escapeChar
  by_cases h1 : c = '&' <;> simp [h1]
  by_cases h2 : c = '<' <;> simp [h2]
  by_cases h3 : c = '>' <;> simp [h3]
  cases quote
  · simp [h1]
  · by_cases h4 : c = '"' <;> simp [h4]
    by_cases h5 : c = '\'' <;> simp [h1, h5]

lemma escapeChar_count_semi (c : Char) (quote : Bool) :
    (escapeChar c quote).count ';' =
      (if c == ';' then 1 else 0) + (if c == '&' then 1 else 0) + (if c == '<' then 1 else 0) +
        (if c == '>' then 1 else 0) +
        (if quote then (if c == '"' then 1 else 0) + (if c == '\'' then 1 else 0) else 0) := by
  unfold escapeChar
  by_cases h1 : c = '&' <;> simp [h1]
  by_cases h2 : c = '<' <;> simp [h2]
  by_cases h3 : c = '>' <;> simp [h3]
  cases quote <;> simp
  · by_cases h6 : c = ';' <;> simp [h6]
  · by_cases h4 : c = '"' <;> simp [h4]
    by_cases h5 : c = '\'' <;> simp [h5]
    by_cases h6 : c = ';' <;> simp [h6]

lemma escapeChar_count_dquote_false (c : Char) :
    (escapeChar c false).count '"' = if c == '"' then 1 else 0 := by
  unfold escapeChar
  by_cases h1 : c = '&' <;> simp [h1]
  by_cases h2 : c = '<' <;> simp [h2]
  by_cases h3 : c = '>' <;> simp [h3]
  by_cases h4 : c = '"' <;> simp [h4]

lemma escapeChar_count_squote_false (c : Char) :
    (escapeChar c false).count '\'' = if c == '\'' then 1 else 0 := by
  unfold escapeChar
  by_cases h1 : c = '&' <;> simp [h1]
  by_cases h2 : c = '<' <;> simp [h2]
  by_cases h3 : c = '>' <;> simp [h3]
  by_cases h4 : c = '\'' <;> simp [h4]

lemma escapeChar_eq_singleton_of_not_special (c : Char) (quote : Bool)
    (h : isSpecialChar c quote = false) :
    escapeChar c quote = [c] := by
  unfold escapeChar isSpecialChar at *
  by_cases h1 : c = '&' <;> simp_all
  by_cases h2 : c = '<' <;> simp_all
  by_cases h3 : c = '>' <;> simp_all
  cases quote <;> simp_all

lemma escapeChar_length_gt_one_of_special (c : Char) (quote : Bool)
    (h : isSpecialChar c quote = true) :
    1 < (escapeChar c quote).length := by
  unfold escapeChar isSpecialChar at *
  by_cases h1 : c = '&' <;> simp_all
  by_cases h2 : c = '<' <;> simp_all
  by_cases h3 : c = '>' <;> simp_all
  cases quote <;> simp_all
  by_cases h4 : c = '"' <;> simp_all

lemma escapeChar_append_inj (quote : Bool) (c₁ c₂ : Char) (l₁ l₂ : List Char)
    (h : escapeChar c₁ quote ++ l₁ = escapeChar c₂ quote ++ l₂) :
    c₁ = c₂ ∧ l₁ = l₂ := by
  unfold escapeChar at h
  split_ifs at h <;> simp_all <;> exact absurd h.1.symm ‹_›

lemma flatMap_escapeChar_inj (quote : Bool) :
    ∀ (l₁ l₂ : List Char),
      l₁.flatMap (fun c => escapeChar c quote) = l₂.flatMap (fun c => escapeChar c quote) →
      l₁ = l₂
  | [], [], _ => rfl
  | c :: cs, [], h => by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_eq_nil_iff] at h
    exact absurd h.1 (escapeChar_ne_nil c quote)
  | [], c :: cs, h => by
    simp only [List.flatMap_cons, List.flatMap_nil, List.nil_eq_append_iff] at h
    exact absurd h.1 (escapeChar_ne_nil c quote)
  | c₁ :: cs₁, c₂ :: cs₂, h => by
    simp only [List.flatMap_cons] at h
    obtain ⟨rfl, hrest⟩ := escapeChar_append_inj quote c₁ c₂ _ _ h
    rw [flatMap_escapeChar_inj quote cs₁ cs₂ hrest]

/-! ### Property 1: Single-Pass Character Mapping Equivalence (No Double-Escaping) -/

/--
Sequential replacement in the order `&`, `<`, `>`, `"`, `'` is equivalent to
single-pass character-by-character escaping via `escapeChar`.
-/
def single_pass_prop (s : String) (quote : Bool := true) : Prop :=
  (escape s quote).data = s.data.flatMap (fun c => escapeChar c quote)

instance (s : String) (quote : Bool) : Decidable (single_pass_prop s quote) :=
  inferInstanceAs (Decidable (_ = _))

theorem single_pass_thm (s : String) (quote : Bool) : single_pass_prop s quote :=
  escape_data s quote

/-! ### Property 2: Empty String Preservation -/

/-- Escaping the empty string returns the empty string regardless of `quote`. -/
def empty_prop (quote : Bool := true) : Prop :=
  escape "" quote = ""

instance (quote : Bool) : Decidable (empty_prop quote) :=
  inferInstanceAs (Decidable (_ = _))

theorem empty_thm (quote : Bool) : empty_prop quote := by
  unfold empty_prop
  ext : 1
  simp

/-! ### Property 3: Concatenation Homomorphism -/

/-- `escape` distributes over string concatenation (`++`). -/
def append_prop (s₁ s₂ : String) (quote : Bool := true) : Prop :=
  escape (s₁ ++ s₂) quote = escape s₁ quote ++ escape s₂ quote

instance (s₁ s₂ : String) (quote : Bool) : Decidable (append_prop s₁ s₂ quote) :=
  inferInstanceAs (Decidable (_ = _))

theorem append_thm (s₁ s₂ : String) (quote : Bool) : append_prop s₁ s₂ quote := by
  unfold append_prop
  ext : 1
  simp [String.data_append]

/-! ### Property 4: Exact Translation of Special Characters -/

/-- Each HTML special character is mapped to its exact entity specification. -/
def special_chars_prop : Prop :=
  escape "&" true = "&amp;" ∧
  escape "&" false = "&amp;" ∧
  escape "<" true = "&lt;" ∧
  escape "<" false = "&lt;" ∧
  escape ">" true = "&gt;" ∧
  escape ">" false = "&gt;" ∧
  escape "\"" true = "&quot;" ∧
  escape "\"" false = "\"" ∧
  escape "'" true = "&#x27;" ∧
  escape "'" false = "'"

instance : Decidable special_chars_prop :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

theorem special_chars_thm : special_chars_prop := by
  unfold special_chars_prop
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · ext : 1; simp [escapeChar]

/-! ### Property 5: Absence of Raw Angle Brackets in Output -/

/-- The escaped string never contains raw `'<'` or `'>'` characters. -/
def no_angle_brackets_prop (s : String) (quote : Bool := true) : Prop :=
  '<' ∉ (escape s quote).data ∧ '>' ∉ (escape s quote).data

instance (s : String) (quote : Bool) : Decidable (no_angle_brackets_prop s quote) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem no_angle_brackets_thm (s : String) (quote : Bool) :
    no_angle_brackets_prop s quote := by
  unfold no_angle_brackets_prop
  rw [escape_data]
  constructor <;>
  · intro h
    rw [List.mem_flatMap] at h
    rcases h with ⟨c, _, hc⟩
    unfold escapeChar at hc
    (split_ifs at hc <;> simp_all); exact absurd hc.symm ‹_›

/-! ### Property 6: Absence of Raw Quotes When `quote = true` -/

/-- When `quote = true`, the escaped string never contains raw `'"'` or `'\''` characters. -/
def no_quotes_when_quote_true_prop (s : String) : Prop :=
  '"' ∉ (escape s true).data ∧ '\'' ∉ (escape s true).data

instance (s : String) : Decidable (no_quotes_when_quote_true_prop s) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem no_quotes_when_quote_true_thm (s : String) :
    no_quotes_when_quote_true_prop s := by
  unfold no_quotes_when_quote_true_prop
  rw [escape_data]
  constructor <;>
  · intro h
    rw [List.mem_flatMap] at h
    rcases h with ⟨c, _, hc⟩
    unfold escapeChar at hc
    (split_ifs at hc <;> simp_all); exact absurd hc.symm ‹_›

/-! ### Property 7: Preservation of Quotes When `quote = false` -/

/-- When `quote = false`, double quotes and single quotes are preserved with identical counts. -/
def quotes_preserved_when_quote_false_prop (s : String) : Prop :=
  (escape s false).data.count '"' = s.data.count '"' ∧
  (escape s false).data.count '\'' = s.data.count '\''

instance (s : String) : Decidable (quotes_preserved_when_quote_false_prop s) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem quotes_preserved_when_quote_false_thm (s : String) :
    quotes_preserved_when_quote_false_prop s := by
  unfold quotes_preserved_when_quote_false_prop
  rw [escape_data]
  induction s.data with
  | nil => simp
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.count_append, List.count_cons,
      escapeChar_count_dquote_false, escapeChar_count_squote_false, ih.1, ih.2]
    omega

/-! ### Property 8: Exact Output Length Formula -/

/--
The length of `escape s quote` equals `s.length` plus the exact expansion overhead of
each special character (`+4` per `'&'`, `+3` per `'<'` and `'>'`, and when `quote = true`,
`+5` per `'"'` and `'\''`).
-/
def exact_length_prop (s : String) (quote : Bool := true) : Prop :=
  (escape s quote).length =
    s.length + 4 * s.data.count '&' + 3 * s.data.count '<' + 3 * s.data.count '>' +
      (if quote then 5 * s.data.count '"' + 5 * s.data.count '\'' else 0)

instance (s : String) (quote : Bool) : Decidable (exact_length_prop s quote) :=
  inferInstanceAs (Decidable (_ = _))

theorem exact_length_thm (s : String) (quote : Bool) : exact_length_prop s quote := by
  unfold exact_length_prop
  simp only [string_length_eq_data_length, escape_data]
  induction s.data with
  | nil => simp
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.count_cons,
      escapeChar_length, ih]
    cases quote <;>
    · simp only [↓reduceIte, Bool.false_eq_true]
      omega

/-! ### Property 9: Tight Length Bounds -/

/--
Escaping never decreases string length and increases it by at most a factor of `6`
when `quote = true` (or `5` when `quote = false`).
-/
def length_bounds_prop (s : String) (quote : Bool := true) : Prop :=
  s.length ≤ (escape s quote).length ∧
  (escape s quote).length ≤ (if quote then 6 else 5) * s.length

instance (s : String) (quote : Bool) : Decidable (length_bounds_prop s quote) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem length_bounds_thm (s : String) (quote : Bool) : length_bounds_prop s quote := by
  unfold length_bounds_prop
  simp only [string_length_eq_data_length, escape_data]
  induction s.data with
  | nil => simp
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have hb := escapeChar_length_bounds c quote
    cases quote <;> simp_all <;> omega

/-! ### Property 10: Fixed-Point Characterization (Unchanged Iff No Special Characters) -/

lemma flatMap_escapeChar_length_gt_of_mem_special (l : List Char) (quote : Bool)
    (c : Char) (hc : c ∈ l) (hspec : isSpecialChar c quote = true) :
    l.length < (l.flatMap (fun x => escapeChar x quote)).length := by
  induction l with
  | nil => contradiction
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rcases List.mem_cons.mp hc with rfl | hmem
    · have hgt := escapeChar_length_gt_one_of_special c quote hspec
      have hge : xs.length ≤ (xs.flatMap (fun x => escapeChar x quote)).length := by
        have := (length_bounds_thm (String.mk xs) quote).1
        simpa [string_length_eq_data_length, escape_data] using this
      omega
    · have hlt := ih hmem
      have hge := (escapeChar_length_bounds x quote).1
      omega

lemma flatMap_escapeChar_eq_self_of_no_special (l : List Char) (quote : Bool)
    (hall : ∀ c ∈ l, isSpecialChar c quote = false) :
    l.flatMap (fun c => escapeChar c quote) = l := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.flatMap_cons]
    rw [escapeChar_eq_singleton_of_not_special c quote (hall c (List.mem_cons_self ..)),
        ih (fun x hx => hall x (List.mem_cons_of_mem c hx)), List.singleton_append]

/-- `escape s quote` equals `s` if and only if `s` contains no special characters. -/
def unchanged_iff_no_special_prop (s : String) (quote : Bool := true) : Prop :=
  escape s quote = s ↔ ∀ c ∈ s.data, isSpecialChar c quote = false

instance (s : String) (quote : Bool) : Decidable (unchanged_iff_no_special_prop s quote) :=
  inferInstanceAs (Decidable (_ ↔ _))

theorem unchanged_iff_no_special_thm (s : String) (quote : Bool) :
    unchanged_iff_no_special_prop s quote := by
  unfold unchanged_iff_no_special_prop
  constructor
  · intro heq c hc
    by_contra hne
    have hspec : isSpecialChar c quote = true := by
      cases h : isSpecialChar c quote <;> simp_all
    have hlt := flatMap_escapeChar_length_gt_of_mem_special s.data quote c hc hspec
    rw [← escape_data, heq] at hlt
    exact Nat.lt_irrefl _ hlt
  · intro hall
    ext : 1
    rw [escape_data]
    exact flatMap_escapeChar_eq_self_of_no_special s.data quote hall

/-! ### Property 11: Exact Ampersand Count -/

/--
Every special character in `s` produces exactly one `'&'` in `escape s quote`,
and non-special characters produce none.
-/
def ampersand_count_prop (s : String) (quote : Bool := true) : Prop :=
  (escape s quote).data.count '&' =
    s.data.count '&' + s.data.count '<' + s.data.count '>' +
      (if quote then s.data.count '"' + s.data.count '\'' else 0)

instance (s : String) (quote : Bool) : Decidable (ampersand_count_prop s quote) :=
  inferInstanceAs (Decidable (_ = _))

theorem ampersand_count_thm (s : String) (quote : Bool) :
    ampersand_count_prop s quote := by
  unfold ampersand_count_prop
  rw [escape_data]
  induction s.data with
  | nil => simp
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.count_append, List.count_cons,
      escapeChar_count_amp, ih]
    cases quote <;>
    · simp only [↓reduceIte, Bool.false_eq_true]
      omega

/-! ### Property 12: Exact Semicolon Count (No Double-Escaping Witness) -/

/--
Every special character in `s` adds exactly one semicolon `';'` to `escape s quote`
(proving no entity is ever double-escaped into two semicolons such as `"&amp;lt;"`).
-/
def semicolon_count_prop (s : String) (quote : Bool := true) : Prop :=
  (escape s quote).data.count ';' =
    s.data.count ';' + s.data.count '&' + s.data.count '<' + s.data.count '>' +
      (if quote then s.data.count '"' + s.data.count '\'' else 0)

instance (s : String) (quote : Bool) : Decidable (semicolon_count_prop s quote) :=
  inferInstanceAs (Decidable (_ = _))

theorem semicolon_count_thm (s : String) (quote : Bool) :
    semicolon_count_prop s quote := by
  unfold semicolon_count_prop
  rw [escape_data]
  induction s.data with
  | nil => simp
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.count_append, List.count_cons,
      escapeChar_count_semi, ih]
    cases quote <;>
    · simp only [↓reduceIte, Bool.false_eq_true]
      omega

/-! ### Property 13: Relationship Between `quote = true` and `quote = false` -/

/--
`escape s true` is obtained by escaping `'"'` and `'\''` in `escape s false`,
and `escape s true = escape s false` whenever `s` contains no quotes.
-/
def quote_flag_relation_prop (s : String) : Prop :=
  escape s true = replaceChar (replaceChar (escape s false) '"' "&quot;") '\'' "&#x27;" ∧
  (('"' ∉ s.data ∧ '\'' ∉ s.data) → escape s true = escape s false)

instance (s : String) : Decidable (quote_flag_relation_prop s) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem quote_flag_relation_thm (s : String) : quote_flag_relation_prop s := by
  unfold quote_flag_relation_prop
  refine ⟨rfl, ?_⟩
  rintro ⟨hdq, hsq⟩
  ext : 1
  simp only [escape_data]
  refine List.flatMap_congr (fun c hc => ?_)
  have h1 : (c == '"') = false := beq_false_of_ne (fun h => hdq (h ▸ hc))
  have h2 : (c == '\'') = false := beq_false_of_ne (fun h => hsq (h ▸ hc))
  simp [escapeChar, h1, h2]

/-! ### Property 14: Injectivity (Lossless Encoding) -/

/-- `escape` is injective for any fixed `quote` flag. -/
def injective_prop (s₁ s₂ : String) (quote : Bool := true) : Prop :=
  escape s₁ quote = escape s₂ quote ↔ s₁ = s₂

instance (s₁ s₂ : String) (quote : Bool) : Decidable (injective_prop s₁ s₂ quote) :=
  inferInstanceAs (Decidable (_ ↔ _))

theorem injective_thm (s₁ s₂ : String) (quote : Bool) : injective_prop s₁ s₂ quote := by
  unfold injective_prop
  constructor
  · intro h
    have hdata : (escape s₁ quote).data = (escape s₂ quote).data := congrArg String.data h
    rw [escape_data, escape_data] at hdata
    ext : 1
    exact flatMap_escapeChar_inj quote s₁.data s₂.data hdata
  · rintro rfl
    rfl

/-! ### Property 15: Agreement of `benchmark_escape` and `escape` -/

/-- `benchmark_escape` agrees with `escape` on all strings. -/
def benchmark_escape_eq_prop (s : String) (quote : Bool := true) : Prop :=
  benchmark_escape s quote = escape s quote

instance (s : String) (quote : Bool) : Decidable (benchmark_escape_eq_prop s quote) :=
  inferInstanceAs (Decidable (_ = _))

theorem benchmark_escape_eq_thm (s : String) (quote : Bool) :
    benchmark_escape_eq_prop s quote := by
  rfl

/-! ## 8. Post-Condition (`Post_prop`) as Conjunction of Properties -/

/-- Full post-condition specification for `escape(s, quote)`. -/
def Post_prop (s : String) (quote : Bool := true) : Prop :=
  single_pass_prop s quote ∧
  empty_prop quote ∧
  append_prop s "" quote ∧
  special_chars_prop ∧
  no_angle_brackets_prop s quote ∧
  no_quotes_when_quote_true_prop s ∧
  quotes_preserved_when_quote_false_prop s ∧
  exact_length_prop s quote ∧
  length_bounds_prop s quote ∧
  unchanged_iff_no_special_prop s quote ∧
  ampersand_count_prop s quote ∧
  semicolon_count_prop s quote ∧
  quote_flag_relation_prop s ∧
  injective_prop s s quote ∧
  benchmark_escape_eq_prop s quote

instance (s : String) (quote : Bool) : Decidable (Post_prop s quote) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-! ## 9. Property-Based Tests (PBTs) -/

/-- Representative corpus of strings for bounded exhaustive property-based testing. -/
def pbtCorpus : List String :=
  [ "", "a", "hello world", "&", "<", ">", "\"", "'", ";",
    "&<", "<>", "<b>\"&'</b>", "&amp;", "&lt;", "&gt;", "&quot;", "&#x27;",
    "&&<<>>\"\"''", "<script>alert(\"xss\" & 'test');</script>",
    "a&b<c>d\"e'f;g" ]

-- Randomized PBTs via Plausible for every `_prop` and `Post_prop`
#eval Plausible.Testable.check (∀ (s : String) (quote : Bool), single_pass_prop s quote)
#eval Plausible.Testable.check (∀ (quote : Bool), empty_prop quote)
#eval Plausible.Testable.check (∀ (s₁ s₂ : String) (quote : Bool), append_prop s₁ s₂ quote)
#eval Plausible.Testable.check special_chars_prop
#eval Plausible.Testable.check (∀ (s : String) (quote : Bool), no_angle_brackets_prop s quote)
#eval Plausible.Testable.check (∀ (s : String), no_quotes_when_quote_true_prop s)
#eval Plausible.Testable.check (∀ (s : String), quotes_preserved_when_quote_false_prop s)
#eval Plausible.Testable.check (∀ (s : String) (quote : Bool), exact_length_prop s quote)
#eval Plausible.Testable.check (∀ (s : String) (quote : Bool), length_bounds_prop s quote)
#eval Plausible.Testable.check (∀ (s : String) (quote : Bool), unchanged_iff_no_special_prop s quote)
#eval Plausible.Testable.check (∀ (s : String) (quote : Bool), ampersand_count_prop s quote)
#eval Plausible.Testable.check (∀ (s : String) (quote : Bool), semicolon_count_prop s quote)
#eval Plausible.Testable.check (∀ (s : String), quote_flag_relation_prop s)
#eval Plausible.Testable.check (∀ (s₁ s₂ : String) (quote : Bool), injective_prop s₁ s₂ quote)
#eval Plausible.Testable.check (∀ (s : String) (quote : Bool), benchmark_escape_eq_prop s quote)
#eval Plausible.Testable.check (∀ (s : String) (quote : Bool), Post_prop s quote)

-- Bounded PBTs via `native_decide` across `pbtCorpus`
example : pbtCorpus.all (fun s => decide (single_pass_prop s true) && decide (single_pass_prop s false)) = true := by native_decide
example : (decide (empty_prop true) && decide (empty_prop false)) = true := by native_decide
example : pbtCorpus.all (fun s₁ => pbtCorpus.all (fun s₂ => decide (append_prop s₁ s₂ true) && decide (append_prop s₁ s₂ false))) = true := by native_decide
example : decide special_chars_prop = true := by native_decide
example : pbtCorpus.all (fun s => decide (no_angle_brackets_prop s true) && decide (no_angle_brackets_prop s false)) = true := by native_decide
example : pbtCorpus.all (fun s => decide (no_quotes_when_quote_true_prop s)) = true := by native_decide
example : pbtCorpus.all (fun s => decide (quotes_preserved_when_quote_false_prop s)) = true := by native_decide
example : pbtCorpus.all (fun s => decide (exact_length_prop s true) && decide (exact_length_prop s false)) = true := by native_decide
example : pbtCorpus.all (fun s => decide (length_bounds_prop s true) && decide (length_bounds_prop s false)) = true := by native_decide
example : pbtCorpus.all (fun s => decide (unchanged_iff_no_special_prop s true) && decide (unchanged_iff_no_special_prop s false)) = true := by native_decide
example : pbtCorpus.all (fun s => decide (ampersand_count_prop s true) && decide (ampersand_count_prop s false)) = true := by native_decide
example : pbtCorpus.all (fun s => decide (semicolon_count_prop s true) && decide (semicolon_count_prop s false)) = true := by native_decide
example : pbtCorpus.all (fun s => decide (quote_flag_relation_prop s)) = true := by native_decide
example : pbtCorpus.all (fun s₁ => pbtCorpus.all (fun s₂ => decide (injective_prop s₁ s₂ true) && decide (injective_prop s₁ s₂ false))) = true := by native_decide
example : pbtCorpus.all (fun s => decide (benchmark_escape_eq_prop s true) && decide (benchmark_escape_eq_prop s false)) = true := by native_decide
example : pbtCorpus.all (fun s => decide (Post_prop s true) && decide (Post_prop s false)) = true := by native_decide

/-! ## 10. Correctness Theorem (`Pre -> Post`) -/

/-- Main partial/total correctness theorem: `Pre s quote → Post_prop s quote`. -/
theorem escape_correct (s : String) (quote : Bool := true) (_hPre : Pre s quote) :
    Post_prop s quote := by
  refine ⟨single_pass_thm s quote,
          empty_thm quote,
          append_thm s "" quote,
          special_chars_thm,
          no_angle_brackets_thm s quote,
          no_quotes_when_quote_true_thm s,
          quotes_preserved_when_quote_false_thm s,
          exact_length_thm s quote,
          length_bounds_thm s quote,
          unchanged_iff_no_special_thm s quote,
          ampersand_count_thm s quote,
          semicolon_count_thm s quote,
          quote_flag_relation_thm s,
          injective_thm s s quote,
          benchmark_escape_eq_thm s quote⟩

/-! ## 11. Imperative Implementation (`Id.run do` with Mutable State) -/

/-- Imperative character replacement using `Id.run do` and mutable accumulator `acc`. -/
def replaceCharImp (s : String) (target : Char) (replacement : String) : String := Id.run do
  let mut acc : List Char := []
  for c in s.data do
    if c == target then
      acc := acc ++ replacement.data
    else
      acc := acc ++ [c]
  return String.mk acc

/--
Imperative multi-pass HTML escaping mirroring Python's sequential `s = s.replace(...)`
mutations using `Id.run do` and mutable string state `res`.
-/
def escapeImp (s : String) (quote : Bool := true) : String := Id.run do
  let mut res : String := s
  res := replaceCharImp res '&' "&amp;"
  res := replaceCharImp res '<' "&lt;"
  res := replaceCharImp res '>' "&gt;"
  if quote then
    res := replaceCharImp res '"' "&quot;"
    res := replaceCharImp res '\'' "&#x27;"
  return res

/--
Imperative single-pass HTML escaping using `Id.run do` with a single `for` loop
and mutable character buffer `acc`.
-/
def escapeSinglePassImp (s : String) (quote : Bool := true) : String := Id.run do
  let mut acc : List Char := []
  for c in s.data do
    if c == '&' then
      acc := acc ++ "&amp;".data
    else if c == '<' then
      acc := acc ++ "&lt;".data
    else if c == '>' then
      acc := acc ++ "&gt;".data
    else if quote && c == '"' then
      acc := acc ++ "&quot;".data
    else if quote && c == '\'' then
      acc := acc ++ "&#x27;".data
    else
      acc := acc ++ [c]
  return String.mk acc

/-! ## 12. Imperative Tests -/

example : escapeImp "<b>\"&'</b>" = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by native_decide
example : escapeImp "" = "" := by native_decide
example : escapeImp "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by native_decide
example : escapeImp "&<" = "&amp;&lt;" := by native_decide
example : check (fun s q => escapeImp s q) = true := by native_decide

example : escapeSinglePassImp "<b>\"&'</b>" = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by native_decide
example : escapeSinglePassImp "" = "" := by native_decide
example : escapeSinglePassImp "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by native_decide
example : escapeSinglePassImp "&<" = "&amp;&lt;" := by native_decide
example : check (fun s q => escapeSinglePassImp s q) = true := by native_decide

#eval escapeImp "<b>\"&'</b>"
#eval escapeImp "<b>\"&'</b>" false
#eval escapeSinglePassImp "<b>\"&'</b>"
#eval escapeSinglePassImp "<b>\"&'</b>" false
#eval Plausible.Testable.check (∀ (s : String) (quote : Bool), escape s quote = escapeImp s quote)
#eval Plausible.Testable.check (∀ (s : String) (quote : Bool), escape s quote = escapeSinglePassImp s quote)

/-! ## 13. Equivalence Theorems (Functional = Imperative) -/

/-- Functional `replaceChar` is equivalent to imperative `replaceCharImp`. -/
theorem replaceChar_eq_replaceCharImp (s : String) (target : Char) (replacement : String) :
    replaceChar s target replacement = replaceCharImp s target replacement := by
  simp only [replaceChar, replaceCharImp]
  congr 1
  have h : ∀ (l : List Char) (acc : List Char),
      Id.run (forIn l acc fun c r =>
        if c = target then
          pure (ForInStep.yield (r ++ replacement.data))
        else
          pure (ForInStep.yield (r ++ [c]))) =
      acc ++ l.flatMap (fun c => if c = target then replacement.data else [c]) := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons c cs ih =>
      intro acc
      by_cases hc : c = target <;> simp [hc, ih, List.append_assoc]
  simpa using (h s.data []).symm

/-- Functional `escape` is equivalent to imperative multi-pass `escapeImp`. -/
theorem escape_eq_escapeImp (s : String) (quote : Bool := true) :
    escape s quote = escapeImp s quote := by
  cases quote <;>
  · simp only [escape, escapeImp, replaceChar_eq_replaceCharImp]
    rfl

/-- Functional `escape` is equivalent to imperative single-pass `escapeSinglePassImp`. -/
theorem escape_eq_escapeSinglePassImp (s : String) (quote : Bool := true) :
    escape s quote = escapeSinglePassImp s quote := by
  ext : 1
  rw [escape_data]
  simp only [escapeSinglePassImp]
  have h : ∀ (l : List Char) (acc : List Char),
      Id.run (forIn l acc fun c r =>
        if (c == '&') = true then pure (ForInStep.yield (r ++ "&amp;".data))
        else if (c == '<') = true then pure (ForInStep.yield (r ++ "&lt;".data))
        else if (c == '>') = true then pure (ForInStep.yield (r ++ "&gt;".data))
        else if (quote && c == '"') = true then pure (ForInStep.yield (r ++ "&quot;".data))
        else if (quote && c == '\'') = true then pure (ForInStep.yield (r ++ "&#x27;".data))
        else pure (ForInStep.yield (r ++ [c]))) =
      acc ++ l.flatMap (fun c => escapeChar c quote) := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons c cs ih =>
      intro acc
      simp only [List.forIn_cons, List.flatMap_cons]
      split_ifs <;> ·
        change Id.run (forIn cs _ _) = _
        rw [ih, List.append_assoc]
        congr 1; congr 1
        simp [escapeChar, *]
  simpa using (h s.data []).symm

/-- Both imperative implementations (`escapeImp` and `escapeSinglePassImp`) are equivalent. -/
theorem escapeImp_eq_escapeSinglePassImp (s : String) (quote : Bool := true) :
    escapeImp s quote = escapeSinglePassImp s quote := by
  rw [← escape_eq_escapeImp s quote, escape_eq_escapeSinglePassImp s quote]

end «20_html_escape»
