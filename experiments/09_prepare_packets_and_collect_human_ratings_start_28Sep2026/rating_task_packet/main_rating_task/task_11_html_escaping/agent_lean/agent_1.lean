import Mathlib

/-!
# HTML Escape (`20_html_escape`)

Lean 4 formalization of Python's `html.escape` function.

Replaces special characters `"&"`, `"<"`, and `">"` with HTML-safe sequences
(`"&amp;"`, `"&lt;"`, `"&gt;"`). If the optional flag `quote` is `true` (the default),
both double quote (`"`) and single quote (`'`) characters are also translated
(`"&quot;"` and `"&#x27;"`).
-/

namespace «20_html_escape»

/-! ## 4. Implementation (Functional Definition) -/

/-- Pre-condition check corresponding to Python's `pre_escape`. -/
def pre_escape (_s : String) : Bool :=
  true

/-- Replace every occurrence of a character `target` in `s` with `replacement`. -/
def replaceChar (s : String) (target : Char) (replacement : String) : String :=
  String.mk (s.data.flatMap (fun c => if c = target then replacement.data else [c]))

/--
Replace special characters `"&"`, `"<"` and `">"` with HTML-safe sequences.
If the optional flag `quote` is `true` (the default), double quote (`"`) and
single quote (`'`) characters are also translated.
Order matters: `&` must be replaced first to avoid double-escaping.
-/
def escape (s : String) (quote : Bool := true) : String :=
  let s := replaceChar s '&' "&amp;"
  let s := replaceChar s '<' "&lt;"
  let s := replaceChar s '>' "&gt;"
  if quote then
    let s := replaceChar s '"' "&quot;"
    let s := replaceChar s '\'' "&#x27;"
    s
  else
    s

/-- Main benchmark entry point corresponding to Python's `benchmark_escape`. -/
def benchmark_escape (s : String) (quote : Bool := true) : String :=
  escape s quote

/-- Single-character HTML escape specification. -/
def escapeChar (c : Char) (quote : Bool := true) : String :=
  if c = '&' then "&amp;"
  else if c = '<' then "&lt;"
  else if c = '>' then "&gt;"
  else if quote && c = '"' then "&quot;"
  else if quote && c = '\'' then "&#x27;"
  else String.mk [c]

/-- Predicate indicating whether a character is left untouched by `escape`. -/
def isSafeChar (c : Char) (quote : Bool := true) : Bool :=
  c != '&' && c != '<' && c != '>' && (!quote || (c != '"' && c != '\''))

/-- Executable test suite matching Python's `check` function. -/
def check (escape_candidate : String → Bool → String) : Bool :=
  -- 1. Quote=True (Default)
  (escape_candidate "<b>\"&'</b>" true == "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;") &&
  (escape_candidate "" true == "") &&
  -- 2. Quote=False
  (escape_candidate "<b>\"&'</b>" false == "&lt;b&gt;\"&amp;'&lt;/b&gt;") &&
  -- 3. Order check
  (escape_candidate "&<" true == "&amp;&lt;")

/-! ## 5. Unit Tests -/

-- 1. Quote=True (Default)
example : escape "<b>\"&'</b>" = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by native_decide
example : escape "" = "" := by native_decide

-- 2. Quote=False
example : escape "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by native_decide

-- 3. Order check
example : escape "&<" = "&amp;&lt;" := by native_decide

-- 4. Additional unit tests
example : benchmark_escape "<b>\"&'</b>" = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by native_decide
example : benchmark_escape "" = "" := by native_decide
example : benchmark_escape "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by native_decide
example : benchmark_escape "&<" = "&amp;&lt;" := by native_decide
example : escape "hello world" = "hello world" := by native_decide
example : escape "hello world" false = "hello world" := by native_decide
example : check (fun s q => escape s q) = true := by native_decide
example : check (fun s q => benchmark_escape s q) = true := by native_decide

#eval escape "<b>\"&'</b>"
#eval escape ""
#eval escape "<b>\"&'</b>" false
#eval escape "&<"
#eval check (fun s q => benchmark_escape s q)

/-! ## 6. Pre-condition Predicate -/

/--
Pre-condition for `escape`. In Python, `pre_escape(s)` checks `isinstance(s, str)`,
which holds for all `s : String`.
-/
def Pre (s : String) (_quote : Bool := true) : Prop :=
  pre_escape s = true

theorem pre_trivial (s : String) (quote : Bool := true) : Pre s quote := by
  rfl

/-! ## 7. Property Propositions and Theorems -/

/--
Property 1 (Single-pass character specification):
Sequential replacement of `&`, `<`, `>`, and (optionally) `"` and `'` is equivalent
to a single-pass `flatMap` applying `escapeChar` to each character.
-/
def char_spec_prop (s : String) (quote : Bool := true) : Prop :=
  (escape s quote).data = s.data.flatMap (fun c => (escapeChar c quote).data)

theorem char_spec_thm (s : String) (quote : Bool := true) : char_spec_prop s quote := by
  unfold char_spec_prop
  cases quote <;>
  · simp only [escape, replaceChar, escapeChar, List.flatMap_assoc]
    apply congrFun (congrArg List.flatMap _)
    funext c
    by_cases h1 : c = '&'; · subst h1; decide
    by_cases h2 : c = '<'; · subst h2; decide
    by_cases h3 : c = '>'; · subst h3; decide
    by_cases h4 : c = '"'; · subst h4; decide
    by_cases h5 : c = '\''; · subst h5; decide
    simp [h1, h2, h3, h4, h5]

/--
Property 2 (Empty string preservation):
Escaping the empty string returns the empty string.
-/
def empty_prop (quote : Bool := true) : Prop :=
  escape "" quote = ""

theorem empty_thm (quote : Bool := true) : empty_prop quote := by
  unfold empty_prop
  apply String.ext
  rw [char_spec_thm "" quote]
  rfl

/--
Property 3 (Concatenation homomorphism):
Escaping the concatenation of two strings equals the concatenation of their escaped results.
-/
def append_prop (s₁ s₂ : String) (quote : Bool := true) : Prop :=
  escape (s₁ ++ s₂) quote = escape s₁ quote ++ escape s₂ quote

theorem append_thm (s₁ s₂ : String) (quote : Bool := true) : append_prop s₁ s₂ quote := by
  unfold append_prop
  apply String.ext
  rw [String.data_append, char_spec_thm (s₁ ++ s₂) quote, char_spec_thm s₁ quote,
    char_spec_thm s₂ quote, String.data_append, List.flatMap_append]

/--
Property 4 (No raw angle brackets in output):
The escaped string never contains `'<'` or `'>'`.
-/
def no_angle_brackets_prop (s : String) (quote : Bool := true) : Prop :=
  '<' ∉ (escape s quote).data ∧ '>' ∉ (escape s quote).data

theorem no_angle_brackets_thm (s : String) (quote : Bool := true) :
    no_angle_brackets_prop s quote := by
  unfold no_angle_brackets_prop
  rw [char_spec_thm s quote]
  constructor <;> intro h <;> rw [List.mem_flatMap] at h <;> rcases h with ⟨c, _, hc⟩
  · cases quote <;>
    · by_cases h1 : c = '&'; · subst h1; revert hc; decide
      by_cases h2 : c = '<'; · subst h2; revert hc; decide
      by_cases h3 : c = '>'; · subst h3; revert hc; decide
      by_cases h4 : c = '"'; · subst h4; revert hc; decide
      by_cases h5 : c = '\''; · subst h5; revert hc; decide
      simp [escapeChar, h1, h2, h3, h4, h5, eq_comm] at hc
  · cases quote <;>
    · by_cases h1 : c = '&'; · subst h1; revert hc; decide
      by_cases h2 : c = '<'; · subst h2; revert hc; decide
      by_cases h3 : c = '>'; · subst h3; revert hc; decide
      by_cases h4 : c = '"'; · subst h4; revert hc; decide
      by_cases h5 : c = '\''; · subst h5; revert hc; decide
      simp [escapeChar, h1, h2, h3, h4, h5, eq_comm] at hc

/--
Property 5 (No raw quotes when `quote = true`):
When `quote = true`, the escaped string never contains `'"'` or `'\''`.
-/
def no_quotes_when_quote_true_prop (s : String) : Prop :=
  '"' ∉ (escape s true).data ∧ '\'' ∉ (escape s true).data

theorem no_quotes_when_quote_true_thm (s : String) :
    no_quotes_when_quote_true_prop s := by
  unfold no_quotes_when_quote_true_prop
  rw [char_spec_thm s true]
  constructor <;> intro h <;> rw [List.mem_flatMap] at h <;> rcases h with ⟨c, _, hc⟩
  · by_cases h1 : c = '&'; · subst h1; revert hc; decide
    by_cases h2 : c = '<'; · subst h2; revert hc; decide
    by_cases h3 : c = '>'; · subst h3; revert hc; decide
    by_cases h4 : c = '"'; · subst h4; revert hc; decide
    by_cases h5 : c = '\''; · subst h5; revert hc; decide
    simp [escapeChar, h1, h2, h3, h4, h5, eq_comm] at hc
  · by_cases h1 : c = '&'; · subst h1; revert hc; decide
    by_cases h2 : c = '<'; · subst h2; revert hc; decide
    by_cases h3 : c = '>'; · subst h3; revert hc; decide
    by_cases h4 : c = '"'; · subst h4; revert hc; decide
    by_cases h5 : c = '\''; · subst h5; revert hc; decide
    simp [escapeChar, h1, h2, h3, h4, h5, eq_comm] at hc

/--
Property 6 (Quotes preserved when `quote = false`):
When `quote = false`, double quotes and single quotes appear in the output
if and only if they appear in the input.
-/
def quotes_preserved_when_quote_false_prop (s : String) : Prop :=
  ('"' ∈ (escape s false).data ↔ '"' ∈ s.data) ∧
  ('\'' ∈ (escape s false).data ↔ '\'' ∈ s.data)

theorem quotes_preserved_when_quote_false_thm (s : String) :
    quotes_preserved_when_quote_false_prop s := by
  unfold quotes_preserved_when_quote_false_prop
  rw [char_spec_thm s false]
  constructor
  · rw [List.mem_flatMap]
    constructor
    · rintro ⟨c, hcs, hc⟩
      by_cases h1 : c = '&'; · subst h1; exact False.elim (by revert hc; decide)
      by_cases h2 : c = '<'; · subst h2; exact False.elim (by revert hc; decide)
      by_cases h3 : c = '>'; · subst h3; exact False.elim (by revert hc; decide)
      simp [escapeChar, h1, h2, h3] at hc
      subst hc; exact hcs
    · intro h
      exact ⟨'"', h, by decide⟩
  · rw [List.mem_flatMap]
    constructor
    · rintro ⟨c, hcs, hc⟩
      by_cases h1 : c = '&'; · subst h1; exact False.elim (by revert hc; decide)
      by_cases h2 : c = '<'; · subst h2; exact False.elim (by revert hc; decide)
      by_cases h3 : c = '>'; · subst h3; exact False.elim (by revert hc; decide)
      simp [escapeChar, h1, h2, h3] at hc
      subst hc; exact hcs
    · intro h
      exact ⟨'\'', h, by decide⟩

/--
Property 7 (Quote mode dispatch):
In `quote = true` mode, quotes are removed; in `quote = false` mode, quotes are preserved.
-/
def quote_dispatch_prop (s : String) (quote : Bool := true) : Prop :=
  (quote = true → no_quotes_when_quote_true_prop s) ∧
  (quote = false → quotes_preserved_when_quote_false_prop s)

theorem quote_dispatch_thm (s : String) (quote : Bool := true) :
    quote_dispatch_prop s quote := by
  exact ⟨fun _ => no_quotes_when_quote_true_thm s, fun _ => quotes_preserved_when_quote_false_thm s⟩

/-- Helper lemma: each escaped character has length between 1 and 6. -/
theorem escapeChar_length_bounds (c : Char) (quote : Bool) :
    1 ≤ (escapeChar c quote).data.length ∧ (escapeChar c quote).data.length ≤ 6 := by
  cases quote <;>
  · by_cases h1 : c = '&'; · subst h1; decide
    by_cases h2 : c = '<'; · subst h2; decide
    by_cases h3 : c = '>'; · subst h3; decide
    by_cases h4 : c = '"'; · subst h4; decide
    by_cases h5 : c = '\''; · subst h5; decide
    simp [escapeChar, h1, h2, h3, h4, h5]

/--
Property 8 (Length bounds):
Escaping never shrinks a string and expands its length by at most a factor of 6.
-/
def length_bounds_prop (s : String) (quote : Bool := true) : Prop :=
  s.length ≤ (escape s quote).length ∧ (escape s quote).length ≤ 6 * s.length

theorem length_bounds_thm (s : String) (quote : Bool := true) :
    length_bounds_prop s quote := by
  change s.data.length ≤ (escape s quote).data.length ∧ (escape s quote).data.length ≤ 6 * s.data.length
  rw [char_spec_thm s quote]
  induction s.data with
  | nil => simp
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have hc := escapeChar_length_bounds c quote
    omega

/-- Helper lemma: exact length of `escapeChar c quote`. -/
theorem escapeChar_exact_length (c : Char) (quote : Bool) :
    (escapeChar c quote).data.length =
      1 + 4 * (if c == '&' then 1 else 0) + 3 * (if c == '<' then 1 else 0) +
      3 * (if c == '>' then 1 else 0) +
      (if quote then 5 * (if c == '"' then 1 else 0) + 5 * (if c == '\'' then 1 else 0) else 0) := by
  cases quote <;>
  · by_cases h1 : c = '&'; · subst h1; decide
    by_cases h2 : c = '<'; · subst h2; decide
    by_cases h3 : c = '>'; · subst h3; decide
    by_cases h4 : c = '"'; · subst h4; decide
    by_cases h5 : c = '\''; · subst h5; decide
    simp [escapeChar, h1, h2, h3, h4, h5]

/--
Property 9 (Exact output length formula):
Each `'&'` adds 4 characters, each `'<'` or `'>'` adds 3 characters, and when `quote = true`,
each `'"'` or `'\''` adds 5 characters (confirming no double-escaping occurs).
-/
def exact_length_prop (s : String) (quote : Bool := true) : Prop :=
  (escape s quote).length =
    s.length + 4 * s.data.count '&' + 3 * s.data.count '<' + 3 * s.data.count '>' +
    (if quote then 5 * s.data.count '"' + 5 * s.data.count '\'' else 0)

theorem exact_length_thm (s : String) (quote : Bool := true) :
    exact_length_prop s quote := by
  change (escape s quote).data.length =
    s.data.length + 4 * s.data.count '&' + 3 * s.data.count '<' + 3 * s.data.count '>' +
    (if quote then 5 * s.data.count '"' + 5 * s.data.count '\'' else 0)
  rw [char_spec_thm s quote]
  induction s.data with
  | nil => cases quote <;> simp
  | cons c cs ih =>
    have hc := escapeChar_exact_length c quote
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.count_cons, ih, hc]
    cases quote <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega

/-- Helper lemma: safe characters map to singleton `[c]`. -/
theorem escapeChar_eq_singleton_of_safe {c : Char} {quote : Bool} (h : isSafeChar c quote = true) :
    (escapeChar c quote).data = [c] := by
  cases quote <;>
  · by_cases h1 : c = '&'; · subst h1; revert h; decide
    by_cases h2 : c = '<'; · subst h2; revert h; decide
    by_cases h3 : c = '>'; · subst h3; revert h; decide
    by_cases h4 : c = '"'; · subst h4; revert h; decide
    by_cases h5 : c = '\''; · subst h5; revert h; decide
    simp [escapeChar, h1, h2, h3, h4, h5]

/-- Helper lemma: unsafe characters expand to length strictly greater than 1. -/
theorem escapeChar_length_gt_one_of_unsafe {c : Char} {quote : Bool} (h : isSafeChar c quote = false) :
    1 < (escapeChar c quote).data.length := by
  cases quote <;>
  · by_cases h1 : c = '&'; · subst h1; decide
    by_cases h2 : c = '<'; · subst h2; decide
    by_cases h3 : c = '>'; · subst h3; decide
    by_cases h4 : c = '"'; · subst h4; revert h; decide
    by_cases h5 : c = '\''; · subst h5; revert h; decide
    simp [isSafeChar, h1, h2, h3, h4, h5] at h

theorem safe_string_id (s : String) (quote : Bool)
    (h : s.data.all (fun c => isSafeChar c quote) = true) :
    escape s quote = s := by
  apply String.ext
  rw [char_spec_thm s quote]
  revert h
  induction s.data with
  | nil =>
    intro _
    rfl
  | cons c cs ih =>
    intro h
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [List.flatMap_cons]
    rw [escapeChar_eq_singleton_of_safe h.1, List.singleton_append]
    congr 1
    exact ih h.2

theorem strict_length_of_unsafe (s : String) (quote : Bool)
    (h : s.data.all (fun c => isSafeChar c quote) = false) :
    s.length < (escape s quote).length := by
  change s.data.length < (escape s quote).data.length
  rw [char_spec_thm s quote]
  revert h
  induction s.data with
  | nil =>
    intro h
    simp at h
  | cons c cs ih =>
    intro h
    simp only [List.all_cons, Bool.and_eq_false_iff] at h
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rcases h with hc | hcs
    · have h1 := escapeChar_length_gt_one_of_unsafe hc
      have h2 : cs.length ≤ (cs.flatMap (fun c => (escapeChar c quote).data)).length := by
        clear h1 hc ih
        induction cs with
        | nil => simp
        | cons x xs ihx =>
          simp only [List.flatMap_cons, List.length_append, List.length_cons]
          have hx := (escapeChar_length_bounds x quote).1
          omega
      omega
    · have h1 := (escapeChar_length_bounds c quote).1
      have h2 := ih hcs
      omega

/--
Property 10 (Fixed-point characterization):
`escape s quote = s` if and only if every character in `s` is safe under `quote`.
-/
def fixed_point_iff_safe_prop (s : String) (quote : Bool := true) : Prop :=
  escape s quote = s ↔ s.data.all (fun c => isSafeChar c quote) = true

theorem fixed_point_iff_safe_thm (s : String) (quote : Bool := true) :
    fixed_point_iff_safe_prop s quote := by
  unfold fixed_point_iff_safe_prop
  constructor
  · intro h
    by_contra hns
    simp only [Bool.not_eq_true] at hns
    have hlt := strict_length_of_unsafe s quote hns
    rw [h] at hlt
    omega
  · exact safe_string_id s quote

/--
Property 11 (Ampersand witness for escaped characters):
Since every HTML entity starts with `'&'` and `'&'` itself is unsafe,
`'&'` appears in `escape s quote` if and only if `s` contains at least one unsafe character.
-/
def ampersand_iff_unsafe_prop (s : String) (quote : Bool := true) : Prop :=
  '&' ∈ (escape s quote).data ↔ s.data.any (fun c => !isSafeChar c quote) = true

theorem ampersand_iff_unsafe_thm (s : String) (quote : Bool := true) :
    ampersand_iff_unsafe_prop s quote := by
  unfold ampersand_iff_unsafe_prop
  rw [char_spec_thm s quote, List.mem_flatMap, List.any_eq_true]
  constructor
  · rintro ⟨c, hcs, hc⟩
    refine ⟨c, hcs, ?_⟩
    cases quote <;>
    · by_cases h1 : c = '&'; · subst h1; decide
      by_cases h2 : c = '<'; · subst h2; decide
      by_cases h3 : c = '>'; · subst h3; decide
      by_cases h4 : c = '"'; · subst h4; revert hc; decide
      by_cases h5 : c = '\''; · subst h5; revert hc; decide
      simp [escapeChar, h1, h2, h3, h4, h5, eq_comm] at hc
  · rintro ⟨c, hcs, hc⟩
    refine ⟨c, hcs, ?_⟩
    cases quote <;>
    · by_cases h1 : c = '&'; · subst h1; decide
      by_cases h2 : c = '<'; · subst h2; decide
      by_cases h3 : c = '>'; · subst h3; decide
      by_cases h4 : c = '"'; · subst h4; revert hc; decide
      by_cases h5 : c = '\''; · subst h5; revert hc; decide
      simp [isSafeChar, h1, h2, h3, h4, h5] at hc

/-- Helper lemma: each escaped character has 1 ampersand iff unsafe, else 0. -/
theorem escapeChar_count_amp (c : Char) (quote : Bool) :
    (escapeChar c quote).data.count '&' = if !isSafeChar c quote then 1 else 0 := by
  cases quote <;>
  · by_cases h1 : c = '&'; · subst h1; decide
    by_cases h2 : c = '<'; · subst h2; decide
    by_cases h3 : c = '>'; · subst h3; decide
    by_cases h4 : c = '"'; · subst h4; decide
    by_cases h5 : c = '\''; · subst h5; decide
    simp [escapeChar, isSafeChar, h1, h2, h3, h4, h5]

/--
Property 12 (Exact ampersand count / No double-escaping):
The number of `'&'` characters in `escape s quote` equals the number of unsafe characters in `s`.
-/
def ampersand_count_prop (s : String) (quote : Bool := true) : Prop :=
  (escape s quote).data.count '&' = s.data.countP (fun c => !isSafeChar c quote)

theorem ampersand_count_thm (s : String) (quote : Bool := true) :
    ampersand_count_prop s quote := by
  unfold ampersand_count_prop
  rw [char_spec_thm s quote]
  induction s.data with
  | nil => simp
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.count_append, List.countP_cons, ih,
      escapeChar_count_amp]
    omega

/--
Property 13 (Relationship between `quote = true` and `quote = false`):
Escaping with `quote = true` is equal to escaping with `quote = false` followed by
replacing `"` and `'`.
-/
def quote_mode_relation_prop (s : String) : Prop :=
  escape s true = replaceChar (replaceChar (escape s false) '"' "&quot;") '\'' "&#x27;"

theorem quote_mode_relation_thm (s : String) : quote_mode_relation_prop s := by
  rfl

/-! ## 8. Post-condition -/

/--
Full post-condition for `escape s quote` combining all specification properties.
-/
def Post_prop (s : String) (quote : Bool := true) : Prop :=
  char_spec_prop s quote ∧
  no_angle_brackets_prop s quote ∧
  quote_dispatch_prop s quote ∧
  length_bounds_prop s quote ∧
  exact_length_prop s quote ∧
  fixed_point_iff_safe_prop s quote ∧
  ampersand_iff_unsafe_prop s quote ∧
  ampersand_count_prop s quote ∧
  quote_mode_relation_prop s

/-! ## 9. Property-Based Tests (PBTs) -/

/-- Executable Boolean form of `Post_prop` for property-based testing. -/
def check_post_b (s : String) (quote : Bool) : Bool :=
  let res := escape s quote
  let char_spec_b := decide (res.data = s.data.flatMap (fun c => (escapeChar c quote).data))
  let no_angle_b := decide ('<' ∉ res.data ∧ '>' ∉ res.data)
  let quote_dispatch_b :=
    if quote then
      decide ('"' ∉ res.data ∧ '\'' ∉ res.data)
    else
      decide ((res.data.contains '"' = s.data.contains '"') ∧
              (res.data.contains '\'' = s.data.contains '\''))
  let length_bounds_b := decide (s.length ≤ res.length ∧ res.length ≤ 6 * s.length)
  let exact_length_b :=
    decide (res.length =
      s.length + 4 * s.data.count '&' + 3 * s.data.count '<' + 3 * s.data.count '>' +
      (if quote then 5 * s.data.count '"' + 5 * s.data.count '\'' else 0))
  let fixed_point_b := decide ((res = s) ↔ s.data.all (fun c => isSafeChar c quote) = true)
  let ampersand_b := decide (res.data.contains '&' = s.data.any (fun c => !isSafeChar c quote))
  let ampersand_count_b := decide (res.data.count '&' = s.data.countP (fun c => !isSafeChar c quote))
  let quote_rel_b := decide (escape s true = replaceChar (replaceChar (escape s false) '"' "&quot;") '\'' "&#x27;")
  char_spec_b && no_angle_b && quote_dispatch_b && length_bounds_b && exact_length_b &&
    fixed_point_b && ampersand_b && ampersand_count_b && quote_rel_b

-- Randomized Property-Based Tests via Plausible
#eval Plausible.Testable.check (∀ (s : String) (quote : Bool),
  (escape s quote).data = s.data.flatMap (fun c => (escapeChar c quote).data))

#eval Plausible.Testable.check (∀ (quote : Bool),
  escape "" quote = "")

#eval Plausible.Testable.check (∀ (s₁ s₂ : String) (quote : Bool),
  escape (s₁ ++ s₂) quote = escape s₁ quote ++ escape s₂ quote)

#eval Plausible.Testable.check (∀ (s : String) (quote : Bool),
  !((escape s quote).data.contains '<') = true ∧ !((escape s quote).data.contains '>') = true)

#eval Plausible.Testable.check (∀ (s : String),
  !((escape s true).data.contains '"') = true ∧ !((escape s true).data.contains '\'') = true)

#eval Plausible.Testable.check (∀ (s : String),
  ((escape s false).data.contains '"' = s.data.contains '"') ∧
  ((escape s false).data.contains '\'' = s.data.contains '\''))

#eval Plausible.Testable.check (∀ (s : String) (quote : Bool),
  s.length ≤ (escape s quote).length ∧ (escape s quote).length ≤ 6 * s.length)

#eval Plausible.Testable.check (∀ (s : String) (quote : Bool),
  (escape s quote).length =
    s.length + 4 * s.data.count '&' + 3 * s.data.count '<' + 3 * s.data.count '>' +
    (if quote then 5 * s.data.count '"' + 5 * s.data.count '\'' else 0))

#eval Plausible.Testable.check (∀ (s : String) (quote : Bool),
  (escape s quote == s) = s.data.all (fun c => isSafeChar c quote))

#eval Plausible.Testable.check (∀ (s : String) (quote : Bool),
  (escape s quote).data.contains '&' = s.data.any (fun c => !isSafeChar c quote))

#eval Plausible.Testable.check (∀ (s : String) (quote : Bool),
  (escape s quote).data.count '&' = s.data.countP (fun c => !isSafeChar c quote))

#eval Plausible.Testable.check (∀ (s : String),
  escape s true = replaceChar (replaceChar (escape s false) '"' "&quot;") '\'' "&#x27;")

#eval Plausible.Testable.check (∀ (s : String) (quote : Bool),
  check_post_b s quote = true)

-- Bounded exhaustive PBT over strings built from HTML special characters and regular characters
def pbtAlphabet : List Char := ['&', '<', '>', '"', '\'', 'a']

def pbtStrings : List String :=
  let len0 : List (List Char) := [[]]
  let len1 := pbtAlphabet.map (fun c => [c])
  let len2 := pbtAlphabet.flatMap (fun c₁ => pbtAlphabet.map (fun c₂ => [c₁, c₂]))
  let len3 := pbtAlphabet.flatMap (fun c₁ =>
    pbtAlphabet.flatMap (fun c₂ => pbtAlphabet.map (fun c₃ => [c₁, c₂, c₃])))
  (len0 ++ len1 ++ len2 ++ len3).map String.mk

example : pbtStrings.all (fun s => check_post_b s true && check_post_b s false) = true := by
  native_decide

example : pbtStrings.all (fun s₁ =>
    (pbtStrings.take 20).all (fun s₂ =>
      (escape (s₁ ++ s₂) true == escape s₁ true ++ escape s₂ true) &&
      (escape (s₁ ++ s₂) false == escape s₁ false ++ escape s₂ false))) = true := by
  native_decide

/-! ## 10. Correctness Theorem (`Pre → Post`) -/

theorem escape_correct (s : String) (quote : Bool := true) (_hPre : Pre s quote) :
    Post_prop s quote :=
  ⟨char_spec_thm s quote,
   no_angle_brackets_thm s quote,
   quote_dispatch_thm s quote,
   length_bounds_thm s quote,
   exact_length_thm s quote,
   fixed_point_iff_safe_thm s quote,
   ampersand_iff_unsafe_thm s quote,
   ampersand_count_thm s quote,
   quote_mode_relation_thm s⟩

theorem benchmark_escape_correct (s : String) (quote : Bool := true) (hPre : Pre s quote) :
    Post_prop s quote :=
  escape_correct s quote hPre

/-! ## 11. Imperative Implementation -/

/--
Imperative implementation of `escape` using `Id.run do` and mutable state.
Iterates over the characters of `s` and accumulates the escaped string.
-/
def escape_imp (s : String) (quote : Bool := true) : String := Id.run do
  let mut acc : String := ""
  for c in s.data do
    if c = '&' then
      acc := acc ++ "&amp;"
    else if c = '<' then
      acc := acc ++ "&lt;"
    else if c = '>' then
      acc := acc ++ "&gt;"
    else if quote && c = '"' then
      acc := acc ++ "&quot;"
    else if quote && c = '\'' then
      acc := acc ++ "&#x27;"
    else
      acc := acc ++ String.mk [c]
  return acc

/-- Imperative benchmark entry point. -/
def benchmark_escape_imp (s : String) (quote : Bool := true) : String :=
  escape_imp s quote

/-! ## 12. Imperative Tests -/

-- 1. Quote=True (Default)
example : escape_imp "<b>\"&'</b>" = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by native_decide
example : escape_imp "" = "" := by native_decide

-- 2. Quote=False
example : escape_imp "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by native_decide

-- 3. Order check
example : escape_imp "&<" = "&amp;&lt;" := by native_decide

-- 4. Full check suite on imperative implementation
example : check (fun s q => escape_imp s q) = true := by native_decide
example : check (fun s q => benchmark_escape_imp s q) = true := by native_decide
example : pbtStrings.all (fun s =>
    (escape s true == escape_imp s true) && (escape s false == escape_imp s false)) = true := by
  native_decide

#eval escape_imp "<b>\"&'</b>"
#eval escape_imp ""
#eval escape_imp "<b>\"&'</b>" false
#eval escape_imp "&<"
#eval check (fun s q => escape_imp s q)

#eval Plausible.Testable.check (∀ (s : String) (quote : Bool),
  escape s quote = escape_imp s quote)

/-! ## 13. Equivalence Theorem (Functional = Imperative) -/

/-- Loop invariant lemma for `escape_imp`. -/
theorem escape_imp_loop (cs : List Char) (acc : String) (quote : Bool) :
    (Id.run do
      let mut acc : String := acc
      for c in cs do
        if c = '&' then
          acc := acc ++ "&amp;"
        else if c = '<' then
          acc := acc ++ "&lt;"
        else if c = '>' then
          acc := acc ++ "&gt;"
        else if quote && c = '"' then
          acc := acc ++ "&quot;"
        else if quote && c = '\'' then
          acc := acc ++ "&#x27;"
        else
          acc := acc ++ String.mk [c]
      return acc).data = acc.data ++ cs.flatMap (fun c => (escapeChar c quote).data) := by
  induction cs generalizing acc with
  | nil => simp
  | cons c cs ih =>
    simp only [Id.run, bind, pure] at ih
    simp only [List.forIn_cons, Id.run, bind, pure, List.flatMap_cons, escapeChar]
    split_ifs <;> simp only [ih, String.data_append, List.append_assoc] <;> rfl

/--
Equivalence theorem proving that the functional implementation `escape`
and the imperative implementation `escape_imp` produce identical results
for all inputs `s` and `quote`.
-/
theorem escape_equiv (s : String) (quote : Bool := true) :
    escape s quote = escape_imp s quote := by
  apply String.ext
  rw [char_spec_thm s quote]
  unfold escape_imp
  have h := escape_imp_loop s.data "" quote
  simpa using h.symm

theorem benchmark_escape_equiv (s : String) (quote : Bool := true) :
    benchmark_escape s quote = benchmark_escape_imp s quote :=
  escape_equiv s quote

end «20_html_escape»
