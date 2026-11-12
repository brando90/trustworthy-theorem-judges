import Mathlib

/-!
# Translation of Python `shlex.quote` to Lean 4

This module formalizes Python's `shlex.quote` function, which returns a shell-escaped
version of a string `s` suitable for POSIX shells:
- If `s` is empty, it returns `"''"`.
- If every character of `s` is in the POSIX safe character set
  (ASCII letters, digits, and the punctuation characters `_@%+=:,./` and `-`),
  it returns `s` unchanged.
- Otherwise, it wraps `s` in single quotes `'...'` and replaces each single quote `'`
  in `s` with `"'\"'\"'"`.
-/

namespace «21_shlex_quote»

-- ============================================================================
-- 4. Implementation (functional definition)
-- ============================================================================

/-- The set of safe characters for POSIX shells that do not require escaping. -/
def safe_chars : List Char :=
  "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_@%+=:,./-".data

/-- Boolean predicate checking whether a character is in `safe_chars`. -/
def is_safe_char (c : Char) : Bool :=
  safe_chars.contains c

/-- Boolean predicate checking whether all characters in string `s` are safe. -/
def all_safe (s : String) : Bool :=
  s.data.all is_safe_char

/-- Escape sequence `"'\"'\"'"` used to replace a single quote inside single-quoted strings. -/
def single_quote_escape : String :=
  "'\"'\"'"

/-- Replace every occurrence of `'` in `s` with `"'\"'\"'"`. -/
def replace_single_quotes (s : String) : String :=
  String.mk (s.data.flatMap (fun c => if c == '\'' then single_quote_escape.data else [c]))

/-- Return a shell-escaped version of the string `s`. -/
def quote (s : String) : String :=
  if s = "" then
    "''"
  else if all_safe s then
    s
  else
    "'" ++ replace_single_quotes s ++ "'"

/-- Executable pre-condition check (`isinstance(s, str)` holds statically for `s : String`). -/
def pre_quote (_s : String) : Bool :=
  true

/-- Main benchmark function to be verified. -/
def benchmark_quote (s : String) : String :=
  if !pre_quote s then
    ""
  else
    quote s

/-- Test harness translating Python's `check(quote_cand)`. -/
def check (quote_cand : String → String) : Bool :=
  (quote_cand "" == "''") &&
  (quote_cand "abc" == "abc") &&
  (quote_cand "a b c" == "'a b c'") &&
  (quote_cand "a'b" == "'a'\"'\"'b'")

-- ============================================================================
-- 5. Unit tests
-- ============================================================================

-- 1. Test empty string
example : quote "" = "''" := by native_decide
example : benchmark_quote "" = "''" := by native_decide

-- 2. Test safe string
example : quote "abc" = "abc" := by native_decide
example : benchmark_quote "abc" = "abc" := by native_decide
example : quote "AZ_09@%+=:,./-" = "AZ_09@%+=:,./-" := by native_decide

-- 3. Test string with spaces
example : quote "a b c" = "'a b c'" := by native_decide
example : benchmark_quote "a b c" = "'a b c'" := by native_decide

-- 4. Test string with quotes
example : quote "a'b" = "'a'\"'\"'b'" := by native_decide
example : benchmark_quote "a'b" = "'a'\"'\"'b'" := by native_decide
example : quote "'" = "''\"'\"''" := by native_decide

-- 5. Test `check` harness
example : check quote = true := by native_decide
example : check benchmark_quote = true := by native_decide

#eval quote ""
#eval quote "abc"
#eval quote "a b c"
#eval quote "a'b"
#eval check benchmark_quote

-- ============================================================================
-- 6. Pre-condition predicate
-- ============================================================================

/-- Pre-condition for `quote`: in Lean, `s : String` is guaranteed by the type system. -/
@[reducible]
def Pre (_s : String) : Prop :=
  True

theorem pre_quote_iff_Pre (s : String) : pre_quote s = true ↔ Pre s := by
  simp [pre_quote, Pre]

-- ============================================================================
-- 7. Property propositions and theorems
-- ============================================================================

theorem single_quote_escape_data :
    single_quote_escape.data = ['\'', '"', '\'', '"', '\''] := rfl

theorem single_quote_escape_length :
    single_quote_escape.length = 5 := rfl

theorem replace_single_quotes_data (s : String) :
    (replace_single_quotes s).data =
      s.data.flatMap (fun c => if c == '\'' then single_quote_escape.data else [c]) := rfl

theorem string_length_append (a b : String) :
    (a ++ b).length = a.length + b.length := by
  rw [← String.length_data, String.data_append, List.length_append, String.length_data, String.length_data]

theorem flatMap_escape_length (cs : List Char) :
    (cs.flatMap (fun c => if c == '\'' then single_quote_escape.data else [c])).length =
      cs.length + 4 * cs.count '\'' := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.count_cons, ih]
    by_cases h : c = '\''
    · subst h
      simp [single_quote_escape_data]
      omega
    · have hbeq : (c == '\'') = false := beq_false_of_ne h
      simp [hbeq]
      omega

theorem replace_single_quotes_length (s : String) :
    (replace_single_quotes s).length = s.length + 4 * s.data.count '\'' := by
  rw [← String.length_data, replace_single_quotes_data, flatMap_escape_length, String.length_data]

theorem length_le_replace_single_quotes_length (s : String) :
    s.length ≤ (replace_single_quotes s).length := by
  rw [replace_single_quotes_length]
  omega

theorem flatMap_escape_eq_self {cs : List Char} (h : '\'' ∉ cs) :
    cs.flatMap (fun c => if c == '\'' then single_quote_escape.data else [c]) = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.mem_cons, not_or] at h
    have hne : c ≠ '\'' := Ne.symm h.1
    have hbeq : (c == '\'') = false := beq_false_of_ne hne
    simp only [List.flatMap_cons, hbeq, Bool.false_eq_true, ↓reduceIte, List.cons_append,
      List.nil_append, ih h.2]

theorem replace_single_quotes_eq_self {s : String} (h : '\'' ∉ s.data) :
    replace_single_quotes s = s := by
  apply String.ext
  rw [replace_single_quotes_data]
  exact flatMap_escape_eq_self h

theorem mem_replace_single_quotes_of_mem {s : String} {c : Char} (h : c ∈ s.data) :
    c ∈ (replace_single_quotes s).data := by
  rw [replace_single_quotes_data, List.mem_flatMap]
  refine ⟨c, h, ?_⟩
  by_cases hc : c = '\''
  · subst hc
    simp [single_quote_escape_data]
  · have hbeq : (c == '\'') = false := beq_false_of_ne hc
    simp [hbeq]

theorem mem_replace_single_quotes_char {s : String} {c : Char}
    (h : c ∈ (replace_single_quotes s).data) :
    c ∈ s.data ∨ c = '\'' ∨ c = '"' := by
  rw [replace_single_quotes_data, List.mem_flatMap] at h
  rcases h with ⟨x, hx, hcx⟩
  by_cases hxq : x = '\''
  · subst hxq
    simp only [beq_self_eq_true, ↓reduceIte, single_quote_escape_data, List.mem_cons,
      List.not_mem_nil, or_false] at hcx
    rcases hcx with rfl | rfl | rfl | rfl | rfl <;> tauto
  · have hbeq : (x == '\'') = false := beq_false_of_ne hxq
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hcx
    subst hcx
    exact Or.inl hx

theorem single_quote_not_safe : is_safe_char '\'' = false := rfl

theorem all_safe_false_of_mem_single_quote {s : String} (h : '\'' ∈ s.data) :
    all_safe s = false := by
  cases hall : all_safe s
  · rfl
  · exfalso
    rw [all_safe, List.all_eq_true] at hall
    have hsafe := hall '\'' h
    rw [single_quote_not_safe] at hsafe
    contradiction

-- Property 1: Empty string produces `"''"`
@[reducible]
def quote_empty_prop (s : String) : Prop :=
  s = "" → quote s = "''"

theorem quote_empty_thm (s : String) : quote_empty_prop s := by
  intro h
  simp [quote, h]

-- Property 2: Non-empty safe string is returned unchanged
@[reducible]
def quote_safe_prop (s : String) : Prop :=
  s ≠ "" → all_safe s = true → quote s = s

theorem quote_safe_thm (s : String) : quote_safe_prop s := by
  intro hne hsafe
  simp [quote, hne, hsafe]

-- Property 3: Non-empty unsafe string is wrapped in single quotes with single quotes escaped
@[reducible]
def quote_unsafe_prop (s : String) : Prop :=
  s ≠ "" → all_safe s = false → quote s = "'" ++ replace_single_quotes s ++ "'"

theorem quote_unsafe_thm (s : String) : quote_unsafe_prop s := by
  intro hne hunsafe
  simp [quote, hne, hunsafe]

-- Property 4: Non-empty unsafe string without single quotes is simply wrapped in `'...'`
@[reducible]
def quote_unsafe_no_single_quote_prop (s : String) : Prop :=
  s ≠ "" → all_safe s = false → '\'' ∉ s.data → quote s = "'" ++ s ++ "'"

theorem quote_unsafe_no_single_quote_thm (s : String) :
    quote_unsafe_no_single_quote_prop s := by
  intro hne hunsafe hnoq
  rw [quote_unsafe_thm s hne hunsafe, replace_single_quotes_eq_self hnoq]

-- Property 5: Exact length specification across all three branches
@[reducible]
def quote_length_prop (s : String) : Prop :=
  (s = "" → (quote s).length = 2) ∧
  (s ≠ "" → all_safe s = true → (quote s).length = s.length) ∧
  (s ≠ "" → all_safe s = false → (quote s).length = s.length + 2 + 4 * s.data.count '\'')

theorem quote_length_thm (s : String) : quote_length_prop s := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    rw [quote_empty_thm s h]
    rfl
  · intro hne hsafe
    rw [quote_safe_thm s hne hsafe]
  · intro hne hunsafe
    rw [quote_unsafe_thm s hne hunsafe]
    rw [string_length_append, string_length_append, replace_single_quotes_length]
    have h1 : ("'" : String).length = 1 := rfl
    omega

-- Property 6: Quoting never decreases the length of the string
@[reducible]
def quote_length_ge_prop (s : String) : Prop :=
  (quote s).length ≥ s.length

theorem quote_length_ge_thm (s : String) : quote_length_ge_prop s := by
  unfold quote_length_ge_prop
  obtain ⟨h1, h2, h3⟩ := quote_length_thm s
  by_cases hs : s = ""
  · rw [h1 hs, hs]
    decide
  · cases hsafe : all_safe s
    · rw [h3 hs hsafe]
      omega
    · rw [h2 hs hsafe]

-- Property 7: The quoted output is never the empty string
@[reducible]
def quote_nonempty_prop (s : String) : Prop :=
  quote s ≠ ""

theorem quote_nonempty_thm (s : String) : quote_nonempty_prop s := by
  intro h
  have hlen : (quote s).length = 0 := by rw [h]; rfl
  obtain ⟨h1, h2, h3⟩ := quote_length_thm s
  by_cases hs : s = ""
  · have := h1 hs
    omega
  · cases hsafe : all_safe s
    · have := h3 hs hsafe
      omega
    · have hq : quote s = s := quote_safe_thm s hs hsafe
      rw [hq] at h
      exact hs h

-- Property 8: Fixed-point characterization (`quote s = s` iff `s` is non-empty and safe)
@[reducible]
def quote_fixed_point_prop (s : String) : Prop :=
  quote s = s ↔ (s ≠ "" ∧ all_safe s = true)

theorem quote_fixed_point_thm (s : String) : quote_fixed_point_prop s := by
  constructor
  · intro h
    by_cases hs : s = ""
    · subst hs
      revert h
      decide
    · refine ⟨hs, ?_⟩
      cases hsafe : all_safe s
      · exfalso
        have hlen := (quote_length_thm s).2.2 hs hsafe
        rw [h] at hlen
        omega
      · rfl
  · rintro ⟨hne, hsafe⟩
    exact quote_safe_thm s hne hsafe

-- Property 9: Non-safe or empty strings are enclosed in single-quote delimiters
@[reducible]
def quote_delimiters_prop (s : String) : Prop :=
  (s = "" ∨ all_safe s = false) → ∃ mid : String, quote s = "'" ++ mid ++ "'"

theorem quote_delimiters_thm (s : String) : quote_delimiters_prop s := by
  intro h
  by_cases hs : s = ""
  · refine ⟨"", ?_⟩
    rw [quote_empty_thm s hs]
    rfl
  · rcases h with rfl | hunsafe
    · contradiction
    · exact ⟨replace_single_quotes s, quote_unsafe_thm s hs hunsafe⟩

theorem single_quote_mem_quote_of_not_safe {s : String} (h : s = "" ∨ all_safe s = false) :
    '\'' ∈ (quote s).data := by
  obtain ⟨mid, hmid⟩ := quote_delimiters_thm s h
  rw [hmid, String.data_append, String.data_append]
  simp

theorem all_safe_quote_iff_thm (s : String) :
    all_safe (quote s) = true ↔ (s ≠ "" ∧ all_safe s = true) := by
  constructor
  · intro h
    by_cases hs : s = ""
    · have hmem : '\'' ∈ (quote s).data := single_quote_mem_quote_of_not_safe (Or.inl hs)
      have hfalse := all_safe_false_of_mem_single_quote hmem
      rw [h] at hfalse
      contradiction
    · refine ⟨hs, ?_⟩
      cases hsafe : all_safe s
      · have hmem : '\'' ∈ (quote s).data := single_quote_mem_quote_of_not_safe (Or.inr hsafe)
        have hfalse := all_safe_false_of_mem_single_quote hmem
        rw [h] at hfalse
        contradiction
      · rfl
  · rintro ⟨hne, hsafe⟩
    rw [quote_safe_thm s hne hsafe]
    exact hsafe

-- Property 10: Idempotence characterization (`quote (quote s) = quote s` iff `s` is non-empty and safe)
@[reducible]
def quote_idempotent_prop (s : String) : Prop :=
  quote (quote s) = quote s ↔ (s ≠ "" ∧ all_safe s = true)

theorem quote_idempotent_thm (s : String) : quote_idempotent_prop s := by
  unfold quote_idempotent_prop
  have hfp : quote (quote s) = quote s ↔ (quote s ≠ "" ∧ all_safe (quote s) = true) := quote_fixed_point_thm (quote s)
  have hne : quote s ≠ "" := quote_nonempty_thm s
  have hsafe : all_safe (quote s) = true ↔ (s ≠ "" ∧ all_safe s = true) := all_safe_quote_iff_thm s
  tauto

-- Property 11: Every character of `s` is preserved in `quote s`
@[reducible]
def quote_char_preserves_prop (s : String) : Prop :=
  ∀ c ∈ s.data, c ∈ (quote s).data

theorem quote_char_preserves_thm (s : String) : quote_char_preserves_prop s := by
  intro c hc
  by_cases hs : s = ""
  · subst hs
    simp at hc
  · cases hsafe : all_safe s
    · rw [quote_unsafe_thm s hs hsafe, String.data_append, String.data_append]
      simp only [List.mem_append]
      exact Or.inl (Or.inr (mem_replace_single_quotes_of_mem hc))
    · rw [quote_safe_thm s hs hsafe]
      exact hc

-- Property 12: Every character in `quote s` comes from `s` or is a quote character (`'` or `"`)
@[reducible]
def quote_char_origin_prop (s : String) : Prop :=
  ∀ c ∈ (quote s).data, c ∈ s.data ∨ c = '\'' ∨ c = '"'

theorem quote_char_origin_thm (s : String) : quote_char_origin_prop s := by
  intro c hc
  by_cases hs : s = ""
  · rw [quote_empty_thm s hs] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact Or.inr (Or.inl rfl)
  · cases hsafe : all_safe s
    · rw [quote_unsafe_thm s hs hsafe, String.data_append, String.data_append] at hc
      simp only [List.mem_append] at hc
      rcases hc with (hc1 | hc2) | hc3
      · simp only [List.mem_singleton] at hc1
        exact Or.inr (Or.inl hc1)
      · exact mem_replace_single_quotes_char hc2
      · simp only [List.mem_singleton] at hc3
        exact Or.inr (Or.inl hc3)
    · rw [quote_safe_thm s hs hsafe] at hc
      exact Or.inl hc

-- Property 13: `benchmark_quote` agrees with `quote`
@[reducible]
def benchmark_quote_eq_quote_prop (s : String) : Prop :=
  benchmark_quote s = quote s

theorem benchmark_quote_eq_quote_thm (s : String) : benchmark_quote_eq_quote_prop s := by
  rfl

-- ============================================================================
-- 8. Post-condition as conjunction of properties
-- ============================================================================

/-- Full post-condition combining all specification properties of `quote` and `benchmark_quote`. -/
@[reducible]
def Post_prop (s : String) : Prop :=
  quote_empty_prop s ∧
  quote_safe_prop s ∧
  quote_unsafe_prop s ∧
  quote_unsafe_no_single_quote_prop s ∧
  quote_length_prop s ∧
  quote_length_ge_prop s ∧
  quote_nonempty_prop s ∧
  quote_fixed_point_prop s ∧
  quote_delimiters_prop s ∧
  quote_idempotent_prop s ∧
  quote_char_preserves_prop s ∧
  quote_char_origin_prop s ∧
  benchmark_quote_eq_quote_prop s

-- ============================================================================
-- 9. Property-based tests
-- ============================================================================

/-- Helper to construct safe strings from arbitrary indices for randomized testing. -/
def mk_safe_string (idxs : List Nat) : String :=
  String.mk (idxs.map (fun i => safe_chars.getD (i % safe_chars.length) 'a'))

/-- Executable Boolean check for `quote_empty_prop`. -/
def quote_empty_check (s : String) : Bool :=
  !(s == "") || (quote s == "''")

/-- Executable Boolean check for `quote_safe_prop`. -/
def quote_safe_check (s : String) : Bool :=
  (s == "") || !all_safe s || (quote s == s)

/-- Executable Boolean check for `quote_unsafe_prop`. -/
def quote_unsafe_check (s : String) : Bool :=
  (s == "") || all_safe s || (quote s == "'" ++ replace_single_quotes s ++ "'")

/-- Executable Boolean check for `quote_unsafe_no_single_quote_prop`. -/
def quote_unsafe_no_single_quote_check (s : String) : Bool :=
  (s == "") || all_safe s || s.data.contains '\'' || (quote s == "'" ++ s ++ "'")

/-- Executable Boolean check for `quote_length_prop`. -/
def quote_length_check (s : String) : Bool :=
  ((!(s == "") || (quote s).length == 2)) &&
  ((s == "") || !all_safe s || ((quote s).length == s.length)) &&
  ((s == "") || all_safe s || ((quote s).length == s.length + 2 + 4 * s.data.count '\''))

/-- Executable Boolean check for `quote_length_ge_prop`. -/
def quote_length_ge_check (s : String) : Bool :=
  decide ((quote s).length ≥ s.length)

/-- Executable Boolean check for `quote_nonempty_prop`. -/
def quote_nonempty_check (s : String) : Bool :=
  quote s != ""

/-- Executable Boolean check for `quote_fixed_point_prop`. -/
def quote_fixed_point_check (s : String) : Bool :=
  (quote s == s) == ((s != "") && all_safe s)

/-- Executable Boolean check for `quote_delimiters_prop`. -/
def quote_delimiters_check (s : String) : Bool :=
  (!((s == "") || !all_safe s)) ||
  ((quote s).startsWith "'" && (quote s).endsWith "'" && decide ((quote s).length ≥ 2))

/-- Executable Boolean check for `quote_idempotent_prop`. -/
def quote_idempotent_check (s : String) : Bool :=
  (quote (quote s) == quote s) == ((s != "") && all_safe s)

/-- Executable Boolean check for `quote_char_preserves_prop`. -/
def quote_char_preserves_check (s : String) : Bool :=
  s.data.all (fun c => (quote s).data.contains c)

/-- Executable Boolean check for `quote_char_origin_prop`. -/
def quote_char_origin_check (s : String) : Bool :=
  (quote s).data.all (fun c => s.data.contains c || c == '\'' || c == '"')

/-- Executable Boolean check for `benchmark_quote_eq_quote_prop`. -/
def benchmark_quote_eq_quote_check (s : String) : Bool :=
  benchmark_quote s == quote s

/-- Executable Boolean check for `Post_prop`. -/
def Post_check (s : String) : Bool :=
  quote_empty_check s &&
  quote_safe_check s &&
  quote_unsafe_check s &&
  quote_unsafe_no_single_quote_check s &&
  quote_length_check s &&
  quote_length_ge_check s &&
  quote_nonempty_check s &&
  quote_fixed_point_check s &&
  quote_delimiters_check s &&
  quote_idempotent_check s &&
  quote_char_preserves_check s &&
  quote_char_origin_check s &&
  benchmark_quote_eq_quote_check s

-- Randomized Property-Based Tests (Plausible)
#eval Plausible.Testable.check (∀ s : String, quote_empty_check s = true)
#eval Plausible.Testable.check (∀ s : String, quote_safe_check s = true)
#eval Plausible.Testable.check (∀ idxs : List Nat, quote_safe_check (mk_safe_string idxs) = true)
#eval Plausible.Testable.check (∀ s : String, quote_unsafe_check s = true)
#eval Plausible.Testable.check (∀ s : String, quote_unsafe_no_single_quote_check s = true)
#eval Plausible.Testable.check (∀ s : String, quote_length_check s = true)
#eval Plausible.Testable.check (∀ s : String, quote_length_ge_check s = true)
#eval Plausible.Testable.check (∀ s : String, quote_nonempty_check s = true)
#eval Plausible.Testable.check (∀ s : String, quote_fixed_point_check s = true)
#eval Plausible.Testable.check (∀ idxs : List Nat, quote_fixed_point_check (mk_safe_string idxs) = true)
#eval Plausible.Testable.check (∀ s : String, quote_delimiters_check s = true)
#eval Plausible.Testable.check (∀ s : String, quote_idempotent_check s = true)
#eval Plausible.Testable.check (∀ idxs : List Nat, quote_idempotent_check (mk_safe_string idxs) = true)
#eval Plausible.Testable.check (∀ s : String, quote_char_preserves_check s = true)
#eval Plausible.Testable.check (∀ s : String, quote_char_origin_check s = true)
#eval Plausible.Testable.check (∀ s : String, benchmark_quote_eq_quote_check s = true)
#eval Plausible.Testable.check (∀ s : String, Post_check s = true)
#eval Plausible.Testable.check (∀ idxs : List Nat, Post_check (mk_safe_string idxs) = true)

-- Bounded Property-Based Tests across representative corpus
def pbt_corpus : List String := [
  "",
  "a",
  "abc",
  "0123456789",
  "_@%+=:,.-/",
  "/usr/local/bin/env",
  "file_name-1.2.3:4@host",
  " ",
  "a b c",
  "'",
  "''",
  "a'b",
  "'a'b'",
  "\"hello\"",
  "it's a \"test\"!",
  "$HOME/path; rm -rf *",
  "line1\nline2\ttab",
  "a|b&c<d>e(f)"
]

example : pbt_corpus.all quote_empty_check = true := by native_decide
example : pbt_corpus.all quote_safe_check = true := by native_decide
example : pbt_corpus.all quote_unsafe_check = true := by native_decide
example : pbt_corpus.all quote_unsafe_no_single_quote_check = true := by native_decide
example : pbt_corpus.all quote_length_check = true := by native_decide
example : pbt_corpus.all quote_length_ge_check = true := by native_decide
example : pbt_corpus.all quote_nonempty_check = true := by native_decide
example : pbt_corpus.all quote_fixed_point_check = true := by native_decide
example : pbt_corpus.all quote_delimiters_check = true := by native_decide
example : pbt_corpus.all quote_idempotent_check = true := by native_decide
example : pbt_corpus.all quote_char_preserves_check = true := by native_decide
example : pbt_corpus.all quote_char_origin_check = true := by native_decide
example : pbt_corpus.all benchmark_quote_eq_quote_check = true := by native_decide
example : pbt_corpus.all Post_check = true := by native_decide

-- ============================================================================
-- 10. Correctness theorem: Pre -> Post
-- ============================================================================

theorem quote_correctness_thm (s : String) (_hpre : Pre s) : Post_prop s :=
  ⟨quote_empty_thm s,
   quote_safe_thm s,
   quote_unsafe_thm s,
   quote_unsafe_no_single_quote_thm s,
   quote_length_thm s,
   quote_length_ge_thm s,
   quote_nonempty_thm s,
   quote_fixed_point_thm s,
   quote_delimiters_thm s,
   quote_idempotent_thm s,
   quote_char_preserves_thm s,
   quote_char_origin_thm s,
   benchmark_quote_eq_quote_thm s⟩

-- ============================================================================
-- 11. Imperative implementation using `Id.run do` with mutable state
-- ============================================================================

/-- Imperative implementation of `replace_single_quotes` using mutable state. -/
def replace_single_quotes_imp (s : String) : String := Id.run do
  let mut escaped : List Char := []
  for c in s.data do
    if c == '\'' then
      escaped := escaped ++ single_quote_escape.data
    else
      escaped := escaped ++ [c]
  return String.mk escaped

/-- Imperative implementation of `quote` using `Id.run do` and mutable variables. -/
def quote_imp (s : String) : String := Id.run do
  if s = "" then
    return "''"
  let mut safe : Bool := true
  for c in s.data do
    safe := safe && is_safe_char c
  if safe then
    return s
  let mut escaped : List Char := []
  for c in s.data do
    if c == '\'' then
      escaped := escaped ++ single_quote_escape.data
    else
      escaped := escaped ++ [c]
  return "'" ++ String.mk escaped ++ "'"

/-- Imperative implementation of `benchmark_quote`. -/
def benchmark_quote_imp (s : String) : String := Id.run do
  if !pre_quote s then
    return ""
  return quote_imp s

-- ============================================================================
-- 12. Imperative tests
-- ============================================================================

example : quote_imp "" = "''" := by native_decide
example : quote_imp "abc" = "abc" := by native_decide
example : quote_imp "a b c" = "'a b c'" := by native_decide
example : quote_imp "a'b" = "'a'\"'\"'b'" := by native_decide
example : check quote_imp = true := by native_decide
example : check benchmark_quote_imp = true := by native_decide
example : pbt_corpus.all (fun s => quote s == quote_imp s) = true := by native_decide

#eval quote_imp ""
#eval quote_imp "abc"
#eval quote_imp "a b c"
#eval quote_imp "a'b"
#eval check benchmark_quote_imp
#eval Plausible.Testable.check (∀ s : String, quote s = quote_imp s)

-- ============================================================================
-- 13. Equivalence theorem: functional = imperative
-- ============================================================================

@[simp]
theorem ite_pure_yield {α : Type} (p : Prop) [Decidable p] (a b : α) :
    (if p then (pure (ForInStep.yield a) : Id (ForInStep α)) else pure (ForInStep.yield b)) =
      pure (ForInStep.yield (if p then a else b)) := by
  split_ifs <;> rfl

@[simp]
theorem id_run_ite {α : Type} (p : Prop) [Decidable p] (a b : Id α) :
    (if p then a else b).run = if p then a.run else b.run := by
  split_ifs <;> rfl

theorem foldl_safe_eq_all (cs : List Char) (init : Bool) :
    List.foldl (fun b c => b && is_safe_char c) init cs = (init && cs.all is_safe_char) := by
  induction cs generalizing init with
  | nil => simp
  | cons c cs ih =>
    simp [List.foldl_cons, List.all_cons, ih, Bool.and_assoc]

theorem foldl_escape_eq_flatMap (cs : List Char) (acc : List Char) :
    List.foldl (fun escaped c =>
      if c = '\'' then escaped ++ single_quote_escape.data else escaped ++ [c]) acc cs =
      acc ++ cs.flatMap (fun c => if c = '\'' then single_quote_escape.data else [c]) := by
  induction cs generalizing acc with
  | nil => simp
  | cons c cs ih =>
    simp only [List.foldl_cons, List.flatMap_cons, ih]
    by_cases h : c = '\''
    · simp [h]
    · simp [h]

theorem replace_single_quotes_equiv_thm (s : String) :
    replace_single_quotes s = replace_single_quotes_imp s := by
  simp [replace_single_quotes, replace_single_quotes_imp, foldl_escape_eq_flatMap]

theorem quote_equiv_thm (s : String) : quote s = quote_imp s := by
  simp only [quote, quote_imp, all_safe, replace_single_quotes]
  by_cases hs : s = ""
  · simp [hs]
  · simp [hs, foldl_safe_eq_all, foldl_escape_eq_flatMap]

theorem benchmark_quote_equiv_thm (s : String) :
    benchmark_quote s = benchmark_quote_imp s := by
  simp [benchmark_quote, benchmark_quote_imp, pre_quote, quote_equiv_thm]

end «21_shlex_quote»
