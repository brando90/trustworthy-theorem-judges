import Mathlib

/-!
# Shell-Escaping a String (`shlex.quote`)

Formalization of Python's `shlex.quote` function from the standard `shlex` library.
Given an input string `s`, `quote` returns a shell-escaped version suitable for POSIX shells:
1. If `s` is empty (`""`), it returns `"''"`.
2. If `s` is non-empty and every character in `s` belongs to the POSIX safe character set
   (`a`..`z`, `A`..`Z`, `0`..`9`, and `_`, `@`, `%`, `+`, `=`, `:`, `,`, `.`, `/`, `-`),
   it returns `s` unchanged.
3. Otherwise, it encloses `s` in single quotes `'...'` and replaces each single quote `'`
   inside `s` with the 5-character sequence `"'\"'\"'"`.
-/

namespace «21_shlex_quote»

/-! ## 4. Implementation (Functional Definition) -/

/-- The list of safe characters for POSIX shells that do not require escaping. -/
def safeChars : List Char :=
  "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_@%+=:,./-".toList

/-- Returns `true` iff `c` is a safe character for POSIX shells. -/
def isSafeChar (c : Char) : Bool :=
  decide (c ∈ safeChars)

/-- Escapes a single character for use inside a single-quoted POSIX shell string:
    `'` becomes `"'\"'\"'"`, and every other character remains `[c]`. -/
def escapeChar (c : Char) : List Char :=
  if c == '\'' then "'\"'\"'".toList else [c]

/-- Replaces every single quote `'` in `s` with `"'\"'\"'"`. -/
def replaceSingleQuotes (s : String) : String :=
  String.mk (s.toList.flatMap escapeChar)

/-- Inverse of `escapeChar` over character lists: converts each `"'\"'\"'"` sequence back to `'\''`. -/
def unescapeChars : List Char → List Char
  | [] => []
  | c :: rest =>
    if c == '\'' then
      match rest with
      | _ :: _ :: _ :: _ :: tail => '\'' :: unescapeChars tail
      | _ => ['\'']
    else
      c :: unescapeChars rest

/-- Inverse of `quote` on character lists. -/
def unquoteChars : List Char → List Char
  | [] => []
  | c :: cs => if c == '\'' then unescapeChars cs.dropLast else c :: cs

/-- Unquotes a shell-escaped string produced by `quote`. -/
def unquote (q : String) : String :=
  String.mk (unquoteChars q.toList)

/-- Functional implementation of Python's `shlex.quote`. -/
def quote (s : String) : String :=
  if s = "" then
    "''"
  else if s.toList.all isSafeChar then
    s
  else
    "'" ++ replaceSingleQuotes s ++ "'"

/-- Main function to be verified, corresponding to Python's `benchmark_quote`. -/
def benchmark_quote (s : String) : String :=
  quote s

/-! ## 5. Unit Tests -/

-- 1. Test empty string
example : quote "" = "''" := by native_decide
-- 2. Test safe string
example : quote "abc" = "abc" := by native_decide
-- 3. Test string with spaces
example : quote "a b c" = "'a b c'" := by native_decide
-- 4. Test string with quotes
example : quote "a'b" = "'a'\"'\"'b'" := by native_decide
-- 5. Additional tests on punctuation and benchmark_quote
example : quote "path/to/file_1.txt" = "path/to/file_1.txt" := by native_decide
example : quote "'" = "''\"'\"''" := by native_decide
example : benchmark_quote "a'b" = "'a'\"'\"'b'" := by native_decide

#eval quote ""
#eval quote "abc"
#eval quote "a b c"
#eval quote "a'b"
#eval benchmark_quote "a'b"

/-! ## 6. Pre-condition Predicate -/

/-- Pre-condition for `quote`: in Lean 4, the input `s : String` is statically guaranteed
    to be a string (`isinstance(s, str)`). -/
def Pre (_s : String) : Prop :=
  True

/-- Alias matching the Python `pre_quote` name. -/
abbrev pre_quote (s : String) : Prop :=
  Pre s

instance (s : String) : Decidable (Pre s) :=
  isTrue trivial

/-! ## Helper Lemmas for Properties -/

theorem toList_mk (cs : List Char) : (String.mk cs).toList = cs := rfl

theorem length_mk (cs : List Char) : (String.mk cs).length = cs.length := rfl

theorem toList_append (s₁ s₂ : String) : (s₁ ++ s₂).toList = s₁.toList ++ s₂.toList := rfl

theorem length_append (s₁ s₂ : String) : (s₁ ++ s₂).length = s₁.length + s₂.length :=
  String.length_append s₁ s₂

theorem escapeChar_length (c : Char) :
    (escapeChar c).length = 1 + (if c == '\'' then 4 else 0) := by
  unfold escapeChar
  split <;> rfl

theorem flatMap_escapeChar_length (cs : List Char) :
    (cs.flatMap escapeChar).length = cs.length + 4 * cs.count '\'' := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.length_append, ih, List.length_cons, List.count_cons,
      escapeChar_length, beq_iff_eq]
    split <;> omega

theorem replaceSingleQuotes_length (s : String) :
    (replaceSingleQuotes s).length = s.length + 4 * s.toList.count '\'' :=
  flatMap_escapeChar_length s.toList

theorem flatMap_escapeChar_eq_self {cs : List Char} (h : '\'' ∉ cs) :
    cs.flatMap escapeChar = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hc : c ≠ '\'' := fun heq => h (heq ▸ List.mem_cons_self)
    have hcs : '\'' ∉ cs := fun hm => h (List.mem_cons_of_mem c hm)
    simp [List.flatMap_cons, escapeChar, hc, ih hcs]

theorem replaceSingleQuotes_eq_self {s : String} (h : '\'' ∉ s.toList) :
    replaceSingleQuotes s = s := by
  cases s with
  | mk cs =>
    simp only [replaceSingleQuotes, toList_mk]
    congr 1
    exact flatMap_escapeChar_eq_self h

theorem isSafeChar_single_quote : isSafeChar '\'' = false := by
  decide

theorem all_isSafeChar_false_of_single_quote_mem {s : String} (h : '\'' ∈ s.toList) :
    s.toList.all isSafeChar = false := by
  rw [List.all_eq_false]
  exact ⟨'\'', h, by simp [isSafeChar_single_quote]⟩

theorem empty_all_isSafeChar : ("" : String).toList.all isSafeChar = true :=
  rfl

theorem unsafe_nonempty {s : String} (h : s.toList.all isSafeChar = false) : s ≠ "" := by
  intro hs
  subst hs
  revert h
  decide

theorem quoted_length (s : String) :
    ("'" ++ replaceSingleQuotes s ++ "'").length = s.length + 2 + 4 * s.toList.count '\'' := by
  have h1 : ("'" : String).length = 1 := rfl
  rw [length_append, length_append, h1, replaceSingleQuotes_length]
  omega

theorem getLast?_append_singleton (xs : List Char) (c : Char) :
    (xs ++ [c]).getLast? = some c := by
  simp

theorem unescapeChars_flatMap_escapeChar (cs : List Char) :
    unescapeChars (cs.flatMap escapeChar) = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    by_cases hc : c = '\''
    · subst hc
      change '\'' :: unescapeChars (cs.flatMap escapeChar) = '\'' :: cs
      rw [ih]
    · have hbeq : (c == '\'') = false := beq_false_of_ne hc
      simp only [List.flatMap_cons, escapeChar, hbeq, Bool.false_eq_true, ↓reduceIte,
        List.singleton_append]
      unfold unescapeChars
      simp [hbeq, ih]

theorem dropLast_append_singleton (xs : List Char) (c : Char) :
    (xs ++ [c]).dropLast = xs := by
  simp

/-! ## 7. Property Propositions and Theorems -/

/-- Property 1: An empty input string is escaped as `"''"`. -/
def empty_string_prop (s : String) : Prop :=
  s = "" → quote s = "''"

instance (s : String) : Decidable (empty_string_prop s) := by
  unfold empty_string_prop; infer_instance

theorem empty_string_thm (s : String) : empty_string_prop s := by
  intro hs
  simp [quote, hs]

/-- Property 2: Any non-empty string consisting exclusively of safe characters is returned unchanged. -/
def safe_nonempty_prop (s : String) : Prop :=
  s ≠ "" → s.toList.all isSafeChar = true → quote s = s

instance (s : String) : Decidable (safe_nonempty_prop s) := by
  unfold safe_nonempty_prop; infer_instance

theorem safe_nonempty_thm (s : String) : safe_nonempty_prop s := by
  intro hne hsafe
  simp only [quote, hne, hsafe, ↓reduceIte]

/-- Property 3: Any string containing at least one unsafe character is enclosed in single quotes
    with internal single quotes replaced by `"'\"'\"'"`. -/
def unsafe_string_prop (s : String) : Prop :=
  s.toList.all isSafeChar = false → quote s = "'" ++ replaceSingleQuotes s ++ "'"

instance (s : String) : Decidable (unsafe_string_prop s) := by
  unfold unsafe_string_prop; infer_instance

theorem unsafe_string_thm (s : String) : unsafe_string_prop s := by
  intro hunsafe
  have hne : s ≠ "" := unsafe_nonempty hunsafe
  simp only [quote, hne, hunsafe, Bool.false_eq_true, ↓reduceIte]

/-- Property 4: Any string with at least one unsafe character and no single quotes is simply
    wrapped in single quotes `"'" ++ s ++ "'"`. -/
def unsafe_no_single_quote_prop (s : String) : Prop :=
  s.toList.all isSafeChar = false → '\'' ∉ s.toList → quote s = "'" ++ s ++ "'"

instance (s : String) : Decidable (unsafe_no_single_quote_prop s) := by
  unfold unsafe_no_single_quote_prop; infer_instance

theorem unsafe_no_single_quote_thm (s : String) : unsafe_no_single_quote_prop s := by
  intro hunsafe hnoq
  rw [unsafe_string_thm s hunsafe, replaceSingleQuotes_eq_self hnoq]

/-- Property 5: Any string containing a single quote `'` is treated as unsafe and escaped. -/
def single_quote_escaped_prop (s : String) : Prop :=
  '\'' ∈ s.toList → quote s = "'" ++ replaceSingleQuotes s ++ "'"

instance (s : String) : Decidable (single_quote_escaped_prop s) := by
  unfold single_quote_escaped_prop; infer_instance

theorem single_quote_escaped_thm (s : String) : single_quote_escaped_prop s := by
  intro hmem
  exact unsafe_string_thm s (all_isSafeChar_false_of_single_quote_mem hmem)

/-- Property 6: The output of `quote` is never empty. -/
def nonempty_output_prop (s : String) : Prop :=
  quote s ≠ "" ∧ 0 < (quote s).length

instance (s : String) : Decidable (nonempty_output_prop s) := by
  unfold nonempty_output_prop; infer_instance

theorem nonempty_output_thm (s : String) : nonempty_output_prop s := by
  unfold nonempty_output_prop quote
  split
  · decide
  · next hne =>
    split
    · refine ⟨hne, ?_⟩
      cases s with
      | mk cs =>
        cases cs with
        | nil => contradiction
        | cons c cs =>
          change 0 < (c :: cs).length
          simp
    · have hlen := quoted_length s
      refine ⟨?_, by omega⟩
      intro heq
      have h0 : ("'" ++ replaceSingleQuotes s ++ "'").length = 0 := by
        rw [heq]; rfl
      omega

/-- Property 7: Shell-escaping never decreases the length of the string. -/
def length_ge_input_prop (s : String) : Prop :=
  s.length ≤ (quote s).length

instance (s : String) : Decidable (length_ge_input_prop s) := by
  unfold length_ge_input_prop; infer_instance

theorem length_ge_input_thm (s : String) : length_ge_input_prop s := by
  unfold length_ge_input_prop quote
  split
  · next hs =>
    subst hs
    decide
  · split
    · exact Nat.le_refl _
    · have hlen := quoted_length s
      omega

/-- Property 8: Whenever `s` is empty or contains an unsafe character, `quote s` has length at least 2
    and starts and ends with `'\''`. -/
def unsafe_or_empty_enclosing_quotes_prop (s : String) : Prop :=
  (s = "" ∨ s.toList.all isSafeChar = false) →
    2 ≤ (quote s).length ∧
    (quote s).toList.head? = some '\'' ∧
    (quote s).toList.getLast? = some '\''

instance (s : String) : Decidable (unsafe_or_empty_enclosing_quotes_prop s) := by
  unfold unsafe_or_empty_enclosing_quotes_prop; infer_instance

theorem unsafe_or_empty_enclosing_quotes_thm (s : String) :
    unsafe_or_empty_enclosing_quotes_prop s := by
  intro h
  rcases h with rfl | hunsafe
  · decide
  · rw [unsafe_string_thm s hunsafe]
    have hlen := quoted_length s
    refine ⟨by omega, ?_, ?_⟩
    · rfl
    · change (('\'' :: (replaceSingleQuotes s).toList) ++ ['\'']).getLast? = some '\''
      exact getLast?_append_singleton _ '\''

/-- Property 9: Exact length formula for strings containing at least one unsafe character. -/
def unsafe_length_exact_prop (s : String) : Prop :=
  s.toList.all isSafeChar = false →
    (quote s).length = s.length + 2 + 4 * s.toList.count '\''

instance (s : String) : Decidable (unsafe_length_exact_prop s) := by
  unfold unsafe_length_exact_prop; infer_instance

theorem unsafe_length_exact_thm (s : String) : unsafe_length_exact_prop s := by
  intro hunsafe
  rw [unsafe_string_thm s hunsafe, quoted_length]

/-- Property 10: `quote` is idempotent on non-empty safe strings. -/
def safe_idempotent_prop (s : String) : Prop :=
  s ≠ "" → s.toList.all isSafeChar = true → quote (quote s) = quote s

instance (s : String) : Decidable (safe_idempotent_prop s) := by
  unfold safe_idempotent_prop; infer_instance

theorem safe_idempotent_thm (s : String) : safe_idempotent_prop s := by
  intro hne hsafe
  rw [safe_nonempty_thm s hne hsafe, safe_nonempty_thm s hne hsafe]

/-- Property 11: Exact characterization of fixed points: `quote s = s` iff `s` is non-empty and all-safe. -/
def unchanged_iff_safe_nonempty_prop (s : String) : Prop :=
  quote s = s ↔ (s ≠ "" ∧ s.toList.all isSafeChar = true)

instance (s : String) : Decidable (unchanged_iff_safe_nonempty_prop s) := by
  unfold unchanged_iff_safe_nonempty_prop; infer_instance

theorem unchanged_iff_safe_nonempty_thm (s : String) : unchanged_iff_safe_nonempty_prop s := by
  unfold unchanged_iff_safe_nonempty_prop
  constructor
  · intro heq
    by_cases hs : s = ""
    · subst hs
      revert heq
      decide
    · by_cases hsafe : s.toList.all isSafeChar = true
      · exact ⟨hs, hsafe⟩
      · have hfalse : s.toList.all isSafeChar = false :=
          Bool.eq_false_iff.mpr hsafe
        have hlen : (quote s).length = s.length + 2 + 4 * s.toList.count '\'' :=
          unsafe_length_exact_thm s hfalse
        rw [heq] at hlen
        omega
  · rintro ⟨hs, hsafe⟩
    exact safe_nonempty_thm s hs hsafe

/-- Property 12: Round-trip (lossless escaping) property: `unquote (quote s) = s` for every string `s`. -/
def unquote_quote_prop (s : String) : Prop :=
  unquote (quote s) = s

instance (s : String) : Decidable (unquote_quote_prop s) := by
  unfold unquote_quote_prop; infer_instance

theorem unquote_quote_thm (s : String) : unquote_quote_prop s := by
  unfold unquote_quote_prop
  by_cases hs : s = ""
  · subst hs
    rfl
  · by_cases hsafe : s.toList.all isSafeChar = true
    · rw [safe_nonempty_thm s hs hsafe]
      cases s with
      | mk cs =>
        cases cs with
        | nil => contradiction
        | cons c cs =>
          have hcsafe : isSafeChar c = true := by
            simp only [toList_mk, List.all_cons, Bool.and_eq_true] at hsafe
            exact hsafe.1
          have hcne : c ≠ '\'' := by
            intro heq
            subst heq
            revert hcsafe
            decide
          have hbeq : (c == '\'') = false := beq_false_of_ne hcne
          simp [unquote, unquoteChars, hbeq]
    · have hfalse : s.toList.all isSafeChar = false := Bool.eq_false_iff.mpr hsafe
      rw [unsafe_string_thm s hfalse]
      cases s with
      | mk cs =>
        unfold unquote replaceSingleQuotes
        change String.mk (unescapeChars (cs.flatMap escapeChar ++ ['\'']).dropLast) = String.mk cs
        rw [dropLast_append_singleton, unescapeChars_flatMap_escapeChar]

/-- Injectivity of `quote`: distinct input strings always produce distinct shell-escaped strings. -/
theorem quote_injective {s₁ s₂ : String} (h : quote s₁ = quote s₂) : s₁ = s₂ := by
  have h1 := unquote_quote_thm s₁
  have h2 := unquote_quote_thm s₂
  unfold unquote_quote_prop at h1 h2
  rw [← h1, ← h2, h]

/-! ## 8. Post-condition as Conjunction of Properties -/

/-- Post-condition combining all semantic properties of `quote`. -/
def Post_prop (s : String) : Prop :=
  empty_string_prop s ∧
  safe_nonempty_prop s ∧
  unsafe_string_prop s ∧
  unsafe_no_single_quote_prop s ∧
  single_quote_escaped_prop s ∧
  nonempty_output_prop s ∧
  length_ge_input_prop s ∧
  unsafe_or_empty_enclosing_quotes_prop s ∧
  unsafe_length_exact_prop s ∧
  safe_idempotent_prop s ∧
  unchanged_iff_safe_nonempty_prop s ∧
  unquote_quote_prop s

instance (s : String) : Decidable (Post_prop s) := by
  unfold Post_prop; infer_instance

/-! ## 9. Property-Based Tests -/

/-- Representative sample corpus covering empty, safe, space-containing, single-quoted,
    double-quoted, mixed, and multi-quote strings for bounded PBTs. -/
def pbtSampleStrings : List String :=
  [ "", "a", "abc", "ABC_0123456789", "_@%+=:,./-",
    "a b c", " ", "hello world!", "a'b", "'", "''", "'''",
    "'hello'", "a'b'c", "\"quoted\"", "foo$bar", "line1\nline2",
    "tab\there", "semi;colon", "pipe|cmd", "back`tick", "a'\"'\"'b" ]

-- Randomized PBTs (via Plausible) for each property and the post-condition
#eval Plausible.Testable.check (∀ s : String, decide (empty_string_prop s) = true)
#eval Plausible.Testable.check (∀ s : String, decide (safe_nonempty_prop s) = true)
#eval Plausible.Testable.check (∀ s : String, decide (unsafe_string_prop s) = true)
#eval Plausible.Testable.check (∀ s : String, decide (unsafe_no_single_quote_prop s) = true)
#eval Plausible.Testable.check (∀ s : String, decide (single_quote_escaped_prop s) = true)
#eval Plausible.Testable.check (∀ s : String, decide (nonempty_output_prop s) = true)
#eval Plausible.Testable.check (∀ s : String, decide (length_ge_input_prop s) = true)
#eval Plausible.Testable.check (∀ s : String, decide (unsafe_or_empty_enclosing_quotes_prop s) = true)
#eval Plausible.Testable.check (∀ s : String, decide (unsafe_length_exact_prop s) = true)
#eval Plausible.Testable.check (∀ s : String, decide (safe_idempotent_prop s) = true)
#eval Plausible.Testable.check (∀ s : String, decide (unchanged_iff_safe_nonempty_prop s) = true)
#eval Plausible.Testable.check (∀ s : String, decide (unquote_quote_prop s) = true)
#eval Plausible.Testable.check (∀ s : String, decide (Post_prop s) = true)

-- Bounded PBTs across `pbtSampleStrings` for each property and the post-condition
example : pbtSampleStrings.all (fun s => decide (empty_string_prop s)) = true := by native_decide
example : pbtSampleStrings.all (fun s => decide (safe_nonempty_prop s)) = true := by native_decide
example : pbtSampleStrings.all (fun s => decide (unsafe_string_prop s)) = true := by native_decide
example : pbtSampleStrings.all (fun s => decide (unsafe_no_single_quote_prop s)) = true := by native_decide
example : pbtSampleStrings.all (fun s => decide (single_quote_escaped_prop s)) = true := by native_decide
example : pbtSampleStrings.all (fun s => decide (nonempty_output_prop s)) = true := by native_decide
example : pbtSampleStrings.all (fun s => decide (length_ge_input_prop s)) = true := by native_decide
example : pbtSampleStrings.all (fun s => decide (unsafe_or_empty_enclosing_quotes_prop s)) = true := by native_decide
example : pbtSampleStrings.all (fun s => decide (unsafe_length_exact_prop s)) = true := by native_decide
example : pbtSampleStrings.all (fun s => decide (safe_idempotent_prop s)) = true := by native_decide
example : pbtSampleStrings.all (fun s => decide (unchanged_iff_safe_nonempty_prop s)) = true := by native_decide
example : pbtSampleStrings.all (fun s => decide (unquote_quote_prop s)) = true := by native_decide
example : pbtSampleStrings.all (fun s => decide (Post_prop s)) = true := by native_decide

/-! ## 10. Correctness Theorem (`Pre -> Post`) -/

/-- Main correctness theorem: for every string `s`, `Pre s` implies `Post_prop s`. -/
theorem quote_correct (s : String) (_hPre : Pre s) : Post_prop s :=
  ⟨empty_string_thm s,
   safe_nonempty_thm s,
   unsafe_string_thm s,
   unsafe_no_single_quote_thm s,
   single_quote_escaped_thm s,
   nonempty_output_thm s,
   length_ge_input_thm s,
   unsafe_or_empty_enclosing_quotes_thm s,
   unsafe_length_exact_thm s,
   safe_idempotent_thm s,
   unchanged_iff_safe_nonempty_thm s,
   unquote_quote_thm s⟩

/-! ## 11. Imperative Implementation -/

/-- Imperative implementation of `shlex.quote` using `Id.run do` and mutable state. -/
def quote_imp (s : String) : String := Id.run do
  if s = "" then
    "''"
  else
    let mut allSafe : Bool := true
    for c in s.toList do
      allSafe := allSafe && isSafeChar c
    if allSafe then
      s
    else
      let mut escaped : List Char := []
      for c in s.toList do
        escaped := escaped ++ (if c == '\'' then "'\"'\"'".toList else [c])
      "'" ++ String.mk escaped ++ "'"

/-! ## 12. Imperative Tests -/

example : quote_imp "" = "''" := by native_decide
example : quote_imp "abc" = "abc" := by native_decide
example : quote_imp "a b c" = "'a b c'" := by native_decide
example : quote_imp "a'b" = "'a'\"'\"'b'" := by native_decide
example : quote_imp "path/to/file_1.txt" = "path/to/file_1.txt" := by native_decide
example : quote_imp "'" = "''\"'\"''" := by native_decide
example : pbtSampleStrings.all (fun s => quote s == quote_imp s) = true := by native_decide

#eval quote_imp ""
#eval quote_imp "abc"
#eval quote_imp "a b c"
#eval quote_imp "a'b"
#eval Plausible.Testable.check (∀ s : String, quote s = quote_imp s)

/-! ## 13. Equivalence Theorem (Functional = Imperative) -/

theorem foldl_allSafe (cs : List Char) (init : Bool) :
    cs.foldl (fun acc c => acc && isSafeChar c) init = (init && cs.all isSafeChar) := by
  induction cs generalizing init with
  | nil => simp
  | cons c cs ih =>
    simp only [List.foldl_cons, List.all_cons, ih, Bool.and_assoc]

/-- Equivalence theorem proving that the functional `quote` and imperative `quote_imp`
    produce identical results on all inputs. -/
theorem quote_equiv (s : String) : quote s = quote_imp s := by
  unfold quote quote_imp replaceSingleQuotes escapeChar
  split
  · rfl
  · simp [foldl_allSafe, List.flatMap_def, Id.run]

theorem benchmark_quote_equiv (s : String) : benchmark_quote s = quote_imp s :=
  quote_equiv s

end «21_shlex_quote»
