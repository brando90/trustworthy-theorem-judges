import Mathlib
import Plausible

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# Shell quoting (`shlex.quote`)

Lean 4 formalization of Python's `shlex.quote` (CPython `Lib/shlex.py`), as
specialized by the task's `benchmark_quote`.

Given a string `s`, the function returns a POSIX-shell-escaped word:

* the empty string becomes `''`;
* a nonempty string whose every character lies in the POSIX safe set
  letters, digits, and `_@%+=:,.` `/` `-`
  is returned unchanged;
* otherwise the string is wrapped in single quotes, and each embedded single
  quote is replaced by the five-character sequence `'"'"'` (end single quote,
  double-quoted single quote, start single quote). That is exactly
  `"'" + s.replace("'", "'\"'\"'") + "'"`.

Non-string inputs raise `TypeError("expected string object")` in Python.
Lean excludes that case from `quote` / `benchmark_quote` by typing; it is
modeled separately by `benchmark_quote_exc`.
-/

namespace «21_shlex_quote»

/-! ## Implementation -/

/-- The POSIX safe set used by the Python source, as a string. -/
def safeSetString : String :=
  "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_@%+=:,./-"

/-- Characters of `safeSetString`, in source order. -/
def safeChars : List Char :=
  safeSetString.data

/-- `true` iff `c` belongs to the Python safe set. -/
def isSafeChar (c : Char) : Bool :=
  safeChars.contains c

/-- Replacement for an embedded `'`: the characters of `'"'"'`. -/
def escapedQuote : List Char :=
  ['\'', '"', '\'', '"', '\'']

/-- List model of `str.replace("'", "'\"'\"'")`. -/
def escapeQuotes (cs : List Char) : List Char :=
  cs.flatMap fun c => if c == '\'' then escapedQuote else [c]

/-- Every character is in the POSIX safe set. Vacuous for `[]`. -/
def allSafe (cs : List Char) : Bool :=
  cs.all isSafeChar

/-- Number of single quotes in a character list. -/
def quoteCount : List Char → Nat
  | [] => 0
  | c :: cs => (if c == '\'' then 1 else 0) + quoteCount cs

/-- List-level `shlex.quote`, following the Python control flow. -/
def quoteList (cs : List Char) : List Char :=
  if cs.isEmpty then
    ['\'', '\'']
  else if allSafe cs then
    cs
  else
    ['\''] ++ escapeQuotes cs ++ ['\'']

/-- Shell-escape a string. Functional model of `quote` / `benchmark_quote`. -/
def quote (s : String) : String :=
  String.mk (quoteList s.data)

/-- Entry point matching the Python function under test. -/
def benchmark_quote (s : String) : String :=
  quote s

/-- Invert `escapeQuotes`. Every `'` in a well-formed escape begins `'"'"'`. -/
def unescapeQuotes : List Char → List Char
  | [] => []
  | '\'' :: '"' :: '\'' :: '"' :: '\'' :: rest => '\'' :: unescapeQuotes rest
  | c :: rest => c :: unescapeQuotes rest

/-- Recover the original characters from a `quoteList` result.
This is the shell-word reading of a value produced by `quote`. -/
def unquoteList (cs : List Char) : List Char :=
  if allSafe cs then
    cs
  else
    unescapeQuotes ((cs.drop 1).dropLast)

/-- Inverse of `quote` on the image of `quote`. -/
def unquote (s : String) : String :=
  String.mk (unquoteList s.data)

/-- A character list is a valid body of a single-quoted `shlex` word:
either a non-quote character, or the escape token `'"'"'`. -/
def isValidEscaped : List Char → Bool
  | [] => true
  | '\'' :: '"' :: '\'' :: '"' :: '\'' :: rest => isValidEscaped rest
  | c :: rest => (c != '\'') && isValidEscaped rest

/-- A string is one safe shell token: either a nonempty safe word, or a
single-quoted word whose interior is a valid escape sequence. -/
def isShellToken (cs : List Char) : Bool :=
  (!cs.isEmpty && allSafe cs) ||
    (cs.head? == some '\'' && cs.getLast? == some '\'' &&
      isValidEscaped ((cs.drop 1).dropLast))

/-! ### Basic lemmas -/

theorem if_false_true {α : Type} (a b : α) :
    (if false = true then a else b) = b :=
  if_neg (by decide)

theorem bool_eq_false_of_not_true {b : Bool} (h : ¬ b = true) : b = false := by
  cases b <;> simp_all

theorem isSafe_quote : isSafeChar '\'' = false := by
  decide

theorem beq_quote_true : ('\'' == '\'') = true := rfl

theorem ne_of_not_beq {c : Char} (h : ¬ (c == '\'') = true) : c ≠ '\'' := by
  intro heq
  apply h
  simpa [heq] using beq_quote_true

theorem beq_false_of_not_true {c : Char} (h : ¬ (c == '\'') = true) :
    (c == '\'') = false :=
  bool_eq_false_of_not_true h

theorem bne_quote_of_false (c : Char) (hb : (c == '\'') = false) :
    (c != '\'') = true := by
  simp [bne, hb]

theorem escape_cons (c : Char) (cs : List Char) :
    escapeQuotes (c :: cs) =
      (if c == '\'' then escapedQuote else [c]) ++ escapeQuotes cs := by
  simp [escapeQuotes]

theorem if_escape_false (c : Char) (hb : (c == '\'') = false) :
    (if c == '\'' then escapedQuote else [c]) = [c] := by
  simp [hb]

theorem isSafeChar_iff (c : Char) :
    isSafeChar c = true ↔ c ∈ safeChars := by
  simp [isSafeChar]

theorem str_append_mk (xs ys : List Char) :
    String.mk xs ++ String.mk ys = String.mk (xs ++ ys) := by
  rfl

theorem two_quotes_eq : String.mk ['\'', '\''] = "''" := by
  rfl

theorem one_quote_eq : String.mk ['\''] = "'" := by
  rfl

theorem empty_data : ("" : String).data = [] := rfl

theorem getLast_concat (xs : List Char) (a : Char) :
    (xs ++ [a]).getLast? = some a := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases xs with
    | nil => simp
    | cons y ys => simpa using ih

theorem unescape_escape (cs : List Char) :
    unescapeQuotes (escapeQuotes cs) = cs := by
  induction cs with
  | nil => simp [escapeQuotes, unescapeQuotes.eq_1]
  | cons c cs ih =>
    rw [escape_cons]
    by_cases h : (c == '\'') = true
    · have hc : c = '\'' := eq_of_beq h
      subst hc
      have happ : escapedQuote ++ escapeQuotes cs =
          '\'' :: '"' :: '\'' :: '"' :: '\'' :: escapeQuotes cs := by
        simp [escapedQuote]
      rw [if_pos h, happ, unescapeQuotes.eq_2, ih]
    · have hne : c ≠ '\'' := ne_of_not_beq h
      have hb : (c == '\'') = false := beq_false_of_not_true h
      rw [if_escape_false c hb, List.singleton_append]
      rw [unescapeQuotes.eq_3 c (escapeQuotes cs) (by
        intro rest hc _hrest
        exact hne hc)]
      exact congrArg (fun t => c :: t) ih

theorem escape_valid (cs : List Char) :
    isValidEscaped (escapeQuotes cs) = true := by
  induction cs with
  | nil => simp [escapeQuotes, isValidEscaped]
  | cons c cs ih =>
    rw [escape_cons]
    by_cases h : (c == '\'') = true
    · have hc : c = '\'' := eq_of_beq h
      subst hc
      have happ : escapedQuote ++ escapeQuotes cs =
          '\'' :: '"' :: '\'' :: '"' :: '\'' :: escapeQuotes cs := by
        simp [escapedQuote]
      rw [if_pos h, happ, isValidEscaped.eq_2, ih]
    · have hne : c ≠ '\'' := ne_of_not_beq h
      have hb : (c == '\'') = false := beq_false_of_not_true h
      rw [if_escape_false c hb, List.singleton_append]
      rw [isValidEscaped.eq_3 c (escapeQuotes cs) (by
        intro rest hc _hrest
        exact hne hc)]
      simp [bne_quote_of_false c hb, ih]

theorem drop_wrap (cs : List Char) :
    ((['\''] ++ escapeQuotes cs ++ ['\'']).drop 1).dropLast = escapeQuotes cs := by
  have hdrop : (['\''] ++ escapeQuotes cs ++ ['\'']).drop 1 =
      escapeQuotes cs ++ ['\''] := by
    simp [List.append_assoc, List.cons_append, List.nil_append,
      List.drop_succ_cons, List.drop_zero]
  rw [hdrop]
  simp [List.dropLast_concat]

theorem foldl_and_aux (cs : List Char) (b : Bool) :
    cs.foldl (fun acc c => acc && isSafeChar c) b = (b && cs.all isSafeChar) := by
  induction cs generalizing b with
  | nil => simp
  | cons c cs ih =>
    simp only [List.foldl_cons, List.all_cons, ih, Bool.and_assoc]

theorem foldl_escape_aux (cs init : List Char) :
    cs.foldl (fun out c => if (c == '\'') = true then out ++ escapedQuote else out ++ [c]) init
      = init ++ escapeQuotes cs := by
  induction cs generalizing init with
  | nil => simp [escapeQuotes]
  | cons c cs ih =>
    simp only [List.foldl_cons, escapeQuotes, List.flatMap_cons]
    rw [ih]
    by_cases h : (c == '\'') = true
    · simp [h, escapeQuotes, List.append_assoc]
    · have hb : (c == '\'') = false := beq_false_of_not_true h
      simp [hb, escapeQuotes, List.append_assoc]

theorem escape_length_aux (cs : List Char) :
    (escapeQuotes cs).length = cs.length + 4 * quoteCount cs := by
  induction cs with
  | nil => simp [escapeQuotes, quoteCount]
  | cons c cs ih =>
    rw [escape_cons, List.length_append, ih, List.length_cons]
    by_cases h : (c == '\'') = true
    · simp only [h, if_true, quoteCount, escapedQuote, List.length_cons, List.length_nil]
      omega
    · have hb : (c == '\'') = false := beq_false_of_not_true h
      simp only [hb, if_false, if_false_true, quoteCount, List.length_singleton]
      omega

theorem unquote_quote_list (cs : List Char) :
    unquoteList (quoteList cs) = cs := by
  unfold unquoteList quoteList
  by_cases h0 : cs.isEmpty = true
  · have hempty : cs = [] := by simpa [List.isEmpty_eq_true] using h0
    subst hempty
    simp [allSafe, isSafe_quote, unescapeQuotes.eq_1, List.dropLast]
  · have hempty : cs.isEmpty = false := bool_eq_false_of_not_true h0
    simp only [hempty, if_false_true]
    by_cases hs : allSafe cs = true
    · simp [hs]
    · have hsf : allSafe cs = false := bool_eq_false_of_not_true hs
      simp only [hsf, if_false_true]
      have hnot : allSafe (['\''] ++ escapeQuotes cs ++ ['\'']) = false := by
        simp [allSafe, List.all_append, List.all_cons, isSafe_quote]
      simp only [hnot, if_false_true]
      rw [drop_wrap, unescape_escape]

theorem quoteList_isShellToken (cs : List Char) :
    isShellToken (quoteList cs) = true := by
  unfold quoteList
  by_cases h0 : cs.isEmpty = true
  · have hempty : cs = [] := by simpa [List.isEmpty_eq_true] using h0
    subst hempty
    decide
  · have hempty : cs.isEmpty = false := bool_eq_false_of_not_true h0
    simp only [hempty, if_false_true]
    by_cases hs : allSafe cs = true
    · have hne : cs ≠ [] := by
        intro h
        apply h0
        simp [h]
      simp [isShellToken, hs, hempty]
    · have hsf : allSafe cs = false := bool_eq_false_of_not_true hs
      simp only [hsf, if_false_true]
      have hlastCons : ('\'' :: (escapeQuotes cs ++ ['\''])).getLast? = some '\'' :=
        getLast_concat ('\'' :: escapeQuotes cs) '\''
      have hdrop : ((('\'' :: (escapeQuotes cs ++ ['\''])).drop 1).dropLast) =
          escapeQuotes cs := by
        simp [List.drop_succ_cons, List.drop_zero, List.dropLast_concat]
      have h2 :
          (('\'' :: (escapeQuotes cs ++ ['\''])).head? == some '\'' &&
            ('\'' :: (escapeQuotes cs ++ ['\''])).getLast? == some '\'' &&
            isValidEscaped (((('\'' :: (escapeQuotes cs ++ ['\''])).drop 1).dropLast))) = true := by
        simp [List.head?_cons, hlastCons, hdrop, escape_valid]
      simp [isShellToken, h2, Bool.or_true]
      exact Or.inr ⟨hlastCons, escape_valid cs⟩

theorem quoteList_ne_nil (cs : List Char) : quoteList cs ≠ [] := by
  unfold quoteList
  by_cases h0 : cs.isEmpty = true
  · have hempty : cs = [] := by simpa [List.isEmpty_eq_true] using h0
    subst hempty
    decide
  · have hempty : cs.isEmpty = false := bool_eq_false_of_not_true h0
    simp only [hempty, if_false_true]
    by_cases hs : allSafe cs = true
    · intro h
      apply h0
      simpa [hs, List.isEmpty_iff] using h
    · have hsf : allSafe cs = false := bool_eq_false_of_not_true hs
      simp only [hsf, if_false_true]
      intro h
      simp [List.cons_append] at h

/-! ## Unit tests -/

example : quote "" = "''" := by native_decide
example : quote "abc" = "abc" := by native_decide
example : quote "a b c" = "'a b c'" := by native_decide
example : quote "a'b" = "'a'\"'\"'b'" := by native_decide
example : quote "'" = "''\"'\"''" := by native_decide
example : quote "-" = "-" := by native_decide
example : quote "hello-world" = "hello-world" := by native_decide
example : quote "a\"b" = "'a\"b'" := by native_decide
example : benchmark_quote "abc" = "abc" := by native_decide
example : unquote (quote "a'b") = "a'b" := by native_decide
example : unquote (quote "") = "" := by native_decide

#eval quote ""
#eval quote "abc"
#eval quote "a b c"
#eval quote "a'b"
#eval quote "'"

/-! ## Pre-condition -/

/-- Python `pre_quote`: the input is a string.
On the Lean type `String` this holds for every value. -/
def Pre (_s : String) : Prop := True

/-- Dynamic Python values, so the `TypeError` branch can be stated. -/
inductive PyVal where
  | str : String → PyVal
  | nonStr : PyVal

/-- `pre_quote` from the Python source. -/
def pre_quote (v : PyVal) : Bool :=
  match v with
  | .str _ => true
  | .nonStr => false

/-- `benchmark_quote` including the non-string `TypeError`. -/
def benchmark_quote_exc (v : PyVal) : Except String String :=
  match v with
  | .nonStr => .error "expected string object"
  | .str s => .ok (quote s)


/-! ## Properties -/

def empty_quote_prop (s : String) : Prop :=
  s = "" → quote s = "''"

theorem empty_quote_thm (s : String) : empty_quote_prop s := by
  intro h
  subst h
  simp [quote, quoteList, empty_data, two_quotes_eq]

def safe_identity_prop (s : String) : Prop :=
  s ≠ "" → allSafe s.data = true → quote s = s

theorem safe_identity_thm (s : String) : safe_identity_prop s := by
  intro hne hs
  cases s with
  | mk data =>
    cases data with
    | nil => simp at hne
    | cons c cs =>
      simp [quote, quoteList, List.isEmpty_cons, hs]

def unsafe_wrap_prop (s : String) : Prop :=
  s ≠ "" → allSafe s.data = false →
    quote s = "'" ++ String.mk (escapeQuotes s.data) ++ "'"

theorem unsafe_wrap_thm (s : String) : unsafe_wrap_prop s := by
  intro hne hs
  cases s with
  | mk data =>
    cases data with
    | nil =>
      exfalso
      exact hne rfl
    | cons c cs =>
      simp only [quote, quoteList, List.isEmpty_cons, hs, if_false_true]
      rw [← one_quote_eq, str_append_mk, str_append_mk]

def roundtrip_prop (s : String) : Prop :=
  unquote (quote s) = s

theorem roundtrip_thm (s : String) : roundtrip_prop s := by
  cases s with
  | mk data =>
    simpa [roundtrip_prop, quote, unquote] using unquote_quote_list data

def output_nonempty_prop (s : String) : Prop :=
  quote s ≠ ""

theorem output_nonempty_thm (s : String) : output_nonempty_prop s := by
  intro h
  have hdata : quoteList s.data = [] := by
    have := congrArg String.data h
    simpa [quote, empty_data] using this
  exact quoteList_ne_nil s.data hdata

def quote_cases_prop (s : String) : Prop :=
  (s = "" ∧ quote s = "''") ∨
  (s ≠ "" ∧ allSafe s.data = true ∧ quote s = s) ∨
  (s ≠ "" ∧ allSafe s.data = false ∧
    quote s = "'" ++ String.mk (escapeQuotes s.data) ++ "'")

theorem quote_cases_thm (s : String) : quote_cases_prop s := by
  by_cases h0 : s = ""
  · exact Or.inl ⟨h0, empty_quote_thm s h0⟩
  · by_cases hs : allSafe s.data = true
    · exact Or.inr (Or.inl ⟨h0, hs, safe_identity_thm s h0 hs⟩)
    · have hsf := bool_eq_false_of_not_true hs
      exact Or.inr (Or.inr ⟨h0, hsf, unsafe_wrap_thm s h0 hsf⟩)

def quote_spec_prop (s : String) : Prop :=
  quote s =
    if s.data.isEmpty then "''"
    else if allSafe s.data then s
    else "'" ++ String.mk (escapeQuotes s.data) ++ "'"

theorem quote_spec_thm (s : String) : quote_spec_prop s := by
  cases s with
  | mk data =>
    cases data with
    | nil =>
      simp [quote_spec_prop, quote, quoteList, empty_data, two_quotes_eq]
    | cons c cs =>
      simp only [quote_spec_prop, quote, quoteList, List.isEmpty_cons, if_false_true]
      by_cases hs : allSafe (c :: cs) = true
      · simp [hs]
      · have hsf := bool_eq_false_of_not_true hs
        simp only [hsf, if_false_true]
        rw [← one_quote_eq, str_append_mk, str_append_mk]

def wrapped_boundary_prop (s : String) : Prop :=
  s = "" ∨ allSafe s.data = false →
    (quote s).data.head? = some '\'' ∧ (quote s).data.getLast? = some '\''

theorem wrapped_boundary_thm (s : String) : wrapped_boundary_prop s := by
  intro h
  cases s with
  | mk data =>
    cases data with
    | nil =>
      simp [quote, quoteList]
    | cons c cs =>
      have hsf : allSafe (c :: cs) = false := by
        cases h with
        | inl hempty =>
          have : (String.mk (c :: cs)).data = [] := by
            simpa [empty_data] using congrArg String.data hempty
          simp at this
        | inr hsf =>
          simpa using hsf
      simp only [quote, quoteList, List.isEmpty_cons, hsf, if_false_true]
      refine ⟨?_, ?_⟩
      · simp
      · simpa [List.append_assoc] using
          getLast_concat (['\''] ++ escapeQuotes (c :: cs)) '\''

def escape_length_prop (s : String) : Prop :=
  (escapeQuotes s.data).length = s.data.length + 4 * quoteCount s.data

theorem escape_length_thm (s : String) : escape_length_prop s :=
  escape_length_aux s.data

def shell_token_prop (s : String) : Prop :=
  isShellToken (quote s).data = true

theorem shell_token_thm (s : String) : shell_token_prop s := by
  simpa [shell_token_prop, quote] using quoteList_isShellToken s.data

def idempotent_safe_prop (s : String) : Prop :=
  s ≠ "" → allSafe s.data = true → quote (quote s) = quote s

theorem idempotent_safe_thm (s : String) : idempotent_safe_prop s := by
  intro hne hs
  have h := safe_identity_thm s hne hs
  simp [h]

def quote_length_prop (s : String) : Prop :=
  if s.data.isEmpty then (quote s).data.length = 2
  else if allSafe s.data then (quote s).data.length = s.data.length
  else (quote s).data.length = s.data.length + 4 * quoteCount s.data + 2

theorem quote_length_thm (s : String) : quote_length_prop s := by
  cases s with
  | mk data =>
    cases data with
    | nil => simp [quote_length_prop, quote, quoteList]
    | cons c cs =>
      simp only [quote_length_prop, List.isEmpty_cons, if_false_true, quote, quoteList]
      by_cases hs : allSafe (c :: cs) = true
      · simp [hs]
      · have hsf := bool_eq_false_of_not_true hs
        simp only [hsf, if_false_true, List.length_append, List.length_cons,
          List.length_nil, escape_length_aux, quoteCount]
        omega

def safe_set_prop (c : Char) : Prop :=
  isSafeChar c = true ↔ c ∈ safeSetString.data

theorem safe_set_thm (c : Char) : safe_set_prop c := by
  simp [safe_set_prop, isSafeChar, safeChars]

/-- Shell metacharacters excluded by the Python safe set. -/
def shellMetaChars : List Char :=
  [' ', '\t', '\n', '\r', '"', '\'', '\\', '!', '#', '$', '&', '(', ')', '*',
   ';', '<', '>', '?', '[', ']', '^', '`', '{', '|', '}', '~']

def metachar_unsafe_prop : Prop :=
  shellMetaChars.all (fun c => !isSafeChar c) = true

theorem metachar_unsafe_thm : metachar_unsafe_prop := by
  unfold metachar_unsafe_prop
  decide

def replacement_prop : Prop :=
  String.mk escapedQuote = "'\"'\"'"

theorem replacement_thm : replacement_prop := by
  rfl

def escape_injective_prop (cs₁ cs₂ : List Char) : Prop :=
  escapeQuotes cs₁ = escapeQuotes cs₂ → cs₁ = cs₂

theorem escape_injective_thm (cs₁ cs₂ : List Char) :
    escape_injective_prop cs₁ cs₂ := by
  intro h
  rw [← unescape_escape cs₁, ← unescape_escape cs₂, h]

def pre_quote_prop (v : PyVal) : Prop :=
  pre_quote v = true ↔ ∃ s, v = .str s

theorem pre_quote_thm (v : PyVal) : pre_quote_prop v := by
  cases v <;> simp [pre_quote_prop, pre_quote]

def type_error_prop (v : PyVal) : Prop :=
  pre_quote v = false →
    benchmark_quote_exc v = .error "expected string object"

theorem type_error_thm (v : PyVal) : type_error_prop v := by
  intro h
  cases v with
  | str s => simp [pre_quote] at h
  | nonStr => rfl

def dyn_ok_prop (s : String) : Prop :=
  benchmark_quote_exc (.str s) = .ok (quote s)

theorem dyn_ok_thm (s : String) : dyn_ok_prop s := rfl

def benchmark_eq_prop (s : String) : Prop :=
  benchmark_quote s = quote s

theorem benchmark_eq_thm (s : String) : benchmark_eq_prop s := rfl

/-! ## Post-condition -/

/-- Full post-condition: the Python case split, round-trip, shell-token
safety, length of the quote-escape, and the safe-string idempotence law. -/
def Post_prop (s : String) : Prop :=
  empty_quote_prop s ∧
  safe_identity_prop s ∧
  unsafe_wrap_prop s ∧
  roundtrip_prop s ∧
  output_nonempty_prop s ∧
  quote_cases_prop s ∧
  quote_spec_prop s ∧
  wrapped_boundary_prop s ∧
  escape_length_prop s ∧
  shell_token_prop s ∧
  idempotent_safe_prop s ∧
  quote_length_prop s

/-! ## Property-based tests -/

def b_empty (s : String) : Bool :=
  s != "" || quote s == "''"

def b_safe (s : String) : Bool :=
  !(s != "" && allSafe s.data) || quote s == s

def b_unsafe (s : String) : Bool :=
  !(s != "" && allSafe s.data == false) ||
    quote s == "'" ++ String.mk (escapeQuotes s.data) ++ "'"

def b_round (s : String) : Bool :=
  unquote (quote s) == s

def b_nonempty (s : String) : Bool :=
  quote s != ""

def b_shell (s : String) : Bool :=
  isShellToken (quote s).data

def b_len (s : String) : Bool :=
  (escapeQuotes s.data).length == s.data.length + 4 * quoteCount s.data

def b_idemp (s : String) : Bool :=
  !(s != "" && allSafe s.data) || quote (quote s) == quote s

def b_wrap (s : String) : Bool :=
  !(s == "" || allSafe s.data == false) ||
    ((quote s).data.head? == some '\'' && (quote s).data.getLast? == some '\'')

def b_spec (s : String) : Bool :=
  quote s ==
    if s.data.isEmpty then "''"
    else if allSafe s.data then s
    else "'" ++ String.mk (escapeQuotes s.data) ++ "'"

def b_post (s : String) : Bool :=
  b_empty s && b_safe s && b_unsafe s && b_round s && b_nonempty s &&
    b_shell s && b_len s && b_idemp s && b_wrap s && b_spec s

def pbtChars : List Char :=
  ['a', 'Z', '0', ' ', '\'', '"', '-', '_', '@', '\n', '/', '.', '%', '+']

def pbtStrings : List String :=
  let cs := pbtChars
  "" :: (cs.map fun c => String.mk [c]) ++
    (cs.flatMap fun c1 => cs.map fun c2 => String.mk [c1, c2])

-- PBT for empty_quote_prop
example : pbtStrings.all b_empty = true := by native_decide
-- PBT for safe_identity_prop
example : pbtStrings.all b_safe = true := by native_decide
-- PBT for unsafe_wrap_prop
example : pbtStrings.all b_unsafe = true := by native_decide
-- PBT for roundtrip_prop
example : pbtStrings.all b_round = true := by native_decide
-- PBT for output_nonempty_prop
example : pbtStrings.all b_nonempty = true := by native_decide
-- PBT for shell_token_prop
example : pbtStrings.all b_shell = true := by native_decide
-- PBT for escape_length_prop
example : pbtStrings.all b_len = true := by native_decide
-- PBT for idempotent_safe_prop
example : pbtStrings.all b_idemp = true := by native_decide
-- PBT for wrapped_boundary_prop
example : pbtStrings.all b_wrap = true := by native_decide
-- PBT for quote_spec_prop
example : pbtStrings.all b_spec = true := by native_decide
-- PBT for Post_prop
example : pbtStrings.all b_post = true := by native_decide
-- PBT for safe_set_prop on the ASCII range
example : (List.range 128).all (fun n =>
    let c := Char.ofNat n
    isSafeChar c == safeChars.contains c) = true := by native_decide
-- PBT for metachar_unsafe_prop
example : shellMetaChars.all (fun c => !isSafeChar c) = true := by native_decide
-- PBT for quote_cases_prop / quote_length_prop on the same sample
example : pbtStrings.all (fun s =>
    (quote s).data.length ==
      (if s.data.isEmpty then 2
       else if allSafe s.data then s.data.length
       else s.data.length + 4 * quoteCount s.data + 2)) = true := by native_decide

-- PBT for quote_cases_prop
example : pbtStrings.all (fun s =>
    (s == "" && quote s == "''") ||
    (s != "" && allSafe s.data && quote s == s) ||
    (s != "" && allSafe s.data == false &&
      quote s == "'" ++ String.mk (escapeQuotes s.data) ++ "'")) = true := by native_decide
-- PBT for replacement_prop
example : String.mk escapedQuote = "'" ++ "\"" ++ "'" ++ "\"" ++ "'" := by native_decide
-- PBT for escape_injective_prop on the sample set
example : pbtStrings.all (fun s1 => pbtStrings.all (fun s2 =>
    !(escapeQuotes s1.data == escapeQuotes s2.data) || s1.data == s2.data)) = true := by native_decide
-- PBT for pre_quote_prop / type_error_prop / dyn_ok_prop / benchmark_eq_prop
example : pre_quote PyVal.nonStr = false := by native_decide
example : (match benchmark_quote_exc PyVal.nonStr with | .error m => m == "expected string object" | .ok _ => false) = true := by native_decide
example : pbtStrings.all (fun s =>
    pre_quote (PyVal.str s) && benchmark_quote s == quote s &&
      (match benchmark_quote_exc (PyVal.str s) with
       | .ok t => t == quote s
       | .error _ => false)) = true := by native_decide

#eval Plausible.Testable.check (∀ s : String, unquote (quote s) = s)
#eval Plausible.Testable.check (∀ s : String, quote s ≠ "")
#eval Plausible.Testable.check (∀ s : String, b_empty s = true)
#eval Plausible.Testable.check (∀ s : String, b_shell s = true)
#eval Plausible.Testable.check (∀ s : String, b_safe s = true)
#eval Plausible.Testable.check (∀ s : String, b_post s = true)

/-! ## Correctness -/

theorem correctness_thm (s : String) (_h : Pre s) : Post_prop s := by
  exact ⟨empty_quote_thm s, safe_identity_thm s, unsafe_wrap_thm s, roundtrip_thm s,
    output_nonempty_thm s, quote_cases_thm s, quote_spec_thm s, wrapped_boundary_thm s,
    escape_length_thm s, shell_token_thm s, idempotent_safe_thm s, quote_length_thm s⟩

/-! ## Imperative implementation -/

/-- Imperative `shlex.quote`, using mutable accumulators in `Id`. -/
def quoteImp (s : String) : String :=
  Id.run do
    let cs := s.data
    if cs.isEmpty then
      return String.mk ['\'', '\'']
    let mut allSafeAcc : Bool := true
    for c in cs do
      allSafeAcc := allSafeAcc && isSafeChar c
    if allSafeAcc then
      return s
    let mut out : List Char := ['\'']
    for c in cs do
      if c == '\'' then
        out := out ++ escapedQuote
      else
        out := out ++ [c]
    out := out ++ ['\'']
    return String.mk out

/-! ## Imperative tests -/

example : quoteImp "" = "''" := by native_decide
example : quoteImp "abc" = "abc" := by native_decide
example : quoteImp "a b c" = "'a b c'" := by native_decide
example : quoteImp "a'b" = "'a'\"'\"'b'" := by native_decide
example : quoteImp "'" = "''\"'\"''" := by native_decide
example : quoteImp "hello-world" = "hello-world" := by native_decide

#eval quoteImp "a b c"
#eval quoteImp "a'b"

/-! ## Equivalence -/

theorem quote_equiv_thm (s : String) : quote s = quoteImp s := by
  cases s with
  | mk data =>
    cases data with
    | nil =>
      unfold quote quoteList quoteImp
      simp only [Id.run, bind, pure, List.isEmpty_nil]
      rfl
    | cons c cs =>
      unfold quote quoteList quoteImp
      simp only [Id.run, bind, pure, List.isEmpty_cons]
      have hforSafe :
          (forIn (m := Id) (c :: cs) true fun ch r => ForInStep.yield (r && isSafeChar ch))
            = (c :: cs).foldl (fun acc x => acc && isSafeChar x) true :=
        List.forIn_yield_eq_foldl (fun ch r => r && isSafeChar ch) true
      rw [hforSafe]
      rw [foldl_and_aux, Bool.true_and]
      by_cases hs : allSafe (c :: cs) = true
      · simp only [allSafe] at hs
        simp only [hs, allSafe]
        rfl
      · have hs' : allSafe (c :: cs) = false := bool_eq_false_of_not_true hs
        simp only [allSafe] at hs'
        simp only [hs', if_false_true]
        have hfun :
            (fun ch r =>
              if (ch == '\'') = true then ForInStep.yield (r ++ escapedQuote)
              else ForInStep.yield (r ++ [ch]))
            = (fun ch r =>
              ForInStep.yield (if (ch == '\'') = true then r ++ escapedQuote else r ++ [ch])) := by
          funext ch r
          by_cases hb : (ch == '\'') = true <;> simp [hb]
        rw [hfun]
        rw [List.forIn_yield_eq_foldl
          (fun ch r => if (ch == '\'') = true then r ++ escapedQuote else r ++ [ch]) ['\'']]
        rw [foldl_escape_aux]
        simp only [allSafe, hs', if_false_true]

end «21_shlex_quote»
