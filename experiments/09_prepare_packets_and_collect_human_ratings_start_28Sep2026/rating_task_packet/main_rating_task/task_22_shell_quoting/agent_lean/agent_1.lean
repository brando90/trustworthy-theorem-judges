import Mathlib

/-!
# VeriBench 21 — `shlex.quote`

Formalization of CPython's `shlex.quote` (and the benchmark wrapper
`benchmark_quote`).

A string is returned unchanged when it is non-empty and every character
belongs to the POSIX safe set

`abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_@%+=:,.` plus `/` and `-`.

Otherwise the result is a single-quoted shell word: the string is wrapped in
`'...'`, and each embedded `'` is replaced by the five-character sequence
`'"'"'` (end single quote, double-quoted `'`, reopen single quote). The empty
string is falsy in Python, so it takes this branch and becomes `''`.

`benchmark_quote` raises `TypeError: expected string object` on non-strings.
That branch is modeled by `ShellInput.nonString`. Every Lean `String` satisfies
`pre_quote`.

Correctness is stated both as the algorithm above and as a round trip through
a POSIX quoting decoder: bare characters must be safe, single quotes are
literal, and the only double-quoted text `shlex.quote` emits is `'`.
-/

namespace «21_shlex_quote»

/-! ## Implementation -/

/-- The safe character literal from CPython `shlex.quote`. -/
def safeAlphabet : String :=
  "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_@%+=:,./-"

/-- `c` is in the POSIX safe set used by `shlex.quote`. -/
def isSafeChar (c : Char) : Bool :=
  safeAlphabet.data.contains c

/-- ASCII classes that make up `safeAlphabet`, in the same order as the literal. -/
def lowers : List Char := (List.range 26).map fun i => Char.ofNat (97 + i)

def uppers : List Char := (List.range 26).map fun i => Char.ofNat (65 + i)

def digits : List Char := (List.range 10).map fun i => Char.ofNat (48 + i)

/-- Punctuation in the safe set: `_@%+=:,.` plus slash and hyphen. -/
def punct : List Char := ['_', '@', '%', '+', '=', ':', ',', '.', '/', '-']

/-- Replacement for one single quote: `'"'"'`. -/
def quoteRepl : List Char := ['\'', '"', '\'', '"', '\'']

/-- `str.replace("'", "'\"'\"'")` on a single character. -/
def escapeChar (c : Char) : List Char :=
  if c == '\'' then quoteRepl else [c]

/-- `s.replace("'", "'\"'\"'")` as a characterwise substitution. -/
def escape (cs : List Char) : List Char :=
  cs.flatMap escapeChar

/-- Character list of `shlex.quote`. Empty is not returned raw: `all` is
vacuous on `[]`, but Python's `if not s` fires first. -/
def quoteList (cs : List Char) : List Char :=
  if !cs.isEmpty && cs.all isSafeChar then
    cs
  else
    ['\''] ++ escape cs ++ ['\'']

/-- Shell-escaped form of `s`, matching `shlex.quote` on strings. -/
def quote (s : String) : String :=
  String.mk (quoteList s.data)

/-- Modes of a POSIX shell word while reading quotes. -/
inductive QuoteMode where
  | bare
  | single
  | double
deriving DecidableEq, Repr

/-- One step of a shell-word decoder for the quoting forms `shlex.quote` emits.

* Bare mode accepts only safe characters (no IFS and no expansions).
* Single quotes are literal until the next `'`.
* Double quotes are literal except the closing `"`. `$`, `` ` ``, `\` and
  newline are rejected: a shell would expand or escape them, and `shlex.quote`
  never places them inside double quotes. The only double-quoted span it emits
  is `"'"` . -/
def quoteStep (mode : QuoteMode) (acc : List Char) (c : Char) :
    Option (QuoteMode × List Char) :=
  match mode with
  | .bare =>
    if c == '\'' then some (.single, acc)
    else if c == '"' then some (.double, acc)
    else if isSafeChar c then some (.bare, c :: acc)
    else none
  | .single =>
    if c == '\'' then some (.bare, acc)
    else some (.single, c :: acc)
  | .double =>
    if c == '"' then some (.bare, acc)
    else if c == '\\' || c == '$' || c == '`' || c == '\n' then none
    else some (.double, c :: acc)

/-- Run the decoder from `mode`, accumulating decoded characters in reverse. -/
def runDecode (mode : QuoteMode) (acc : List Char) :
    List Char → Option (QuoteMode × List Char)
  | [] => some (mode, acc)
  | c :: cs =>
    match quoteStep mode acc c with
    | none => none
    | some (mode', acc') => runDecode mode' acc' cs

/-- Decode one shell word. `none` if quotes are unmatched or a bare character
is outside the safe set. -/
def shellDecode (cs : List Char) : Option (List Char) :=
  match runDecode .bare [] cs with
  | some (.bare, acc) => some acc.reverse
  | _ => none

/-- `shellDecode` lifted to `String`. -/
def shellDecodeStr (s : String) : Option String :=
  (shellDecode s.data).map String.mk

/-- Inputs of `benchmark_quote`. `.nonString` is every Python value that is
not a `str` (the `TypeError` branch). -/
inductive ShellInput where
  | str (s : String)
  | nonString
deriving DecidableEq, Repr

/-- Python `pre_quote`: true iff the input is a string. -/
def preQuote : ShellInput → Bool
  | .str _ => true
  | .nonString => false

/-- `benchmark_quote`: `TypeError` on non-strings, otherwise `quote`. -/
def benchmarkQuote : ShellInput → Except String String
  | .str s => .ok (quote s)
  | .nonString => .error "expected string object"

/-! ## Unit tests -/

example : quote "" = "''" := by native_decide

example : quote "abc" = "abc" := by native_decide

example : quote "a b c" = "'a b c'" := by native_decide

example : quote "a'b" = "'a'\"'\"'b'" := by native_decide

example : quote " " = "' '" := by native_decide

example : quote "'" = "''\"'\"''" := by native_decide

example : quote "a/b" = "a/b" := by native_decide

example : quote "it's" = "'it'\"'\"'s'" := by native_decide

example : quote "ä" = "'ä'" := by native_decide

example : benchmarkQuote .nonString = .error "expected string object" := by
  rfl

example : benchmarkQuote (.str "abc") = .ok "abc" := by rfl

#eval quote ""

#eval quote "abc"

#eval quote "a b c"

#eval quote "a'b"

#eval quote "'"

#eval benchmarkQuote .nonString

/-! ## Pre-condition -/

/-- `pre_quote` on the string domain of `benchmark_quote`.
Every Lean `String` is a Python `str`, so the precondition holds for every
input of `quote`. Non-strings are rejected by `typeerror_prop`. -/
def Pre (_s : String) : Prop := True

/-! ## Properties -/

theorem squote_not_safe : isSafeChar '\'' = false := by decide

theorem dquote_not_safe : isSafeChar '"' = false := by decide

theorem safe_ne_squote {c : Char} (h : isSafeChar c = true) : c ≠ '\'' := by
  intro eq
  rw [eq, squote_not_safe] at h
  simp at h

theorem safe_ne_dquote {c : Char} (h : isSafeChar c = true) : c ≠ '"' := by
  intro eq
  rw [eq, dquote_not_safe] at h
  simp at h

theorem quoteStep_bare_safe (acc : List Char) {c : Char} (h : isSafeChar c = true) :
    quoteStep .bare acc c = some (.bare, c :: acc) := by
  have h1 : (c == '\'') = false := (beq_eq_false_iff_ne).2 (safe_ne_squote h)
  have h2 : (c == '"') = false := (beq_eq_false_iff_ne).2 (safe_ne_dquote h)
  simp [quoteStep, h, h1, h2]

theorem runDecode_append (mode : QuoteMode) (acc xs ys : List Char) :
    runDecode mode acc (xs ++ ys) =
      match runDecode mode acc xs with
      | none => none
      | some (m, a) => runDecode m a ys := by
  induction xs generalizing mode acc with
  | nil => simp [runDecode]
  | cons x xs ih =>
    simp only [List.cons_append, runDecode]
    cases quoteStep mode acc x with
    | none => simp
    | some v =>
      cases v with
      | mk m a =>
        simpa using ih (mode := m) (acc := a)

theorem runDecode_bare_safe (acc cs : List Char) (h : cs.all isSafeChar = true) :
    runDecode .bare acc cs = some (.bare, cs.reverse ++ acc) := by
  induction cs generalizing acc with
  | nil => simp [runDecode]
  | cons c cs ih =>
    rw [List.all_cons, Bool.and_eq_true_iff] at h
    simp only [runDecode, quoteStep_bare_safe acc h.1]
    rw [ih (c :: acc) h.2]
    simp [List.reverse_cons, List.append_assoc]

theorem runDecode_quoteRepl (acc : List Char) :
    runDecode .single acc quoteRepl = some (.single, '\'' :: acc) := by
  simp [quoteRepl, runDecode, quoteStep]

theorem runDecode_single_escape (acc cs : List Char) :
    runDecode .single acc (escape cs) = some (.single, cs.reverse ++ acc) := by
  induction cs generalizing acc with
  | nil => simp [escape, runDecode]
  | cons c cs ih =>
    cases h : c == '\'' with
    | true =>
      have hc : c = '\'' := (beq_iff_eq).1 h
      subst hc
      show runDecode .single acc (escape ('\'' :: cs)) =
        some (.single, ('\'' :: cs).reverse ++ acc)
      rw [escape, List.flatMap_cons]
      have hchar : escapeChar '\'' = quoteRepl := by simp [escapeChar, quoteRepl]
      rw [hchar, runDecode_append, runDecode_quoteRepl]
      simp
      rw [show List.flatMap escapeChar cs = escape cs from rfl]
      rw [ih]
    | false =>
      rw [escape, List.flatMap_cons]
      have hchar : escapeChar c = [c] := by simp [escapeChar, h]
      rw [hchar]
      have hstep : quoteStep .single acc c = some (.single, c :: acc) := by
        simp [quoteStep, h]
      simp [runDecode, hstep]
      rw [show List.flatMap escapeChar cs = escape cs from rfl]
      rw [ih]

theorem runDecode_wrapped (cs : List Char) :
    runDecode .bare [] ('\'' :: (escape cs ++ ['\''])) = some (.bare, cs.reverse) := by
  have hopen : runDecode .bare [] ('\'' :: (escape cs ++ ['\''])) =
      runDecode .single [] (escape cs ++ ['\'']) := by
    simp [runDecode, quoteStep]
  rw [hopen, runDecode_append, runDecode_single_escape]
  simp [runDecode, quoteStep]

theorem shellDecode_wrapped (cs : List Char) :
    shellDecode ('\'' :: (escape cs ++ ['\''])) = some cs := by
  simp [shellDecode, runDecode_wrapped, List.reverse_reverse]

theorem shellDecode_safe (cs : List Char) (h : cs.all isSafeChar = true) :
    shellDecode cs = some cs := by
  simp [shellDecode, runDecode_bare_safe [] cs h, List.append_nil, List.reverse_reverse]

theorem shellDecode_quoteList (cs : List Char) :
    shellDecode (quoteList cs) = some cs := by
  cases hcond : (!cs.isEmpty && cs.all isSafeChar)
  · have hform : quoteList cs = '\'' :: (escape cs ++ ['\'']) := by
      simp [quoteList, hcond]
    rw [hform]
    exact shellDecode_wrapped cs
  · have hall : cs.all isSafeChar = true := (Bool.and_eq_true_iff.mp hcond).2
    have hform : quoteList cs = cs := by simp [quoteList, hcond]
    rw [hform]
    exact shellDecode_safe cs hall

theorem mk_data (s : String) : String.mk s.data = s := by
  cases s
  rfl

/-- The Python safe literal is exactly the ASCII letters, digits, and the
punctuation `_@%+=:,.` together with slash and hyphen. -/
theorem safeAlphabet_decomp_thm :
    safeAlphabet.data = lowers ++ uppers ++ digits ++ punct := by
  rfl

/-- `isSafeChar` accepts exactly the Python safe set. -/
@[reducible] def charset_prop (c : Char) : Prop :=
  isSafeChar c = true ↔
    c ∈ lowers ∨ c ∈ uppers ∨ c ∈ digits ∨ c ∈ punct

theorem charset_thm (c : Char) : charset_prop c := by
  simp [charset_prop, isSafeChar, safeAlphabet_decomp_thm, List.mem_append,
    List.contains_eq_mem, decide_eq_true_eq]

/-- Each `'` expands from 1 character to 5, so the escape is longer by `4`
per quote. -/
theorem escape_length (cs : List Char) :
    (escape cs).length = cs.length + 4 * cs.count '\'' := by
  induction cs with
  | nil => simp [escape]
  | cons c cs ih =>
    cases h : c == '\'' with
    | true =>
      have hc : c = '\'' := (beq_iff_eq).1 h
      subst hc
      rw [escape, List.flatMap_cons]
      have hchar : escapeChar '\'' = quoteRepl := by simp [escapeChar]
      rw [hchar, List.length_append]
      rw [show List.flatMap escapeChar cs = escape cs from rfl, ih]
      have hlen : quoteRepl.length = 5 := by decide
      simp [hlen, List.count_cons_self, List.length_cons]
      omega
    | false =>
      have hc : c ≠ '\'' := (beq_eq_false_iff_ne).1 h
      rw [escape, List.flatMap_cons]
      have hchar : escapeChar c = [c] := by simp [escapeChar, h]
      rw [hchar, List.length_append]
      rw [show List.flatMap escapeChar cs = escape cs from rfl, ih, List.count_cons_of_ne hc]
      simp [List.length_cons]
      omega

theorem quoteList_length (cs : List Char) :
    (quoteList cs).length =
      if !cs.isEmpty && cs.all isSafeChar then cs.length
      else cs.length + 4 * cs.count '\'' + 2 := by
  cases hcond : (!cs.isEmpty && cs.all isSafeChar)
  · have hform : quoteList cs = '\'' :: (escape cs ++ ['\'']) := by simp [quoteList, hcond]
    rw [hform]
    simp [List.length_cons, List.length_append, escape_length, Nat.add_assoc]
  · have hform : quoteList cs = cs := by simp [quoteList, hcond]
    simp [hform]

theorem length_data (s : String) : s.length = s.data.length := by
  cases s
  rfl

/-- Empty string quotes to `''` (Python's `if not s`). -/
@[reducible] def empty_prop : Prop := quote "" = "''"

/-- Control flow of `quote` on strings: raw when non-empty and safe, otherwise
single-quote wrapping with `'` replaced by `'"'"'`. -/
@[reducible] def algorithm_prop (s : String) : Prop :=
  quote s =
    if s.data.isEmpty then "''"
    else if s.data.all isSafeChar then s
    else String.mk ('\'' :: (escape s.data ++ ['\'']))

theorem algorithm_thm (s : String) : algorithm_prop s := by
  cases hemp : s.data.isEmpty
  · cases hall : s.data.all isSafeChar <;>
      simp [algorithm_prop, quote, quoteList, hemp, hall, mk_data]
  · have hnil : s.data = [] := List.isEmpty_iff.mp hemp
    simp [algorithm_prop, quote, quoteList, hnil, escape]

theorem empty_thm : empty_prop := by
  have h := algorithm_thm ""
  simp only [algorithm_prop] at h
  simpa using h

/-- A shell word decoder recovers the original string from `quote`. -/
@[reducible] def roundtrip_prop (s : String) : Prop :=
  shellDecodeStr (quote s) = some s

theorem roundtrip_thm (s : String) : roundtrip_prop s := by
  simp [roundtrip_prop, shellDecodeStr, quote, shellDecode_quoteList, mk_data]

/-- Distinct strings have distinct shell spellings. -/
@[reducible] def injective_prop (s t : String) : Prop :=
  quote s = quote t → s = t

theorem injective_thm (s t : String) : injective_prop s t := by
  intro h
  have hs := roundtrip_thm s
  have ht := roundtrip_thm t
  simp only [roundtrip_prop] at hs ht
  rw [h] at hs
  exact Option.some.inj (hs.symm.trans ht)

/-- Length of the escaped word: unchanged when returned raw, otherwise the
source length plus 2 wrapper quotes plus 4 per embedded `'`. -/
@[reducible] def length_prop (s : String) : Prop :=
  (quote s).length =
    if !s.data.isEmpty && s.data.all isSafeChar then s.length
    else s.length + 4 * (s.data.count '\'') + 2

theorem length_thm (s : String) : length_prop s := by
  unfold length_prop
  have hlen : (quote s).length = (quoteList s.data).length := by
    simp only [quote, String.length_mk]
  rw [hlen, quoteList_length, length_data]

/-- `quote` never returns the empty string. -/
@[reducible] def nonempty_result_prop (s : String) : Prop :=
  quote s ≠ ""

theorem nonempty_result_thm (s : String) : nonempty_result_prop s := by
  intro h
  have hround := shellDecode_quoteList s.data
  have hdata : quoteList s.data = [] := by
    have : (quote s).data = [] := by simp [h]
    simpa [quote] using this
  rw [hdata] at hround
  have hempty : shellDecode [] = some [] := by simp [shellDecode, runDecode]
  rw [hempty] at hround
  have hnil : s.data = [] := Option.some.inj hround.symm
  simp [quoteList, escape, hnil] at hdata

/-- When the string is not returned raw, the result starts and ends with `'`. -/
@[reducible] def boundary_prop (s : String) : Prop :=
  (!s.data.isEmpty && s.data.all isSafeChar) = false →
    (quote s).data.head? = some '\'' ∧ (quote s).data.getLast? = some '\''

theorem boundary_thm (s : String) : boundary_prop s := by
  intro hcond
  have hform : (quote s).data = '\'' :: (escape s.data ++ ['\'']) := by
    simp [quote, quoteList, hcond]
  refine ⟨?_, ?_⟩
  · simp [hform]
  · have happ : '\'' :: (escape s.data ++ ['\'']) = ('\'' :: escape s.data) ++ ['\''] := by
      simp [List.cons_append]
    rw [hform, happ]
    exact List.getLast?_concat

/-- Non-empty safe strings are fixed points of `quote`. -/
@[reducible] def raw_id_prop (s : String) : Prop :=
  s ≠ "" → s.data.all isSafeChar = true → quote s = s

theorem raw_id_thm (s : String) : raw_id_prop s := by
  intro hne hall
  have hemp : s.data.isEmpty = false := by
    cases h : s.data.isEmpty
    · rfl
    · exact False.elim <| hne <| by
        have hnil : s.data = [] := List.isEmpty_iff.mp h
        exact String.ext hnil
  have h := algorithm_thm s
  simp only [algorithm_prop] at h
  rw [h]
  simp [hemp, hall]

/-- A string with an unsafe character is the wrapped escape. -/
@[reducible] def unsafe_wrap_prop (s : String) : Prop :=
  s.data.all isSafeChar = false →
    quote s = String.mk ('\'' :: (escape s.data ++ ['\'']))

theorem unsafe_wrap_thm (s : String) : unsafe_wrap_prop s := by
  intro hall
  have hemp : s.data.isEmpty = false := by
    cases h : s.data.isEmpty
    · rfl
    · have hnil : s.data = [] := List.isEmpty_iff.mp h
      simp [hnil] at hall
  have h := algorithm_thm s
  simp only [algorithm_prop] at h
  rw [h]
  simp [hemp, hall]

/-- Non-strings raise `TypeError: expected string object`. -/
@[reducible] def typeerror_prop (v : ShellInput) : Prop :=
  preQuote v = false → benchmarkQuote v = .error "expected string object"

theorem typeerror_thm (v : ShellInput) : typeerror_prop v := by
  intro h
  cases v with
  | nonString => rfl
  | str _ => simp [preQuote] at h

/-- On strings, `benchmark_quote` returns `quote`. -/
@[reducible] def benchmark_ok_prop (s : String) : Prop :=
  benchmarkQuote (.str s) = .ok (quote s)

theorem benchmark_ok_thm (s : String) : benchmark_ok_prop s := rfl

/-! ## Post-condition -/

/-- Successful `benchmark_quote` on a string: the Python control flow, a shell
round trip, the length formula, and the raw / wrapped boundary cases. -/
@[reducible] def Post_prop (s : String) : Prop :=
  algorithm_prop s ∧
  roundtrip_prop s ∧
  length_prop s ∧
  nonempty_result_prop s ∧
  boundary_prop s ∧
  raw_id_prop s ∧
  unsafe_wrap_prop s ∧
  benchmark_ok_prop s ∧
  empty_prop

instance instDecidableEqExceptString : DecidableEq (Except String String) := fun a b =>
  match a, b with
  | .ok x, .ok y =>
      if h : x = y then isTrue (h ▸ rfl) else isFalse (fun eq => h (by cases eq; rfl))
  | .error x, .error y =>
      if h : x = y then isTrue (h ▸ rfl) else isFalse (fun eq => h (by cases eq; rfl))
  | .ok _, .error _ => isFalse (fun eq => by cases eq)
  | .error _, .ok _ => isFalse (fun eq => by cases eq)

/-! ## Property-based tests -/

/-- Small alphabet covering safe characters, space, quotes, `$`, and a
non-ASCII letter. -/
def pbtChars : List Char := ['a', 'Z', '0', '/', ' ', '\'', '"', '$', 'ä', '_']

def extendWords (ws : List String) : List String :=
  ws.flatMap fun w => pbtChars.map fun c => w.push c

/-- Every string of length at most 2 over `pbtChars`, plus the empty string. -/
def boundedWords : List String :=
  let w0 : List String := [""]
  let w1 := extendWords w0
  let w2 := extendWords w1
  w0 ++ w1 ++ w2

example : decide empty_prop = true := by native_decide

example : boundedWords.all (fun s => decide (algorithm_prop s)) = true := by native_decide

example : boundedWords.all (fun s => decide (roundtrip_prop s)) = true := by native_decide

example : boundedWords.all (fun s => decide (length_prop s)) = true := by native_decide

example : boundedWords.all (fun s => decide (nonempty_result_prop s)) = true := by
  native_decide

example : boundedWords.all (fun s => decide (boundary_prop s)) = true := by native_decide

example : boundedWords.all (fun s => decide (raw_id_prop s)) = true := by native_decide

example : boundedWords.all (fun s => decide (unsafe_wrap_prop s)) = true := by native_decide

example : boundedWords.all (fun s => decide (benchmark_ok_prop s)) = true := by native_decide

example : boundedWords.all (fun s => decide (Post_prop s)) = true := by native_decide

example : (List.range 128).all (fun n => decide (charset_prop (Char.ofNat n))) = true := by
  native_decide

example : decide (typeerror_prop .nonString) && decide (typeerror_prop (.str "x")) = true := by
  native_decide

def injWords : List String := ["", "a", " ", "'", "ab", "a'b", "a b", "/", "ä"]

example : injWords.all (fun s => injWords.all (fun t => decide (injective_prop s t))) = true := by
  native_decide

/-- Modest random configuration so the file checks many strings without a long search. -/
def pbtCfg : Plausible.Configuration where
  numInst := 30
  maxSize := 12

#eval Plausible.Testable.check (∀ s : String, algorithm_prop s) pbtCfg

#eval Plausible.Testable.check (∀ s : String, roundtrip_prop s) pbtCfg

#eval Plausible.Testable.check (∀ s : String, length_prop s) pbtCfg

#eval Plausible.Testable.check (∀ s : String, nonempty_result_prop s) pbtCfg

#eval Plausible.Testable.check (∀ s : String, boundary_prop s) pbtCfg

#eval Plausible.Testable.check (∀ s : String, raw_id_prop s) pbtCfg

#eval Plausible.Testable.check (∀ s : String, unsafe_wrap_prop s) pbtCfg

#eval Plausible.Testable.check (∀ s : String, benchmark_ok_prop s) pbtCfg

#eval Plausible.Testable.check (∀ s : String, Post_prop s) pbtCfg

#eval Plausible.Testable.check (∀ s t : String, injective_prop s t) pbtCfg

#eval Plausible.Testable.check (∀ c : Char, charset_prop c) pbtCfg

/-! ## Correctness -/

theorem correctness_thm (s : String) (_h : Pre s) : Post_prop s :=
  ⟨algorithm_thm s, roundtrip_thm s, length_thm s, nonempty_result_thm s,
   boundary_thm s, raw_id_thm s, unsafe_wrap_thm s, benchmark_ok_thm s, empty_thm⟩

/-! ## Imperative implementation -/

/-- Mutable scan: every character is safe. Matches `str` truth of
`all(c in safe_chars for c in s)`, without short-circuit (the Bool result is the same). -/
def allSafeAcc (ok : Bool) (cs : List Char) : Bool :=
  Id.run do
    let mut ok := ok
    for c in cs do
      if !isSafeChar c then
        ok := false
    return ok

/-- Append the escape of one character. -/
def pushEscape (acc : List Char) (c : Char) : List Char :=
  acc ++ escapeChar c

/-- Mutable left-to-right build of `s.replace("'", "'\"'\"'")`. -/
def escapeAcc (acc : List Char) (cs : List Char) : List Char :=
  Id.run do
    let mut acc := acc
    for c in cs do
      acc := pushEscape acc c
    return acc

theorem allSafeAcc_nil (ok : Bool) : allSafeAcc ok [] = ok := by
  unfold allSafeAcc
  simp [List.forIn_nil, bind, pure, Id.run]

theorem allSafeAcc_cons (ok : Bool) (c : Char) (cs : List Char) :
    allSafeAcc ok (c :: cs) = allSafeAcc (ok && isSafeChar c) cs := by
  cases h : isSafeChar c <;>
    simp [allSafeAcc, List.forIn_cons, bind, pure, Id.run, h]

theorem allSafeAcc_eq (ok : Bool) (cs : List Char) :
    allSafeAcc ok cs = (ok && cs.all isSafeChar) := by
  induction cs generalizing ok with
  | nil => simp [allSafeAcc_nil, List.all_nil]
  | cons c cs ih =>
    rw [allSafeAcc_cons, ih, List.all_cons]
    cases ok <;> cases isSafeChar c <;> simp

theorem escapeAcc_nil (acc : List Char) : escapeAcc acc [] = acc := by
  unfold escapeAcc
  simp [List.forIn_nil, bind, pure, Id.run]

theorem escapeAcc_cons (acc : List Char) (c : Char) (cs : List Char) :
    escapeAcc acc (c :: cs) = escapeAcc (pushEscape acc c) cs := by
  simp only [escapeAcc, pushEscape, List.forIn_cons, bind, pure, Id.run]

theorem escapeAcc_eq (acc cs : List Char) : escapeAcc acc cs = acc ++ escape cs := by
  induction cs generalizing acc with
  | nil => simp [escapeAcc_nil, escape]
  | cons c cs ih =>
    rw [escapeAcc_cons, ih]
    simp [pushEscape, escape, List.flatMap_cons, List.append_assoc]

/-- Imperative `quote`: empty check, a mutable safe-scan, then a mutable escape. -/
def quoteImp (s : String) : String :=
  Id.run do
    let cs := s.data
    if cs.isEmpty then
      return "''"
    else if allSafeAcc true cs then
      return s
    else
      return String.mk ('\'' :: (escapeAcc [] cs ++ ['\'']))

/-! ## Imperative tests -/

example : quoteImp "" = "''" := by native_decide

example : quoteImp "abc" = "abc" := by native_decide

example : quoteImp "a b c" = "'a b c'" := by native_decide

example : quoteImp "a'b" = "'a'\"'\"'b'" := by native_decide

example : quoteImp "it's" = "'it'\"'\"'s'" := by native_decide

example : quote "a'b" = quoteImp "a'b" := by native_decide

example : quote "" = quoteImp "" := by native_decide

#eval quoteImp ""

#eval quoteImp "abc"

#eval quoteImp "a b c"

#eval quoteImp "a'b"

/-! ## Equivalence -/

theorem quote_equiv_thm (s : String) : quote s = quoteImp s := by
  cases hemp : s.data.isEmpty
  · cases hall : s.data.all isSafeChar <;>
      simp [quote, quoteImp, quoteList, hemp, hall, escape, Id.run, pure, allSafeAcc_eq,
        escapeAcc_eq, mk_data]
  · have hnil : s.data = [] := List.isEmpty_iff.mp hemp
    simp [quote, quoteImp, quoteList, hnil, escape, Id.run, pure]

end «21_shlex_quote»
