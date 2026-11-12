import Mathlib

/-!
# HTML-safe escaping - VeriBench task `20_html_escape`

This file formalises the Python program

```
def pre_escape(s):
    return isinstance(s, str)

def escape(s, quote=True):
    # Order matters: & must be first to avoid double-escaping
    s = s.replace("&", "&amp;")
    s = s.replace("<", "&lt;")
    s = s.replace(">", "&gt;")
    if quote:
        s = s.replace('"', "&quot;")
        s = s.replace("'", "&#x27;")
    return s

def benchmark_escape(s, quote=True):
    if not pre_escape(s):
        raise TypeError("expected str object")
    return escape(s, quote)
```

## Modelling notes

* Every pattern passed to Python's `str.replace` is a *single character*, and the
  ampersand substitution is performed first.  Hence the whole chain is exactly a
  character-wise map: each input character independently becomes either itself or
  its entity, and the `&` that an entity introduces is never re-escaped (this is
  precisely what "order matters" means in the Python comment).  `tokenOf`/`escapeGo`/
  `escape` below are that character-wise model, and they are the definitions every
  theorem in this file is proved about: Lean's `String.replace` is implemented with
  an opaque byte-offset loop that the kernel cannot reason about.
* `escapeReplace` is the literal transcription of the Python body with
  `String.replace`.  It is checked against `escape` on the Python unit tests and,
  in the property-based-test section, exhaustively on every string of length <= 4
  over the alphabet `& < > " ' a b`, which contains one representative of every
  character class the function distinguishes (the five special characters, plus two
  mutually distinct ordinary characters).
* Python is dynamically typed: `benchmark_escape` raises `TypeError` for a non-`str`
  argument.  `PyVal` models a Python value (either a `str` object or another object),
  `Pre` models `pre_escape`, and `benchmarkEscape` returns `Except String String`
  where `Except.error "expected str object"` models the raised `TypeError`.
* `unescape` decodes the five entities again; it is used to state (and prove) that
  escaping is lossless, i.e. injective.
-/

namespace HtmlEscape

/-! ## 1. Functional implementation -/

/-- The HTML-safe replacement of a single character: the five special characters
become their entity (the two quote characters only when `quote` is true), every
other character is left alone.  This is one step of Python's `str.replace` chain. -/
def tokenOf (c : Char) (quote : Bool) : List Char :=
  if c = '&' then ['&', 'a', 'm', 'p', ';']
  else if c = '<' then ['&', 'l', 't', ';']
  else if c = '>' then ['&', 'g', 't', ';']
  else if c = '"' then (if quote then ['&', 'q', 'u', 'o', 't', ';'] else ['"'])
  else if c = '\'' then (if quote then ['&', '#', 'x', '2', '7', ';'] else ['\''])
  else [c]

/-- Character-wise escaping of a whole character list. -/
def escapeGo : List Char → Bool → List Char
  | [], _ => []
  | c :: cs, quote => tokenOf c quote ++ escapeGo cs quote

/-- `html.escape`: replace the special characters `&`, `<`, `>` by HTML-safe
sequences, and additionally `"` and `'` when `quote` is true (the default). -/
def escape (s : String) (quote : Bool := true) : String :=
  String.mk (escapeGo s.toList quote)

/-- Literal transcription of the Python body, using `String.replace`. -/
def escapeReplace (s : String) (quote : Bool := true) : String :=
  let s1 := s.replace "&" "&amp;"
  let s2 := s1.replace "<" "&lt;"
  let s3 := s2.replace ">" "&gt;"
  if quote then (s3.replace "\"" "&quot;").replace "'" "&#x27;" else s3

/-- A Python-level value: either a `str` object or some other object. -/
inductive PyVal where
  | str : String → PyVal
  | other : PyVal

/-- `benchmark_escape`: raises `TypeError("expected str object")` when the argument
is not a string, otherwise returns `escape s quote`. -/
def benchmarkEscape (v : PyVal) (quote : Bool := true) : Except String String :=
  match v with
  | PyVal.str s => Except.ok (escape s quote)
  | PyVal.other => Except.error "expected str object"

/-- Pretty printer used by the `#eval` tests below (`Except` has no `Repr`). -/
def showExcept (e : Except String String) : String :=
  match e with
  | Except.ok s => "ok: " ++ s
  | Except.error m => "TypeError: " ++ m

/-! ## 2. Unit tests - the assertions of the Python `check` function -/

-- 1. quote = true (the default)
example : escape "<b>\"&'</b>" = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by native_decide
example : escape "" = "" := by rfl

-- 2. quote = false: `"` and `'` remain untouched
example : escape "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by native_decide

-- 3. order check: `&` is escaped first, so it is not double-escaped
example : escape "&<" = "&amp;&lt;" := by rfl
example : escape "&amp;" = "&amp;amp;" := by rfl

-- the same four assertions for the literal `String.replace` transcription
example : escapeReplace "<b>\"&'</b>" = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by native_decide
example : escapeReplace "" = "" := by native_decide
example : escapeReplace "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by native_decide
example : escapeReplace "&<" = "&amp;&lt;" := by native_decide
example : escapeReplace "&amp;" = "&amp;amp;" := by native_decide

-- `benchmark_escape` on a string argument
example : (benchmarkEscape (PyVal.str "<b>\"&'</b>")).toOption =
    some "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by native_decide
example : benchmarkEscape (PyVal.str "&<") false = Except.ok "&amp;&lt;" := by rfl
-- `benchmark_escape` on a non-string argument: the modelled `TypeError`
example : benchmarkEscape PyVal.other = Except.error "expected str object" := by rfl
example : benchmarkEscape PyVal.other false = Except.error "expected str object" := by rfl

#eval escape "<b>\"&'</b>"
#eval escape "<b>\"&'</b>" false
#eval escape "&<"
#eval escapeReplace "<b>\"&'</b>"
#eval escapeReplace "<b>\"&'</b>" false
#eval showExcept (benchmarkEscape (PyVal.str "a&b<c>"))
#eval showExcept (benchmarkEscape PyVal.other)

/-! ## 3. Pre-condition (`pre_escape`) -/

/-- `pre_escape(s)` is true iff the input is a string.  In the model this means that
the Python value is a `str` object. -/
def Pre (v : PyVal) : Prop := ∃ s : String, v = PyVal.str s

theorem Pre_str (s : String) : Pre (PyVal.str s) := ⟨s, rfl⟩

theorem not_Pre_other : ¬ Pre PyVal.other := by
  rintro ⟨s, h⟩
  cases h

/-! ## 4. Auxiliary definitions used to state the properties -/

/-- Exhaustive case analysis over the five characters that `escape` treats specially. -/
theorem char_eq_or_ne (c : Char) :
    c = '&' ∨ c = '<' ∨ c = '>' ∨ c = '"' ∨ c = '\'' ∨
      (c ≠ '&' ∧ c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '"' ∧ c ≠ '\'') := by
  by_cases h1 : c = '&'
  · exact Or.inl h1
  · by_cases h2 : c = '<'
    · exact Or.inr (Or.inl h2)
    · by_cases h3 : c = '>'
      · exact Or.inr (Or.inr (Or.inl h3))
      · by_cases h4 : c = '"'
        · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
        · by_cases h5 : c = '\''
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2, h3, h4, h5⟩))))

theorem decide_Char_eq_false {c d : Char} (h : c ≠ d) : decide (c = d) = false :=
  decide_eq_false_iff_not.mpr h

theorem tokenOf_eq_single (c : Char) (q : Bool)
    (h1 : c ≠ '&') (h2 : c ≠ '<') (h3 : c ≠ '>') (h4 : c ≠ '"') (h5 : c ≠ '\'') :
    tokenOf c q = [c] := by simp [tokenOf, h1, h2, h3, h4, h5]

/-- `true` iff `c` may not occur literally in the output of `escape · quote`. -/
def isRawSpecial (c : Char) (quote : Bool) : Bool :=
  decide (c = '<') || decide (c = '>') ||
    (quote && (decide (c = '"') || decide (c = '\'')))

/-- `true` iff some character of the list is a forbidden literal character. -/
def anyRawSpecial : List Char → Bool → Bool
  | [], _ => false
  | c :: cs, q => isRawSpecial c q || anyRawSpecial cs q

/-- `true` iff the list starts with the body of one of the five entities that
`escape` produces (`amp;`, `lt;`, `gt;`, `quot;`, `#x27;`). -/
def startsEntity : List Char → Bool
  | 'a' :: 'm' :: 'p' :: ';' :: _ => true
  | 'l' :: 't' :: ';' :: _ => true
  | 'g' :: 't' :: ';' :: _ => true
  | 'q' :: 'u' :: 'o' :: 't' :: ';' :: _ => true
  | '#' :: 'x' :: '2' :: '7' :: ';' :: _ => true
  | _ => false

/-- `true` iff every `&` of the list starts one of the five entities. -/
def ampOk : List Char → Bool
  | [] => true
  | c :: cs => (if c = '&' then startsEntity cs else true) && ampOk cs

/-- Number of occurrences of a character. -/
def countChar (x : Char) : List Char → Nat
  | [] => 0
  | c :: cs => (if c = x then 1 else 0) + countChar x cs

/-- Number of characters that `escape · quote` inserts. -/
def extraLen (cs : List Char) (q : Bool) : Nat :=
  4 * countChar '&' cs + 3 * countChar '<' cs + 3 * countChar '>' cs +
    (if q then 5 * countChar '"' cs + 5 * countChar '\'' cs else 0)

/-- Number of characters that `escape · quote` replaces by an entity. -/
def numEscaped (cs : List Char) (q : Bool) : Nat :=
  countChar '&' cs + countChar '<' cs + countChar '>' cs +
    (if q then countChar '"' cs + countChar '\'' cs else 0)

/-- The five special characters, as a proposition. -/
def IsSpecial (c : Char) : Prop := c = '&' ∨ c = '<' ∨ c = '>' ∨ c = '"' ∨ c = '\''

/-- The five special characters, as a Boolean (used by the property-based tests). -/
def isSpecialB (c : Char) : Bool :=
  decide (c = '&') || decide (c = '<') || decide (c = '>') ||
    decide (c = '"') || decide (c = '\'')

theorem isSpecialB_eq_false {c : Char} : isSpecialB c = false ↔ ¬ IsSpecial c := by
  by_cases h1 : c = '&' <;> by_cases h2 : c = '<' <;> by_cases h3 : c = '>' <;>
    by_cases h4 : c = '"' <;> by_cases h5 : c = '\'' <;>
    simp [isSpecialB, IsSpecial, *]

/- `unescapeGo` decodes the five entities again; `unescapeAmp cs` decodes a list `cs`
that directly follows a leading `&`.  Both are structurally recursive, so all the
equations used below hold definitionally. -/
mutual
/-- Decode every entity of a character list. -/
def unescapeGo : List Char → List Char
  | [] => []
  | c :: cs => if c = '&' then unescapeAmp cs else c :: unescapeGo cs

/-- Decode a character list that directly follows a leading `&`. -/
def unescapeAmp : List Char → List Char
  | 'a' :: 'm' :: 'p' :: ';' :: r => '&' :: unescapeGo r
  | 'l' :: 't' :: ';' :: r => '<' :: unescapeGo r
  | 'g' :: 't' :: ';' :: r => '>' :: unescapeGo r
  | 'q' :: 'u' :: 'o' :: 't' :: ';' :: r => '"' :: unescapeGo r
  | '#' :: 'x' :: '2' :: '7' :: ';' :: r => '\'' :: unescapeGo r
  | [] => ['&']
  | '&' :: r => '&' :: unescapeAmp r
  | d :: r => '&' :: d :: unescapeGo r
end

/-- The inverse of `escape` (like `html.unescape`, restricted to the five entities
that `escape` produces). -/
def unescape (s : String) : String := String.mk (unescapeGo s.toList)

/-! ## 5. Helper lemmas about the character-level model -/

theorem anyRawSpecial_append : ∀ (a b : List Char) (q : Bool),
    anyRawSpecial (a ++ b) q = (anyRawSpecial a q || anyRawSpecial b q)
  | [], b, q => by simp [anyRawSpecial]
  | c :: a, b, q => by simp [anyRawSpecial, anyRawSpecial_append a b q, Bool.or_assoc]

theorem tokenOf_no_raw (c : Char) (q : Bool) : anyRawSpecial (tokenOf c q) q = false := by
  rcases char_eq_or_ne c with (rfl|rfl|rfl|rfl|rfl|⟨h1,h2,h3,h4,h5⟩)
  · cases q <;> decide
  · cases q <;> decide
  · cases q <;> decide
  · cases q <;> decide
  · cases q <;> decide
  · rw [tokenOf_eq_single c q h1 h2 h3 h4 h5]
    simp [anyRawSpecial, isRawSpecial, decide_Char_eq_false h2, decide_Char_eq_false h3,
      decide_Char_eq_false h4, decide_Char_eq_false h5]

theorem escapeGo_no_raw (cs : List Char) (q : Bool) :
    anyRawSpecial (escapeGo cs q) q = false := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      show anyRawSpecial (tokenOf c q ++ escapeGo cs q) q = false
      rw [anyRawSpecial_append, tokenOf_no_raw, ih]
      simp

theorem startsEntity_amp (t : List Char) : startsEntity (['a','m','p',';'] ++ t) = true := by rfl
theorem startsEntity_lt (t : List Char) : startsEntity (['l','t',';'] ++ t) = true := by rfl
theorem startsEntity_gt (t : List Char) : startsEntity (['g','t',';'] ++ t) = true := by rfl
theorem startsEntity_quot (t : List Char) : startsEntity (['q','u','o','t',';'] ++ t) = true := by rfl
theorem startsEntity_apos (t : List Char) : startsEntity (['#','x','2','7',';'] ++ t) = true := by rfl

theorem noAmp_amp : ∀ x ∈ (['a','m','p',';'] : List Char), x ≠ '&' := by decide
theorem noAmp_lt : ∀ x ∈ (['l','t',';'] : List Char), x ≠ '&' := by decide
theorem noAmp_gt : ∀ x ∈ (['g','t',';'] : List Char), x ≠ '&' := by decide
theorem noAmp_quot : ∀ x ∈ (['q','u','o','t',';'] : List Char), x ≠ '&' := by decide
theorem noAmp_apos : ∀ x ∈ (['#','x','2','7',';'] : List Char), x ≠ '&' := by decide

theorem ampOk_append_noAmp : ∀ (L t : List Char), (∀ x ∈ L, x ≠ '&') → ampOk (L ++ t) = ampOk t
  | [], t, _ => by rfl
  | a :: l, t, h => by
      have ha : a ≠ '&' := h a (by simp)
      have hl : ∀ x ∈ l, x ≠ '&' := fun x hx => h x (by simp [hx])
      have ih := ampOk_append_noAmp l t hl
      show ((if a = '&' then startsEntity (l ++ t) else true) && ampOk (l ++ t)) = ampOk t
      rw [if_neg ha, Bool.true_and, ih]

theorem ampOk_single (c : Char) (t : List Char) (h : c ≠ '&') :
    ampOk ([c] ++ t) = ampOk t := by
  show ((if c = '&' then startsEntity t else true) && ampOk t) = ampOk t
  rw [if_neg h, Bool.true_and]

theorem ampOk_amp (t : List Char) : ampOk (['&','a','m','p',';'] ++ t) = ampOk t := by
  show ((if '&' = '&' then startsEntity (['a','m','p',';'] ++ t) else true) &&
      ampOk (['a','m','p',';'] ++ t)) = ampOk t
  rw [if_pos (rfl : '&' = '&'), startsEntity_amp, Bool.true_and,
    ampOk_append_noAmp (['a','m','p',';']) t noAmp_amp]

theorem ampOk_lt (t : List Char) : ampOk (['&','l','t',';'] ++ t) = ampOk t := by
  show ((if '&' = '&' then startsEntity (['l','t',';'] ++ t) else true) &&
      ampOk (['l','t',';'] ++ t)) = ampOk t
  rw [if_pos (rfl : '&' = '&'), startsEntity_lt, Bool.true_and,
    ampOk_append_noAmp (['l','t',';']) t noAmp_lt]

theorem ampOk_gt (t : List Char) : ampOk (['&','g','t',';'] ++ t) = ampOk t := by
  show ((if '&' = '&' then startsEntity (['g','t',';'] ++ t) else true) &&
      ampOk (['g','t',';'] ++ t)) = ampOk t
  rw [if_pos (rfl : '&' = '&'), startsEntity_gt, Bool.true_and,
    ampOk_append_noAmp (['g','t',';']) t noAmp_gt]

theorem ampOk_quot (t : List Char) : ampOk (['&','q','u','o','t',';'] ++ t) = ampOk t := by
  show ((if '&' = '&' then startsEntity (['q','u','o','t',';'] ++ t) else true) &&
      ampOk (['q','u','o','t',';'] ++ t)) = ampOk t
  rw [if_pos (rfl : '&' = '&'), startsEntity_quot, Bool.true_and,
    ampOk_append_noAmp (['q','u','o','t',';']) t noAmp_quot]

theorem ampOk_apos (t : List Char) : ampOk (['&','#','x','2','7',';'] ++ t) = ampOk t := by
  show ((if '&' = '&' then startsEntity (['#','x','2','7',';'] ++ t) else true) &&
      ampOk (['#','x','2','7',';'] ++ t)) = ampOk t
  rw [if_pos (rfl : '&' = '&'), startsEntity_apos, Bool.true_and,
    ampOk_append_noAmp (['#','x','2','7',';']) t noAmp_apos]

theorem ampOk_tokenOf (c : Char) (q : Bool) (t : List Char) :
    ampOk (tokenOf c q ++ t) = ampOk t := by
  rcases char_eq_or_ne c with (rfl|rfl|rfl|rfl|rfl|⟨h1,h2,h3,h4,h5⟩)
  · exact ampOk_amp t
  · exact ampOk_lt t
  · exact ampOk_gt t
  · cases q with
    | true => exact ampOk_quot t
    | false => exact ampOk_single '"' t (by decide)
  · cases q with
    | true => exact ampOk_apos t
    | false => exact ampOk_single '\'' t (by decide)
  · rw [tokenOf_eq_single c q h1 h2 h3 h4 h5]
    exact ampOk_single c t h1

theorem escapeGo_ampOk (cs : List Char) (q : Bool) : ampOk (escapeGo cs q) = true := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      show ampOk (tokenOf c q ++ escapeGo cs q) = true
      rw [ampOk_tokenOf c q (escapeGo cs q), ih]

theorem unescapeGo_amp (r : List Char) :
    unescapeGo (['&','a','m','p',';'] ++ r) = '&' :: unescapeGo r := by rfl
theorem unescapeGo_lt (r : List Char) :
    unescapeGo (['&','l','t',';'] ++ r) = '<' :: unescapeGo r := by rfl
theorem unescapeGo_gt (r : List Char) :
    unescapeGo (['&','g','t',';'] ++ r) = '>' :: unescapeGo r := by rfl
theorem unescapeGo_quot (r : List Char) :
    unescapeGo (['&','q','u','o','t',';'] ++ r) = '"' :: unescapeGo r := by rfl
theorem unescapeGo_apos (r : List Char) :
    unescapeGo (['&','#','x','2','7',';'] ++ r) = '\'' :: unescapeGo r := by rfl

theorem unescapeGo_cons_ne (c : Char) (t : List Char) (h : c ≠ '&') :
    unescapeGo ([c] ++ t) = c :: unescapeGo t := by simp [unescapeGo, h]

theorem unescapeGo_escapeGo (cs : List Char) (q : Bool) : unescapeGo (escapeGo cs q) = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      show unescapeGo (tokenOf c q ++ escapeGo cs q) = c :: cs
      rcases char_eq_or_ne c with (rfl|rfl|rfl|rfl|rfl|⟨h1,h2,h3,h4,h5⟩)
      · rw [show tokenOf '&' q = ['&','a','m','p',';'] from rfl, unescapeGo_amp, ih]
      · rw [show tokenOf '<' q = ['&','l','t',';'] from rfl, unescapeGo_lt, ih]
      · rw [show tokenOf '>' q = ['&','g','t',';'] from rfl, unescapeGo_gt, ih]
      · cases q with
        | true =>
            rw [show tokenOf '"' true = ['&','q','u','o','t',';'] from rfl, unescapeGo_quot, ih]
        | false =>
            rw [show tokenOf '"' false = ['"'] from rfl, unescapeGo_cons_ne '"' _ (by decide), ih]
      · cases q with
        | true =>
            rw [show tokenOf '\'' true = ['&','#','x','2','7',';'] from rfl, unescapeGo_apos, ih]
        | false =>
            rw [show tokenOf '\'' false = ['\''] from rfl,
              unescapeGo_cons_ne '\'' _ (by decide), ih]
      · rw [tokenOf_eq_single c q h1 h2 h3 h4 h5, unescapeGo_cons_ne c _ h1, ih]

theorem countChar_append (x : Char) : ∀ (a b : List Char),
    countChar x (a ++ b) = countChar x a + countChar x b
  | [], b => by simp [countChar]
  | a :: as, b => by
      show (if a = x then 1 else 0) + countChar x (as ++ b) =
        ((if a = x then 1 else 0) + countChar x as) + countChar x b
      rw [countChar_append x as b]
      omega

theorem tokenOf_length (c : Char) (q : Bool) :
    (tokenOf c q).length =
      1 + 4 * (if c = '&' then 1 else 0) + 3 * (if c = '<' then 1 else 0) +
        3 * (if c = '>' then 1 else 0) +
        (if q then 5 * (if c = '"' then 1 else 0) + 5 * (if c = '\'' then 1 else 0) else 0) := by
  rcases char_eq_or_ne c with (rfl|rfl|rfl|rfl|rfl|⟨h1,h2,h3,h4,h5⟩) <;>
    cases q <;> simp [tokenOf, *]

theorem escapeGo_length (cs : List Char) (q : Bool) :
    (escapeGo cs q).length = cs.length + extraLen cs q := by
  induction cs with
  | nil => simp [escapeGo, extraLen, countChar]
  | cons c cs ih =>
      simp only [escapeGo, List.length_append, List.length_cons, extraLen, countChar, ih,
        tokenOf_length]
      rcases char_eq_or_ne c with (rfl|rfl|rfl|rfl|rfl|⟨h1,h2,h3,h4,h5⟩) <;>
        cases q <;> simp [*] <;> omega

theorem countChar_amp_tokenOf (c : Char) (q : Bool) :
    countChar '&' (tokenOf c q) =
      (if c = '&' then 1 else 0) + (if c = '<' then 1 else 0) + (if c = '>' then 1 else 0) +
        (if q then (if c = '"' then 1 else 0) + (if c = '\'' then 1 else 0) else 0) := by
  rcases char_eq_or_ne c with (rfl|rfl|rfl|rfl|rfl|⟨h1,h2,h3,h4,h5⟩) <;>
    cases q <;> simp [tokenOf, countChar, *]

theorem countChar_dq_tokenOf (c : Char) (q : Bool) :
    countChar '"' (tokenOf c q) = (if q then 0 else if c = '"' then 1 else 0) := by
  rcases char_eq_or_ne c with (rfl|rfl|rfl|rfl|rfl|⟨h1,h2,h3,h4,h5⟩) <;>
    cases q <;> simp [tokenOf, countChar, *]

theorem countChar_sq_tokenOf (c : Char) (q : Bool) :
    countChar '\'' (tokenOf c q) = (if q then 0 else if c = '\'' then 1 else 0) := by
  rcases char_eq_or_ne c with (rfl|rfl|rfl|rfl|rfl|⟨h1,h2,h3,h4,h5⟩) <;>
    cases q <;> simp [tokenOf, countChar, *]

theorem escapeGo_ampCount (cs : List Char) (q : Bool) :
    countChar '&' (escapeGo cs q) = numEscaped cs q := by
  induction cs with
  | nil => simp [escapeGo, countChar, numEscaped]
  | cons c cs ih =>
      simp only [escapeGo, countChar_append, countChar_amp_tokenOf, countChar, numEscaped, ih]
      cases q <;> simp <;> omega

theorem escapeGo_quotePreserved (cs : List Char) :
    countChar '"' (escapeGo cs false) = countChar '"' cs ∧
    countChar '\'' (escapeGo cs false) = countChar '\'' cs := by
  induction cs with
  | nil => simp [escapeGo, countChar]
  | cons c cs ih =>
      constructor
      · show countChar '"' (tokenOf c false ++ escapeGo cs false) =
          (if c = '"' then 1 else 0) + countChar '"' cs
        rw [countChar_append, countChar_dq_tokenOf, ih.1]
        simp
      · show countChar '\'' (tokenOf c false ++ escapeGo cs false) =
          (if c = '\'' then 1 else 0) + countChar '\'' cs
        rw [countChar_append, countChar_sq_tokenOf, ih.2]
        simp

theorem escapeGo_id : ∀ (cs : List Char) (q : Bool),
    (∀ c ∈ cs, ¬ IsSpecial c) → escapeGo cs q = cs
  | [], q, _ => rfl
  | c :: cs, q, h => by
      have hc : ¬ IsSpecial c := h c (by simp)
      have hcs : ∀ x ∈ cs, ¬ IsSpecial x := fun x hx => h x (by simp [hx])
      have h1 : c ≠ '&' := fun e => hc (Or.inl e)
      have h2 : c ≠ '<' := fun e => hc (Or.inr (Or.inl e))
      have h3 : c ≠ '>' := fun e => hc (Or.inr (Or.inr (Or.inl e)))
      have h4 : c ≠ '"' := fun e => hc (Or.inr (Or.inr (Or.inr (Or.inl e))))
      have h5 : c ≠ '\'' := fun e => hc (Or.inr (Or.inr (Or.inr (Or.inr e))))
      show tokenOf c q ++ escapeGo cs q = c :: cs
      rw [tokenOf_eq_single c q h1 h2 h3 h4 h5, escapeGo_id cs q hcs]
      rfl

theorem escapeGo_append : ∀ (a b : List Char) (q : Bool),
    escapeGo (a ++ b) q = escapeGo a q ++ escapeGo b q
  | [], b, q => by rfl
  | a :: as, b, q => by
      show tokenOf a q ++ escapeGo (as ++ b) q =
        (tokenOf a q ++ escapeGo as q) ++ escapeGo b q
      rw [escapeGo_append as b q, List.append_assoc]

theorem escapeGo_eq_flatten_map (cs : List Char) (q : Bool) :
    escapeGo cs q = (cs.map (fun c => tokenOf c q)).flatten := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [escapeGo, List.map, List.flatten, ih]

/-! ## 6. Properties of `escape` and their proofs -/

/-- Property 1. The output contains no literal `<` or `>` and, when `quote` is true,
no literal `"` or `'`: every such character has been replaced by an HTML-safe
sequence. -/
def no_raw_specials_prop (s : String) (quote : Bool) : Prop :=
  anyRawSpecial (escape s quote).toList quote = false

theorem no_raw_specials_thm (s : String) (quote : Bool) : no_raw_specials_prop s quote :=
  escapeGo_no_raw s.toList quote

/-- Property 2. Every `&` of the output starts one of the five entities
`&amp;`, `&lt;`, `&gt;`, `&quot;`, `&#x27;` - the output is well-formed escaped HTML. -/
def amp_entity_prop (s : String) (quote : Bool) : Prop :=
  ampOk (escape s quote).toList = true

theorem amp_entity_thm (s : String) (quote : Bool) : amp_entity_prop s quote :=
  escapeGo_ampOk s.toList quote

/-- Property 3. Escaping is lossless: decoding the entities gives the input back. -/
def roundtrip_prop (s : String) (quote : Bool) : Prop := unescape (escape s quote) = s

theorem roundtrip_thm (s : String) (quote : Bool) : roundtrip_prop s quote := by
  show String.mk (unescapeGo (escapeGo s.toList quote)) = s
  rw [unescapeGo_escapeGo]
  rfl

/-- Property 4. Exact output length: `&` adds four characters, `<` and `>` add three
each, and (when `quote` is true) `"` and `'` add five each. -/
def length_prop (s : String) (quote : Bool) : Prop :=
  (escape s quote).length = s.length + extraLen s.toList quote

theorem length_thm (s : String) (quote : Bool) : length_prop s quote :=
  escapeGo_length s.toList quote

/-- Property 5. The output contains exactly one `&` per escaped character.  This is
the precise meaning of the Python comment "order matters: & must be first to avoid
double-escaping": the `&` that an entity introduces is never escaped again. -/
def amp_count_prop (s : String) (quote : Bool) : Prop :=
  countChar '&' (escape s quote).toList = numEscaped s.toList quote

theorem amp_count_thm (s : String) (quote : Bool) : amp_count_prop s quote :=
  escapeGo_ampCount s.toList quote

/-- Property 6. With `quote = false` the quotation marks are left untouched. -/
def quote_preserved_prop (s : String) : Prop :=
  countChar '"' (escape s false).toList = countChar '"' s.toList ∧
  countChar '\'' (escape s false).toList = countChar '\'' s.toList

theorem quote_preserved_thm (s : String) : quote_preserved_prop s :=
  escapeGo_quotePreserved s.toList

/-- Property 7. A string that contains none of the five special characters is
returned unchanged. -/
def unchanged_prop (s : String) (quote : Bool) : Prop :=
  (∀ c ∈ s.toList, ¬ IsSpecial c) → escape s quote = s

theorem unchanged_thm (s : String) (quote : Bool) : unchanged_prop s quote := by
  intro h
  show String.mk (escapeGo s.toList quote) = s
  rw [escapeGo_id s.toList quote h]
  rfl

/-- Property 8. Escaping distributes over concatenation. -/
def append_prop (s t : String) (quote : Bool) : Prop :=
  escape (s ++ t) quote = escape s quote ++ escape t quote

theorem append_thm (s t : String) (quote : Bool) : append_prop s t quote := by
  show String.mk (escapeGo (s ++ t).toList quote) =
    String.mk (escapeGo s.toList quote) ++ String.mk (escapeGo t.toList quote)
  rw [show (s ++ t).toList = s.toList ++ t.toList from rfl, escapeGo_append]
  rfl

/-- Property 9. The empty string is a fixed point (Python: `escape('') == ''`). -/
def empty_prop (quote : Bool) : Prop := escape "" quote = ""

theorem empty_thm (quote : Bool) : empty_prop quote := rfl

/-- Property 10. The five substitutions of the Python `str.replace` chain. -/
def substitution_prop : Prop :=
  (∀ quote : Bool, escape "&" quote = "&amp;" ∧ escape "<" quote = "&lt;" ∧
      escape ">" quote = "&gt;") ∧
  escape "\"" true = "&quot;" ∧ escape "'" true = "&#x27;" ∧
  escape "\"" false = "\"" ∧ escape "'" false = "'"

theorem substitution_thm : substitution_prop :=
  ⟨fun q => by cases q <;> exact ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩

/-- Property 11. Escaping is injective (a consequence of the round-trip). -/
def injective_prop (quote : Bool) : Prop :=
  Function.Injective (fun s : String => escape s quote)

theorem injective_thm (quote : Bool) : injective_prop quote :=
  Function.LeftInverse.injective (fun s => roundtrip_thm s quote)

/-- Property 12. No double escaping: an entity that is already in the input has only
its `&` escaped, and the Python test `escape("&<") == "&amp;&lt;"` holds. -/
def no_double_escape_prop : Prop :=
  escape "&amp;" = "&amp;amp;" ∧ escape "&<" = "&amp;&lt;" ∧
    escape "&amp;" false = "&amp;amp;" ∧ escape "&<" false = "&amp;&lt;"

theorem no_double_escape_thm : no_double_escape_prop := ⟨rfl, rfl, rfl, rfl⟩

/-! ## 7. Post-condition -/

/-- The post-condition of `benchmark_escape`.  For a `str` argument the result is
`Except.ok (escape s quote)` and every property of `escape` proved above holds; for a
non-string argument the result is the modelled `TypeError`. -/
def Post_prop (v : PyVal) (quote : Bool) (r : Except String String) : Prop :=
  match v with
  | PyVal.str s =>
      r = Except.ok (escape s quote) ∧
      no_raw_specials_prop s quote ∧
      amp_entity_prop s quote ∧
      roundtrip_prop s quote ∧
      length_prop s quote ∧
      amp_count_prop s quote ∧
      quote_preserved_prop s ∧
      unchanged_prop s quote ∧
      (∀ t : String, append_prop s t quote) ∧
      empty_prop quote ∧
      substitution_prop ∧
      injective_prop quote ∧
      no_double_escape_prop
  | PyVal.other => r = Except.error "expected str object"

/-! ## 8. Property-based tests -/

/-- All words of length <= `n` over `alpha` (as character lists). -/
def wordsOf (alpha : List Char) : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 => ((wordsOf alpha n).map (fun w => alpha.map (fun c => w ++ [c]))).flatten

/-- An alphabet containing the five special characters plus two ordinary ones: every
character class that `escape` distinguishes is represented. -/
def specialAlpha : List Char := ['&', '<', '>', '"', '\'', 'a', 'b']

/-- Hand-picked interesting inputs. -/
def pool : List String :=
  ["", "&", "<", ">", "\"", "'", "a", "&<", "<b>\"&'</b>", "&amp;", "&#x27;",
   "a&b<c>d\"e'f", "&&<<>>\"\"''", "&amp;&lt;", "x'y\"z", "&\"'<>", "abc", "&a&m?p;"]

#eval (wordsOf specialAlpha 2).length

/-- Safe indexing into `pool` (Plausible's `Nat` sampler is unbounded). -/
def poolGet (n : Nat) : String := pool.getD n ""

-- executable (Boolean) forms of the properties
def no_raw_specials_check (s : String) (q : Bool) : Bool :=
  anyRawSpecial (escape s q).toList q == false

def amp_entity_check (s : String) (q : Bool) : Bool := ampOk (escape s q).toList

def roundtrip_check (s : String) (q : Bool) : Bool := unescape (escape s q) == s

def length_check (s : String) (q : Bool) : Bool :=
  (escape s q).length == s.length + extraLen s.toList q

def amp_count_check (s : String) (q : Bool) : Bool :=
  countChar '&' (escape s q).toList == numEscaped s.toList q

def quote_preserved_check (s : String) : Bool :=
  countChar '"' (escape s false).toList == countChar '"' s.toList &&
  countChar '\'' (escape s false).toList == countChar '\'' s.toList

def unchanged_check (s : String) (q : Bool) : Bool :=
  if s.toList.all (fun c => isSpecialB c == false) then escape s q == s else true

def append_check (s t : String) (q : Bool) : Bool :=
  escape (s ++ t) q == escape s q ++ escape t q

def empty_check (q : Bool) : Bool := escape "" q == ""

def substitution_check : Bool :=
  (escape "&" true == "&amp;") && (escape "&" false == "&amp;") &&
  (escape "<" true == "&lt;") && (escape "<" false == "&lt;") &&
  (escape ">" true == "&gt;") && (escape ">" false == "&gt;") &&
  (escape "\"" true == "&quot;") && (escape "'" true == "&#x27;") &&
  (escape "\"" false == "\"") && (escape "'" false == "'")

def injective_check (s t : String) (q : Bool) : Bool :=
  if escape s q == escape t q then s == t else true

def no_double_escape_check : Bool :=
  (escape "&amp;" == "&amp;amp;") && (escape "&<" == "&amp;&lt;") &&
  (escape "&amp;" false == "&amp;amp;") && (escape "&<" false == "&amp;&lt;")

/-- Executable form of the whole post-condition (both branches of `benchmarkEscape`). -/
def post_check (s t : String) (q : Bool) : Bool :=
  (benchmarkEscape (PyVal.str s) q).toOption == some (escape s q) &&
  (benchmarkEscape PyVal.other q).toOption == (none : Option String) &&
  no_raw_specials_check s q && amp_entity_check s q && roundtrip_check s q &&
  length_check s q && amp_count_check s q && quote_preserved_check s &&
  unchanged_check s q && append_check s t q && empty_check q &&
  substitution_check && injective_check s t q && no_double_escape_check

-- PBT: randomized (Plausible samples `String`, `Bool` and `Nat`)
#eval Plausible.Testable.check (∀ s : String, ∀ q : Bool, no_raw_specials_check s q = true)
#eval Plausible.Testable.check (∀ s : String, ∀ q : Bool, amp_entity_check s q = true)
#eval Plausible.Testable.check (∀ s : String, ∀ q : Bool, roundtrip_check s q = true)
#eval Plausible.Testable.check (∀ s : String, ∀ q : Bool, length_check s q = true)
#eval Plausible.Testable.check (∀ s : String, ∀ q : Bool, amp_count_check s q = true)
#eval Plausible.Testable.check (∀ s : String, quote_preserved_check s = true)
#eval Plausible.Testable.check (∀ s : String, ∀ q : Bool, unchanged_check s q = true)
#eval Plausible.Testable.check (∀ s t : String, ∀ q : Bool, append_check s t q = true)
#eval Plausible.Testable.check (∀ q : Bool, empty_check q = true)
#eval Plausible.Testable.check (substitution_check = true)
#eval Plausible.Testable.check (∀ s t : String, ∀ q : Bool, injective_check s t q = true)
#eval Plausible.Testable.check (no_double_escape_check = true)
#eval Plausible.Testable.check (∀ s t : String, ∀ q : Bool, post_check s t q = true)

-- PBT: randomized over the pool of hand-picked inputs (random `String`s rarely hit
-- the five special characters, so the pool makes these checks meaningful)
#eval Plausible.Testable.check
  (∀ n m : Nat, ∀ q : Bool, post_check (poolGet n) (poolGet m) q = true)
#eval Plausible.Testable.check
  (∀ n m : Nat, ∀ q : Bool, append_check (poolGet n) (poolGet m) q = true)
#eval Plausible.Testable.check
  (∀ n m : Nat, ∀ q : Bool, injective_check (poolGet n) (poolGet m) q = true)

-- PBT: bounded / exhaustive over every word of length <= 3 on `specialAlpha`
example : (wordsOf specialAlpha 3).all (fun cs => [true, false].all (fun q =>
    no_raw_specials_check (String.mk cs) q && amp_entity_check (String.mk cs) q &&
    roundtrip_check (String.mk cs) q && length_check (String.mk cs) q &&
    amp_count_check (String.mk cs) q && unchanged_check (String.mk cs) q)) = true := by
  native_decide

example : (wordsOf specialAlpha 3).all (fun cs =>
    quote_preserved_check (String.mk cs)) = true := by native_decide

example : (wordsOf specialAlpha 2).all (fun cs => (wordsOf specialAlpha 2).all (fun ds =>
    [true, false].all (fun q => post_check (String.mk cs) (String.mk ds) q))) = true := by
  native_decide

example : substitution_check = true := by native_decide
example : no_double_escape_check = true := by native_decide

-- PBT: the character-wise model `escape` agrees with the literal `String.replace`
-- transcription `escapeReplace` on every word of length <= 4 over `specialAlpha`.
example : (wordsOf specialAlpha 4).all (fun cs => [true, false].all (fun q =>
    escapeReplace (String.mk cs) q == escape (String.mk cs) q)) = true := by native_decide

#eval (wordsOf specialAlpha 4).all (fun cs => [true, false].all (fun q =>
    escapeReplace (String.mk cs) q == escape (String.mk cs) q))

/-! ## 9. Correctness theorem: `Pre -> Post` -/

theorem correctness (v : PyVal) (quote : Bool) (h : Pre v) :
    Post_prop v quote (benchmarkEscape v quote) := by
  obtain ⟨s, rfl⟩ := h
  exact ⟨rfl, no_raw_specials_thm s quote, amp_entity_thm s quote, roundtrip_thm s quote,
    length_thm s quote, amp_count_thm s quote, quote_preserved_thm s, unchanged_thm s quote,
    fun t => append_thm s t quote, empty_thm quote, substitution_thm, injective_thm quote,
    no_double_escape_thm⟩

/-- The other branch of `benchmark_escape`: a non-string argument yields the modelled
`TypeError`. -/
theorem correctness_type_error (quote : Bool) :
    Post_prop PyVal.other quote (benchmarkEscape PyVal.other quote) := rfl

theorem benchmarkEscape_type_error (quote : Bool) :
    benchmarkEscape PyVal.other quote = Except.error "expected str object" := rfl

/-! ## 10. Imperative implementation (`Id.run do` with mutable state) -/

/-- Imperative transcription of `escape`: a mutable accumulator is extended, one
input character at a time, with that character's HTML-safe replacement. -/
def escapeImp (s : String) (quote : Bool := true) : String :=
  Id.run do
    let mut out : List Char := []
    for c in s.toList do
      out := out ++ tokenOf c quote
    return String.mk out

/-- Imperative transcription of `benchmark_escape`: a mutable result variable that
stays at the modelled `TypeError` unless the input really is a string. -/
def benchmarkEscapeImp (v : PyVal) (quote : Bool := true) : Except String String :=
  Id.run do
    let mut res : Except String String := Except.error "expected str object"
    match v with
    | PyVal.str s => res := Except.ok (escapeImp s quote)
    | PyVal.other => res := Except.error "expected str object"
    return res

/-! ## 11. Imperative tests -/

example : escapeImp "<b>\"&'</b>" = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by native_decide
example : escapeImp "" = "" := by native_decide
example : escapeImp "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by native_decide
example : escapeImp "&<" = "&amp;&lt;" := by native_decide
example : escapeImp "&amp;" = "&amp;amp;" := by native_decide
example : (benchmarkEscapeImp (PyVal.str "a&b<c>")).toOption = some "a&amp;b&lt;c&gt;" := by
  native_decide
example : benchmarkEscapeImp PyVal.other = Except.error "expected str object" := by rfl

#eval escapeImp "<b>\"&'</b>"
#eval escapeImp "<b>\"&'</b>" false
#eval escapeImp "&<"
#eval showExcept (benchmarkEscapeImp (PyVal.str "a&b<c>"))
#eval showExcept (benchmarkEscapeImp PyVal.other)

-- PBT: randomized, functional = imperative
#eval Plausible.Testable.check (∀ s : String, ∀ q : Bool, escapeImp s q = escape s q)
#eval Plausible.Testable.check
  (∀ n : Nat, ∀ q : Bool, escapeImp (poolGet n) q = escape (poolGet n) q)
#eval Plausible.Testable.check
  (∀ n : Nat, ∀ q : Bool, (benchmarkEscapeImp (PyVal.str (poolGet n)) q).toOption =
    (benchmarkEscape (PyVal.str (poolGet n)) q).toOption)
#eval Plausible.Testable.check
  (∀ q : Bool, (benchmarkEscapeImp PyVal.other q).toOption =
    (benchmarkEscape PyVal.other q).toOption)

-- PBT: bounded / exhaustive over every word of length <= 3 on `specialAlpha`
example : (wordsOf specialAlpha 3).all (fun cs => [true, false].all (fun q =>
    escapeImp (String.mk cs) q == escape (String.mk cs) q)) = true := by native_decide

example : (wordsOf specialAlpha 3).all (fun cs => [true, false].all (fun q =>
    escapeImp (String.mk cs) q == escapeReplace (String.mk cs) q)) = true := by native_decide

/-! ## 12. Equivalence: functional = imperative -/

theorem escapeImp_eq_escape (s : String) (quote : Bool) :
    escapeImp s quote = escape s quote := by
  simp [escapeImp, escape, escapeGo_eq_flatten_map]

theorem benchmarkEscapeImp_eq (v : PyVal) (quote : Bool) :
    benchmarkEscapeImp v quote = benchmarkEscape v quote := by
  cases v with
  | str s => simp [benchmarkEscapeImp, benchmarkEscape, escapeImp_eq_escape]
  | other => simp [benchmarkEscapeImp, benchmarkEscape]

/-- The imperative implementation satisfies the same specification. -/
theorem correctness_imp (v : PyVal) (quote : Bool) (h : Pre v) :
    Post_prop v quote (benchmarkEscapeImp v quote) := by
  rw [benchmarkEscapeImp_eq]
  exact correctness v quote h

/-! ## 13. Axiom audit: every theorem above only uses the three standard axioms -/

#print axioms no_raw_specials_thm
#print axioms amp_entity_thm
#print axioms roundtrip_thm
#print axioms length_thm
#print axioms amp_count_thm
#print axioms quote_preserved_thm
#print axioms unchanged_thm
#print axioms append_thm
#print axioms empty_thm
#print axioms substitution_thm
#print axioms injective_thm
#print axioms no_double_escape_thm
#print axioms correctness
#print axioms correctness_type_error
#print axioms benchmarkEscape_type_error
#print axioms escapeImp_eq_escape
#print axioms benchmarkEscapeImp_eq
#print axioms correctness_imp

end HtmlEscape
