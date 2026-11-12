import Mathlib

/-!
# HTML escaping (port of Python's `html.escape`)

This file formalizes the Python program that replaces the special characters
`&`, `<` and `>` by their HTML-safe entities and -- when the optional flag
`quote` is set (the default) -- also the two quotation marks `"` and `'`.

The Python implementation performs five *sequential* string replacements, and
the order matters: `&` has to be rewritten first, otherwise the ampersands
introduced by the later replacements would be escaped a second time.

Contents:

* `escapeChar` / `escapeList` / `escape` : the functional (per-character) model;
* `escapeSeq` : a faithful transcription of Python's sequential `str.replace`
  chain, proved equal to the per-character model (`escapeSeq_eq_thm`);
* a collection of correctness properties, assembled into `Post_prop` and proved
  in `correctness_thm`;
* `escapeImp` : an imperative implementation using `Id.run do` and a mutable
  accumulator, proved equal to the functional one (`escape_eq_escapeImp_thm`).
-/

namespace «20_html_escape»

/-! ## Implementation (functional) -/

/-- The HTML entity a single character is replaced by.  `quote` decides whether
the two quotation marks are escaped as well. -/
def escapeChar (quote : Bool) (c : Char) : List Char :=
  if c = '&' then "&amp;".toList
  else if c = '<' then "&lt;".toList
  else if c = '>' then "&gt;".toList
  else if c = '"' then (if quote then "&quot;".toList else ['"'])
  else if c = '\'' then (if quote then "&#x27;".toList else ['\''])
  else [c]

/-- Escaping of a list of characters. -/
def escapeList (quote : Bool) (l : List Char) : List Char :=
  l.flatMap (escapeChar quote)

/-- `escape s quote` is the Lean counterpart of Python's `escape(s, quote)`. -/
def escape (s : String) (quote : Bool := true) : String :=
  ⟨escapeList quote s.data⟩

/-- `benchmark_escape`.  The Python function raises `TypeError` unless the
argument is a string; in Lean that is guaranteed by the type, so the wrapper
simply calls `escape`. -/
def benchmarkEscape (s : String) (quote : Bool := true) : String :=
  escape s quote

/-! ### Python's sequential replacement chain -/

/-- `repl c r l` replaces every occurrence of the character `c` in `l` by the
list `r`; this is Python's `str.replace` for a one-character pattern. -/
def repl (c : Char) (r : List Char) (l : List Char) : List Char :=
  l.flatMap (fun x => if x = c then r else [x])

/-- Literal transcription of the body of Python's `escape`: the five
replacements performed one after another, in exactly that order. -/
def escapeSeq (quote : Bool) (l : List Char) : List Char :=
  if quote then
    repl '\'' "&#x27;".toList
      (repl '"' "&quot;".toList
        (repl '>' "&gt;".toList (repl '<' "&lt;".toList (repl '&' "&amp;".toList l))))
  else
    repl '>' "&gt;".toList (repl '<' "&lt;".toList (repl '&' "&amp;".toList l))

/-! ## Unit tests (mirroring the Python `check` function) -/

-- 1. quote = True (the default)
example : escape "<b>\"&'</b>" = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by native_decide
example : escape "" = "" := by native_decide
-- 2. quote = False: `"` and `'` are left untouched
example : escape "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by native_decide
-- 3. order check: `&` is escaped first, so no double escaping happens
example : escape "&<" = "&amp;&lt;" := by native_decide
example : benchmarkEscape "&<" = "&amp;&lt;" := by native_decide

#eval escape "<b>\"&'</b>"
#eval escape "<b>\"&'</b>" false
#eval escape "&<"

/-! ## Pre-condition -/

/-- Python's `pre_escape` demands `isinstance(s, str)`; in Lean the argument is
already a `String`, so the pre-condition holds unconditionally. -/
def Pre (_s : String) : Prop := True

/-! ## Basic simplification lemmas -/

@[simp] theorem escapeChar_amp (q : Bool) : escapeChar q '&' = ['&', 'a', 'm', 'p', ';'] := rfl
@[simp] theorem escapeChar_lt (q : Bool) : escapeChar q '<' = ['&', 'l', 't', ';'] := rfl
@[simp] theorem escapeChar_gt (q : Bool) : escapeChar q '>' = ['&', 'g', 't', ';'] := rfl
@[simp] theorem escapeChar_dq_true : escapeChar true '"' = ['&', 'q', 'u', 'o', 't', ';'] := rfl
@[simp] theorem escapeChar_dq_false : escapeChar false '"' = ['"'] := rfl
@[simp] theorem escapeChar_sq_true : escapeChar true '\'' = ['&', '#', 'x', '2', '7', ';'] := rfl
@[simp] theorem escapeChar_sq_false : escapeChar false '\'' = ['\''] := rfl

theorem escapeChar_other (q : Bool) (c : Char) (h1 : c ≠ '&') (h2 : c ≠ '<') (h3 : c ≠ '>')
    (h4 : c ≠ '"') (h5 : c ≠ '\'') : escapeChar q c = [c] := by
  simp [escapeChar, h1, h2, h3, h4, h5]

@[simp] theorem escapeList_nil (q : Bool) : escapeList q [] = [] := by
  simp [escapeList]

@[simp] theorem escapeList_cons (q : Bool) (x : Char) (xs : List Char) :
    escapeList q (x :: xs) = escapeChar q x ++ escapeList q xs := by
  simp [escapeList]

theorem escapeList_append (q : Bool) (l₁ l₂ : List Char) :
    escapeList q (l₁ ++ l₂) = escapeList q l₁ ++ escapeList q l₂ := by
  simp [escapeList]

/-! ## Properties -/

/-- `escape` maps the empty string to the empty string. -/
def escape_empty_prop (q : Bool) : Prop := escape "" q = ""

theorem escape_empty_thm (q : Bool) : escape_empty_prop q := by
  simp [escape_empty_prop, escape, escapeList]

/-- `escape` is a homomorphism for concatenation: it acts character-wise. -/
def escape_append_prop (s t : String) (q : Bool) : Prop :=
  escape (s ++ t) q = escape s q ++ escape t q

theorem escape_append_thm (s t : String) (q : Bool) : escape_append_prop s t q := by
  show escape (s ++ t) q = escape s q ++ escape t q
  have h : (s ++ t).data = s.data ++ t.data := rfl
  simp [escape, h, escapeList_append]
  rfl

/-- Escaping never shortens the string. -/
def escape_length_prop (s : String) (q : Bool) : Prop :=
  s.data.length ≤ (escape s q).data.length

theorem escapeChar_length_pos (q : Bool) (c : Char) : 1 ≤ (escapeChar q c).length := by
  unfold escapeChar
  split_ifs <;> simp

theorem escape_length_thm (s : String) (q : Bool) : escape_length_prop s q := by
  show s.data.length ≤ (escape s q).data.length
  simp only [escape, escapeList]
  induction s.data with
  | nil => simp
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.length_cons, List.length_append]
      have := escapeChar_length_pos q x
      omega

/-! ### The output is HTML-safe -/

theorem escapeChar_safe (q : Bool) (c : Char) :
    '<' ∉ escapeChar q c ∧ '>' ∉ escapeChar q c ∧
      (q = true → '"' ∉ escapeChar q c ∧ '\'' ∉ escapeChar q c) := by
  by_cases h1 : c = '&'
  · subst h1; cases q <;> simp
  · by_cases h2 : c = '<'
    · subst h2; cases q <;> simp
    · by_cases h3 : c = '>'
      · subst h3; cases q <;> simp
      · by_cases h4 : c = '"'
        · subst h4; cases q <;> simp
        · by_cases h5 : c = '\''
          · subst h5; cases q <;> simp
          · rw [escapeChar_other q c h1 h2 h3 h4 h5]
            simp [Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5]

/-- No unescaped `<` or `>` survives, and with `quote = true` no quotation mark
survives either. -/
def escape_safe_prop (s : String) (q : Bool) : Prop :=
  '<' ∉ (escape s q).data ∧ '>' ∉ (escape s q).data ∧
    (q = true → '"' ∉ (escape s q).data ∧ '\'' ∉ (escape s q).data)

theorem escape_safe_thm (s : String) (q : Bool) : escape_safe_prop s q := by
  have key : ∀ (d : Char), (∀ x, d ∉ escapeChar q x) → d ∉ (escape s q).data := by
    intro d hd
    simp only [escape, escapeList, List.mem_flatMap, not_exists, not_and]
    exact fun x _ => hd x
  refine ⟨key '<' (fun x => (escapeChar_safe q x).1),
          key '>' (fun x => (escapeChar_safe q x).2.1), ?_⟩
  intro hq
  exact ⟨key '"' (fun x => ((escapeChar_safe q x).2.2 hq).1),
         key '\'' (fun x => ((escapeChar_safe q x).2.2 hq).2)⟩

/-- With `quote = false` the quotation marks are left untouched. -/
def escape_noquote_prop (s : String) : Prop :=
  ('"' ∈ s.data → '"' ∈ (escape s false).data) ∧
    ('\'' ∈ s.data → '\'' ∈ (escape s false).data)

theorem escape_noquote_thm (s : String) : escape_noquote_prop s := by
  constructor
  · intro h
    simp only [escape, escapeList, List.mem_flatMap]
    exact ⟨'"', h, by simp⟩
  · intro h
    simp only [escape, escapeList, List.mem_flatMap]
    exact ⟨'\'', h, by simp⟩

/-- A string containing none of the five special characters is left unchanged. -/
def escape_id_prop (s : String) (q : Bool) : Prop :=
  (∀ c ∈ s.data, c ≠ '&' ∧ c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '"' ∧ c ≠ '\'') → escape s q = s

theorem escapeList_id (q : Bool) : ∀ (l : List Char),
    (∀ c ∈ l, c ≠ '&' ∧ c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '"' ∧ c ≠ '\'') → escapeList q l = l
  | [], _ => by simp
  | x :: xs, h => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := h x (by simp)
      have ih := escapeList_id q xs (fun c hc => h c (by simp [hc]))
      rw [escapeList_cons, escapeChar_other q x h1 h2 h3 h4 h5, ih]
      simp

theorem escape_id_thm (s : String) (q : Bool) : escape_id_prop s q := by
  intro h
  show (⟨escapeList q s.data⟩ : String) = s
  rw [escapeList_id q s.data h]

/-! ### Python's sequential replacements agree with the character-wise model -/

@[simp] theorem repl_nil (c : Char) (r : List Char) : repl c r [] = [] := by
  simp [repl]

theorem repl_singleton (c x : Char) (r : List Char) :
    repl c r [x] = if x = c then r else [x] := by
  simp [repl]

theorem repl_append (c : Char) (r l₁ l₂ : List Char) :
    repl c r (l₁ ++ l₂) = repl c r l₁ ++ repl c r l₂ := by
  simp [repl]

theorem escapeSeq_append (q : Bool) (l₁ l₂ : List Char) :
    escapeSeq q (l₁ ++ l₂) = escapeSeq q l₁ ++ escapeSeq q l₂ := by
  cases q <;> simp [escapeSeq, repl_append]

theorem escapeSeq_singleton (q : Bool) (x : Char) :
    escapeSeq q [x] = escapeChar q x := by
  cases q <;>
    simp only [escapeSeq, escapeChar, if_true, if_false, Bool.false_eq_true] <;>
    split_ifs with h1 h2 h3 h4 h5 <;>
    subst_vars <;>
    simp only [repl_singleton] <;>
    first
      | decide
      | simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, repl_singleton]

/-- Doing the five replacements one after another (Python's implementation, with
`&` first) is the same as replacing every character in a single pass -- i.e. no
entity introduced by an earlier replacement is escaped again by a later one. -/
def escapeSeq_eq_prop (s : String) (q : Bool) : Prop :=
  escapeSeq q s.data = (escape s q).data

theorem escapeSeq_eq_escapeList (q : Bool) (l : List Char) :
    escapeSeq q l = escapeList q l := by
  induction l with
  | nil => cases q <;> simp [escapeSeq]
  | cons x xs ih =>
      have hx : x :: xs = [x] ++ xs := rfl
      rw [hx, escapeSeq_append, escapeSeq_singleton, ih, escapeList_append,
        escapeList_cons, escapeList_nil, List.append_nil]

theorem escapeSeq_eq_thm (s : String) (q : Bool) : escapeSeq_eq_prop s q := by
  simp [escapeSeq_eq_prop, escape, escapeSeq_eq_escapeList]

/-! ## Post-condition and total correctness -/

/-- Everything `benchmark_escape` guarantees about its result. -/
def Post_prop (s : String) (q : Bool) (out : String) : Prop :=
  out = escape s q ∧
  escapeSeq q s.data = out.data ∧
  s.data.length ≤ out.data.length ∧
  '<' ∉ out.data ∧ '>' ∉ out.data ∧
  (q = true → '"' ∉ out.data ∧ '\'' ∉ out.data) ∧
  (q = false → ('"' ∈ s.data → '"' ∈ out.data) ∧ ('\'' ∈ s.data → '\'' ∈ out.data)) ∧
  ((∀ c ∈ s.data, c ≠ '&' ∧ c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '"' ∧ c ≠ '\'') → out = s)

/-- Correctness of `benchmarkEscape`: the pre-condition implies the
post-condition. -/
theorem correctness_thm (s : String) (q : Bool) (_h : Pre s) :
    Post_prop s q (benchmarkEscape s q) := by
  obtain ⟨hlt, hgt, hq⟩ := escape_safe_thm s q
  refine ⟨rfl, escapeSeq_eq_thm s q, escape_length_thm s q, hlt, hgt, hq, ?_,
    escape_id_thm s q⟩
  rintro rfl
  exact escape_noquote_thm s

/-! ## Imperative implementation -/

/-- The loop of the imperative implementation: walk over the characters of `l`,
appending each character's escape to a mutable accumulator. -/
def escapeImpAux (quote : Bool) (l : List Char) (acc : String) : String := Id.run do
  let mut out : String := acc
  for c in l do
    if c = '&' then
      out := out ++ "&amp;"
    else if c = '<' then
      out := out ++ "&lt;"
    else if c = '>' then
      out := out ++ "&gt;"
    else if c = '"' then
      out := out ++ (if quote then "&quot;" else "\"")
    else if c = '\'' then
      out := out ++ (if quote then "&#x27;" else "'")
    else
      out := out.push c
  return out

/-- Imperative counterpart of `escape`. -/
def escapeImp (s : String) (quote : Bool := true) : String :=
  escapeImpAux quote s.data ""

/-! ### Imperative unit tests -/

example : escapeImp "<b>\"&'</b>" = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by native_decide
example : escapeImp "" = "" := by native_decide
example : escapeImp "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by native_decide
example : escapeImp "&<" = "&amp;&lt;" := by native_decide

#eval escapeImp "<b>\"&'</b>"
#eval escapeImp "<b>\"&'</b>" false

/-! ### The functional and the imperative version agree -/

/-- Loop invariant: running the loop over `l` from an arbitrary accumulator
appends exactly the escaping of `l`. -/
theorem escapeImpAux_data (quote : Bool) (l : List Char) (acc : String) :
    (escapeImpAux quote l acc).data = acc.data ++ escapeList quote l := by
  induction l generalizing acc with
  | nil => simp [escapeImpAux, escapeList]
  | cons x xs ih =>
      cases quote <;>
        (simp [escapeImpAux, escapeList, escapeChar, Id.run] at *
         split_ifs <;> simp [ih])

def escape_eq_escapeImp_prop (s : String) (q : Bool) : Prop :=
  escape s q = escapeImp s q

theorem escape_eq_escapeImp_thm (s : String) (q : Bool) : escape_eq_escapeImp_prop s q := by
  show escape s q = escapeImp s q
  apply String.ext
  simp [escapeImp, escapeImpAux_data, escape]

/-- The imperative version also satisfies the post-condition. -/
theorem escapeImp_correct_thm (s : String) (q : Bool) (h : Pre s) :
    Post_prop s q (escapeImp s q) := by
  have := correctness_thm s q h
  rwa [show benchmarkEscape s q = escapeImp s q from escape_eq_escapeImp_thm s q] at this

end «20_html_escape»
