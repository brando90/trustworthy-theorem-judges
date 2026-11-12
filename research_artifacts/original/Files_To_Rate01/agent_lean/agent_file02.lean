import Mathlib

/-!
# VeriBench Task 20: HTML escape

Formalization of Python's `html.escape` from the standard `html` library.

The Python program replaces the special characters `&`, `<`, `>` (and, when the
optional flag `quote` is true, also the quotation marks `"` and `'`) with
HTML-safe sequences.  Because the replacements introduced by the escaping only
contain characters that have already been processed (the `&` replacement happens
first), the sequential string replacements of the Python program are equivalent
to a character-by-character map, which is how we model the function here:
`escapeChar` maps a single character to its replacement (as a list of
characters) and `escape` flat-maps it over the characters of the input string.

Contents:
* `escapeChar`, `escape` - the functional implementation.
* Unit tests (via `example ... := by native_decide` and `#eval`).
* `Pre` - the precondition (Python's `isinstance(s, str)`, which is discharged
  by Lean's type system, hence `True`).
* Properties (`escape_preserves_safe_prop`, `escape_append_prop`,
  `escape_no_special_prop`, `escape_quote_false_prop`) with proofs.
* `Post_prop` - the conjunction of the properties, and the correctness theorem
  `correctness_thm : Pre s → Post_prop`.
* Bounded/exhaustive property-based tests for every property and the
  post-condition.
* `escapeImp` - an imperative implementation using `Id.run do` with mutable
  state, its tests, and the equivalence theorem `escapeImp_eq_escape`.
-/

namespace «20_html_escape»

def escapeChar (c : Char) (quote : Bool) : List Char :=
  if c = '&' then ['&','a','m','p',';']
  else if c = '<' then ['&','l','t',';']
  else if c = '>' then ['&','g','t',';']
  else if quote then
    (if c = '"' then ['&','q','u','o','t',';']
     else if c = '\'' then ['&','#','x','2','7',';']
     else [c])
  else [c]

def escape (s : String) (quote : Bool := true) : String :=
  String.mk (s.toList.flatMap fun c => escapeChar c quote)

example : escape "<b>\"&'</b>" = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by native_decide
example : escape "" = "" := by native_decide
example : escape "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by native_decide
example : escape "&<" = "&amp;&lt;" := by native_decide
#eval escape "<b>\"&'</b>"

def Pre (_s : String) : Prop := True

theorem escapeChar_of_not_special (c : Char) (q : Bool)
    (h1 : c ≠ '&') (h2 : c ≠ '<') (h3 : c ≠ '>') (h4 : c ≠ '"') (h5 : c ≠ '\'') :
    escapeChar c q = [c] := by
  simp [escapeChar, h1, h2, h3, h4, h5]

theorem escapeChar_quote_false (c : Char)
    (h1 : c ≠ '&') (h2 : c ≠ '<') (h3 : c ≠ '>') :
    escapeChar c false = [c] := by
  simp [escapeChar, h1, h2, h3]

theorem escapeChar_mem_safe (c d : Char) (q : Bool) (hd : d ∈ escapeChar c q) :
    d ≠ '<' ∧ d ≠ '>' ∧ (q = true → d ≠ '"' ∧ d ≠ '\'') := by
  unfold escapeChar at hd
  split_ifs at hd <;> fin_cases hd <;> simp_all

theorem flatMap_escapeChar_self (l : List Char) (q : Bool)
    (h : ∀ c ∈ l, c ≠ '&' ∧ c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '"' ∧ c ≠ '\'') :
    l.flatMap (fun c => escapeChar c q) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := h x List.mem_cons_self
    rw [List.flatMap_cons, escapeChar_of_not_special x q h1 h2 h3 h4 h5,
      ih (fun c hc => h c (List.mem_cons_of_mem x hc))]
    rfl

theorem flatMap_escapeChar_quote_false (l : List Char)
    (h : ∀ c ∈ l, c ≠ '&' ∧ c ≠ '<' ∧ c ≠ '>') :
    l.flatMap (fun c => escapeChar c false) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨h1, h2, h3⟩ := h x List.mem_cons_self
    rw [List.flatMap_cons, escapeChar_quote_false x h1 h2 h3,
      ih (fun c hc => h c (List.mem_cons_of_mem x hc))]
    rfl

def escape_preserves_safe_prop : Prop :=
  ∀ s : String, ∀ quote : Bool,
    (∀ c ∈ s.toList, c ≠ '&' ∧ c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '"' ∧ c ≠ '\'') →
    escape s quote = s

def escape_append_prop : Prop :=
  ∀ s₁ s₂ : String, ∀ quote : Bool,
    escape (s₁ ++ s₂) quote = escape s₁ quote ++ escape s₂ quote

def escape_no_special_prop : Prop :=
  ∀ s : String, ∀ quote : Bool, ∀ c ∈ (escape s quote).toList,
    c ≠ '<' ∧ c ≠ '>' ∧ (quote = true → c ≠ '"' ∧ c ≠ '\'')

def escape_quote_false_prop : Prop :=
  ∀ s : String, (∀ c ∈ s.toList, c ≠ '&' ∧ c ≠ '<' ∧ c ≠ '>') → escape s false = s

theorem escape_preserves_safe_thm : escape_preserves_safe_prop := by
  intro s q h
  unfold escape
  rw [flatMap_escapeChar_self s.toList q h]
  rfl

theorem escape_append_thm : escape_append_prop := by
  intro s1 s2 q
  show String.mk ((s1.toList ++ s2.toList).flatMap fun c => escapeChar c q) =
       String.mk (s1.toList.flatMap fun c => escapeChar c q) ++ String.mk (s2.toList.flatMap fun c => escapeChar c q)
  rw [List.flatMap_append]
  rfl

theorem escape_no_special_thm : escape_no_special_prop := by
  intro s q d hd
  have hd' : d ∈ s.toList.flatMap (fun c => escapeChar c q) := hd
  rw [List.mem_flatMap] at hd'
  obtain ⟨c, _, hd''⟩ := hd'
  exact escapeChar_mem_safe c d q hd''

theorem escape_quote_false_thm : escape_quote_false_prop := by
  intro s h
  unfold escape
  rw [flatMap_escapeChar_quote_false s.toList h]
  rfl

def Post_prop : Prop :=
  escape_preserves_safe_prop ∧ escape_append_prop ∧ escape_no_special_prop ∧ escape_quote_false_prop

theorem correctness_thm (s : String) (_q : Bool) : Pre s → Post_prop :=
  fun _ => ⟨escape_preserves_safe_thm, escape_append_thm, escape_no_special_thm, escape_quote_false_thm⟩

-- PBT infrastructure
def pbtAlphabet : List Char := ['a', '&', '<', '>', '"', '\'']

def allListsOfLen (alpha : List Char) : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 => (allListsOfLen alpha n).flatMap fun rest => alpha.map fun c => c :: rest

def allStringsUpTo (n : Nat) : List String :=
  (List.range (n + 1)).flatMap fun k => (allListsOfLen pbtAlphabet k).map String.mk

example : (allStringsUpTo 4).all (fun s =>
    let safe := s.toList.all (fun c => c != '&' && c != '<' && c != '>' && c != '"' && c != '\'')
    (!safe) || (escape s true == s && escape s false == s)) = true := by native_decide

example : (allStringsUpTo 3).all (fun s1 => (allStringsUpTo 3).all (fun s2 =>
    (escape (s1 ++ s2) true == escape s1 true ++ escape s2 true) &&
    (escape (s1 ++ s2) false == escape s1 false ++ escape s2 false))) = true := by native_decide

example : (allStringsUpTo 4).all (fun s =>
    ((escape s true).toList.all (fun c => c != '<' && c != '>' && c != '"' && c != '\'')) &&
    ((escape s false).toList.all (fun c => c != '<' && c != '>'))) = true := by native_decide

example : (allStringsUpTo 4).all (fun s =>
    let nospec := s.toList.all (fun c => c != '&' && c != '<' && c != '>')
    (!nospec) || (escape s false == s)) = true := by native_decide

def escapeImp (s : String) (quote : Bool := true) : String := Id.run do
  let mut out : List Char := []
  for c in s.toList do
    out := out ++ escapeChar c quote
  return String.mk out

example : escapeImp "<b>\"&'</b>" = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by native_decide
example : escapeImp "" = "" := by native_decide
example : escapeImp "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by native_decide
example : escapeImp "&<" = "&amp;&lt;" := by native_decide
#eval escapeImp "<b>\"&'</b>"

theorem escapeImp_loop (as l : List Char) (q : Bool) :
    ∀ (acc : List Char) (h : ∃ bs, bs ++ l = as),
    List.forIn'.loop (m := Id) as (fun c _ out => pure (ForInStep.yield (out ++ escapeChar c q))) l acc h =
      acc ++ l.flatMap (fun c => escapeChar c q) := by
  induction l with
  | nil =>
    intro acc h
    show acc = acc ++ []
    rw [List.append_nil]
  | cons x xs ih =>
    intro acc h
    show List.forIn'.loop (m := Id) as (fun c _ out => pure (ForInStep.yield (out ++ escapeChar c q))) xs
        (acc ++ escapeChar x q) _ = acc ++ (x :: xs).flatMap (fun c => escapeChar c q)
    rw [ih, List.flatMap_cons, ← List.append_assoc]

theorem escapeImp_eq_escape (s : String) (q : Bool) : escapeImp s q = escape s q := by
  show String.mk (List.forIn'.loop (m := Id) s.toList (fun c _ out => pure (ForInStep.yield (out ++ escapeChar c q))) s.toList [] _) =
       String.mk (s.toList.flatMap fun c => escapeChar c q)
  rw [escapeImp_loop, List.nil_append]

end «20_html_escape»
