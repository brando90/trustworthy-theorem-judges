import Mathlib

/-!
# VeriBench 20 -- HTML-safe escaping (`html.escape`)

Formalisation of the Python program

```python
# -- Pre-condition --
def pre_escape(s) -> bool:
    return isinstance(s, str)

# -- Implementation --
def escape(s, quote=True):
    # Order matters: & must be first to avoid double-escaping
    s = s.replace("&", "&amp;")
    s = s.replace("<", "&lt;")
    s = s.replace(">", "&gt;")
    if quote:
        s = s.replace('"', "&quot;")
        s = s.replace('\'', "&#x27;")
    return s

def benchmark_escape(s, quote=True):
    if not pre_escape(s):
        raise TypeError("expected str object")
    return escape(s, quote)
```

## Modelling notes

* Python is dynamically typed, so the pre-condition `isinstance(s, str)` is modelled with an
  inductive type `PyValue` of Python-like values. `Pre v` states that `v` is a string, and
  `benchmarkEscape` returns `Except String String` so that the `TypeError` branch of the source
  program is representable instead of being hidden in the type system.
* In Lean 4.22 `String.replace` is implemented directly on the UTF-8 byte array
  (`String.replace.loop`), which the kernel cannot reason about symbolically. The *verified*
  implementation `escape` therefore performs exactly the same five replacements at the character
  level (`escTokenChars`), which is precisely what the left-to-right `str.replace` scan of the
  Python source computes (the `&` replacement first, then `<`, `>`, and -- when `quote` is set --
  `"` and `'`). The literal transliteration `escapeReplace`, written with `String.replace`, is kept
  as well; it is checked to agree with `escape` on the Python test vectors, on random strings and
  exhaustively on all strings of length <= 3 over an alphabet containing every special character.
* `unescape` decodes the five entities; `unescape (escape s q) = s` is the formal statement that
  the escaping is lossless and that `&` is replaced first (no double escaping).
* `entitiesOk cs` states that every `&` occurring in `cs` begins one of the five entities, i.e.
  the output of `escape` never contains a "bare" ampersand.
* The namespace is `X20_html_escape` because a Lean identifier may not begin with a digit, so
  `namespace 20_html_escape` is not legal syntax.
* Proof policy: every `theorem` below is accepted by the Lean kernel and depends only on
  `propext`, `Classical.choice` and `Quot.sound`; no proof placeholder and no extra axiom is used
  anywhere, and `native_decide` appears only inside `example` tests, never inside a theorem proof.
-/


namespace X20_html_escape

/-! ## 1. A small model of dynamically typed Python values -/

inductive PyValue where
  | str  : String → PyValue
  | int  : Int → PyValue
  | bool : Bool → PyValue
  | none : PyValue
  | list : List PyValue → PyValue
  deriving Inhabited, Repr

/-- The string carried by a value (used only after the pre-condition has been checked). -/
def PyValue.asString : PyValue → String
  | PyValue.str s => s
  | _ => ""

@[simp] theorem PyValue.asString_str (s : String) : (PyValue.str s).asString = s := rfl

/-! ## 2. Functional implementation -/

/-- The five HTML entities produced by `escape`, as character lists. -/
def ampEntity  : List Char := ['&', 'a', 'm', 'p', ';']      -- `&amp;`
def ltEntity   : List Char := ['&', 'l', 't', ';']           -- `&lt;`
def gtEntity   : List Char := ['&', 'g', 't', ';']           -- `&gt;`
def quotEntity : List Char := ['&', 'q', 'u', 'o', 't', ';'] -- `&quot;`
def aposEntity : List Char := ['&', '#', 'x', '2', '7', ';'] -- `&#x27;`

theorem ampEntity_str  : String.mk ampEntity  = "&amp;"   := rfl
theorem ltEntity_str   : String.mk ltEntity   = "&lt;"    := rfl
theorem gtEntity_str   : String.mk gtEntity   = "&gt;"    := rfl
theorem quotEntity_str : String.mk quotEntity = "&quot;"  := rfl
theorem aposEntity_str : String.mk aposEntity = "&#x27;"  := rfl

/-- The characters that `escape` translates. -/
def specialChars : List Char := ['&', '<', '>', '"', '\'']

/-- The HTML-safe replacement of a single character: this is the character level version of the
five `str.replace` calls of the Python source (the `&` replacement comes first, and the last two
are performed only when `quote` is true). -/
def escTokenChars (quote : Bool) (c : Char) : List Char :=
  if c = '&' then ampEntity
  else if c = '<' then ltEntity
  else if c = '>' then gtEntity
  else if c = '"' then (if quote then quotEntity else ['"'])
  else if c = '\'' then (if quote then aposEntity else ['\''])
  else [c]

/-- The replacement of a single character, as a `String`. -/
def escToken (quote : Bool) (c : Char) : String := String.mk (escTokenChars quote c)

/-- `escape` on character lists: every character is replaced by its token, left to right. -/
def escapeChars (quote : Bool) (cs : List Char) : List Char :=
  (cs.map (escTokenChars quote)).flatten

@[simp] theorem escapeChars_nil (quote : Bool) : escapeChars quote [] = [] := rfl

@[simp] theorem escapeChars_cons (quote : Bool) (c : Char) (cs : List Char) :
    escapeChars quote (c :: cs) = escTokenChars quote c ++ escapeChars quote cs := rfl

/-- The function under verification: `html.escape(s, quote)`. -/
def escape (s : String) (quote : Bool := true) : String :=
  String.mk (escapeChars quote s.toList)

/-- The literal transliteration of the Python body, using `String.replace`.
It is used in the tests below to check that `escape` really computes what the Python
`str.replace` chain computes. -/
def escapeReplace (s : String) (quote : Bool := true) : String :=
  let s1 := s.replace "&" "&amp;"
  let s2 := s1.replace "<" "&lt;"
  let s3 := s2.replace ">" "&gt;"
  if quote then (s3.replace "\"" "&quot;").replace "'" "&#x27;" else s3

/-! ## 3. Decoding and entity well-formedness -/

mutual
/-- Decode a list of characters, translating the five entities back to the characters
they stand for. -/
def unescapeChars : List Char → List Char
  | [] => []
  | c :: r => if c = '&' then unescapeAmpTail r else c :: unescapeChars r

/-- Decode the text that follows an ampersand. -/
def unescapeAmpTail : List Char → List Char
  | 'a' :: 'm' :: 'p' :: ';' :: r => '&' :: unescapeChars r
  | 'l' :: 't' :: ';' :: r => '<' :: unescapeChars r
  | 'g' :: 't' :: ';' :: r => '>' :: unescapeChars r
  | 'q' :: 'u' :: 'o' :: 't' :: ';' :: r => '"' :: unescapeChars r
  | '#' :: 'x' :: '2' :: '7' :: ';' :: r => '\'' :: unescapeChars r
  | [] => ['&']
  | '&' :: r => '&' :: unescapeAmpTail r
  | c :: r => '&' :: c :: unescapeChars r
end

def unescape (s : String) : String := String.mk (unescapeChars s.toList)

theorem unescapeChars_amp (r : List Char) :
    unescapeChars (ampEntity ++ r) = '&' :: unescapeChars r := by
  rfl
theorem unescapeChars_lt (r : List Char) :
    unescapeChars (ltEntity ++ r) = '<' :: unescapeChars r := by
  rfl
theorem unescapeChars_gt (r : List Char) :
    unescapeChars (gtEntity ++ r) = '>' :: unescapeChars r := by
  rfl
theorem unescapeChars_quot (r : List Char) :
    unescapeChars (quotEntity ++ r) = '"' :: unescapeChars r := by
  rfl
theorem unescapeChars_apos (r : List Char) :
    unescapeChars (aposEntity ++ r) = '\'' :: unescapeChars r := by
  rfl
theorem unescapeChars_cons_ne (c : Char) (h : c ≠ '&') (r : List Char) :
    unescapeChars (c :: r) = c :: unescapeChars r := by simp only [unescapeChars, if_neg h]

/-- Does `r` begin with the body of one of the five entities? -/
def startsEntityBody : List Char → Bool
  | 'a' :: 'm' :: 'p' :: ';' :: _ => true
  | 'l' :: 't' :: ';' :: _ => true
  | 'g' :: 't' :: ';' :: _ => true
  | 'q' :: 'u' :: 'o' :: 't' :: ';' :: _ => true
  | '#' :: 'x' :: '2' :: '7' :: ';' :: _ => true
  | _ => false

/-- `entitiesOk cs` is true iff every `&` in `cs` begins one of the five entities, i.e. `cs`
contains no bare (un-escaped) ampersand. -/
def entitiesOk : List Char → Bool
  | [] => true
  | c :: r => (if c = '&' then startsEntityBody r else true) && entitiesOk r

theorem entitiesOk_cons (c : Char) (r : List Char) :
    entitiesOk (c :: r) = ((if c = '&' then startsEntityBody r else true) && entitiesOk r) := rfl

@[simp] theorem entitiesOk_nil : entitiesOk [] = true := rfl

/-! ## 4. Unit tests -- the `check` function of the Python source -/

/-- Direct transliteration of the Python `check` test function. -/
def check (f : String → Bool → String) : Bool :=
  (f "<b>\"&'</b>" true == "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;") &&
  (f "" true == "") &&
  (f "<b>\"&'</b>" false == "&lt;b&gt;\"&amp;'&lt;/b&gt;") &&
  (f "&<" true == "&amp;&lt;")

example : escape "<b>\"&'</b>" true = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by native_decide
example : escape "" true = "" := by native_decide
example : escape "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by native_decide
example : escape "&<" true = "&amp;&lt;" := by native_decide
example : escape "&amp;" true = "&amp;amp;" := by native_decide
example : check (fun s q => escape s q) = true := by native_decide
example : check (fun s q => escapeReplace s q) = true := by native_decide
example : escapeReplace "&<" true = "&amp;&lt;" := by native_decide

#eval escape "<b>\"&'</b>"        -- "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;"
#eval escape "<b>\"&'</b>" false  -- "&lt;b&gt;\"&amp;'&lt;/b&gt;"
#eval escape "" true              -- ""
#eval escape "&<"                 -- "&amp;&lt;"
#eval escape "&amp;"              -- "&amp;amp;"  (no double escaping)
#eval escapeReplace "<b>\"&'</b>"
#eval escapeReplace "<b>\"&'</b>" false
#eval check (fun s q => escape s q)
#eval check (fun s q => escapeReplace s q)

/-! ## 5. Pre-condition and the entry point `benchmark_escape` -/

/-- `pre_escape(s) := isinstance(s, str)`. -/
def preEscape (v : PyValue) : Bool :=
  match v with
  | PyValue.str _ => true
  | _ => false

/-- The pre-condition of `benchmark_escape`: the argument has to be a string. -/
def Pre (v : PyValue) : Prop := ∃ s : String, v = PyValue.str s

theorem preEscape_iff (v : PyValue) : (preEscape v = true) ↔ Pre v := by
  cases v <;> simp [preEscape, Pre]

/-- `benchmark_escape`: raises `TypeError` when the pre-condition fails. -/
def benchmarkEscape (v : PyValue) (quote : Bool := true) : Except String String :=
  if preEscape v then .ok (escape v.asString quote) else .error "expected str object"

/-- Boolean equality on `Except String String` (there is no `DecidableEq` instance for it). -/
def exceptEq : Except String String → Except String String → Bool
  | .ok x, .ok y => x == y
  | .error x, .error y => x == y
  | _, _ => false

#eval benchmarkEscape (PyValue.str "&<") true
#eval benchmarkEscape (PyValue.int 7) true
#eval benchmarkEscape PyValue.none false

/-! ## 6. Helper lemmas about the character level implementation -/

theorem flatten_append {α : Type _} (xs ys : List (List α)) :
    (xs ++ ys).flatten = xs.flatten ++ ys.flatten := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem escapeChars_append (quote : Bool) (xs ys : List Char) :
    escapeChars quote (xs ++ ys) = escapeChars quote xs ++ escapeChars quote ys := by
  simp [escapeChars]

/-- Case analysis over the six possible shapes of a replacement token. -/
theorem escTokenChars_cases {quote : Bool} {c : Char} {P : List Char → Prop}
    (hamp : P ampEntity) (hlt : P ltEntity) (hgt : P gtEntity)
    (hquot : P (if quote then quotEntity else ['"']))
    (hapos : P (if quote then aposEntity else ['\'']))
    (hself : ∀ d, d ∉ specialChars → P [d]) : P (escTokenChars quote c) := by
  by_cases e1 : c = '&'
  · subst e1; exact hamp
  · by_cases e2 : c = '<'
    · subst e2; exact hlt
    · by_cases e3 : c = '>'
      · subst e3; exact hgt
      · by_cases e4 : c = '"'
        · subst e4; exact hquot
        · by_cases e5 : c = '\''
          · subst e5; exact hapos
          · have ht : escTokenChars quote c = [c] := by
              simp [escTokenChars, e1, e2, e3, e4, e5]
            rw [ht]
            exact hself c (fun hc => by simp [specialChars, e1, e2, e3, e4, e5] at hc)

theorem notMem_lt_escTokenChars (quote : Bool) (c : Char) : '<' ∉ escTokenChars quote c := by
  apply @escTokenChars_cases quote c (fun l => '<' ∉ l)
  · decide
  · decide
  · decide
  · split_ifs <;> decide
  · split_ifs <;> decide
  · intro d hd h
    simp at h
    subst h
    exact hd (by simp [specialChars])

theorem notMem_gt_escTokenChars (quote : Bool) (c : Char) : '>' ∉ escTokenChars quote c := by
  apply @escTokenChars_cases quote c (fun l => '>' ∉ l)
  · decide
  · decide
  · decide
  · split_ifs <;> decide
  · split_ifs <;> decide
  · intro d hd h
    simp at h
    subst h
    exact hd (by simp [specialChars])

theorem notMem_quot_escTokenChars (c : Char) : '"' ∉ escTokenChars true c := by
  apply @escTokenChars_cases true c (fun l => '"' ∉ l)
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro d hd h
    simp at h
    subst h
    exact hd (by simp [specialChars])

theorem notMem_apos_escTokenChars (c : Char) : '\'' ∉ escTokenChars true c := by
  apply @escTokenChars_cases true c (fun l => '\'' ∉ l)
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro d hd h
    simp at h
    subst h
    exact hd (by simp [specialChars])

theorem notMem_lt_escapeChars (quote : Bool) : ∀ cs : List Char, '<' ∉ escapeChars quote cs := by
  intro cs
  induction cs with
  | nil => simp [escapeChars]
  | cons c cs ih =>
      rw [escapeChars_cons]
      exact List.not_mem_append (notMem_lt_escTokenChars quote c) ih

theorem notMem_gt_escapeChars (quote : Bool) : ∀ cs : List Char, '>' ∉ escapeChars quote cs := by
  intro cs
  induction cs with
  | nil => simp [escapeChars]
  | cons c cs ih =>
      rw [escapeChars_cons]
      exact List.not_mem_append (notMem_gt_escTokenChars quote c) ih

theorem notMem_quot_escapeChars : ∀ cs : List Char, '"' ∉ escapeChars true cs := by
  intro cs
  induction cs with
  | nil => simp [escapeChars]
  | cons c cs ih =>
      rw [escapeChars_cons]
      exact List.not_mem_append (notMem_quot_escTokenChars c) ih

theorem notMem_apos_escapeChars : ∀ cs : List Char, '\'' ∉ escapeChars true cs := by
  intro cs
  induction cs with
  | nil => simp [escapeChars]
  | cons c cs ih =>
      rw [escapeChars_cons]
      exact List.not_mem_append (notMem_apos_escTokenChars c) ih

theorem escTokenChars_length_pos (quote : Bool) (c : Char) :
    0 < (escTokenChars quote c).length := by
  apply @escTokenChars_cases quote c (fun l => 0 < l.length)
  · decide
  · decide
  · decide
  · split_ifs <;> decide
  · split_ifs <;> decide
  · intro _ _; simp

theorem escapeChars_length (quote : Bool) : ∀ cs : List Char,
    cs.length ≤ (escapeChars quote cs).length := by
  intro cs
  induction cs with
  | nil => simp [escapeChars]
  | cons c cs ih =>
      have hpos := escTokenChars_length_pos quote c
      rw [escapeChars_cons, List.length_append, List.length_cons]
      omega

theorem unescapeChars_escapeChars (quote : Bool) : ∀ cs : List Char,
    unescapeChars (escapeChars quote cs) = cs := by
  intro cs
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      rw [escapeChars_cons]
      by_cases h1 : c = '&'
      · subst h1
        have ht : escTokenChars quote '&' = ampEntity := rfl
        rw [ht, unescapeChars_amp, ih]
      · by_cases h2 : c = '<'
        · subst h2
          have ht : escTokenChars quote '<' = ltEntity := rfl
          rw [ht, unescapeChars_lt, ih]
        · by_cases h3 : c = '>'
          · subst h3
            have ht : escTokenChars quote '>' = gtEntity := rfl
            rw [ht, unescapeChars_gt, ih]
          · by_cases h4 : c = '"'
            · subst h4
              cases quote with
              | true =>
                  have ht : escTokenChars true '"' = quotEntity := rfl
                  rw [ht, unescapeChars_quot, ih]
              | false =>
                  have ht : escTokenChars false '"' = ['"'] := rfl
                  rw [ht]
                  show unescapeChars ('"' :: escapeChars false cs) = '"' :: cs
                  rw [unescapeChars_cons_ne _ (by decide : '"' ≠ '&'), ih]
            · by_cases h5 : c = '\''
              · subst h5
                cases quote with
                | true =>
                    have ht : escTokenChars true '\'' = aposEntity := rfl
                    rw [ht, unescapeChars_apos, ih]
                | false =>
                    have ht : escTokenChars false '\'' = ['\''] := rfl
                    rw [ht]
                    show unescapeChars ('\'' :: escapeChars false cs) = '\'' :: cs
                    rw [unescapeChars_cons_ne _ (by decide : '\'' ≠ '&'), ih]
              · have ht : escTokenChars quote c = [c] := by
                  simp [escTokenChars, h1, h2, h3, h4, h5]
                rw [ht]
                show unescapeChars (c :: escapeChars quote cs) = c :: cs
                rw [unescapeChars_cons_ne c h1, ih]

theorem entitiesOk_amp (ys : List Char) : entitiesOk (ampEntity ++ ys) = entitiesOk ys := rfl
theorem entitiesOk_lt (ys : List Char) : entitiesOk (ltEntity ++ ys) = entitiesOk ys := rfl
theorem entitiesOk_gt (ys : List Char) : entitiesOk (gtEntity ++ ys) = entitiesOk ys := rfl
theorem entitiesOk_quot (ys : List Char) : entitiesOk (quotEntity ++ ys) = entitiesOk ys := rfl
theorem entitiesOk_apos (ys : List Char) : entitiesOk (aposEntity ++ ys) = entitiesOk ys := rfl

theorem entitiesOk_singleton (c : Char) (h : c ≠ '&') (ys : List Char) :
    entitiesOk ([c] ++ ys) = entitiesOk ys := by
  show ((if c = '&' then startsEntityBody ys else true) && entitiesOk ys) = entitiesOk ys
  rw [if_neg h]
  rfl

theorem entitiesOk_escTokenChars (quote : Bool) (c : Char) (ys : List Char) :
    entitiesOk (escTokenChars quote c ++ ys) = entitiesOk ys := by
  apply @escTokenChars_cases quote c (fun l => entitiesOk (l ++ ys) = entitiesOk ys)
  · exact entitiesOk_amp ys
  · exact entitiesOk_lt ys
  · exact entitiesOk_gt ys
  · cases quote with
    | true => exact entitiesOk_quot ys
    | false => exact entitiesOk_singleton '"' (by decide) ys
  · cases quote with
    | true => exact entitiesOk_apos ys
    | false => exact entitiesOk_singleton '\'' (by decide) ys
  · intro d hd
    exact entitiesOk_singleton d (fun he => hd (by rw [he]; simp [specialChars])) ys

theorem entitiesOk_escapeChars (quote : Bool) : ∀ cs : List Char,
    entitiesOk (escapeChars quote cs) = true := by
  intro cs
  induction cs with
  | nil => simp [escapeChars]
  | cons c cs ih =>
      rw [escapeChars_cons, entitiesOk_escTokenChars]
      exact ih

theorem escTokenChars_eq_self (quote : Bool) (c : Char) (h : c ∉ specialChars) :
    escTokenChars quote c = [c] := by
  have h1 : c ≠ '&' := fun hc => h (by simp [specialChars, hc])
  have h2 : c ≠ '<' := fun hc => h (by simp [specialChars, hc])
  have h3 : c ≠ '>' := fun hc => h (by simp [specialChars, hc])
  have h4 : c ≠ '"' := fun hc => h (by simp [specialChars, hc])
  have h5 : c ≠ '\'' := fun hc => h (by simp [specialChars, hc])
  simp [escTokenChars, h1, h2, h3, h4, h5]

theorem escapeChars_id (quote : Bool) : ∀ cs : List Char,
    (∀ c ∈ cs, c ∉ specialChars) → escapeChars quote cs = cs := by
  intro cs
  induction cs with
  | nil => intro _; simp [escapeChars]
  | cons c cs ih =>
      intro h
      rw [escapeChars_cons, escTokenChars_eq_self quote c (h c (by simp))]
      rw [ih (fun d hd => h d (List.mem_cons_of_mem _ hd))]
      rfl

/-! ### The quote pass as a separate rewriting pass

The Python body first performs the three unconditional replacements and then, if `quote` is set,
two more. `quotePass` models that second pass; `escapeChars_quote` below states that escaping with
`quote = true` is the same as escaping with `quote = false` followed by the quote pass. -/

def quoteTokenChars (c : Char) : List Char :=
  if c = '"' then quotEntity else if c = '\'' then aposEntity else [c]

def quotePassChars (cs : List Char) : List Char := (cs.map quoteTokenChars).flatten

def quotePass (s : String) : String := String.mk (quotePassChars s.toList)

theorem quotePassChars_append (xs ys : List Char) :
    quotePassChars (xs ++ ys) = quotePassChars xs ++ quotePassChars ys := by
  simp [quotePassChars]

theorem quotePassChars_escTokenChars (c : Char) :
    quotePassChars (escTokenChars false c) = escTokenChars true c := by
  by_cases h1 : c = '&'
  · subst h1; decide
  · by_cases h2 : c = '<'
    · subst h2; decide
    · by_cases h3 : c = '>'
      · subst h3; decide
      · by_cases h4 : c = '"'
        · subst h4; decide
        · by_cases h5 : c = '\''
          · subst h5; decide
          · have e1 : escTokenChars false c = [c] := by simp [escTokenChars, h1, h2, h3, h4, h5]
            have e2 : escTokenChars true c = [c] := by simp [escTokenChars, h1, h2, h3, h4, h5]
            rw [e1, e2]
            simp [quotePassChars, quoteTokenChars, h4, h5]

theorem escapeChars_quote (cs : List Char) :
    escapeChars true cs = quotePassChars (escapeChars false cs) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      rw [escapeChars_cons, escapeChars_cons, quotePassChars_append, ih]
      rw [← quotePassChars_escTokenChars c]

/-! ## 7. Properties of `escape`: propositions and proofs -/

theorem escape_empty (quote : Bool) : escape "" quote = "" := by simp [escape]

theorem escape_amp (quote : Bool) : escape "&" quote = "&amp;" := rfl
theorem escape_lt (quote : Bool) : escape "<" quote = "&lt;" := rfl
theorem escape_gt (quote : Bool) : escape ">" quote = "&gt;" := rfl
theorem escape_quot_true : escape "\"" true = "&quot;" := rfl
theorem escape_quot_false : escape "\"" false = "\"" := rfl
theorem escape_apos_true : escape "'" true = "&#x27;" := rfl
theorem escape_apos_false : escape "'" false = "'" := rfl

/-- `&` is replaced first: an ampersand that already belongs to an entity is escaped again
(this is the "order matters" comment of the Python source). -/
theorem escape_amp_amp (quote : Bool) : escape "&amp;" quote = "&amp;amp;" := rfl
theorem escape_amp_lt (quote : Bool) : escape "&lt;" quote = "&amp;lt;" := rfl
theorem escape_amp_lt_str (quote : Bool) : escape "&<" quote = "&amp;&lt;" := rfl

theorem String_mk_append (l₁ l₂ : List Char) :
    String.mk (l₁ ++ l₂) = String.mk l₁ ++ String.mk l₂ := rfl

theorem String_mk_toList (s : String) : String.mk s.toList = s := rfl

theorem escape_append (s t : String) (quote : Bool) :
    escape (s ++ t) quote = escape s quote ++ escape t quote := by
  have h1 : (s ++ t).toList = s.toList ++ t.toList := by simp
  have h2 : escape (s ++ t) quote = String.mk (escapeChars quote (s ++ t).toList) := rfl
  have h3 : escape s quote = String.mk (escapeChars quote s.toList) := rfl
  have h4 : escape t quote = String.mk (escapeChars quote t.toList) := rfl
  rw [h2, h1, escapeChars_append, h3, h4, String_mk_append]

theorem escape_no_lt (s : String) (quote : Bool) : '<' ∉ (escape s quote).toList := by
  simp [escape, notMem_lt_escapeChars]

theorem escape_no_gt (s : String) (quote : Bool) : '>' ∉ (escape s quote).toList := by
  simp [escape, notMem_gt_escapeChars]

theorem escape_no_quot (s : String) : '"' ∉ (escape s true).toList := by
  simp [escape, notMem_quot_escapeChars]

theorem escape_no_apos (s : String) : '\'' ∉ (escape s true).toList := by
  simp [escape, notMem_apos_escapeChars]

theorem escape_entitiesOk (s : String) (quote : Bool) :
    entitiesOk (escape s quote).toList = true := by
  simp [escape, entitiesOk_escapeChars]

theorem escape_roundtrip (s : String) (quote : Bool) : unescape (escape s quote) = s := by
  simp [unescape, escape, unescapeChars_escapeChars]

theorem escape_injective (s t : String) (quote : Bool) (h : escape s quote = escape t quote) :
    s = t := by
  rw [← escape_roundtrip s quote, ← escape_roundtrip t quote, h]

theorem escape_length (s : String) (quote : Bool) : s.length ≤ (escape s quote).length := by
  have h := escapeChars_length quote s.toList
  have h1 : s.toList.length = s.length := by simp
  have h2 : (escape s quote).toList = escapeChars quote s.toList := by simp [escape]
  have h3 : (escape s quote).toList.length = (escape s quote).length := by simp
  rw [← h1, ← h3, h2]
  exact h

theorem escape_id (s : String) (quote : Bool) (h : ∀ c ∈ s.toList, c ∉ specialChars) :
    escape s quote = s := by
  have h1 : escapeChars quote s.toList = s.toList := escapeChars_id quote s.toList h
  have h2 : escape s quote = String.mk (escapeChars quote s.toList) := rfl
  rw [h2, h1, String_mk_toList]

theorem escape_quote_decompose (s : String) : escape s true = quotePass (escape s false) := by
  simp [escape, quotePass, escapeChars_quote]

/-! ### The four assertions of the Python `check` function, as kernel checked theorems -/

theorem escape_test_1 : escape "<b>\"&'</b>" true = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := rfl
theorem escape_test_2 : escape "" true = "" := rfl
theorem escape_test_3 : escape "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := rfl
theorem escape_test_4 : escape "&<" true = "&amp;&lt;" := rfl

/-- The Python `check` function returns `True` for our implementation. -/
theorem check_thm : check (fun s q => escape s q) = true := by
  simp [check, escape_test_1, escape_test_2, escape_test_3, escape_test_4]

theorem benchmarkEscape_ok (s : String) (quote : Bool) :
    benchmarkEscape (PyValue.str s) quote = .ok (escape s quote) := by
  simp [benchmarkEscape, preEscape]

/-! ### The properties as propositions -/

def escape_empty_prop (quote : Bool) : Prop := escape "" quote = ""
theorem escape_empty_thm (quote : Bool) : escape_empty_prop quote := escape_empty quote

def escape_chars_prop (quote : Bool) : Prop :=
  escape "&" quote = "&amp;" ∧ escape "<" quote = "&lt;" ∧ escape ">" quote = "&gt;" ∧
  escape "\"" true = "&quot;" ∧ escape "\"" false = "\"" ∧
  escape "'" true = "&#x27;" ∧ escape "'" false = "'"
theorem escape_chars_thm (quote : Bool) : escape_chars_prop quote :=
  ⟨escape_amp quote, escape_lt quote, escape_gt quote, escape_quot_true, escape_quot_false,
    escape_apos_true, escape_apos_false⟩

def escape_order_prop (quote : Bool) : Prop :=
  escape "&amp;" quote = "&amp;amp;" ∧ escape "&lt;" quote = "&amp;lt;" ∧
  escape "&<" quote = "&amp;&lt;"
theorem escape_order_thm (quote : Bool) : escape_order_prop quote :=
  ⟨escape_amp_amp quote, escape_amp_lt quote, escape_amp_lt_str quote⟩

def escape_append_prop (s t : String) (quote : Bool) : Prop :=
  escape (s ++ t) quote = escape s quote ++ escape t quote
theorem escape_append_thm (s t : String) (quote : Bool) : escape_append_prop s t quote :=
  escape_append s t quote

def escape_no_angle_prop (s : String) (quote : Bool) : Prop :=
  '<' ∉ (escape s quote).toList ∧ '>' ∉ (escape s quote).toList
theorem escape_no_angle_thm (s : String) (quote : Bool) : escape_no_angle_prop s quote :=
  ⟨escape_no_lt s quote, escape_no_gt s quote⟩

def escape_no_quote_prop (s : String) (quote : Bool) : Prop :=
  quote = true → '"' ∉ (escape s quote).toList ∧ '\'' ∉ (escape s quote).toList
theorem escape_no_quote_thm (s : String) (quote : Bool) : escape_no_quote_prop s quote := by
  intro hq
  subst hq
  exact ⟨escape_no_quot s, escape_no_apos s⟩

def escape_entities_prop (s : String) (quote : Bool) : Prop :=
  entitiesOk (escape s quote).toList = true
theorem escape_entities_thm (s : String) (quote : Bool) : escape_entities_prop s quote :=
  escape_entitiesOk s quote

def escape_roundtrip_prop (s : String) (quote : Bool) : Prop := unescape (escape s quote) = s
theorem escape_roundtrip_thm (s : String) (quote : Bool) : escape_roundtrip_prop s quote :=
  escape_roundtrip s quote

def escape_injective_prop (s t : String) (quote : Bool) : Prop :=
  escape s quote = escape t quote → s = t
theorem escape_injective_thm (s t : String) (quote : Bool) : escape_injective_prop s t quote :=
  escape_injective s t quote

def escape_length_prop (s : String) (quote : Bool) : Prop := s.length ≤ (escape s quote).length
theorem escape_length_thm (s : String) (quote : Bool) : escape_length_prop s quote :=
  escape_length s quote

def escape_id_prop (s : String) (quote : Bool) : Prop :=
  (∀ c ∈ s.toList, c ∉ specialChars) → escape s quote = s
theorem escape_id_thm (s : String) (quote : Bool) : escape_id_prop s quote := escape_id s quote

def escape_quote_prop (s : String) : Prop := escape s true = quotePass (escape s false)
theorem escape_quote_thm (s : String) : escape_quote_prop s := escape_quote_decompose s

def pre_prop (v : PyValue) : Prop := (preEscape v = true) ↔ Pre v
theorem pre_thm (v : PyValue) : pre_prop v := preEscape_iff v

def typeerror_prop (v : PyValue) (quote : Bool) : Prop :=
  ¬ Pre v → benchmarkEscape v quote = .error "expected str object"
theorem typeerror_thm (v : PyValue) (quote : Bool) : typeerror_prop v quote := by
  intro h
  have hpre : preEscape v = false := by
    cases v with
    | str s => exact absurd ⟨s, rfl⟩ h
    | _ => rfl
  simp [benchmarkEscape, hpre]

/-! ## 8. Post-condition -/

/-- The post-condition of `benchmark_escape`, as a conjunction of the verified properties. -/
def Post_prop (v : PyValue) (quote : Bool) (r : Except String String) : Prop :=
  (Pre v → ∃ s : String, v = PyValue.str s ∧ r = .ok (escape s quote)
      ∧ escape_no_angle_prop s quote
      ∧ escape_no_quote_prop s quote
      ∧ escape_entities_prop s quote
      ∧ escape_roundtrip_prop s quote
      ∧ escape_length_prop s quote) ∧
  (¬ Pre v → r = .error "expected str object")

/-- Executable (Boolean) version of `Post_prop`, used by the property based tests. -/
def postCheck (v : PyValue) (quote : Bool) (r : Except String String) : Bool :=
  match v with
  | PyValue.str s =>
      match r with
      | .ok out =>
          (out == escape s quote) &&
          (!out.contains '<') && (!out.contains '>') &&
          (if quote then (!out.contains '"') && (!out.contains '\'') else true) &&
          (unescape out == s) &&
          (decide (s.length ≤ out.length)) &&
          (entitiesOk out.toList)
      | .error _ => false
  | _ =>
      match r with
      | .ok _ => false
      | .error e => e == "expected str object"

/-! ## 9. Property based tests -/

/-- An alphabet containing every special character, so that the bounded tests below are
meaningful (random strings would almost never contain a special character). -/
def pbtAlphabet : List Char := ['&', '<', '>', '"', '\'', 'a', ';']

/-- All words of length `n` over `pbtAlphabet`. -/
def wordsOf : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 => wordsOf n >>= (fun w => pbtAlphabet.map (fun c => c :: w))

/-- All strings of length at most `n` over `pbtAlphabet`. -/
def pbtStrings (n : Nat) : List String := ((List.range (n + 1)) >>= wordsOf).map String.mk

#eval (pbtStrings 2).length   -- 1 + 7 + 49 = 57
#eval (pbtStrings 3).length   -- 1 + 7 + 49 + 343 = 400

-- Randomised property based tests (Plausible).  Each of them tests a property that is also
-- proved as a theorem below/above, so they cannot fail; they guard against a mismatch between
-- the stated property and the executable implementation.
#eval Plausible.Testable.check (∀ s : String, unescape (escape s true) = s)
#eval Plausible.Testable.check (∀ s : String, unescape (escape s false) = s)
#eval Plausible.Testable.check (∀ s : String, ∀ q : Bool,
  '<' ∉ (escape s q).toList ∧ '>' ∉ (escape s q).toList)
#eval Plausible.Testable.check (∀ s : String, s.length ≤ (escape s true).length)
#eval Plausible.Testable.check (∀ s t : String, ∀ q : Bool,
  escape (s ++ t) q = escape s q ++ escape t q)
#eval Plausible.Testable.check (∀ s : String, escape s true = quotePass (escape s false))
#eval Plausible.Testable.check (∀ s : String, entitiesOk (escape s true).toList = true)
-- The character level model agrees with the literal `String.replace` transliteration.
#eval Plausible.Testable.check (∀ s : String, escape s true = escapeReplace s true)
#eval Plausible.Testable.check (∀ s : String, escape s false = escapeReplace s false)

-- Bounded (exhaustive) property based tests over all 400 strings of length <= 3 built from
-- `pbtAlphabet`.
example : (pbtStrings 3).all (fun s => unescape (escape s true) == s) = true := by native_decide
example : (pbtStrings 3).all (fun s => unescape (escape s false) == s) = true := by native_decide
example : (pbtStrings 3).all (fun s =>
    !((escape s true).contains '<') && !((escape s true).contains '>') &&
    !((escape s true).contains '"') && !((escape s true).contains '\'')) = true := by native_decide
example : (pbtStrings 3).all (fun s =>
    !((escape s false).contains '<') && !((escape s false).contains '>')) = true := by native_decide
example : (pbtStrings 3).all (fun s =>
    entitiesOk (escape s true).toList && entitiesOk (escape s false).toList) = true :=
  by native_decide
example : (pbtStrings 3).all (fun s => decide (s.length ≤ (escape s true).length)) = true :=
  by native_decide
example : (pbtStrings 3).all (fun s =>
    escape (s ++ s) true == escape s true ++ escape s true) = true := by native_decide
example : (pbtStrings 3).all (fun s => escape s true == quotePass (escape s false)) = true :=
  by native_decide
example : (pbtStrings 3).all (fun s =>
    escape s true == escapeReplace s true && escape s false == escapeReplace s false) = true :=
  by native_decide
example : (pbtStrings 3).all (fun s =>
    postCheck (PyValue.str s) true (benchmarkEscape (PyValue.str s) true) &&
    postCheck (PyValue.str s) false (benchmarkEscape (PyValue.str s) false)) = true :=
  by native_decide
example : postCheck (PyValue.int 3) true (benchmarkEscape (PyValue.int 3) true) = true :=
  by native_decide
example : postCheck PyValue.none true (benchmarkEscape PyValue.none true) = true :=
  by native_decide

/-- A few Python values of different types, used to test the pre-condition handling. -/
def pbtValues : List PyValue :=
  [PyValue.str "", PyValue.str "&", PyValue.str "<b>\"&'</b>", PyValue.str "a'b\"c",
   PyValue.int 3, PyValue.bool true, PyValue.none, PyValue.list [PyValue.str "x"]]

-- PBT for `escape_empty_prop`
example : [true, false].all (fun q => escape "" q == "") = true := by native_decide
-- PBT for `escape_chars_prop`
example : [true, false].all (fun q =>
    escape "&" q == "&amp;" && escape "<" q == "&lt;" && escape ">" q == "&gt;") = true :=
  by native_decide
example : escape "\"" true == "&quot;" && escape "\"" false == "\"" &&
    escape "'" true == "&#x27;" && escape "'" false == "'" := by native_decide
-- PBT for `escape_order_prop` (`&` is replaced first: no double escaping)
example : [true, false].all (fun q =>
    escape "&amp;" q == "&amp;amp;" && escape "&lt;" q == "&amp;lt;" &&
    escape "&<" q == "&amp;&lt;") = true := by native_decide
-- PBT for `escape_injective_prop`: 57 * 57 pairs of strings
example : (pbtStrings 2).all (fun s => (pbtStrings 2).all (fun t =>
    decide (escape s true = escape t true → s = t))) = true := by native_decide
example : (pbtStrings 2).all (fun s => (pbtStrings 2).all (fun t =>
    decide (escape s false = escape t false → s = t))) = true := by native_decide
-- PBT for `escape_id_prop`: strings without special characters are left untouched
example : (pbtStrings 3).all (fun s =>
    decide ((∀ c ∈ s.toList, c ∉ specialChars) → escape s true = s)) = true := by native_decide
example : (pbtStrings 3).all (fun s =>
    decide ((∀ c ∈ s.toList, c ∉ specialChars) → escape s false = s)) = true := by native_decide
-- PBT for `pre_prop`, `typeerror_prop` and `Post_prop` over values of several Python types
example : pbtValues.all (fun v => [true, false].all (fun q =>
    (if preEscape v then exceptEq (benchmarkEscape v q) (.ok (escape v.asString q))
      else exceptEq (benchmarkEscape v q) (.error "expected str object")) &&
    postCheck v q (benchmarkEscape v q))) = true := by native_decide
#eval Plausible.Testable.check (∀ v : Bool, ∀ q : Bool,
  exceptEq (benchmarkEscape (if v then PyValue.str "&<" else PyValue.int 1) q)
    (if v then .ok (escape "&<" q) else .error "expected str object"))

/-! ## 10. Correctness: `Pre -> Post` -/

theorem correctness_thm (v : PyValue) (quote : Bool) (h : Pre v) :
    Post_prop v quote (benchmarkEscape v quote) := by
  obtain ⟨s, hs⟩ := h
  subst hs
  simp only [Post_prop]
  constructor
  · intro _
    refine ⟨s, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [benchmarkEscape, preEscape]
    · exact escape_no_angle_thm s quote
    · exact escape_no_quote_thm s quote
    · exact escape_entities_thm s quote
    · exact escape_roundtrip_thm s quote
    · exact escape_length_thm s quote
  · intro hn
    exact absurd ⟨s, rfl⟩ hn

theorem correctness_thm' (v : PyValue) (quote : Bool) :
    Pre v → Post_prop v quote (benchmarkEscape v quote) := correctness_thm v quote

/-! ## 11. Imperative implementation (`Id.run do` with mutable state) -/

/-- Imperative version of `escape`: a mutable accumulator that is extended, character by
character, with the HTML-safe replacement of each character. -/
def escapeImp (s : String) (quote : Bool := true) : String := Id.run do
  let mut out : List Char := []
  for c in s.toList do
    out := out ++ escTokenChars quote c
  return String.mk out

/-- Imperative version of `benchmark_escape`: the result is a mutable variable initialised with
the `TypeError` value and overwritten when the pre-condition holds. -/
def benchmarkEscapeImp (v : PyValue) (quote : Bool := true) : Except String String := Id.run do
  let mut res : Except String String := .error "expected str object"
  if preEscape v then
    res := .ok (escapeImp v.asString quote)
  return res

/-! ## 12. Imperative tests -/

example : escapeImp "<b>\"&'</b>" true = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by native_decide
example : escapeImp "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by native_decide
example : escapeImp "" true = "" := by native_decide
example : escapeImp "&<" true = "&amp;&lt;" := by native_decide
example : check (fun s q => escapeImp s q) = true := by native_decide
example : exceptEq (benchmarkEscapeImp (PyValue.str "&<") true) (.ok "&amp;&lt;") = true :=
  by native_decide
example : exceptEq (benchmarkEscapeImp (PyValue.int 3) true) (.error "expected str object") = true :=
  by native_decide
example : exceptEq (benchmarkEscapeImp PyValue.none true) (.error "expected str object") = true :=
  by native_decide
example : exceptEq (benchmarkEscapeImp (PyValue.str "&<") true) (benchmarkEscape (PyValue.str "&<") true) = true :=
  by native_decide

#eval escapeImp "<b>\"&'</b>"
#eval escapeImp "<b>\"&'</b>" false
#eval benchmarkEscapeImp (PyValue.str "<b>\"&'</b>") true
#eval benchmarkEscapeImp (PyValue.list []) true

-- Bounded property based tests: the imperative versions agree with the functional ones on all
-- 400 strings of length <= 3 over `pbtAlphabet`, and satisfy the post-condition.
example : (pbtStrings 3).all (fun s =>
    escapeImp s true == escape s true && escapeImp s false == escape s false) = true :=
  by native_decide
example : (pbtStrings 3).all (fun s =>
    exceptEq (benchmarkEscapeImp (PyValue.str s) true) (benchmarkEscape (PyValue.str s) true) &&
    exceptEq (benchmarkEscapeImp (PyValue.str s) false) (benchmarkEscape (PyValue.str s) false)) =
  true := by native_decide
example : (pbtStrings 3).all (fun s =>
    postCheck (PyValue.str s) true (benchmarkEscapeImp (PyValue.str s) true)) = true :=
  by native_decide

#eval Plausible.Testable.check (∀ s : String, ∀ q : Bool, escapeImp s q = escape s q)

/-! ## 13. Equivalence: functional = imperative -/

theorem escapeImp_eq (s : String) (quote : Bool) : escapeImp s quote = escape s quote := by
  simp [escapeImp, escape, escapeChars]

/-- The imperative implementation also passes the Python `check` function. -/
theorem checkImp_thm : check (fun s q => escapeImp s q) = true := by
  have heq : (fun s q => escapeImp s q) = (fun s q => escape s q) := by
    funext s q
    exact escapeImp_eq s q
  rw [heq, check_thm]

theorem benchmarkEscapeImp_eq (v : PyValue) (quote : Bool) :
    benchmarkEscapeImp v quote = benchmarkEscape v quote := by
  by_cases h : preEscape v = true
  · simp [benchmarkEscapeImp, benchmarkEscape, h]
    exact escapeImp_eq v.asString quote
  · simp [benchmarkEscapeImp, benchmarkEscape, h]

end X20_html_escape
