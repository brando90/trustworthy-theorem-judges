import Mathlib

/-!
# HTML escape

Lean 4 formalization of Python's `html.escape` (and the benchmark wrapper
`benchmark_escape`).

The Python implementation replaces `&`, then `<`, then `>`, and — when
`quote` is true — `"` and `'`, using `str.replace`. Ampersand is replaced
first so that the `&` characters introduced by later entities are not
double-escaped. Patterns are single Unicode code points and the replacement
strings are not rescanned, so the algorithm is exactly the character-wise
expansion proved equivalent below to `escapeSeq`.

In Lean the input is already a `String`, which is the static counterpart of
`pre_escape` / `isinstance(s, str)`.
-/

namespace «20_html_escape»

/-- Characters that `html.escape` rewrites for the given `quote` flag. -/
def isSpecial (quote : Bool) (c : Char) : Bool :=
  c == '&' || c == '<' || c == '>' || (quote && (c == '"' || c == '\''))

/-- HTML expansion of a single character. Mirrors one step of `str.replace`. -/
def escapeChar (quote : Bool) (c : Char) : String :=
  if c == '&' then "&amp;"
  else if c == '<' then "&lt;"
  else if c == '>' then "&gt;"
  else if quote && c == '"' then "&quot;"
  else if quote && c == '\'' then "&#x27;"
  else String.singleton c

/-- Escape a list of code points by concatenating per-character expansions. -/
def escapeList (quote : Bool) : List Char → String
  | [] => ""
  | c :: cs => escapeChar quote c ++ escapeList quote cs

/--
HTML-escape `s`.

`quote = true` (the default, as in Python) also translates `"` and `'`.
-/
def escape (s : String) (quote : Bool := true) : String :=
  escapeList quote s.data

/-- Python `isinstance(s, str)`. At this type the check is identically true. -/
def pre_escape (_s : String) : Bool :=
  true

/--
Benchmark entry point. The Python wrapper raises `TypeError` when the input
is not a string; every Lean `String` satisfies `pre_escape`.
-/
def benchmark_escape (s : String) (quote : Bool := true) : String :=
  if pre_escape s then escape s quote else ""

/-- Replace every occurrence of the code point `old` by `neu`, without
rescanning inserted text. This is `str.replace` for a one-character pattern. -/
def replaceChar (old : Char) (neu : List Char) : List Char → List Char
  | [] => []
  | c :: cs => (if c == old then neu else [c]) ++ replaceChar old neu cs

/--
Python's successive `str.replace` calls, modelled on Unicode code points.
Order is significant: `&` is rewritten before `<`, `>`, `"`, and `'`.
-/
def escapeSeqList (quote : Bool) (cs : List Char) : List Char :=
  let cs := replaceChar '&' "&amp;".data cs
  let cs := replaceChar '<' "&lt;".data cs
  let cs := replaceChar '>' "&gt;".data cs
  if quote then
    let cs := replaceChar '"' "&quot;".data cs
    replaceChar '\'' "&#x27;".data cs
  else
    cs

/-- Sequential-replace model of `html.escape`. -/
def escapeSeq (s : String) (quote : Bool := true) : String :=
  String.mk (escapeSeqList quote s.data)

/-- Left inverse of a single expansion (entities, or a raw one-character string). -/
def decodeExpansion (s : String) : Option Char :=
  if s == "&amp;" then some '&'
  else if s == "&lt;" then some '<'
  else if s == "&gt;" then some '>'
  else if s == "&quot;" then some '"'
  else if s == "&#x27;" then some '\''
  else if s.length == 1 then s.data.head?
  else none

/-! ## Unit tests -/

example : benchmark_escape "<b>\"&'</b>" = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by
  native_decide

example : benchmark_escape "" = "" := by
  native_decide

example : benchmark_escape "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by
  native_decide

example : benchmark_escape "&<" = "&amp;&lt;" := by
  native_decide

example : escape "&" = "&amp;" := by native_decide
example : escape "<" = "&lt;" := by native_decide
example : escape ">" = "&gt;" := by native_decide
example : escape "\"" = "&quot;" := by native_decide
example : escape "'" = "&#x27;" := by native_decide
example : escape "\"" false = "\"" := by native_decide
example : escape "'" false = "'" := by native_decide
example : escape "abc" = "abc" := by native_decide
example : escape "&&" = "&amp;&amp;" := by native_decide
example : escape "<>" false = "&lt;&gt;" := by native_decide

#eval escape "<b>\"&'</b>"
#eval escape "<b>\"&'</b>" false
#eval escape "&<"
#eval benchmark_escape ""

/-! ## Pre-condition -/

/-- Input is a string, i.e. Python `pre_escape(s)`. -/
def Pre (s : String) (_quote : Bool) : Prop :=
  pre_escape s = true


/-! ## Auxiliary lemmas -/

lemma replaceChar_append (old : Char) (neu xs ys : List Char) :
    replaceChar old neu (xs ++ ys) = replaceChar old neu xs ++ replaceChar old neu ys := by
  induction xs with
  | nil => simp [replaceChar]
  | cons x xs ih => simp [replaceChar, ih, List.append_assoc]

lemma escapeSeqList_append (q : Bool) (xs ys : List Char) :
    escapeSeqList q (xs ++ ys) = escapeSeqList q xs ++ escapeSeqList q ys := by
  simp only [escapeSeqList]
  cases q <;> simp [replaceChar_append]

lemma escapeSeqList_flatMap (q : Bool) (cs : List Char) :
    escapeSeqList q cs = cs.flatMap (fun c => escapeSeqList q [c]) := by
  induction cs with
  | nil => simp [escapeSeqList, replaceChar]
  | cons c cs ih =>
    have hcons : c :: cs = [c] ++ cs := by simp
    rw [hcons, escapeSeqList_append, ih]
    simp [List.flatMap]

lemma escapeSeqList_singleton (q : Bool) (c : Char) :
    escapeSeqList q [c] = (escapeChar q c).data := by
  unfold escapeSeqList escapeChar
  cases hamp : c == '&' <;>
  cases hlt : c == '<' <;>
  cases hgt : c == '>' <;>
  cases hqu : c == '"' <;>
  cases hap : c == '\'' <;>
  cases q <;>
  simp [replaceChar, String.singleton_eq, hamp, hlt, hgt, hqu, hap]

lemma escapeList_append (q : Bool) (xs ys : List Char) :
    escapeList q (xs ++ ys) = escapeList q xs ++ escapeList q ys := by
  induction xs with
  | nil => simp [escapeList]
  | cons x xs ih => simp [escapeList, ih, String.append_assoc]

lemma escapeList_data (q : Bool) (cs : List Char) :
    (escapeList q cs).data = cs.flatMap (fun c => (escapeChar q c).data) := by
  induction cs with
  | nil => simp [escapeList]
  | cons c cs ih => simp [escapeList, ih]

lemma escapeChar_no_lt (q : Bool) (c : Char) : '<' ∉ (escapeChar q c).data := by
  unfold escapeChar
  split_ifs with h1 h2 h3 h4 h5
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [String.data_singleton]
    intro h
    simp at h2
    exact h2 h.symm

lemma escapeChar_no_gt (q : Bool) (c : Char) : '>' ∉ (escapeChar q c).data := by
  unfold escapeChar
  split_ifs with h1 h2 h3 h4 h5
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [String.data_singleton]
    intro h
    simp at h3
    exact h3 h.symm

lemma escapeChar_no_quot (c : Char) : '"' ∉ (escapeChar true c).data := by
  unfold escapeChar
  split_ifs with h1 h2 h3 h4 h5
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [String.data_singleton]
    intro h
    simp at h4
    exact h4 h.symm

lemma escapeChar_no_apos (c : Char) : '\'' ∉ (escapeChar true c).data := by
  unfold escapeChar
  split_ifs with h1 h2 h3 h4 h5
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [String.data_singleton]
    intro h
    simp at h5
    exact h5 h.symm

lemma escapeList_no_lt (q : Bool) (cs : List Char) : '<' ∉ (escapeList q cs).data := by
  induction cs with
  | nil => simp [escapeList]
  | cons c cs ih => simp [escapeList, List.mem_append, escapeChar_no_lt q c, ih]

lemma escapeList_no_gt (q : Bool) (cs : List Char) : '>' ∉ (escapeList q cs).data := by
  induction cs with
  | nil => simp [escapeList]
  | cons c cs ih => simp [escapeList, List.mem_append, escapeChar_no_gt q c, ih]

lemma escapeList_no_quot (cs : List Char) : '"' ∉ (escapeList true cs).data := by
  induction cs with
  | nil => simp [escapeList]
  | cons c cs ih => simp [escapeList, List.mem_append, escapeChar_no_quot c, ih]

lemma escapeList_no_apos (cs : List Char) : '\'' ∉ (escapeList true cs).data := by
  induction cs with
  | nil => simp [escapeList]
  | cons c cs ih => simp [escapeList, List.mem_append, escapeChar_no_apos c, ih]

lemma escapeChar_length_ge (q : Bool) (c : Char) : 1 ≤ (escapeChar q c).length := by
  unfold escapeChar
  split_ifs
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp

lemma escapeList_length_eq (q : Bool) (cs : List Char) :
    (escapeList q cs).length = (cs.map (fun c => (escapeChar q c).length)).sum := by
  induction cs with
  | nil => simp [escapeList]
  | cons c cs ih => simp [escapeList, ih, String.length_append]

lemma map_length_sum_ge (q : Bool) (cs : List Char) :
    cs.length ≤ (cs.map (fun c => (escapeChar q c).length)).sum := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp
    have hc : 1 ≤ (escapeChar q c).length := escapeChar_length_ge q c
    omega

lemma singleton_ne_long (c : Char) (e : String) (hlen : e.length ≠ 1) :
    (String.singleton c == e) = false := by
  simp
  intro h
  apply hlen
  have := congrArg String.length h
  simpa [String.length_singleton] using this.symm

lemma decode_escapeChar (q : Bool) (c : Char) :
    decodeExpansion (escapeChar q c) = some c := by
  unfold escapeChar
  split_ifs with h1 h2 h3 h4 h5
  · have hc : c = '&' := by simpa [beq_iff_eq] using h1
    subst hc
    decide
  · have hc : c = '<' := by simpa [beq_iff_eq] using h2
    subst hc
    decide
  · have hc : c = '>' := by simpa [beq_iff_eq] using h3
    subst hc
    decide
  · have hc : c = '"' := by
      simp only [Bool.and_eq_true, beq_iff_eq] at h4
      exact h4.2
    subst hc
    decide
  · have hc : c = '\'' := by
      simp only [Bool.and_eq_true, beq_iff_eq] at h5
      exact h5.2
    subst hc
    decide
  · have n1 : ("&amp;").length ≠ 1 := by decide
    have n2 : ("&lt;").length ≠ 1 := by decide
    have n3 : ("&gt;").length ≠ 1 := by decide
    have n4 : ("&quot;").length ≠ 1 := by decide
    have n5 : ("&#x27;").length ≠ 1 := by decide
    simp [decodeExpansion, String.length_singleton, String.data_singleton,
      singleton_ne_long c "&amp;" n1, singleton_ne_long c "&lt;" n2,
      singleton_ne_long c "&gt;" n3, singleton_ne_long c "&quot;" n4,
      singleton_ne_long c "&#x27;" n5]

lemma escapeChar_nonspecial (q : Bool) (c : Char) (h : isSpecial q c = false) :
    escapeChar q c = String.singleton c := by
  unfold escapeChar
  split_ifs with h1 h2 h3 h4 h5
  · unfold isSpecial at h
    simp [h1] at h
  · unfold isSpecial at h
    simp [h2] at h
  · unfold isSpecial at h
    simp [h3] at h
  · simp only [Bool.and_eq_true, beq_iff_eq] at h4
    have hq : q = true := h4.1
    have hc : c = '"' := h4.2
    unfold isSpecial at h
    simp [hq, hc] at h
  · simp only [Bool.and_eq_true, beq_iff_eq] at h5
    have hq : q = true := h5.1
    have hc : c = '\'' := h5.2
    unfold isSpecial at h
    simp [hq, hc] at h
  · rfl

lemma count_escapeChar_dquot_off (c : Char) :
    (escapeChar false c).data.count '"' = [c].count '"' := by
  by_cases h1 : c = '&'
  · subst h1
    simp [escapeChar]
  · by_cases h2 : c = '<'
    · subst h2
      simp [escapeChar]
    · by_cases h3 : c = '>'
      · subst h3
        simp [escapeChar]
      · have hb1 : (c == '&') = false := by simpa [beq_iff_eq] using h1
        have hb2 : (c == '<') = false := by simpa [beq_iff_eq] using h2
        have hb3 : (c == '>') = false := by simpa [beq_iff_eq] using h3
        simp [escapeChar, hb1, hb2, hb3, Bool.false_and, String.data_singleton]

lemma count_escapeChar_apos_off (c : Char) :
    (escapeChar false c).data.count '\'' = [c].count '\'' := by
  by_cases h1 : c = '&'
  · subst h1
    simp [escapeChar]
  · by_cases h2 : c = '<'
    · subst h2
      simp [escapeChar]
    · by_cases h3 : c = '>'
      · subst h3
        simp [escapeChar]
      · have hb1 : (c == '&') = false := by simpa [beq_iff_eq] using h1
        have hb2 : (c == '<') = false := by simpa [beq_iff_eq] using h2
        have hb3 : (c == '>') = false := by simpa [beq_iff_eq] using h3
        simp [escapeChar, hb1, hb2, hb3, Bool.false_and, String.data_singleton]

lemma count_escapeList_dquot_off (cs : List Char) :
    (escapeList false cs).data.count '"' = cs.count '"' := by
  induction cs with
  | nil => simp [escapeList]
  | cons c cs ih =>
    simp [escapeList, List.count_append, count_escapeChar_dquot_off, ih, List.count_cons]
    omega

lemma count_escapeList_apos_off (cs : List Char) :
    (escapeList false cs).data.count '\'' = cs.count '\'' := by
  induction cs with
  | nil => simp [escapeList]
  | cons c cs ih =>
    simp [escapeList, List.count_append, count_escapeChar_apos_off, ih, List.count_cons]
    omega

lemma foldl_append_strings (xs : List String) (a : String) :
    xs.foldl (fun acc s => acc ++ s) a = a ++ xs.foldl (fun acc s => acc ++ s) "" := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp
    rw [ih (a ++ x), ih x]
    simp [String.append_assoc]

lemma escapeList_eq_join (q : Bool) (cs : List Char) :
    escapeList q cs = String.join (cs.map (escapeChar q)) := by
  induction cs with
  | nil => simp [escapeList, String.join]
  | cons c cs ih =>
    simp [escapeList, String.join, ih]
    exact (foldl_append_strings (cs.map (escapeChar q)) (escapeChar q c)).symm


/-! ## Properties and theorems -/

def benchmark_eq_prop (s : String) (q : Bool) : Prop :=
  benchmark_escape s q = escape s q

theorem benchmark_eq_thm (s : String) (q : Bool) : benchmark_eq_prop s q := by
  simp [benchmark_eq_prop, benchmark_escape, pre_escape]

def escape_empty_prop (q : Bool) : Prop :=
  escape "" q = ""

theorem escape_empty_thm (q : Bool) : escape_empty_prop q := by
  simp [escape_empty_prop, escape, escapeList]

def escape_amp_prop (q : Bool) : Prop :=
  escape "&" q = "&amp;"

theorem escape_amp_thm (q : Bool) : escape_amp_prop q := by
  simp [escape_amp_prop, escape, escapeList, escapeChar]

def escape_lt_prop (q : Bool) : Prop :=
  escape "<" q = "&lt;"

theorem escape_lt_thm (q : Bool) : escape_lt_prop q := by
  simp [escape_lt_prop, escape, escapeList, escapeChar]

def escape_gt_prop (q : Bool) : Prop :=
  escape ">" q = "&gt;"

theorem escape_gt_thm (q : Bool) : escape_gt_prop q := by
  simp [escape_gt_prop, escape, escapeList, escapeChar]

def escape_quot_on_prop : Prop :=
  escape "\"" true = "&quot;"

theorem escape_quot_on_thm : escape_quot_on_prop := by
  simp [escape_quot_on_prop, escape, escapeList, escapeChar]

def escape_apos_on_prop : Prop :=
  escape "'" true = "&#x27;"

theorem escape_apos_on_thm : escape_apos_on_prop := by
  simp [escape_apos_on_prop, escape, escapeList, escapeChar]

def escape_quot_off_prop : Prop :=
  escape "\"" false = "\""

theorem escape_quot_off_thm : escape_quot_off_prop := by
  simp [escape_quot_off_prop, escape, escapeList, escapeChar, String.singleton_eq]

def escape_apos_off_prop : Prop :=
  escape "'" false = "'"

theorem escape_apos_off_thm : escape_apos_off_prop := by
  simp [escape_apos_off_prop, escape, escapeList, escapeChar, String.singleton_eq]

def escape_append_prop (s t : String) (q : Bool) : Prop :=
  escape (s ++ t) q = escape s q ++ escape t q

theorem escape_append_thm (s t : String) (q : Bool) : escape_append_prop s t q := by
  simp [escape_append_prop, escape, String.data_append, escapeList_append]

def amp_first_prop (q : Bool) : Prop :=
  escape "&<" q = "&amp;&lt;" ∧ escape "&<" q ≠ "&amp;amp;lt;"

theorem amp_first_thm (q : Bool) : amp_first_prop q := by
  have hcat : "&<" = "&" ++ "<" := rfl
  have happ : escape "&<" q = escape "&" q ++ escape "<" q := by
    simpa [escape_append_prop, hcat] using escape_append_thm "&" "<" q
  have hamp : escape "&" q = "&amp;" := escape_amp_thm q
  have hlt : escape "<" q = "&lt;" := escape_lt_thm q
  have heq : escape "&<" q = "&amp;&lt;" := by
    rw [happ, hamp, hlt]
    rfl
  refine ⟨heq, ?_⟩
  intro hne
  rw [heq] at hne
  revert hne
  decide

def escape_eq_seq_prop (s : String) (q : Bool) : Prop :=
  escape s q = escapeSeq s q

theorem escape_eq_seq_thm (s : String) (q : Bool) : escape_eq_seq_prop s q := by
  unfold escape_eq_seq_prop escape escapeSeq
  apply String.ext
  rw [escapeList_data, escapeSeqList_flatMap]
  simp only [escapeSeqList_singleton]

def no_raw_lt_prop (s : String) (q : Bool) : Prop :=
  '<' ∉ (escape s q).data

theorem no_raw_lt_thm (s : String) (q : Bool) : no_raw_lt_prop s q := by
  simpa [no_raw_lt_prop, escape] using escapeList_no_lt q s.data

def no_raw_gt_prop (s : String) (q : Bool) : Prop :=
  '>' ∉ (escape s q).data

theorem no_raw_gt_thm (s : String) (q : Bool) : no_raw_gt_prop s q := by
  simpa [no_raw_gt_prop, escape] using escapeList_no_gt q s.data

def no_raw_quot_prop (s : String) (q : Bool) : Prop :=
  q = true → '"' ∉ (escape s q).data

theorem no_raw_quot_thm (s : String) (q : Bool) : no_raw_quot_prop s q := by
  intro hq
  subst hq
  simpa [escape] using escapeList_no_quot s.data

def no_raw_apos_prop (s : String) (q : Bool) : Prop :=
  q = true → '\'' ∉ (escape s q).data

theorem no_raw_apos_thm (s : String) (q : Bool) : no_raw_apos_prop s q := by
  intro hq
  subst hq
  simpa [escape] using escapeList_no_apos s.data

def length_ge_prop (s : String) (q : Bool) : Prop :=
  s.length ≤ (escape s q).length

theorem length_ge_thm (s : String) (q : Bool) : length_ge_prop s q := by
  simp [length_ge_prop, escape, escapeList_length_eq]
  simpa using map_length_sum_ge q s.data

def length_eq_prop (s : String) (q : Bool) : Prop :=
  (escape s q).length = (s.data.map (fun c => (escapeChar q c).length)).sum

theorem length_eq_thm (s : String) (q : Bool) : length_eq_prop s q := by
  simp [length_eq_prop, escape, escapeList_length_eq]

def decode_char_prop (q : Bool) (c : Char) : Prop :=
  decodeExpansion (escapeChar q c) = some c

theorem decode_char_thm (q : Bool) (c : Char) : decode_char_prop q c := by
  simpa [decode_char_prop] using decode_escapeChar q c

def decode_all_prop (s : String) (q : Bool) : Prop :=
  ∀ c ∈ s.data, decodeExpansion (escapeChar q c) = some c

theorem decode_all_thm (s : String) (q : Bool) : decode_all_prop s q := by
  intro c _hc
  exact decode_char_thm q c


def nonspecial_prop (q : Bool) (c : Char) : Prop :=
  isSpecial q c = false → escape (String.singleton c) q = String.singleton c

theorem nonspecial_thm (q : Bool) (c : Char) : nonspecial_prop q c := by
  intro h
  simp [escape, escapeList, escapeChar_nonspecial q c h, String.data_singleton]

def escape_id_prop (s : String) (q : Bool) : Prop :=
  (∀ c ∈ s.data, isSpecial q c = false) → escape s q = s

theorem escape_id_thm (s : String) (q : Bool) : escape_id_prop s q := by
  intro h
  apply String.ext
  simp [escape]
  suffices ∀ cs, (∀ d ∈ cs, isSpecial q d = false) → (escapeList q cs).data = cs by
    exact this s.data h
  intro cs hcs
  induction cs with
  | nil => simp [escapeList]
  | cons c cs ih =>
    have hc : isSpecial q c = false := hcs c (List.Mem.head _)
    have htail : ∀ d ∈ cs, isSpecial q d = false := fun d hd => hcs d (List.Mem.tail _ hd)
    simp [escapeList, escapeChar_nonspecial q c hc, ih htail, String.data_append,
      String.data_singleton]

def preserve_dquot_off_prop (s : String) : Prop :=
  (escape s false).data.count '"' = s.data.count '"'

theorem preserve_dquot_off_thm (s : String) : preserve_dquot_off_prop s := by
  simpa [preserve_dquot_off_prop, escape] using count_escapeList_dquot_off s.data

def preserve_apos_off_prop (s : String) : Prop :=
  (escape s false).data.count '\'' = s.data.count '\''

theorem preserve_apos_off_thm (s : String) : preserve_apos_off_prop s := by
  simpa [preserve_apos_off_prop, escape] using count_escapeList_apos_off s.data

def escape_join_prop (s : String) (q : Bool) : Prop :=
  escape s q = String.join (s.data.map (escapeChar q))

theorem escape_join_thm (s : String) (q : Bool) : escape_join_prop s q := by
  simp [escape_join_prop, escape, escapeList_eq_join]

theorem escape_unique_thm (f : String → Bool → String)
    (h_empty : ∀ q, f "" q = "")
    (h_append : ∀ s t q, f (s ++ t) q = f s q ++ f t q)
    (h_char : ∀ c q, f (String.singleton c) q = escapeChar q c)
    (s : String) (q : Bool) : f s q = escape s q := by
  have hs : s = String.mk s.data := rfl
  suffices ∀ cs, f (String.mk cs) q = escapeList q cs by
    rw [hs, escape]
    exact this s.data
  intro cs
  induction cs with
  | nil =>
    have hempty : String.mk ([] : List Char) = "" := rfl
    rw [hempty, escapeList]
    exact h_empty q
  | cons c cs ih =>
    have hsplit : String.mk (c :: cs) = String.singleton c ++ String.mk cs := by
      apply String.ext
      simp [String.data_append, String.data_singleton]
    rw [hsplit, h_append, h_char, ih, escapeList]

/-! ## Post-condition -/

def Post_prop (s : String) (q : Bool) : Prop :=
  escape_eq_seq_prop s q ∧
  no_raw_lt_prop s q ∧
  no_raw_gt_prop s q ∧
  no_raw_quot_prop s q ∧
  no_raw_apos_prop s q ∧
  length_ge_prop s q ∧
  length_eq_prop s q ∧
  decode_all_prop s q ∧
  escape_join_prop s q ∧
  (q = false → preserve_dquot_off_prop s ∧ preserve_apos_off_prop s)


/-! ## Property-based tests -/

def pbtStrings : List String :=
  ["", "a", "&", "<", ">", "\"", "'", "<b>\"&'</b>", "&<", "&&", "<>",
   "foo", "&amp;", "\"'", "a<b>c", " ", "&#x27;", ">><<"]

def postBool (s : String) (q : Bool) : Bool :=
  (escape s q == escapeSeq s q) &&
  !(escape s q).data.elem '<' &&
  !(escape s q).data.elem '>' &&
  (!q || !(escape s q).data.elem '"') &&
  (!q || !(escape s q).data.elem '\'') &&
  decide (s.length ≤ (escape s q).length) &&
  decide ((escape s q).length = (s.data.map (fun c => (escapeChar q c).length)).sum) &&
  s.data.all (fun c => decodeExpansion (escapeChar q c) == some c) &&
  (escape s q == String.join (s.data.map (escapeChar q))) &&
  (q || ((escape s false).data.count '"' == s.data.count '"' &&
         (escape s false).data.count '\'' == s.data.count '\''))

-- PBT for escape_append_prop
#eval Plausible.Testable.check
  (∀ s t : String, ∀ q : Bool, escape (s ++ t) q = escape s q ++ escape t q)

example : (pbtStrings.all fun s => pbtStrings.all fun t =>
    escape (s ++ t) true == escape s true ++ escape t true &&
    escape (s ++ t) false == escape s false ++ escape t false) = true := by
  native_decide

-- PBT for escape_empty_prop
#eval Plausible.Testable.check (∀ q : Bool, escape "" q = "")

example : escape "" true = "" ∧ escape "" false = "" := by native_decide

-- PBT for escape_amp_prop
#eval Plausible.Testable.check (∀ q : Bool, escape "&" q = "&amp;")

-- PBT for escape_lt_prop
#eval Plausible.Testable.check (∀ q : Bool, escape "<" q = "&lt;")

-- PBT for escape_gt_prop
#eval Plausible.Testable.check (∀ q : Bool, escape ">" q = "&gt;")

-- PBT for escape_quot_on_prop and escape_quot_off_prop
example : escape "\"" true = "&quot;" ∧ escape "\"" false = "\"" := by native_decide

-- PBT for escape_apos_on_prop and escape_apos_off_prop
example : escape "'" true = "&#x27;" ∧ escape "'" false = "'" := by native_decide

-- PBT for amp_first_prop
#eval Plausible.Testable.check
  (∀ q : Bool, escape "&<" q = "&amp;&lt;" ∧ escape "&<" q ≠ "&amp;amp;lt;")

-- PBT for escape_eq_seq_prop
#eval Plausible.Testable.check (∀ s : String, ∀ q : Bool, escape s q = escapeSeq s q)

example : (pbtStrings.all fun s => escape s true == escapeSeq s true &&
    escape s false == escapeSeq s false) = true := by native_decide

-- PBT for no_raw_lt_prop
#eval Plausible.Testable.check (∀ s : String, ∀ q : Bool, '<' ∉ (escape s q).data)

-- PBT for no_raw_gt_prop
#eval Plausible.Testable.check (∀ s : String, ∀ q : Bool, '>' ∉ (escape s q).data)

-- PBT for no_raw_quot_prop
#eval Plausible.Testable.check (∀ s : String, '"' ∉ (escape s true).data)

example : (pbtStrings.all fun s => !(escape s true).data.elem '"') = true := by native_decide

-- PBT for no_raw_apos_prop
#eval Plausible.Testable.check (∀ s : String, '\'' ∉ (escape s true).data)

example : (pbtStrings.all fun s => !(escape s true).data.elem '\'') = true := by native_decide

-- PBT for length_ge_prop
#eval Plausible.Testable.check (∀ s : String, ∀ q : Bool, s.length ≤ (escape s q).length)

-- PBT for length_eq_prop
#eval Plausible.Testable.check
  (∀ s : String, ∀ q : Bool,
    (escape s q).length = (s.data.map (fun c => (escapeChar q c).length)).sum)

-- PBT for decode_char_prop and decode_all_prop
#eval Plausible.Testable.check
  (∀ q : Bool, ∀ c : Char, decodeExpansion (escapeChar q c) = some c)

example : (pbtStrings.all fun s =>
    s.data.all (fun c => decodeExpansion (escapeChar true c) == some c &&
      decodeExpansion (escapeChar false c) == some c)) = true := by native_decide


-- PBT for nonspecial_prop
#eval Plausible.Testable.check
  (∀ q : Bool, ∀ c : Char, isSpecial q c = false →
    escape (String.singleton c) q = String.singleton c)

-- PBT for escape_id_prop
#eval Plausible.Testable.check
  (∀ s : String, ∀ q : Bool,
    s.data.all (fun c => !isSpecial q c) = true → escape s q = s)

example : (pbtStrings.all fun s =>
    (s.data.all (fun c => !isSpecial false c) = true → escape s false == s) &&
    (s.data.all (fun c => !isSpecial true c) = true → escape s true == s)) = true := by
  native_decide

-- PBT for preserve_dquot_off_prop
#eval Plausible.Testable.check
  (∀ s : String, (escape s false).data.count '"' = s.data.count '"')

-- PBT for preserve_apos_off_prop
#eval Plausible.Testable.check
  (∀ s : String, (escape s false).data.count '\'' = s.data.count '\'')

-- PBT for escape_join_prop
#eval Plausible.Testable.check
  (∀ s : String, ∀ q : Bool, escape s q = String.join (s.data.map (escapeChar q)))

-- PBT for benchmark_eq_prop
#eval Plausible.Testable.check
  (∀ s : String, ∀ q : Bool, benchmark_escape s q = escape s q)

-- Bounded PBT for Post_prop
example : (pbtStrings.all fun s => postBool s true && postBool s false) = true := by
  native_decide

-- Randomized PBT for Post_prop
#eval Plausible.Testable.check (∀ s : String, ∀ q : Bool, postBool s q = true)

/-! ## Correctness -/

theorem correctness_thm (s : String) (q : Bool) (_h : Pre s q) : Post_prop s q := by
  unfold Post_prop
  refine ⟨escape_eq_seq_thm s q, no_raw_lt_thm s q, no_raw_gt_thm s q,
    no_raw_quot_thm s q, no_raw_apos_thm s q, length_ge_thm s q, length_eq_thm s q,
    decode_all_thm s q, escape_join_thm s q, ?_⟩
  intro hq
  subst hq
  exact ⟨preserve_dquot_off_thm s, preserve_apos_off_thm s⟩

/-! ## Imperative implementation -/

def escapeImp (s : String) (quote : Bool := true) : String :=
  Id.run do
    let mut acc : String := ""
    for c in s.data do
      acc := acc ++ escapeChar quote c
    return acc

lemma foldl_escape_acc (q : Bool) (cs : List Char) (acc : String) :
    cs.foldl (fun a c => a ++ escapeChar q c) acc
      = acc ++ cs.foldl (fun a c => a ++ escapeChar q c) "" := by
  induction cs generalizing acc with
  | nil => simp
  | cons c cs ih =>
    simp
    rw [ih (acc ++ escapeChar q c), ih (escapeChar q c)]
    simp [String.append_assoc]

lemma escapeList_eq_foldl (q : Bool) (cs : List Char) :
    escapeList q cs = cs.foldl (fun acc c => acc ++ escapeChar q c) "" := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp [escapeList, ih]
    rw [foldl_escape_acc q cs (escapeChar q c)]

/-! ## Imperative tests -/

example : escapeImp "<b>\"&'</b>" = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by
  native_decide

example : escapeImp "" = "" := by
  native_decide

example : escapeImp "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by
  native_decide

example : escapeImp "&<" = "&amp;&lt;" := by
  native_decide

example : escapeImp "\"" false = "\"" := by
  native_decide

example : escapeImp "'" = "&#x27;" := by
  native_decide

#eval escapeImp "<b>\"&'</b>"
#eval escapeImp "<b>\"&'</b>" false
#eval escapeImp "&<"
#eval escapeImp "abc" false

/-! ## Functional / imperative equivalence -/

def escape_eq_imp_prop (s : String) (q : Bool) : Prop :=
  escape s q = escapeImp s q

theorem escape_eq_imp_thm (s : String) (q : Bool) : escape_eq_imp_prop s q := by
  simp [escape_eq_imp_prop, escape, escapeImp, escapeList_eq_foldl]

-- PBT for escape_eq_imp_prop
#eval Plausible.Testable.check (∀ s : String, ∀ q : Bool, escape s q = escapeImp s q)

example : (pbtStrings.all fun s =>
    escape s true == escapeImp s true && escape s false == escapeImp s false) = true := by
  native_decide

end «20_html_escape»
