import Mathlib

/-!
# HTML escape

Lean translation of Python's `html.escape` (the special-character replacement
used by the standard-library helper). The function replaces `&`, `<` and `>`
by `&amp;`, `&lt;` and `&gt;`. When `quote` is true, which is the default, it
also replaces `"` by `&quot;` and `'` by `&#x27;`.

Ampersand is replaced first. The entities introduced by the later replacements
contain `&`, and those ampersands are not escaped again inside a single call.
A second call does escape them, so the function is not idempotent.
-/

namespace «20_html_escape»

inductive CharClass where
  | amp | lt | gt | quot | apos | other
  deriving DecidableEq

def classify (quote : Bool) (c : Char) : CharClass :=
  if c == '&' then .amp
  else if c == '<' then .lt
  else if c == '>' then .gt
  else if quote && c == '"' then .quot
  else if quote && c == '\'' then .apos
  else .other

def escapeChar (quote : Bool) (c : Char) : String :=
  match classify quote c with
  | .amp => "&amp;"
  | .lt => "&lt;"
  | .gt => "&gt;"
  | .quot => "&quot;"
  | .apos => "&#x27;"
  | .other => String.singleton c

def extraLen (quote : Bool) (c : Char) : Nat :=
  match classify quote c with
  | .amp => 4
  | .lt => 3
  | .gt => 3
  | .quot => 5
  | .apos => 5
  | .other => 0

def repl (pat : Char) (rep : List Char) (cs : List Char) : List Char :=
  cs.flatMap fun c => if c == pat then rep else [c]

def replaceChar (s : String) (pat : Char) (rep : String) : String :=
  String.mk (repl pat (rep.data) (s.data))

def escape (s : String) (quote : Bool := true) : String :=
  let s3 := replaceChar (replaceChar (replaceChar s '&' "&amp;") '<' "&lt;") '>' "&gt;"
  cond quote (replaceChar (replaceChar s3 '"' "&quot;") '\'' "&#x27;") s3

/-- Entry point corresponding to Python `benchmark_escape`.
`pre_escape` is the Lean type of `s`; a non-string cannot be passed. -/
def benchmarkEscape (s : String) (quote : Bool := true) : String :=
  escape s quote


-- Unit tests (Python `check`)

example : benchmarkEscape "<b>\"&'</b>" = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by
  native_decide

example : benchmarkEscape "" = "" := by
  native_decide

example : benchmarkEscape "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by
  native_decide

example : benchmarkEscape "&<" = "&amp;&lt;" := by
  native_decide

example : benchmarkEscape "plain" = "plain" := by
  native_decide

#eval benchmarkEscape "<b>\"&'</b>"
#eval benchmarkEscape "<b>\"&'</b>" false
#eval benchmarkEscape "&<"
#eval benchmarkEscape ""
#eval benchmarkEscape "plain"

/-- Python `pre_escape`: the input must be a string. Lean's type system enforces this. -/
def Pre (_s : String) (_quote : Bool) : Prop := True

theorem data_amp : "&amp;".data = ['&', 'a', 'm', 'p', ';'] := rfl
theorem data_lt : "&lt;".data = ['&', 'l', 't', ';'] := rfl
theorem data_gt : "&gt;".data = ['&', 'g', 't', ';'] := rfl
theorem data_quot : "&quot;".data = ['&', 'q', 'u', 'o', 't', ';'] := rfl
theorem data_apos : "&#x27;".data = ['&', '#', 'x', '2', '7', ';'] := rfl
theorem mk_data (l : List Char) : (String.mk l).data = l := rfl
theorem empty_data : "".data = [] := rfl

theorem repl_append (pat : Char) (rep xs ys : List Char) :
    repl pat rep (xs ++ ys) = repl pat rep xs ++ repl pat rep ys := by
  simp [repl, List.flatMap_append]

theorem repl_nil (pat : Char) (rep : List Char) : repl pat rep [] = [] := by
  simp [repl]

theorem image_false (c : Char) :
    repl '>' "&gt;".data (repl '<' "&lt;".data (repl '&' "&amp;".data [c]))
      = (escapeChar false c).data := by
  by_cases hamp : c = '&'
  · subst hamp
    simp [repl, escapeChar, classify]
  · by_cases hlt : c = '<'
    · subst hlt
      simp [repl, escapeChar, classify, hamp]
    · by_cases hgt : c = '>'
      · subst hgt
        simp [repl, escapeChar, classify, hamp, hlt]
      · simp [repl, escapeChar, classify, hamp, hlt, hgt, beq_iff_eq]

theorem image_true (c : Char) :
    repl '\'' "&#x27;".data
      (repl '"' "&quot;".data
        (repl '>' "&gt;".data
          (repl '<' "&lt;".data
            (repl '&' "&amp;".data [c]))))
      = (escapeChar true c).data := by
  by_cases hamp : c = '&'
  · subst hamp; simp [repl, escapeChar, classify]
  · by_cases hlt : c = '<'
    · subst hlt; simp [repl, escapeChar, classify, hamp]
    · by_cases hgt : c = '>'
      · subst hgt; simp [repl, escapeChar, classify, hamp, hlt]
      · by_cases hqu : c = '"'
        · subst hqu; simp [repl, escapeChar, classify, hamp, hlt, hgt]
        · by_cases hap : c = '\''
          · subst hap; simp [repl, escapeChar, classify, hamp, hlt, hgt, hqu]
          · simp [repl, escapeChar, classify, hamp, hlt, hgt, hqu, hap, beq_iff_eq]

def pipeFalse (cs : List Char) : List Char :=
  repl '>' "&gt;".data (repl '<' "&lt;".data (repl '&' "&amp;".data cs))

def pipeTrue (cs : List Char) : List Char :=
  repl '\'' "&#x27;".data
    (repl '"' "&quot;".data
      (repl '>' "&gt;".data (repl '<' "&lt;".data (repl '&' "&amp;".data cs))))

theorem pipeFalse_append (xs ys : List Char) :
    pipeFalse (xs ++ ys) = pipeFalse xs ++ pipeFalse ys := by
  simp [pipeFalse, repl_append]

theorem pipeTrue_append (xs ys : List Char) :
    pipeTrue (xs ++ ys) = pipeTrue xs ++ pipeTrue ys := by
  simp [pipeTrue, repl_append]

theorem pipeFalse_spec (cs : List Char) :
    pipeFalse cs = cs.flatMap (fun c => (escapeChar false c).data) := by
  induction cs with
  | nil => simp [pipeFalse, repl]
  | cons c cs ih =>
    have hcons : pipeFalse (c :: cs) = pipeFalse [c] ++ pipeFalse cs := by
      simpa using pipeFalse_append [c] cs
    have himg : pipeFalse [c] = (escapeChar false c).data := by
      simpa [pipeFalse] using image_false c
    simp [hcons, himg, ih, List.flatMap_cons]

theorem pipeTrue_spec (cs : List Char) :
    pipeTrue cs = cs.flatMap (fun c => (escapeChar true c).data) := by
  induction cs with
  | nil => simp [pipeTrue, repl]
  | cons c cs ih =>
    have hcons : pipeTrue (c :: cs) = pipeTrue [c] ++ pipeTrue cs := by
      simpa using pipeTrue_append [c] cs
    have himg : pipeTrue [c] = (escapeChar true c).data := by
      simpa [pipeTrue] using image_true c
    simp [hcons, himg, ih, List.flatMap_cons]

theorem replaceChar_data (s : String) (pat : Char) (rep : String) :
    (replaceChar s pat rep).data = repl pat (rep.data) (s.data) := by
  simp [replaceChar, mk_data]

theorem escape_data (s : String) (quote : Bool) :
    (escape s quote).data = s.data.flatMap (fun c => (escapeChar quote c).data) := by
  cases quote with
  | false =>
    simp only [escape, cond_false, replaceChar_data]
    simpa [pipeFalse] using pipeFalse_spec s.data
  | true =>
    simp only [escape, cond_true, replaceChar_data]
    simpa [pipeTrue] using pipeTrue_spec s.data

theorem escapeChar_length (q : Bool) (c : Char) :
    (escapeChar q c).length = 1 + extraLen q c := by
  cases h : classify q c
  · simp [escapeChar, extraLen, h]; rfl
  · simp [escapeChar, extraLen, h]; rfl
  · simp [escapeChar, extraLen, h]; rfl
  · simp [escapeChar, extraLen, h]; rfl
  · simp [escapeChar, extraLen, h]; rfl
  · simp [escapeChar, extraLen, h, String.length_singleton]

theorem length_data (s : String) : s.length = s.data.length := rfl

theorem escape_spec (s : String) (quote : Bool) :
    escape s quote = String.mk (s.data.flatMap fun c => (escapeChar quote c).data) := by
  apply String.ext
  simp [escape_data, mk_data]

theorem escape_append (s t : String) (quote : Bool) :
    escape (s ++ t) quote = escape s quote ++ escape t quote := by
  apply String.ext
  simp [escape_spec, mk_data, String.data_append, List.flatMap_append]

theorem escape_empty (quote : Bool) : escape "" quote = "" := by
  apply String.ext
  simp [escape_spec, mk_data, empty_data]

theorem escape_default (s : String) : escape s = escape s true := rfl

theorem sum_map_add {α : Type} (xs : List α) (f g : α → Nat) :
    (xs.map fun a => f a + g a).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

theorem sum_map_one (xs : List Char) : (xs.map fun _ => 1).sum = xs.length := by
  induction xs with
  | nil => simp
  | cons _ xs ih => simp [ih, Nat.add_comm]

theorem escape_length (s : String) (quote : Bool) :
    (escape s quote).length = s.length + (s.data.map (extraLen quote)).sum := by
  have hdata := escape_data s quote
  rw [show (escape s quote).length = (escape s quote).data.length from rfl, hdata, List.length_flatMap]
  have hchar : ∀ c, ((escapeChar quote c).data).length = 1 + extraLen quote c := by
    intro c
    simpa using escapeChar_length quote c
  simp only [hchar, sum_map_add, sum_map_one]
  rfl

theorem classify_other_ne_amp {q : Bool} {c : Char} (h : classify q c = .other) : c ≠ '&' := by
  intro hc; subst hc; simp [classify] at h

theorem classify_other_ne_lt {q : Bool} {c : Char} (h : classify q c = .other) : c ≠ '<' := by
  intro hc; subst hc; simp [classify] at h

theorem classify_other_ne_gt {q : Bool} {c : Char} (h : classify q c = .other) : c ≠ '>' := by
  intro hc; subst hc; simp [classify] at h

theorem classify_other_ne_quot {c : Char} (h : classify true c = .other) : c ≠ '"' := by
  intro hc; subst hc; simp [classify] at h

theorem classify_other_ne_apos {c : Char} (h : classify true c = .other) : c ≠ '\'' := by
  intro hc; subst hc; simp [classify] at h

theorem escapeChar_count_lt (q : Bool) (c : Char) : (escapeChar q c).data.count '<' = 0 := by
  cases h : classify q c
  · simp [escapeChar, h]
  · simp [escapeChar, h]
  · simp [escapeChar, h]
  · simp [escapeChar, h]
  · simp [escapeChar, h]
  · have hne := classify_other_ne_lt h
    simp [escapeChar, h, String.data_singleton, hne]

theorem escapeChar_count_gt (q : Bool) (c : Char) : (escapeChar q c).data.count '>' = 0 := by
  cases h : classify q c
  · simp [escapeChar, h]
  · simp [escapeChar, h]
  · simp [escapeChar, h]
  · simp [escapeChar, h]
  · simp [escapeChar, h]
  · have hne := classify_other_ne_gt h
    simp [escapeChar, h, String.data_singleton, hne]

theorem escapeChar_count_quot_on (c : Char) : (escapeChar true c).data.count '"' = 0 := by
  cases h : classify true c
  · simp [escapeChar, h]
  · simp [escapeChar, h]
  · simp [escapeChar, h]
  · simp [escapeChar, h]
  · simp [escapeChar, h]
  · have hne := classify_other_ne_quot h
    simp [escapeChar, h, String.data_singleton, hne]

theorem escapeChar_count_apos_on (c : Char) : (escapeChar true c).data.count '\'' = 0 := by
  cases h : classify true c
  · simp [escapeChar, h]
  · simp [escapeChar, h]
  · simp [escapeChar, h]
  · simp [escapeChar, h]
  · simp [escapeChar, h]
  · have hne := classify_other_ne_apos h
    simp [escapeChar, h, String.data_singleton, hne]

theorem count_flat_zero {xs : List Char} {f : Char → List Char} {a : Char}
    (h : ∀ c, (f c).count a = 0) : (xs.flatMap f).count a = 0 := by
  induction xs with
  | nil => simp
  | cons c cs ih => simp [List.flatMap_cons, List.count_append, h, ih]

theorem escape_no_lt (s : String) (q : Bool) : '<' ∉ (escape s q).data := by
  apply List.not_mem_of_count_eq_zero
  rw [escape_data]
  exact count_flat_zero (fun c => escapeChar_count_lt q c)

theorem escape_no_gt (s : String) (q : Bool) : '>' ∉ (escape s q).data := by
  apply List.not_mem_of_count_eq_zero
  rw [escape_data]
  exact count_flat_zero (fun c => escapeChar_count_gt q c)

theorem escape_no_quot (s : String) (q : Bool) (hq : q = true) : '"' ∉ (escape s q).data := by
  subst hq
  apply List.not_mem_of_count_eq_zero
  rw [escape_data]
  exact count_flat_zero (fun c => escapeChar_count_quot_on c)

theorem escape_no_apos (s : String) : '\'' ∉ (escape s true).data := by
  apply List.not_mem_of_count_eq_zero
  rw [escape_data]
  exact count_flat_zero (fun c => escapeChar_count_apos_on c)

def isSafeChar (quote : Bool) (c : Char) : Prop :=
  c ≠ '&' ∧ c ≠ '<' ∧ c ≠ '>' ∧ (quote = true → c ≠ '"' ∧ c ≠ '\'')

theorem escapeChar_of_safe {q : Bool} {c : Char} (h : isSafeChar q c) :
    escapeChar q c = String.singleton c := by
  rcases h with ⟨h1, h2, h3, h4⟩
  cases q with
  | false => simp [escapeChar, classify, beq_iff_eq, h1, h2, h3]
  | true =>
    rcases h4 rfl with ⟨h5, h6⟩
    simp [escapeChar, classify, beq_iff_eq, h1, h2, h3, h5, h6]

theorem flatMap_id_of_singleton (xs : List Char) (f : Char → List Char)
    (h : ∀ c ∈ xs, f c = [c]) : xs.flatMap f = xs := by
  induction xs with
  | nil => simp
  | cons c cs ih =>
    simp [List.flatMap_cons, h c (by simp), ih (fun x hx => h x (by simp [hx]))]

theorem escape_safe_id (s : String) (q : Bool) (h : ∀ c ∈ s.data, isSafeChar q c) :
    escape s q = s := by
  apply String.ext
  rw [escape_data]
  refine flatMap_id_of_singleton s.data _ ?_
  intro c hc
  simp [escapeChar_of_safe (h c hc), String.data_singleton]

-- quotes preserved pointwise
theorem escapeChar_singleton_off {c : Char} (h1 : c ≠ '&') (h2 : c ≠ '<') (h3 : c ≠ '>') :
    escapeChar false c = String.singleton c := by
  simp [escapeChar, classify, beq_iff_eq, h1, h2, h3]

theorem escapeChar_count_quot_off (c : Char) :
    (escapeChar false c).data.count '"' = [c].count '"' := by
  by_cases hamp : c = '&'
  · subst hamp; simp [escapeChar, classify]
  · by_cases hlt : c = '<'
    · subst hlt; simp [escapeChar, classify]
    · by_cases hgt : c = '>'
      · subst hgt; simp [escapeChar, classify]
      · simp [escapeChar_singleton_off hamp hlt hgt, String.data_singleton]

theorem escapeChar_count_apos_off (c : Char) :
    (escapeChar false c).data.count '\'' = [c].count '\'' := by
  by_cases hamp : c = '&'
  · subst hamp; simp [escapeChar, classify]
  · by_cases hlt : c = '<'
    · subst hlt; simp [escapeChar, classify]
    · by_cases hgt : c = '>'
      · subst hgt; simp [escapeChar, classify]
      · simp [escapeChar_singleton_off hamp hlt hgt, String.data_singleton]

theorem count_flatMap_pointwise {xs : List Char} {f g : Char → List Char} {a : Char}
    (h : ∀ c, (f c).count a = (g c).count a) :
    (xs.flatMap f).count a = (xs.flatMap g).count a := by
  induction xs with
  | nil => simp
  | cons c cs ih => simp [List.flatMap_cons, List.count_append, h, ih]

theorem escape_quotes_preserved (s : String) :
    (escape s false).data.count '"' = s.data.count '"' ∧
    (escape s false).data.count '\'' = s.data.count '\'' := by
  constructor
  · rw [escape_data]
    have h := count_flatMap_pointwise (xs := s.data)
      (f := fun c => (escapeChar false c).data) (g := fun c => [c]) (a := '"')
      escapeChar_count_quot_off
    simpa [List.flatMap_singleton'] using h
  · rw [escape_data]
    have h := count_flatMap_pointwise (xs := s.data)
      (f := fun c => (escapeChar false c).data) (g := fun c => [c]) (a := '\'')
      escapeChar_count_apos_off
    simpa [List.flatMap_singleton'] using h

def escapeWrong (s : String) : String :=
  replaceChar (replaceChar (replaceChar s '<' "&lt;") '>' "&gt;") '&' "&amp;"

theorem order_lt : escape "<" true = "&lt;" := by
  apply String.ext
  simp [escape_data, data_lt, List.flatMap]
  rfl

theorem order_wrong_lt : escapeWrong "<" = "&amp;lt;" := by
  apply String.ext
  simp [escapeWrong, replaceChar_data, data_lt, data_amp, repl]

theorem not_idem_amp : escape (escape "&" true) true = "&amp;amp;" := by
  apply String.ext
  simp [escape_data, data_amp]
  rfl


theorem order_amp_lt : escape "&<" true = "&amp;&lt;" := by
  apply String.ext
  simp [escape_data, data_amp, data_lt]
  rfl

theorem order_wrong_amp_lt : escapeWrong "&<" = "&amp;&amp;lt;" := by
  apply String.ext
  simp [escapeWrong, replaceChar_data, data_amp, data_lt, repl]

theorem not_idem_lt : escape (escape "<" true) true = "&amp;lt;" := by
  apply String.ext
  simp [escape_data, data_lt, data_amp]
  rfl

theorem not_idem_gt : escape (escape ">" true) true = "&amp;gt;" := by
  apply String.ext
  simp [escape_data, data_gt, data_amp]
  rfl

theorem not_idem_quot : escape (escape "\"" true) true = "&amp;quot;" := by
  apply String.ext
  simp [escape_data, data_quot, data_amp]
  rfl

theorem not_idem_apos : escape (escape "'" true) true = "&amp;#x27;" := by
  apply String.ext
  simp [escape_data, data_apos, data_amp]
  rfl

theorem ex_main : escape "<b>\"&'</b>" true = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by
  apply String.ext
  simp [escape_data]
  rfl

theorem ex_off : escape "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by
  apply String.ext
  simp [escape_data]
  rfl


def escape_spec_prop (s : String) (quote : Bool) : Prop :=
  escape s quote = String.mk (s.data.flatMap fun c => (escapeChar quote c).data)

theorem escape_spec_thm (s : String) (quote : Bool) : escape_spec_prop s quote :=
  escape_spec s quote

def escape_append_prop (s : String) (quote : Bool) : Prop :=
  ∀ t : String, escape (s ++ t) quote = escape s quote ++ escape t quote

theorem escape_append_thm (s : String) (quote : Bool) : escape_append_prop s quote :=
  fun t => escape_append s t quote

def escape_empty_prop (quote : Bool) : Prop :=
  escape "" quote = ""

theorem escape_empty_thm (quote : Bool) : escape_empty_prop quote :=
  escape_empty quote

def escape_length_prop (s : String) (quote : Bool) : Prop :=
  (escape s quote).length = s.length + (s.data.map (extraLen quote)).sum

theorem escape_length_thm (s : String) (quote : Bool) : escape_length_prop s quote :=
  escape_length s quote

def escape_no_lt_prop (s : String) (quote : Bool) : Prop :=
  '<' ∉ (escape s quote).data

theorem escape_no_lt_thm (s : String) (quote : Bool) : escape_no_lt_prop s quote :=
  escape_no_lt s quote

def escape_no_gt_prop (s : String) (quote : Bool) : Prop :=
  '>' ∉ (escape s quote).data

theorem escape_no_gt_thm (s : String) (quote : Bool) : escape_no_gt_prop s quote :=
  escape_no_gt s quote

def escape_no_quot_prop (s : String) (quote : Bool) : Prop :=
  quote = true → '"' ∉ (escape s quote).data

theorem escape_no_quot_thm (s : String) (quote : Bool) : escape_no_quot_prop s quote :=
  fun hq => escape_no_quot s quote hq

def escape_no_apos_prop (s : String) (quote : Bool) : Prop :=
  quote = true → '\'' ∉ (escape s quote).data

theorem escape_no_apos_thm (s : String) (quote : Bool) : escape_no_apos_prop s quote := by
  intro hq
  subst hq
  exact escape_no_apos s

def escape_safe_id_prop (s : String) (quote : Bool) : Prop :=
  (∀ c ∈ s.data, isSafeChar quote c) → escape s quote = s

theorem escape_safe_id_thm (s : String) (quote : Bool) : escape_safe_id_prop s quote :=
  fun h => escape_safe_id s quote h

def escape_quotes_preserved_prop (s : String) (quote : Bool) : Prop :=
  quote = false →
    (escape s quote).data.count '"' = s.data.count '"' ∧
    (escape s quote).data.count '\'' = s.data.count '\''

theorem escape_quotes_preserved_thm (s : String) (quote : Bool) :
    escape_quotes_preserved_prop s quote := by
  intro hq
  subst hq
  exact escape_quotes_preserved s

def escape_default_prop (s : String) : Prop :=
  escape s = escape s true

theorem escape_default_thm (s : String) : escape_default_prop s :=
  escape_default s

def escape_singleton_prop (c : Char) (quote : Bool) : Prop :=
  escape (String.singleton c) quote = escapeChar quote c

theorem escape_singleton_thm (c : Char) (quote : Bool) : escape_singleton_prop c quote := by
  apply String.ext
  simp [escape_data, String.data_singleton]

def escape_examples_prop : Prop :=
  benchmarkEscape "<b>\"&'</b>" true = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" ∧
  benchmarkEscape "" true = "" ∧
  benchmarkEscape "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" ∧
  benchmarkEscape "&<" true = "&amp;&lt;"

theorem escape_examples_thm : escape_examples_prop :=
  ⟨ex_main, escape_empty true, ex_off, order_amp_lt⟩

def escape_order_matters_prop : Prop :=
  escape "<" true = "&lt;" ∧
  escapeWrong "<" = "&amp;lt;" ∧
  escape "&<" true = "&amp;&lt;" ∧
  escapeWrong "&<" = "&amp;&amp;lt;"

theorem escape_order_matters_thm : escape_order_matters_prop :=
  ⟨order_lt, order_wrong_lt, order_amp_lt, order_wrong_amp_lt⟩

/-- A second pass escapes the ampersands introduced by the first. -/
def escape_not_idempotent_prop : Prop :=
  escape (escape "&" true) true = "&amp;amp;" ∧
  escape (escape "<" true) true = "&amp;lt;" ∧
  escape (escape ">" true) true = "&amp;gt;" ∧
  escape (escape "\"" true) true = "&amp;quot;" ∧
  escape (escape "'" true) true = "&amp;#x27;"

theorem escape_not_idempotent_thm : escape_not_idempotent_prop :=
  ⟨not_idem_amp, not_idem_lt, not_idem_gt, not_idem_quot, not_idem_apos⟩

def benchmark_escape_prop (s : String) (quote : Bool) : Prop :=
  benchmarkEscape s quote = escape s quote

theorem benchmark_escape_thm (s : String) (quote : Bool) : benchmark_escape_prop s quote := rfl

/-- Post-condition: the escape contract, as the conjunction of the properties above. -/
def Post_prop (s : String) (quote : Bool) : Prop :=
  escape_spec_prop s quote ∧
  escape_append_prop s quote ∧
  escape_empty_prop quote ∧
  escape_length_prop s quote ∧
  escape_no_lt_prop s quote ∧
  escape_no_gt_prop s quote ∧
  escape_no_quot_prop s quote ∧
  escape_no_apos_prop s quote ∧
  escape_safe_id_prop s quote ∧
  escape_quotes_preserved_prop s quote ∧
  escape_default_prop s ∧
  (∀ c : Char, escape_singleton_prop c quote) ∧
  escape_examples_prop ∧
  escape_order_matters_prop ∧
  escape_not_idempotent_prop ∧
  benchmark_escape_prop s quote

/-! ## Property-based tests -/

def pbtAlphabet : List Char := ['a', '&', '<', '>', '"', '\'', 'x']

def pbtSingles : List String :=
  pbtAlphabet.map fun c => String.singleton c

def pbtDoubles : List String :=
  pbtAlphabet.flatMap fun c =>
    pbtAlphabet.map fun d => String.singleton c ++ String.singleton d

def pbtStrings : List String :=
  ["", "plain", "<b>\"&'</b>", "&<", "&amp;", "<>\"'", "hello"] ++ pbtSingles ++ pbtDoubles

def pbtShort : List String :=
  "" :: pbtSingles

def safeB (quote : Bool) (c : Char) : Bool :=
  c != '&' && c != '<' && c != '>' && (quote == false || (c != '"' && c != '\''))

def encoded (quote : Bool) (s : String) : String :=
  String.mk (s.data.flatMap fun c => (escapeChar quote c).data)

/-- Executable form of `Post_prop` on one input, with append checked against `partners`. -/
def postBool (s : String) (quote : Bool) (partners : List String) : Bool :=
  (escape s quote == encoded quote s) &&
  (escape "" quote == "") &&
  ((escape s quote).length == s.length + (s.data.map (extraLen quote)).sum) &&
  ((escape s quote).data.count '<' == 0) &&
  ((escape s quote).data.count '>' == 0) &&
  (quote == false || (escape s quote).data.count '"' == 0) &&
  (quote == false || (escape s quote).data.count '\'' == 0) &&
  (!(s.data.all (safeB quote)) || escape s quote == s) &&
  (quote == true ||
    ((escape s quote).data.count '"' == s.data.count '"' &&
     (escape s quote).data.count '\'' == s.data.count '\'')) &&
  (escape s == escape s true) &&
  (benchmarkEscape s quote == escape s quote) &&
  partners.all (fun t => escape (s ++ t) quote == escape s quote ++ escape t quote)

def globalsBool : Bool :=
  (benchmarkEscape "<b>\"&'</b>" true == "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;") &&
  (benchmarkEscape "" true == "") &&
  (benchmarkEscape "<b>\"&'</b>" false == "&lt;b&gt;\"&amp;'&lt;/b&gt;") &&
  (benchmarkEscape "&<" true == "&amp;&lt;") &&
  (escape "<" true == "&lt;") &&
  (escapeWrong "<" == "&amp;lt;") &&
  (escape "&<" true == "&amp;&lt;") &&
  (escapeWrong "&<" == "&amp;&amp;lt;") &&
  (escape (escape "&" true) true == "&amp;amp;") &&
  (escape (escape "<" true) true == "&amp;lt;") &&
  (escape (escape ">" true) true == "&amp;gt;") &&
  (escape (escape "\"" true) true == "&amp;quot;") &&
  (escape (escape "'" true) true == "&amp;#x27;")

-- PBT: escape_spec_prop
example : ([true, false]).all (fun q =>
    pbtStrings.all (fun s => escape s q == encoded q s)) = true := by
  native_decide

-- PBT: escape_append_prop
example : ([true, false]).all (fun q =>
    pbtShort.all (fun s =>
      pbtShort.all (fun t =>
        escape (s ++ t) q == escape s q ++ escape t q))) = true := by
  native_decide

-- PBT: escape_empty_prop
example : ([true, false]).all (fun q => escape "" q == "") = true := by
  native_decide

-- PBT: escape_length_prop
example : ([true, false]).all (fun q =>
    pbtStrings.all (fun s =>
      (escape s q).length == s.length + (s.data.map (extraLen q)).sum)) = true := by
  native_decide

-- PBT: escape_no_lt_prop
example : ([true, false]).all (fun q =>
    pbtStrings.all (fun s => (escape s q).data.count '<' == 0)) = true := by
  native_decide

-- PBT: escape_no_gt_prop
example : ([true, false]).all (fun q =>
    pbtStrings.all (fun s => (escape s q).data.count '>' == 0)) = true := by
  native_decide

-- PBT: escape_no_quot_prop
example : pbtStrings.all (fun s => (escape s true).data.count '"' == 0) = true := by
  native_decide

-- PBT: escape_no_apos_prop
example : pbtStrings.all (fun s => (escape s true).data.count '\'' == 0) = true := by
  native_decide

-- PBT: escape_safe_id_prop
example : ([true, false]).all (fun q =>
    pbtStrings.all (fun s =>
      !(s.data.all (safeB q)) || escape s q == s)) = true := by
  native_decide

-- PBT: escape_quotes_preserved_prop
example : pbtStrings.all (fun s =>
    (escape s false).data.count '"' == s.data.count '"' &&
    (escape s false).data.count '\'' == s.data.count '\'') = true := by
  native_decide

-- PBT: escape_default_prop
example : pbtStrings.all (fun s => escape s == escape s true) = true := by
  native_decide

-- PBT: escape_singleton_prop, exhaustive on ASCII
example : (List.range 128).all (fun n =>
    let c := Char.ofNat n
    (escape (String.singleton c) true == escapeChar true c) &&
    (escape (String.singleton c) false == escapeChar false c)) = true := by
  native_decide

-- PBT: escape_examples_prop, escape_order_matters_prop, escape_not_idempotent_prop
example : globalsBool = true := by
  native_decide

-- PBT: benchmark_escape_prop
example : ([true, false]).all (fun q =>
    pbtStrings.all (fun s => benchmarkEscape s q == escape s q)) = true := by
  native_decide

-- PBT: Post_prop
example : ([true, false]).all (fun q =>
    pbtStrings.all (fun s => postBool s q pbtShort)) && globalsBool = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ s t : String, ∀ q : Bool, escape (s ++ t) q = escape s q ++ escape t q)

#eval Plausible.Testable.check
  (∀ s : String, ∀ q : Bool, escape s q = encoded q s)

#eval Plausible.Testable.check
  (∀ s : String, ∀ q : Bool, (escape s q).data.count '<' = 0)

#eval Plausible.Testable.check
  (∀ s : String, ∀ q : Bool, (escape s q).data.count '>' = 0)

#eval Plausible.Testable.check
  (∀ s : String, ∀ q : Bool, (s.data.all (safeB q) = true) → escape s q = s)

#eval Plausible.Testable.check
  (∀ q : Bool, escape "" q = "")

theorem correctness_thm (s : String) (quote : Bool) (_hpre : Pre s quote) :
    Post_prop s quote :=
  ⟨escape_spec_thm s quote,
   escape_append_thm s quote,
   escape_empty_thm quote,
   escape_length_thm s quote,
   escape_no_lt_thm s quote,
   escape_no_gt_thm s quote,
   escape_no_quot_thm s quote,
   escape_no_apos_thm s quote,
   escape_safe_id_thm s quote,
   escape_quotes_preserved_thm s quote,
   escape_default_thm s,
   fun c => escape_singleton_thm c quote,
   escape_examples_thm,
   escape_order_matters_thm,
   escape_not_idempotent_thm,
   benchmark_escape_thm s quote⟩

def replaceStep (pat : Char) (rep acc : String) (c : Char) : String :=
  if c == pat then acc ++ rep else acc.push c

def replaceCharImp (s : String) (pat : Char) (rep : String) : String :=
  Id.run do
    let mut acc := ""
    for c in s.data do
      acc := replaceStep pat rep acc c
    return acc

def escapeImp (s : String) (quote : Bool := true) : String :=
  Id.run do
    let mut out := replaceCharImp (replaceCharImp (replaceCharImp s '&' "&amp;") '<' "&lt;") '>' "&gt;"
    out := cond quote (replaceCharImp (replaceCharImp out '"' "&quot;") '\'' "&#x27;") out
    return out


-- Imperative tests

example : escapeImp "<b>\"&'</b>" = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by
  native_decide

example : escapeImp "" = "" := by
  native_decide

example : escapeImp "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by
  native_decide

example : escapeImp "&<" = "&amp;&lt;" := by
  native_decide

example : escapeImp "plain" = "plain" := by
  native_decide

#eval escapeImp "<b>\"&'</b>"
#eval escapeImp "<b>\"&'</b>" false
#eval escapeImp "&<"
#eval escapeImp ""
#eval escapeImp "plain"

theorem loop_eq (orig xs : List Char) (acc : String) (pat : Char) (rep : String)
    (h : ∃ bs, bs ++ xs = orig) :
    List.forIn'.loop (m := Id) orig
        (fun c _mem r => do
          pure PUnit.unit
          pure (ForInStep.yield (replaceStep pat rep r c)))
        xs acc h
      = xs.foldl (replaceStep pat rep) acc := by
  induction xs generalizing acc orig with
  | nil =>
    rw [List.forIn'.loop.eq_1]
    simp [pure, List.foldl]
  | cons x xs ih =>
    rw [List.forIn'.loop.eq_2]
    simp [bind, pure, List.foldl]
    apply ih

theorem replaceCharImp_foldl (s : String) (pat : Char) (rep : String) :
    replaceCharImp s pat rep = s.data.foldl (replaceStep pat rep) "" := by
  unfold replaceCharImp
  delta Id.run
  simp only [forIn_eq_forIn', ← List.forIn'_eq_forIn']
  unfold List.forIn'
  exact loop_eq s.data s.data "" pat rep ⟨[], by simp⟩

theorem push_append_singleton (s : String) (c : Char) :
    s.push c = s ++ String.singleton c := by
  apply String.ext
  simp [String.data_push, String.data_append, String.data_singleton]

theorem foldl_step_data (xs : List Char) (acc : String) (pat : Char) (rep : String) :
    (xs.foldl (replaceStep pat rep) acc).data = acc.data ++ repl pat (rep.data) xs := by
  induction xs generalizing acc with
  | nil => simp [repl]
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    simp only [repl, List.flatMap_cons, List.append_assoc]
    unfold replaceStep
    split <;> simp [String.data_append, String.data_singleton, push_append_singleton, List.append_assoc]

theorem replaceCharImp_eq (s : String) (pat : Char) (rep : String) :
    replaceCharImp s pat rep = replaceChar s pat rep := by
  apply String.ext
  rw [replaceCharImp_foldl, foldl_step_data]
  simp [replaceChar, empty_data]

theorem escapeImp_unfold (s : String) (quote : Bool) :
    escapeImp s quote =
      let base := replaceCharImp (replaceCharImp (replaceCharImp s '&' "&amp;") '<' "&lt;") '>' "&gt;"
      cond quote (replaceCharImp (replaceCharImp base '"' "&quot;") '\'' "&#x27;") base := by
  rfl

theorem escape_equiv_thm (s : String) (quote : Bool) : escape s quote = escapeImp s quote := by
  rw [escapeImp_unfold]
  cases quote <;> simp [escape, replaceCharImp_eq]

end «20_html_escape»
