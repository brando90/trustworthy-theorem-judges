import Mathlib

/-!
# HTML escaping

Lean formalization of the classic `html.escape` routine (Python's `html`
library): replace `&`, `<` and `>` by HTML-safe entities, and, when `quote`
is true, also replace `"` by `&quot;` and `'` by `&#x27;`.

`&` is replaced first and inserted text is not scanned again, so a single
call does not double-escape. Strings are sequences of Unicode code points,
matching Python 3 `str`. Non-`str` inputs are outside this type; Python would
raise `TypeError` there.
-/

namespace «20_html_escape»

open String

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

abbrev ampR : List Char := "&amp;".data
abbrev ltR : List Char := "&lt;".data
abbrev gtR : List Char := "&gt;".data
abbrev quotR : List Char := "&quot;".data
abbrev aposR : List Char := "&#x27;".data

/-- Python `str.replace` for a one-character pattern. The replacement is not re-scanned. -/
def replaceChar (pat : Char) (repl : List Char) : List Char → List Char
  | [] => []
  | c :: cs => (if c = pat then repl else [c]) ++ replaceChar pat repl cs

/-- One original character, encoded the way `html.escape` encodes it. -/
def encodeChar (quote : Bool) (c : Char) : List Char :=
  if c = '&' then ampR
  else if c = '<' then ltR
  else if c = '>' then gtR
  else if quote = true ∧ c = '"' then quotR
  else if quote = true ∧ c = '\'' then aposR
  else [c]

/-- Successive replacements, in the same order as Python's `html.escape`. -/
def escapeData (quote : Bool) (cs : List Char) : List Char :=
  let core := replaceChar '>' gtR (replaceChar '<' ltR (replaceChar '&' ampR cs))
  if quote = true then
    replaceChar '\'' aposR (replaceChar '"' quotR core)
  else
    core

def escape (s : String) (quote : Bool := true) : String :=
  ⟨escapeData quote s.data⟩

/-- Entry point checked by the Python driver. Every Lean `String` satisfies
`pre_escape`, so this is `escape`. -/
def benchmarkEscape (s : String) (quote : Bool := true) : String :=
  escape s quote

/-- The Python `check` harness, as a Boolean. -/
def check (candidate : String → Bool → String) : Bool :=
  candidate "<b>\"&'</b>" true == "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" &&
  candidate "" true == "" &&
  candidate "<b>\"&'</b>" false == "&lt;b&gt;\"&amp;'&lt;/b&gt;" &&
  candidate "&<" true == "&amp;&lt;"

/-! ## Unit tests -/

example : escape "<b>\"&'</b>" = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by native_decide
example : escape "" = "" := by native_decide
example : escape "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by native_decide
example : escape "&<" = "&amp;&lt;" := by native_decide
example : escape "&<" true = "&amp;&lt;" := by native_decide
example : check (fun s q => escape s q) = true := by native_decide
example : benchmarkEscape "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by native_decide

#eval escape "<b>\"&'</b>"
#eval escape "<b>\"&'</b>" false
#eval escape ""
#eval escape "&<"
#eval check (fun s q => escape s q)

/-! ## Pre-condition -/

/-- Python `pre_escape`: the input is a `str`. Lean's `String` is that domain,
and `quote` may be either Boolean. -/
def Pre (_s : String) (_quote : Bool) : Prop := True

/-! ## Lemmas toward the character-wise specification -/

theorem replaceChar_append (pat : Char) (repl xs ys : List Char) :
    replaceChar pat repl (xs ++ ys) = replaceChar pat repl xs ++ replaceChar pat repl ys := by
  induction xs with
  | nil => simp [replaceChar]
  | cons x xs ih => simp [replaceChar, ih, List.append_assoc]

theorem replaceChar_of_not_mem {pat : Char} {repl xs : List Char} (h : pat ∉ xs) :
    replaceChar pat repl xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : x ≠ pat := by
      intro heq
      exact h (by simp [heq])
    have hxs : pat ∉ xs := fun hm => h (List.mem_cons_of_mem _ hm)
    simp [replaceChar, hx, ih hxs]

theorem replace_one (q : Char) (rq : List Char) (f : Char → List Char) (c : Char)
    (hf_skip : c ≠ q → q ∉ f c) (hf_id : c = q → f c = [c]) :
    replaceChar q rq (f c) = if c = q then rq else f c := by
  by_cases hq : c = q
  · subst hq
    have hid : f c = [c] := hf_id rfl
    rw [hid]
    simp [replaceChar]
  · simp [replaceChar_of_not_mem (hf_skip hq), hq]

theorem replace_on_cascade (q : Char) (rq : List Char) (f : Char → List Char) (cs : List Char)
    (hf_skip : ∀ c, c ≠ q → q ∉ f c) (hf_id : ∀ c, c = q → f c = [c]) :
    replaceChar q rq (cs.flatMap f) = cs.flatMap fun c => if c = q then rq else f c := by
  induction cs with
  | nil => simp [replaceChar]
  | cons c cs ih =>
    simp only [List.flatMap_cons, replaceChar_append, ih,
      replace_one q rq f c (hf_skip c) (hf_id c)]

def enc1 (c : Char) : List Char := if c = '&' then ampR else [c]
def enc2 (c : Char) : List Char := if c = '&' then ampR else if c = '<' then ltR else [c]
def enc3 (c : Char) : List Char :=
  if c = '&' then ampR else if c = '<' then ltR else if c = '>' then gtR else [c]
def enc4 (c : Char) : List Char :=
  if c = '&' then ampR else if c = '<' then ltR else if c = '>' then gtR
  else if c = '"' then quotR else [c]
def enc5 (c : Char) : List Char :=
  if c = '&' then ampR else if c = '<' then ltR else if c = '>' then gtR
  else if c = '"' then quotR else if c = '\'' then aposR else [c]

theorem lt_not_amp : '<' ∉ ampR := by decide
theorem gt_not_amp : '>' ∉ ampR := by decide
theorem gt_not_lt : '>' ∉ ltR := by decide
theorem quot_not_amp : '"' ∉ ampR := by decide
theorem quot_not_lt : '"' ∉ ltR := by decide
theorem quot_not_gt : '"' ∉ gtR := by decide
theorem apos_not_amp : '\'' ∉ ampR := by decide
theorem apos_not_lt : '\'' ∉ ltR := by decide
theorem apos_not_gt : '\'' ∉ gtR := by decide
theorem apos_not_quot : '\'' ∉ quotR := by decide

theorem enc1_id_lt (c : Char) (h : c = '<') : enc1 c = [c] := by
  subst h; decide

theorem enc1_skip_lt (c : Char) (h : c ≠ '<') : '<' ∉ enc1 c := by
  simp only [enc1]
  by_cases hc : c = '&'
  · subst hc; simpa using lt_not_amp
  · simp [hc, List.mem_singleton]
    intro heq
    exact h heq.symm

theorem step_enc2 (c : Char) : (if c = '<' then ltR else enc1 c) = enc2 c := by
  by_cases h1 : c = '&'
  · subst h1; decide
  by_cases h2 : c = '<'
  · subst h2; decide
  · simp [enc1, enc2, h1, h2]

theorem after_lt (cs : List Char) :
    replaceChar '<' ltR (cs.flatMap enc1) = cs.flatMap enc2 := by
  rw [replace_on_cascade '<' ltR enc1 cs enc1_skip_lt enc1_id_lt]
  apply congrArg (fun f => cs.flatMap f)
  funext c
  exact step_enc2 c

theorem enc2_id_gt (c : Char) (h : c = '>') : enc2 c = [c] := by
  subst h; decide

theorem enc2_skip_gt (c : Char) (h : c ≠ '>') : '>' ∉ enc2 c := by
  simp only [enc2]
  by_cases h1 : c = '&'
  · subst h1; simpa using gt_not_amp
  by_cases h2 : c = '<'
  · subst h2; simpa using gt_not_lt
  · simp [h1, h2, List.mem_singleton]
    intro heq
    exact h heq.symm

theorem step_enc3 (c : Char) : (if c = '>' then gtR else enc2 c) = enc3 c := by
  by_cases h1 : c = '&'
  · subst h1; decide
  by_cases h2 : c = '<'
  · subst h2; decide
  by_cases h3 : c = '>'
  · subst h3; decide
  · simp [enc2, enc3, h1, h2, h3]

theorem after_gt (cs : List Char) :
    replaceChar '>' gtR (cs.flatMap enc2) = cs.flatMap enc3 := by
  rw [replace_on_cascade '>' gtR enc2 cs enc2_skip_gt enc2_id_gt]
  apply congrArg (fun f => cs.flatMap f)
  funext c
  exact step_enc3 c

theorem core_eq (cs : List Char) :
    replaceChar '>' gtR (replaceChar '<' ltR (replaceChar '&' ampR cs)) = cs.flatMap enc3 := by
  have h1 : replaceChar '&' ampR cs = cs.flatMap enc1 := by
    induction cs with
    | nil => simp [replaceChar]
    | cons c cs ih => simp [replaceChar, enc1, ih]
  rw [h1, after_lt, after_gt]

theorem enc3_id_quot (c : Char) (h : c = '"') : enc3 c = [c] := by
  subst h; decide

theorem enc3_skip_quot (c : Char) (h : c ≠ '"') : '"' ∉ enc3 c := by
  simp only [enc3]
  by_cases h1 : c = '&'
  · subst h1; simpa using quot_not_amp
  by_cases h2 : c = '<'
  · subst h2; simpa using quot_not_lt
  by_cases h3 : c = '>'
  · subst h3; simpa using quot_not_gt
  · simp [h1, h2, h3, List.mem_singleton]
    intro heq
    exact h heq.symm

theorem step_enc4 (c : Char) : (if c = '"' then quotR else enc3 c) = enc4 c := by
  by_cases h1 : c = '&'
  · subst h1; decide
  by_cases h2 : c = '<'
  · subst h2; decide
  by_cases h3 : c = '>'
  · subst h3; decide
  by_cases h4 : c = '"'
  · subst h4; decide
  · simp [enc3, enc4, h1, h2, h3, h4]

theorem after_quot (cs : List Char) :
    replaceChar '"' quotR (cs.flatMap enc3) = cs.flatMap enc4 := by
  rw [replace_on_cascade '"' quotR enc3 cs enc3_skip_quot enc3_id_quot]
  apply congrArg (fun f => cs.flatMap f)
  funext c
  exact step_enc4 c

theorem enc4_id_apos (c : Char) (h : c = '\'') : enc4 c = [c] := by
  subst h; decide

theorem enc4_skip_apos (c : Char) (h : c ≠ '\'') : '\'' ∉ enc4 c := by
  simp only [enc4]
  by_cases h1 : c = '&'
  · subst h1; simpa using apos_not_amp
  by_cases h2 : c = '<'
  · subst h2; simpa using apos_not_lt
  by_cases h3 : c = '>'
  · subst h3; simpa using apos_not_gt
  by_cases h4 : c = '"'
  · subst h4; simpa using apos_not_quot
  · simp [h1, h2, h3, h4, List.mem_singleton]
    intro heq
    exact h heq.symm

theorem step_enc5 (c : Char) : (if c = '\'' then aposR else enc4 c) = enc5 c := by
  by_cases h1 : c = '&'
  · subst h1; decide
  by_cases h2 : c = '<'
  · subst h2; decide
  by_cases h3 : c = '>'
  · subst h3; decide
  by_cases h4 : c = '"'
  · subst h4; decide
  by_cases h5 : c = '\''
  · subst h5; decide
  · simp [enc4, enc5, h1, h2, h3, h4, h5]

theorem after_apos (cs : List Char) :
    replaceChar '\'' aposR (cs.flatMap enc4) = cs.flatMap enc5 := by
  rw [replace_on_cascade '\'' aposR enc4 cs enc4_skip_apos enc4_id_apos]
  apply congrArg (fun f => cs.flatMap f)
  funext c
  exact step_enc5 c

theorem enc3_encode_false (c : Char) : enc3 c = encodeChar false c := by
  simp [enc3, encodeChar]

theorem enc5_encode_true (c : Char) : enc5 c = encodeChar true c := by
  simp [enc5, encodeChar]

theorem escapeData_eq_flatMap (quote : Bool) (cs : List Char) :
    escapeData quote cs = cs.flatMap (encodeChar quote) := by
  cases quote with
  | false =>
    rw [show escapeData false cs = cs.flatMap enc3 by simp [escapeData, core_eq]]
    apply congrArg (fun f => cs.flatMap f)
    funext c
    exact enc3_encode_false c
  | true =>
    rw [show escapeData true cs = cs.flatMap enc5 by
      simp [escapeData, core_eq, after_quot, after_apos]]
    apply congrArg (fun f => cs.flatMap f)
    funext c
    exact enc5_encode_true c

theorem one_pass (s : String) (quote : Bool) :
    (escape s quote).data = s.data.flatMap (encodeChar quote) := by
  simp [escape, escapeData_eq_flatMap]

theorem escape_append (s t : String) (quote : Bool) :
    escape (s ++ t) quote = escape s quote ++ escape t quote := by
  apply String.ext
  simp [escape, String.data_append, escapeData_eq_flatMap, List.flatMap_append]

theorem encodeChar_no_lt (quote : Bool) (c : Char) : '<' ∉ encodeChar quote c := by
  unfold encodeChar
  by_cases h1 : c = '&'
  · simp [h1]; decide
  by_cases h2 : c = '<'
  · simp [h2]; decide
  by_cases h3 : c = '>'
  · simp [h1, h2, h3]; decide
  by_cases h4 : quote = true ∧ c = '"'
  · simp [h1, h2, h3, h4]; decide
  by_cases h5 : quote = true ∧ c = '\''
  · simp [h1, h2, h3, h4, h5]; decide
  · simp [h1, h2, h3, h4, h5, List.mem_singleton]
    intro heq
    exact h2 heq.symm

theorem no_raw_lt (s : String) (quote : Bool) : '<' ∉ (escape s quote).data := by
  rw [one_pass]
  intro h
  rcases List.mem_flatMap.mp h with ⟨c, _, hc⟩
  exact encodeChar_no_lt quote c hc

theorem encodeChar_no_gt (quote : Bool) (c : Char) : '>' ∉ encodeChar quote c := by
  unfold encodeChar
  by_cases h1 : c = '&'
  · simp [h1]; decide
  by_cases h2 : c = '<'
  · simp [h2]; decide
  by_cases h3 : c = '>'
  · simp [h1, h2, h3]; decide
  by_cases h4 : quote = true ∧ c = '"'
  · simp [h1, h2, h3, h4]; decide
  by_cases h5 : quote = true ∧ c = '\''
  · simp [h1, h2, h3, h4, h5]; decide
  · simp [h1, h2, h3, h4, h5]
    intro heq
    exact h3 heq.symm

theorem no_raw_gt (s : String) (quote : Bool) : '>' ∉ (escape s quote).data := by
  rw [one_pass]
  intro h
  rcases List.mem_flatMap.mp h with ⟨c, _, hc⟩
  exact encodeChar_no_gt quote c hc

theorem encodeChar_no_dquot (c : Char) : '"' ∉ encodeChar true c := by
  unfold encodeChar
  by_cases h1 : c = '&'
  · simp [h1]; decide
  by_cases h2 : c = '<'
  · simp [h2]; decide
  by_cases h3 : c = '>'
  · simp [h1, h2, h3]; decide
  by_cases h4 : c = '"'
  · simp [h1, h2, h3, h4]; decide
  by_cases h5 : c = '\''
  · simp [h1, h2, h3, h4, h5]; decide
  · simp [h1, h2, h3, h4, h5]
    intro heq
    exact h4 heq.symm

theorem no_raw_dquot (s : String) : '"' ∉ (escape s true).data := by
  rw [one_pass]
  intro h
  rcases List.mem_flatMap.mp h with ⟨c, _, hc⟩
  exact encodeChar_no_dquot c hc

theorem encodeChar_no_apos (c : Char) : '\'' ∉ encodeChar true c := by
  unfold encodeChar
  by_cases h1 : c = '&'
  · simp [h1]; decide
  by_cases h2 : c = '<'
  · simp [h2]; decide
  by_cases h3 : c = '>'
  · simp [h1, h2, h3]; decide
  by_cases h4 : c = '"'
  · simp [h1, h2, h3, h4]; decide
  by_cases h5 : c = '\''
  · simp [h1, h2, h3, h4, h5]; decide
  · simp [h1, h2, h3, h4, h5]
    intro heq
    exact h5 heq.symm

theorem no_raw_apos (s : String) : '\'' ∉ (escape s true).data := by
  rw [one_pass]
  intro h
  rcases List.mem_flatMap.mp h with ⟨c, _, hc⟩
  exact encodeChar_no_apos c hc

theorem encodeChar_len_ge (quote : Bool) (c : Char) : 1 ≤ (encodeChar quote c).length := by
  unfold encodeChar
  by_cases h1 : c = '&'
  · simp [h1]; decide
  by_cases h2 : c = '<'
  · simp [h2]; decide
  by_cases h3 : c = '>'
  · simp [h1, h2, h3]; decide
  by_cases h4 : quote = true ∧ c = '"'
  · simp [h1, h2, h3, h4]; decide
  by_cases h5 : quote = true ∧ c = '\''
  · simp [h1, h2, h3, h4, h5]; decide
  · simp [h1, h2, h3, h4, h5, List.length_singleton]

theorem length_flatMap_ge (quote : Bool) (cs : List Char) :
    cs.length ≤ (cs.flatMap (encodeChar quote)).length := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    have hc := encodeChar_len_ge quote c
    calc
      cs.length + 1 ≤ (cs.flatMap (encodeChar quote)).length + 1 := Nat.add_le_add_right ih 1
      _ ≤ (cs.flatMap (encodeChar quote)).length + (encodeChar quote c).length :=
        Nat.add_le_add_left hc _
      _ = (encodeChar quote c).length + (cs.flatMap (encodeChar quote)).length := Nat.add_comm _ _

theorem length_ge (s : String) (quote : Bool) : s.length ≤ (escape s quote).length := by
  have hs : s.length = s.data.length := by cases s; rfl
  rw [hs, escape, String.length_mk, escapeData_eq_flatMap]
  exact length_flatMap_ge quote s.data

theorem length_exact (s : String) (quote : Bool) :
    (escape s quote).length = (s.data.map (fun c => (encodeChar quote c).length)).sum := by
  simp [escape, String.length_mk, escapeData_eq_flatMap, List.length_flatMap]

theorem encodeChar_of_safe (quote : Bool) (c : Char)
    (h1 : c ≠ '&') (h2 : c ≠ '<') (h3 : c ≠ '>')
    (h4 : quote = true → c ≠ '"') (h5 : quote = true → c ≠ '\'') :
    encodeChar quote c = [c] := by
  unfold encodeChar
  simp [h1, h2, h3]
  cases quote with
  | false => simp
  | true => simp [h4 rfl, h5 rfl]

theorem flatMap_id_of (cs : List Char) (f : Char → List Char)
    (h : ∀ c, c ∈ cs → f c = [c]) : cs.flatMap f = cs := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have hc : f c = [c] := h c (by simp)
    have hcs : ∀ x, x ∈ cs → f x = [x] := fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp [List.flatMap_cons, hc, ih hcs]

theorem escape_of_safe (s : String) (quote : Bool)
    (h : ∀ c, c ∈ s.data → encodeChar quote c = [c]) : escape s quote = s := by
  apply String.ext
  simp [escape, escapeData_eq_flatMap, flatMap_id_of s.data (encodeChar quote) h]

theorem quote_branch_data (cs : List Char) :
    escapeData true cs =
      replaceChar '\'' aposR (replaceChar '"' quotR (escapeData false cs)) := by
  simp [escapeData]


/-! ## Properties -/

abbrev one_pass_prop (s : String) (quote : Bool) : Prop :=
  (escape s quote).data = s.data.flatMap (encodeChar quote)

theorem one_pass_thm (s : String) (quote : Bool) : one_pass_prop s quote :=
  one_pass s quote

abbrev empty_prop (quote : Bool) : Prop :=
  escape "" quote = ""

theorem empty_thm (quote : Bool) : empty_prop quote := by
  cases quote <;> decide

abbrev amp_prop (quote : Bool) : Prop :=
  escape "&" quote = "&amp;"

theorem amp_thm (quote : Bool) : amp_prop quote := by
  cases quote <;> decide

abbrev lt_prop (quote : Bool) : Prop :=
  escape "<" quote = "&lt;"

theorem lt_thm (quote : Bool) : lt_prop quote := by
  cases quote <;> decide

abbrev gt_prop (quote : Bool) : Prop :=
  escape ">" quote = "&gt;"

theorem gt_thm (quote : Bool) : gt_prop quote := by
  cases quote <;> decide

abbrev double_quote_prop (quote : Bool) : Prop :=
  escape "\"" quote = if quote then "&quot;" else "\""

theorem double_quote_thm (quote : Bool) : double_quote_prop quote := by
  cases quote <;> decide

abbrev single_quote_prop (quote : Bool) : Prop :=
  escape "'" quote = if quote then "&#x27;" else "'"

theorem single_quote_thm (quote : Bool) : single_quote_prop quote := by
  cases quote <;> decide

/-- The regression from the Python tests: `&` then `<` becomes `&amp;&lt;`,
not `&amp;amp;lt;`. -/
abbrev order_prop (quote : Bool) : Prop :=
  escape "&<" quote = "&amp;&lt;"

theorem order_thm (quote : Bool) : order_prop quote := by
  cases quote <;> decide

/-- One call encodes `<` as `&lt;`. A second call encodes the inserted `&`,
which is why `&` is replaced first and replacements are not re-scanned. -/
abbrev no_double_escape_prop (quote : Bool) : Prop :=
  escape "<" quote = "&lt;" ∧ escape (escape "<" quote) quote = "&amp;lt;"

theorem no_double_escape_thm (quote : Bool) : no_double_escape_prop quote := by
  cases quote <;> decide

abbrev append_prop (s t : String) (quote : Bool) : Prop :=
  escape (s ++ t) quote = escape s quote ++ escape t quote

theorem append_thm (s t : String) (quote : Bool) : append_prop s t quote :=
  escape_append s t quote

abbrev no_raw_lt_prop (s : String) (quote : Bool) : Prop :=
  '<' ∉ (escape s quote).data

theorem no_raw_lt_thm (s : String) (quote : Bool) : no_raw_lt_prop s quote :=
  no_raw_lt s quote

abbrev no_raw_gt_prop (s : String) (quote : Bool) : Prop :=
  '>' ∉ (escape s quote).data

theorem no_raw_gt_thm (s : String) (quote : Bool) : no_raw_gt_prop s quote :=
  no_raw_gt s quote

abbrev no_raw_dquot_prop (s : String) (quote : Bool) : Prop :=
  quote = true → '"' ∉ (escape s quote).data

theorem no_raw_dquot_thm (s : String) (quote : Bool) : no_raw_dquot_prop s quote := by
  intro hq
  subst hq
  exact no_raw_dquot s

abbrev no_raw_apos_prop (s : String) (quote : Bool) : Prop :=
  quote = true → '\'' ∉ (escape s quote).data

theorem no_raw_apos_thm (s : String) (quote : Bool) : no_raw_apos_prop s quote := by
  intro hq
  subst hq
  exact no_raw_apos s

abbrev length_ge_prop (s : String) (quote : Bool) : Prop :=
  s.length ≤ (escape s quote).length

theorem length_ge_thm (s : String) (quote : Bool) : length_ge_prop s quote :=
  length_ge s quote

abbrev length_exact_prop (s : String) (quote : Bool) : Prop :=
  (escape s quote).length = (s.data.map fun c => (encodeChar quote c).length).sum

theorem length_exact_thm (s : String) (quote : Bool) : length_exact_prop s quote :=
  length_exact s quote

abbrev safe_char_prop (c : Char) (quote : Bool) : Prop :=
  (c ≠ '&' ∧ c ≠ '<' ∧ c ≠ '>' ∧ (quote = true → c ≠ '"' ∧ c ≠ '\'')) →
    escape (String.singleton c) quote = String.singleton c

theorem safe_char_thm (c : Char) (quote : Bool) : safe_char_prop c quote := by
  intro h
  rcases h with ⟨h1, h2, h3, hrest⟩
  apply String.ext
  simp [one_pass, String.data_singleton, List.flatMap_cons, List.flatMap_nil,
    encodeChar_of_safe quote c h1 h2 h3 (fun hq => (hrest hq).1) (fun hq => (hrest hq).2)]

/-- If every character is left alone by `encodeChar`, the string is unchanged. -/
abbrev preserves_safe_prop (s : String) (quote : Bool) : Prop :=
  (∀ c, c ∈ s.data → c ≠ '&' ∧ c ≠ '<' ∧ c ≠ '>' ∧
      (quote = true → c ≠ '"' ∧ c ≠ '\'')) →
    escape s quote = s

theorem preserves_safe_thm (s : String) (quote : Bool) : preserves_safe_prop s quote := by
  intro h
  apply escape_of_safe s quote
  intro c hc
  rcases h c hc with ⟨h1, h2, h3, hrest⟩
  exact encodeChar_of_safe quote c h1 h2 h3 (fun hq => (hrest hq).1) (fun hq => (hrest hq).2)

/-- With `quote = false`, only `&`, `<` and `>` change. -/
abbrev quote_false_preserves_prop (s : String) : Prop :=
  (∀ c, c ∈ s.data → c ≠ '&' ∧ c ≠ '<' ∧ c ≠ '>') → escape s false = s

theorem quote_false_preserves_thm (s : String) : quote_false_preserves_prop s := by
  intro h
  apply preserves_safe_thm s false
  intro c hc
  rcases h c hc with ⟨h1, h2, h3⟩
  exact ⟨h1, h2, h3, fun hq => nomatch hq⟩

/-- The Python `if quote` branch: quote-encoding is exactly two extra replacements. -/
abbrev quote_branch_prop (s : String) : Prop :=
  (escape s true).data =
    replaceChar '\'' aposR (replaceChar '"' quotR (escape s false).data)

theorem quote_branch_thm (s : String) : quote_branch_prop s := by
  simp [escape, quote_branch_prop, quote_branch_data] 

abbrev default_quote_prop (s : String) : Prop :=
  escape s = escape s true

theorem default_quote_thm (s : String) : default_quote_prop s := rfl

abbrev benchmark_prop (s : String) (quote : Bool) : Prop :=
  benchmarkEscape s quote = escape s quote

theorem benchmark_thm (s : String) (quote : Bool) : benchmark_prop s quote := rfl

/-! ## Post-condition -/

abbrev Post_prop (s : String) (quote : Bool) : Prop :=
  one_pass_prop s quote ∧
  no_raw_lt_prop s quote ∧
  no_raw_gt_prop s quote ∧
  no_raw_dquot_prop s quote ∧
  no_raw_apos_prop s quote ∧
  length_ge_prop s quote ∧
  length_exact_prop s quote ∧
  benchmark_prop s quote ∧
  default_quote_prop s ∧
  append_prop s s quote

theorem post_parts (s : String) (quote : Bool) : Post_prop s quote :=
  ⟨one_pass_thm s quote, no_raw_lt_thm s quote, no_raw_gt_thm s quote,
   no_raw_dquot_thm s quote, no_raw_apos_thm s quote, length_ge_thm s quote,
   length_exact_thm s quote, benchmark_thm s quote, default_quote_thm s,
   append_thm s s quote⟩

/-! ## Property-based tests -/

open Plausible Plausible.Decorations

/-- Alphabet that includes every character `html.escape` rewrites. -/
def htmlAlphabet : List Char := ['a', 'b', '&', '<', '>', '"', '\'', '/']

/-- All words of length exactly `n` over `htmlAlphabet`. -/
def enumLen : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 => (enumLen n).flatMap fun w => htmlAlphabet.map fun c => c :: w

def smallLists : List (List Char) :=
  enumLen 0 ++ enumLen 1 ++ enumLen 2

#eval Testable.check (∀ s : String, ∀ q : Bool, one_pass_prop s q)
#eval Testable.check (∀ q : Bool, empty_prop q)
#eval Testable.check (∀ q : Bool, amp_prop q)
#eval Testable.check (∀ q : Bool, lt_prop q)
#eval Testable.check (∀ q : Bool, gt_prop q)
#eval Testable.check (∀ q : Bool, double_quote_prop q)
#eval Testable.check (∀ q : Bool, single_quote_prop q)
#eval Testable.check (∀ q : Bool, order_prop q)
#eval Testable.check (∀ q : Bool, no_double_escape_prop q)
#eval Testable.check (∀ s t : String, ∀ q : Bool, append_prop s t q)
#eval Testable.check (∀ s : String, ∀ q : Bool, no_raw_lt_prop s q)
#eval Testable.check (∀ s : String, ∀ q : Bool, no_raw_gt_prop s q)
#eval Testable.check (∀ s : String, ∀ q : Bool, no_raw_dquot_prop s q)
#eval Testable.check (∀ s : String, ∀ q : Bool, no_raw_apos_prop s q)
#eval Testable.check (∀ s : String, ∀ q : Bool, length_ge_prop s q)
#eval Testable.check (∀ s : String, ∀ q : Bool, length_exact_prop s q)
#eval Testable.check (∀ c : Char, ∀ q : Bool, safe_char_prop c q)
#eval Testable.check (∀ s : String, ∀ q : Bool,
  (s.data.all (fun c => c != '&' && c != '<' && c != '>' &&
      (q == false || (c != '"' && c != '\''))) = true → escape s q = s))
#eval Testable.check (∀ s : String,
  (s.data.all (fun c => c != '&' && c != '<' && c != '>') = true → escape s false = s))
#eval Testable.check (∀ s : String, quote_branch_prop s)
#eval Testable.check (∀ s : String, default_quote_prop s)
#eval Testable.check (∀ s : String, ∀ q : Bool, benchmark_prop s q)
#eval Testable.check (∀ s : String, ∀ q : Bool, Post_prop s q)

/-- Exhaustive check on short strings that contain the HTML special characters. -/
example : smallLists.all (fun cs =>
    let s := String.mk cs
    [true, false].all fun q =>
      (escape s q).data == s.data.flatMap (encodeChar q) &&
      !(escape s q).data.elem '<' &&
      !(escape s q).data.elem '>' &&
      (q == false || (!(escape s q).data.elem '"' && !(escape s q).data.elem '\'')) &&
      decide (s.length ≤ (escape s q).length) &&
      (escape s q).length == (s.data.map (fun c => (encodeChar q c).length)).sum &&
      benchmarkEscape s q == escape s q &&
      escape s == escape s true &&
      escape (s ++ s) q == escape s q ++ escape s q) = true := by native_decide

example : smallLists.all (fun cs =>
    let s := String.mk cs
    !(s.data.all (fun c => c != '&' && c != '<' && c != '>')) || escape s false == s) = true := by
  native_decide

example : (htmlAlphabet ++ ['z', ' ', '0']).all (fun c =>
    [true, false].all fun q =>
      !(c != '&' && c != '<' && c != '>' && (q == false || (c != '"' && c != '\''))) ||
        escape (String.singleton c) q == String.singleton c) = true := by native_decide

/-! ## Correctness -/

theorem correctness_thm (s : String) (quote : Bool) (_h : Pre s quote) : Post_prop s quote :=
  post_parts s quote

/-! ## Imperative implementation -/

/-- One-pass builder. Mutable accumulator in `Id`, one character at a time. -/
def escapeImp (s : String) (quote : Bool := true) : String :=
  Id.run do
    let mut acc : List Char := []
    for c in s.data do
      acc := acc ++ encodeChar quote c
    return ⟨acc⟩

theorem escapeImp_foldl (s : String) (quote : Bool) :
    (escapeImp s quote).data = s.data.foldl (fun acc c => acc ++ encodeChar quote c) [] := by
  simp [escapeImp, bind_pure_comp, Id.run_pure, Id.run_bind, map_pure]

theorem foldl_append_init (f : Char → List Char) (init cs : List Char) :
    cs.foldl (fun acc x => acc ++ f x) init = init ++ cs.flatMap f := by
  induction cs generalizing init with
  | nil => simp
  | cons c cs ih => simp [ih, List.append_assoc]

/-! ## Imperative tests -/

example : escapeImp "<b>\"&'</b>" = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by native_decide
example : escapeImp "" = "" := by native_decide
example : escapeImp "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by native_decide
example : escapeImp "&<" = "&amp;&lt;" := by native_decide
example : check (fun s q => escapeImp s q) = true := by native_decide

#eval escapeImp "<b>\"&'</b>"
#eval escapeImp "<b>\"&'</b>" false
#eval escapeImp "&<"
#eval check (fun s q => escapeImp s q)

/-! ## Equivalence -/

abbrev equiv_prop (s : String) (quote : Bool) : Prop :=
  escape s quote = escapeImp s quote

theorem equiv_thm (s : String) (quote : Bool) : equiv_prop s quote := by
  apply String.ext
  simp only [escape, escapeData_eq_flatMap, escapeImp_foldl, foldl_append_init, List.nil_append,
    List.flatMap_def]

#eval Testable.check (∀ s : String, ∀ q : Bool, equiv_prop s q)

example : smallLists.all (fun cs =>
    [true, false].all fun q => escape (String.mk cs) q == escapeImp (String.mk cs) q) = true := by
  native_decide

end «20_html_escape»
