import Mathlib

/-!
# HTML escaping

A Unicode-character model of Python's `html.escape`.  The functional version
emits one entity per original character.  The mutable version performs the
five single-character replacement passes in Python's order, so generated
ampersands are not escaped again.  `Input α` separates strings from arbitrary
non-string objects (the payload type `α` is unrestricted); `benchmark_escape`
models the checked entry point and its TypeError.
-/

namespace HtmlEscape
deriving instance DecidableEq for Except

/-- Exact output contributed by one original character. -/
def escapeChar (quote : Bool) (c : Char) : List Char :=
  if c = '&' then "&amp;".toList
  else if c = '<' then "&lt;".toList
  else if c = '>' then "&gt;".toList
  else if quote && c == '"' then "&quot;".toList
  else if quote && c == '\'' then "&#x27;".toList
  else [c]

/-- Default quote handling agrees with Python's default `quote=True`. -/
def escape (s : String) (quote : Bool := true) : String :=
  String.mk (s.toList.flatMap (escapeChar quote))

/-- A single-character `str.replace` pass, replacing all original occurrences. -/
def replaceChar (s : String) (c : Char) (replacement : String) : String :=
  String.mk (s.toList.flatMap fun d =>
    if d = c then replacement.toList else [d])

/-- `nonString` can contain any Python object that is not a string. -/
inductive Input (α : Type)
  | string : String → Input α
  | nonString : α → Input α
  deriving Repr

/-- Executable version of Python's `isinstance(s, str)` check. -/
def pre_escape (v : Input α) : Bool :=
  match v with
  | .string _ => true
  | .nonString _ => false

inductive EscapeError
  | typeError (message : String)
  deriving DecidableEq, Repr

def benchmark_escape (v : Input α) (quote : Bool := true) : Except EscapeError String :=
  match v with
  | .string s => .ok (escape s quote)
  | .nonString _ => .error (.typeError "expected str object")

-- The four examples from the Python test suite.
example : escape "<b>\"&'</b>" = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by native_decide
example : escape "" = "" := by native_decide
example : escape "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by native_decide
example : escape "&<" = "&amp;&lt;" := by native_decide
example : benchmark_escape (Input.nonString (42 : Nat)) =
    .error (.typeError "expected str object") := by native_decide
-- The checked entry point is the candidate used by the Python test harness.
example : benchmark_escape (.string "<b>\"&'</b>" : Input Unit) =
    .ok "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by native_decide
example : benchmark_escape (.string "" : Input Unit) = .ok "" := by native_decide
example : benchmark_escape (.string "<b>\"&'</b>" : Input Unit) false =
    .ok "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by native_decide
example : benchmark_escape (.string "&<" : Input Unit) = .ok "&amp;&lt;" := by native_decide
-- Existing entities are ordinary input, not recognized as pre-escaped markup.
example : escape "&amp;" = "&amp;amp;" := by native_decide
example : escape "café 😀\n" = "café 😀\n" := by native_decide
#eval escape "<b>\"&'</b>"
#eval escape "<b>\"&'</b>" false
#eval benchmark_escape (Input.nonString (42 : Nat))

/-- The exact Python precondition: the object is a string. -/
def Pre (v : Input α) : Prop :=
  match v with
  | .string _ => True
  | .nonString _ => False

theorem pre_escape_iff (v : Input α) : Pre v ↔ pre_escape v = true := by
  cases v <;> simp [Pre, pre_escape]

/-- The original sequence of Python replacement passes. -/
def orderedPasses (s : String) (quote : Bool) : String :=
  let a := replaceChar s '&' "&amp;"
  let b := replaceChar a '<' "&lt;"
  let c := replaceChar b '>' "&gt;"
  if quote then replaceChar (replaceChar c '"' "&quot;") '\'' "&#x27;" else c

/-- Agreement with the source's ordered `str.replace` semantics. -/
def ordered_prop (s : String) (q : Bool) : Prop := escape s q = orderedPasses s q

private theorem replaceChar_append (s t : String) (c : Char) (r : String) :
    replaceChar (s ++ t) c r = replaceChar s c r ++ replaceChar t c r := by
  apply String.ext
  simp [replaceChar, List.flatMap_append]

private theorem orderedPasses_append (s t : String) (q : Bool) :
    orderedPasses (s ++ t) q = orderedPasses s q ++ orderedPasses t q := by
  cases q <;> simp [orderedPasses, replaceChar_append]

private theorem orderedPasses_char (c : Char) (q : Bool) :
    orderedPasses (String.singleton c) q = String.mk (escapeChar q c) := by
  by_cases ha : c = '&'
  · subst c; cases q <;> decide
  by_cases hl : c = '<'
  · subst c; cases q <;> decide
  by_cases hg : c = '>'
  · subst c; cases q <;> decide
  by_cases hd : c = '"'
  · subst c; cases q <;> decide
  by_cases hs : c = '\''
  · subst c; cases q <;> decide
  cases q <;>
    simp [orderedPasses, replaceChar, escapeChar, String.singleton,
      ha, hl, hg, hd, hs]

theorem ordered_thm (s : String) (q : Bool) : ordered_prop s q := by
  unfold ordered_prop escape
  symm
  cases s with
  | mk xs =>
    induction xs with
    | nil => cases q <;> rfl
    | cons c xs ih =>
      change orderedPasses (String.singleton c ++ String.mk xs) q = _
      rw [orderedPasses_append, orderedPasses_char, ih]
      rfl

/-- Escaping is a homomorphism for concatenation: boundaries do not matter. -/
def append_prop (s t : String) (q : Bool) : Prop :=
  escape (s ++ t) q = escape s q ++ escape t q

theorem append_thm (s t : String) (q : Bool) : append_prop s t q := by
  unfold append_prop
  apply String.ext
  simp [escape, List.flatMap_append]

/-- No raw HTML angle brackets remain, nor raw quotes when quotes are enabled.
Ampersands are intentionally not forbidden: they introduce the HTML entities. -/
def safe_prop (s : String) (q : Bool) : Prop :=
  '<' ∉ (escape s q).toList ∧ '>' ∉ (escape s q).toList ∧
  (q = true → '"' ∉ (escape s q).toList ∧ '\'' ∉ (escape s q).toList)

private theorem escapeChar_safe (c d : Char) (q : Bool) :
    d ∈ escapeChar q c →
    d ≠ '<' ∧ d ≠ '>' ∧ (q = true → d ≠ '"' ∧ d ≠ '\'') := by
  cases q <;>
    simp only [escapeChar, Bool.false_and, Bool.true_and, Bool.false_eq_true,
      beq_iff_eq, ite_false] <;>
    split_ifs <;> simp_all <;> aesop

theorem safe_thm (s : String) (q : Bool) : safe_prop s q := by
  have h (d : Char) (hd : d ∈ (escape s q).toList) :
      d ≠ '<' ∧ d ≠ '>' ∧ (q = true → d ≠ '"' ∧ d ≠ '\'') := by
    obtain ⟨c, _, hc⟩ := List.mem_flatMap.mp hd
    exact escapeChar_safe c d q hc
  refine ⟨?_, ?_, ?_⟩
  · intro hd; exact (h '<' hd).1 rfl
  · intro hd; exact (h '>' hd).2.1 rfl
  · intro hq
    exact ⟨fun hd => (h '"' hd).2.2 hq |>.1 rfl,
      fun hd => (h '\'' hd).2.2 hq |>.2 rfl⟩

/-- An executable test that a source character needs no escaping. -/
def ordinary (q : Bool) (c : Char) : Bool :=
  !(c == '&' || c == '<' || c == '>' || (q && (c == '"' || c == '\'')))

/-- All safe input, including arbitrary Unicode characters, is left unchanged. -/
def unchanged_prop (s : String) (q : Bool) : Prop :=
  s.toList.all (ordinary q) = true → escape s q = s

private theorem ordinary_char (q : Bool) (c : Char) (h : ordinary q c = true) :
    escapeChar q c = [c] := by
  cases q <;> simp_all [ordinary, escapeChar, beq_iff_eq]

theorem unchanged_thm (s : String) (q : Bool) : unchanged_prop s q := by
  intro h
  have he (xs : List Char) : xs.all (ordinary q) = true →
      xs.flatMap (escapeChar q) = xs := by
    induction xs with
    | nil => intro _; rfl
    | cons c cs ih =>
      simp only [List.all_cons, Bool.and_eq_true]
      rintro ⟨hc, hcs⟩
      rw [List.flatMap_cons, ordinary_char q c hc, ih hcs]
      rfl
  exact congrArg String.mk (he s.toList h)

/-- Extra characters introduced for each original character. -/
def extra (q : Bool) (c : Char) : Nat :=
  if c = '&' then 4
  else if c = '<' then 3
  else if c = '>' then 3
  else if q && c == '"' then 5
  else if q && c == '\'' then 5
  else 0

/-- Exact length, not merely a lower bound; length counts Unicode characters. -/
def length_prop (s : String) (q : Bool) : Prop :=
  (escape s q).length = s.length + (s.toList.map (extra q)).sum

private theorem escapeChar_length (q : Bool) (c : Char) :
    (escapeChar q c).length = 1 + extra q c := by
  unfold escapeChar extra
  split_ifs <;> rfl

theorem length_thm (s : String) (q : Bool) : length_prop s q := by
  change (s.toList.flatMap (escapeChar q)).length =
    s.toList.length + (s.toList.map (extra q)).sum
  induction s.toList with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.length_append, escapeChar_length,
      List.length_cons, List.map_cons, List.sum_cons]
    omega

/-- Disabling quote escaping preserves the number of each kind of quote. -/
def quotes_prop (s : String) : Prop :=
  (escape s false).toList.count '"' = s.toList.count '"' ∧
  (escape s false).toList.count '\'' = s.toList.count '\''

private theorem escapeChar_quote_count (c d : Char) (hd : d = '"' ∨ d = '\'') :
    (escapeChar false c).count d = [c].count d := by
  rcases hd with rfl | rfl <;>
    simp only [escapeChar, Bool.false_and, Bool.false_eq_true, ite_false] <;>
    split_ifs <;> simp_all

theorem quotes_thm (s : String) : quotes_prop s := by
  have h (d : Char) (hd : d = '"' ∨ d = '\'') :
      (s.toList.flatMap (escapeChar false)).count d = s.toList.count d := by
    induction s.toList with
    | nil => rfl
    | cons c cs ih =>
      rw [List.flatMap_cons, List.count_append, escapeChar_quote_count c d hd, ih]
      simp [List.count_cons, Nat.add_comm]
  exact ⟨h '"' (Or.inl rfl), h '\'' (Or.inr rfl)⟩

/-- Exactly the empty input has empty output. -/
def empty_prop (s : String) (q : Bool) : Prop := escape s q = "" ↔ s = ""

theorem empty_thm (s : String) (q : Bool) : empty_prop s q := by
  constructor
  · intro h
    have hl := length_thm s q
    change (escape s q).length = s.toList.length + _ at hl
    rw [h] at hl
    have hz : s.toList.length = 0 := by change 0 = _ at hl; omega
    have hn := List.length_eq_zero_iff.mp hz
    exact congrArg String.mk hn
  · intro h; subst s; rfl

/-- Both successful return values and the exact TypeError on every non-string. -/
def result_prop (v : Input α) (q : Bool) : Prop :=
  match v with
  | .string s => benchmark_escape v q = .ok (escape s q)
  | .nonString _ => benchmark_escape v q = .error (.typeError "expected str object")

theorem result_thm (v : Input α) (q : Bool) : result_prop v q := by
  cases v <;> rfl

/-- Postcondition of the checked entry point, including its exceptional behavior. -/
def Post_prop (v : Input α) (q : Bool) : Prop :=
  result_prop v q ∧
  match v with
  | .string s => ordered_prop s q ∧ safe_prop s q ∧ unchanged_prop s q ∧
      length_prop s q ∧ quotes_prop s ∧ empty_prop s q
  | .nonString _ => True

/-! ## Bounded property-based tests

These are exhaustive small-input tests, not proofs of the universal claims.
The alphabet includes every escaped character, entity punctuation, ordinary
characters, whitespace, NUL, and non-ASCII Unicode.  `words n` enumerates all
words of length at most `n`, including the empty word.  Every string property
is checked with both flag values whenever it has a flag parameter.  The
checked-entry-point tests include non-string objects as well as strings.
-/

-- These instances compute the propositions themselves, so the PBTs cannot
-- accidentally test a weaker Boolean surrogate of the stated properties.
instance (s : String) (q : Bool) : Decidable (ordered_prop s q) := by
  unfold ordered_prop; infer_instance
instance (s t : String) (q : Bool) : Decidable (append_prop s t q) := by
  unfold append_prop; infer_instance
instance (s : String) (q : Bool) : Decidable (safe_prop s q) := by
  unfold safe_prop; infer_instance
instance (s : String) (q : Bool) : Decidable (unchanged_prop s q) := by
  unfold unchanged_prop; infer_instance
instance (s : String) (q : Bool) : Decidable (length_prop s q) := by
  unfold length_prop; infer_instance
instance (s : String) : Decidable (quotes_prop s) := by
  unfold quotes_prop; infer_instance
instance (s : String) (q : Bool) : Decidable (empty_prop s q) := by
  unfold empty_prop; infer_instance
instance (v : Input α) (q : Bool) : Decidable (result_prop v q) := by
  cases v <;> unfold result_prop <;> infer_instance
instance (v : Input α) (q : Bool) : Decidable (Post_prop v q) := by
  cases v <;> unfold Post_prop <;> infer_instance

private def alphabet : List Char :=
  ['&', '<', '>', '"', '\'', 'a', ';', ' ', '\n', Char.ofNat 0, 'é', '😀']

private def words : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 => [] :: alphabet.flatMap (fun c => (words n).map (c :: ·))

private def samples : List String := (words 3).map String.mk
private def shortSamples : List String := (words 2).map String.mk
private def flags : List Bool := [false, true]
private def inputSamples : List (Input Nat) :=
  samples.map Input.string ++ (List.range 50).map Input.nonString

-- PBT: ordered_prop (including sequences that would expose double escaping).
example : samples.all (fun s => flags.all (fun q => decide (ordered_prop s q))) = true := by
  native_decide

-- PBT: append_prop, all pairs of words of length at most two.
example : shortSamples.all (fun s => shortSamples.all (fun t =>
    flags.all (fun q => decide (append_prop s t q)))) = true := by
  native_decide

-- PBT: safe_prop.
example : samples.all (fun s => flags.all (fun q => decide (safe_prop s q))) = true := by
  native_decide

-- PBT: unchanged_prop. Its decidable implication restricts to ordinary input.
-- The exhaustive enumeration includes many admissible all-ordinary strings.
example : samples.all (fun s => flags.all (fun q => decide (unchanged_prop s q))) = true := by
  native_decide

-- PBT: length_prop, the exact sum of per-character expansion lengths.
example : samples.all (fun s => flags.all (fun q => decide (length_prop s q))) = true := by
  native_decide

-- PBT: quotes_prop (quote=False).
example : samples.all (fun s => decide (quotes_prop s)) = true := by
  native_decide

-- PBT: empty_prop.
example : samples.all (fun s => flags.all (fun q => decide (empty_prop s q))) = true := by
  native_decide

-- PBT: result_prop, both successful returns and TypeError outcomes.
example : inputSamples.all (fun v => flags.all (fun q => decide (result_prop v q))) = true := by
  native_decide

-- PBT: the full Post_prop, also checking the exceptional branch without Pre.
example : inputSamples.all (fun v => flags.all (fun q => decide (Post_prop v q))) = true := by
  native_decide

-- Executable precondition checks on many strings and non-string objects.
example : samples.all (fun s => pre_escape (Input.string s : Input Nat)) = true := by
  native_decide
example : (List.range 50).all (fun n => !pre_escape (Input.nonString n)) = true := by
  native_decide

#eval (samples.length, shortSamples.length, inputSamples.length)
#eval inputSamples.all (fun v => flags.all (fun q => decide (Post_prop v q)))


theorem correctness (v : Input α) (q : Bool) : Pre v → Post_prop v q := by
  intro hp
  cases v with
  | string s =>
    exact ⟨result_thm (.string s) q, ordered_thm s q, safe_thm s q,
      unchanged_thm s q, length_thm s q, quotes_thm s, empty_thm s q⟩
  | nonString a => exact False.elim hp


/-- The imperative translation preserves the replacement order in the source. -/
def escapeImperative (s : String) (quote : Bool := true) : String := Id.run do
  let mut result := s
  result := replaceChar result '&' "&amp;"
  result := replaceChar result '<' "&lt;"
  result := replaceChar result '>' "&gt;"
  if quote then
    result := replaceChar result '"' "&quot;"
    result := replaceChar result '\'' "&#x27;"
  return result

/-- Checked imperative entry point, with the same unrestricted input model. -/
def benchmarkEscapeImperative (v : Input α) (quote : Bool := true) :
    Except EscapeError String :=
  match v with
  | .string s => .ok (escapeImperative s quote)
  | .nonString _ => .error (.typeError "expected str object")

example : escapeImperative "<b>\"&'</b>" = "&lt;b&gt;&quot;&amp;&#x27;&lt;/b&gt;" := by native_decide
example : escapeImperative "" = "" := by native_decide
example : escapeImperative "<b>\"&'</b>" false = "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by native_decide
example : escapeImperative "&<" = "&amp;&lt;" := by native_decide
#eval escapeImperative "<b>\"&'</b>"

example : benchmarkEscapeImperative (.string "<b>\"&'</b>" : Input Unit) false =
    .ok "&lt;b&gt;\"&amp;'&lt;/b&gt;" := by native_decide
example : benchmarkEscapeImperative (.nonString (42 : Nat)) =
    .error (.typeError "expected str object") := by native_decide

-- Bounded differential tests of both complete implementations.
example : samples.all (fun s => flags.all (fun q =>
    escape s q == escapeImperative s q)) = true := by native_decide
example : inputSamples.all (fun v => flags.all (fun q =>
    decide (benchmark_escape v q = benchmarkEscapeImperative v q))) = true := by native_decide
#eval escapeImperative "<b>\"&'</b>" false
#eval benchmarkEscapeImperative (.nonString (42 : Nat))

/-- For every input and both flag values, the functional algorithm equals
Python's mutable, ordered-replacement algorithm. -/
theorem equivalence (s : String) (q : Bool) : escape s q = escapeImperative s q := by
  have h : escape s q = orderedPasses s q := ordered_thm s q
  rw [h]
  cases q <;> rfl

/-- Entry-point equivalence includes rejection of every non-string object. -/
theorem benchmark_equivalence (v : Input α) (q : Bool) :
    benchmark_escape v q = benchmarkEscapeImperative v q := by
  cases v with
  | string s => simp only [benchmark_escape, benchmarkEscapeImperative, equivalence]
  | nonString _ => rfl

end HtmlEscape
