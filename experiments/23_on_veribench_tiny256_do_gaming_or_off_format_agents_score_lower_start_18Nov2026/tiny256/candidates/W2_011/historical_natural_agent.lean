import Mathlib
namespace Agent

/-!
# Python `shlex.join`

An ASCII-accurate model of `shlex.quote` and `shlex.join`. The typed core accepts
arbitrary Unicode strings. `PyValue` also models dynamic calls: `other` stands
for *any* Python value which is neither a string nor a list (including numbers,
None, dictionaries, etc.). Lists may be heterogeneous or nested. Such inputs
are rejected unless every element is a string. Errors retain Python's message.

Single quotes are escaped by closing the single-quoted region, emitting a
single quote inside double quotes, and reopening the single-quoted region.
The proofs are kernel checked; `native_decide` is used only for executable tests.
-/

namespace ShlexJoin

inductive PyValue where
  | str : String → PyValue
  | list : List PyValue → PyValue
  | other : String → PyValue
  deriving Repr

inductive JoinError where
  | typeError : String → JoinError
  deriving Repr, DecidableEq

deriving instance DecidableEq for Except

instance : BEq (Except JoinError String) := ⟨fun a b => decide (a = b)⟩

/-- ASCII letters, digits, underscore and @ % + = : , . / and - only. -/
def safeChar (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') ||
  ('0' ≤ c && c ≤ '9') || ("_@%+=:,./-".toList.contains c)

def safeString (s : String) : Bool := s.toList.all safeChar

/-- The replacement of one character in a single-quoted shell word. -/
def escapeChar (c : Char) : List Char :=
  if c = '\'' then "'\"'\"'".toList else [c]

def escapeQuotes (s : String) : String :=
  String.mk (s.toList.flatMap escapeChar)

def quote (s : String) : String :=
  if s = "" then "''"
  else if safeString s then s
  else "'" ++ escapeQuotes s ++ "'"

/-- Interpose exactly one ASCII space, with no leading or trailing separator. -/
def join : List String → String
  | [] => ""
  | s :: ss => quote s ++ match ss with
    | [] => ""
    | _ :: _ => " " ++ join ss

def readStrings : List PyValue → Option (List String)
  | [] => some []
  | .str s :: rest => (readStrings rest).map (s :: ·)
  | _ :: _ => none

def asStrings : PyValue → Option (List String)
  | .list xs => readStrings xs
  | _ => none

/-- Executable translation of `pre_join`. -/
def preJoin (v : PyValue) : Bool := (asStrings v).isSome

def input (xs : List String) : PyValue := .list (xs.map PyValue.str)

def benchmarkJoin (v : PyValue) : Except JoinError String :=
  match asStrings v with
  | some xs => .ok (join xs)
  | none => .error (.typeError "expected list of strings")

-- Fixed examples from the Python test suite, including both error cases.
example : benchmarkJoin (input ["ls", "-l"]) = .ok "ls -l" := by native_decide
example : benchmarkJoin (input ["echo", "hello world"]) =
    .ok "echo 'hello world'" := by native_decide
example : benchmarkJoin (input ["cp", "", "dest"]) = .ok "cp '' dest" := by native_decide
example : benchmarkJoin (input []) = .ok "" := by native_decide
example : benchmarkJoin (input ["grep", "foo'bar"]) =
    .ok "grep 'foo'\"'\"'bar'" := by native_decide
example : benchmarkJoin (.str "not a list") =
    .error (.typeError "expected list of strings") := by native_decide
example : benchmarkJoin (.list [.str "ls", .other "123"]) =
    .error (.typeError "expected list of strings") := by native_decide
example : benchmarkJoin (.list [.list []]) =
    .error (.typeError "expected list of strings") := by native_decide
example : quote "é" = "'é'" := by native_decide
example : quote "a\nb" = "'a\nb'" := by native_decide
example : quote "'" = "''\"'\"''" := by native_decide
example : quote "_@%+=:,./-AZaz09" = "_@%+=:,./-AZaz09" := by native_decide
#eval benchmarkJoin (input ["grep", "foo'bar"])
#eval benchmarkJoin (.str "not a list")

/-- The Python precondition: a list, all of whose elements are strings. -/
def Pre (v : PyValue) : Prop := ∃ xs : List String, v = input xs

/-- The complete three-way behavior of quote. -/
def quote_cases_prop (s : String) : Prop :=
  (s = "" → quote s = "''") ∧
  (s ≠ "" → safeString s = true → quote s = s) ∧
  (s ≠ "" → safeString s = false → quote s = "'" ++ escapeQuotes s ++ "'")

/-- Every apostrophe is replaced; other characters are preserved, in order. -/
def escape_prop (s : String) : Prop :=
  (escapeQuotes s).toList = s.toList.flatMap
    (fun c => if c = '\'' then ['\'', '"', '\'', '"', '\''] else [c])

/-- The list operation is precisely space-intercalation of independently quoted words. -/
def join_spec_prop (xs : List String) : Prop :=
  join xs = String.intercalate " " (xs.map quote)

/-- Empty lists emit nothing and singleton lists emit just their quoted word. -/
def boundary_prop (s : String) : Prop :=
  join [] = "" ∧ join [s] = quote s

/-- Concatenating argument lists introduces a separator iff both are nonempty. -/
def append_prop (xs ys : List String) : Prop :=
  join (xs ++ ys) =
    if xs = [] then join ys else if ys = [] then join xs
    else join xs ++ " " ++ join ys

/-- Lists of nonempty, entirely safe words need no escaping. -/
def safe_join_prop (xs : List String) : Prop :=
  (∀ s ∈ xs, s ≠ "" ∧ safeString s = true) →
    join xs = String.intercalate " " xs

/-- A dynamic call succeeds exactly with the specified output on valid inputs. -/
def accepted_prop (xs : List String) : Prop :=
  benchmarkJoin (input xs) = .ok (String.intercalate " " (xs.map quote))

/-- Every inadmissible value is rejected with the exact TypeError message. -/
def rejected_prop (v : PyValue) : Prop :=
  ¬ Pre v → benchmarkJoin v = .error (.typeError "expected list of strings")

theorem quote_cases_thm (s : String) : quote_cases_prop s := by
  unfold quote_cases_prop
  constructor
  · intro h; simp [quote, h]
  constructor
  · intro hn hs; simp [quote, hn, hs]
  · intro hn hs; simp [quote, hn, hs]

theorem escape_thm (s : String) : escape_prop s := by
  rfl

theorem intercalate_go_thm (sep acc : String) (xs : List String) :
    String.intercalate.go acc sep xs =
      acc ++ (xs.foldr (fun s tail => sep ++ s ++ tail) "") := by
  induction xs generalizing acc with
  | nil => simp [String.intercalate.go]
  | cons s ss ih => simp [String.intercalate.go, ih, String.append_assoc]

theorem join_tail_thm (xs : List String) :
    xs.foldr (fun s tail => " " ++ quote s ++ tail) "" =
      match xs with
      | [] => ""
      | _ :: _ => " " ++ join xs := by
  induction xs with
  | nil => rfl
  | cons s ss ih => cases ss <;> simp_all [join, String.append_assoc]

theorem join_spec_thm (xs : List String) : join_spec_prop xs := by
  unfold join_spec_prop
  cases xs with
  | nil => rfl
  | cons s ss =>
    simp only [List.map_cons, String.intercalate, intercalate_go_thm,
      List.foldr_map, join_tail_thm]
    rfl

theorem boundary_thm (s : String) : boundary_prop s := by
  simp [boundary_prop, join]

theorem append_thm (xs ys : List String) : append_prop xs ys := by
  unfold append_prop
  induction xs with
  | nil => simp
  | cons s ss ih =>
    cases ys with
    | nil => simp
    | cons t ts =>
      cases ss with
      | nil => simp [join, String.append_assoc]
      | cons u us => simp_all [join, String.append_assoc]

theorem safe_join_thm (xs : List String) : safe_join_prop xs := by
  intro h
  have hm : xs.map quote = xs := by
    conv_rhs => rw [← List.map_id xs]
    apply List.map_congr_left
    intro s hs
    exact ((quote_cases_thm s).2.1 (h s hs).1 (h s hs).2)
  exact (join_spec_thm xs).trans (congrArg (String.intercalate " ") hm)

@[simp] theorem readStrings_input_thm (xs : List String) :
    readStrings (xs.map PyValue.str) = some xs := by
  induction xs with
  | nil => rfl
  | cons s ss ih => simp [readStrings, ih]

theorem readStrings_exact_thm (vs : List PyValue) (xs : List String) :
    readStrings vs = some xs ↔ vs = xs.map PyValue.str := by
  induction vs generalizing xs with
  | nil => cases xs <;> simp [readStrings]
  | cons v vs ih =>
    cases v with
    | str s =>
      cases xs with
      | nil => simp [readStrings]
      | cons t ts =>
        simp only [readStrings, List.map_cons, List.cons.injEq, PyValue.str.injEq]
        cases hr : readStrings vs with
        | none => simp_all
        | some us => simp_all
    | list zs => cases xs <;> simp [readStrings]
    | other tag => cases xs <;> simp [readStrings]

theorem asStrings_exact_thm (v : PyValue) (xs : List String) :
    asStrings v = some xs ↔ v = input xs := by
  cases v <;> simp [asStrings, input, readStrings_exact_thm]

theorem pre_iff_thm (v : PyValue) :
    Pre v ↔ preJoin v = true := by
  unfold Pre preJoin
  simp only [← asStrings_exact_thm]
  cases asStrings v <;> simp

theorem accepted_thm (xs : List String) : accepted_prop xs := by
  simpa [accepted_prop, benchmarkJoin, input, asStrings] using
    congrArg (Except.ok (ε := JoinError)) (join_spec_thm xs)

theorem rejected_thm (v : PyValue) : rejected_prop v := by
  intro h
  have hn : asStrings v = none := by
    cases hv : asStrings v with
    | none => rfl
    | some xs => exact False.elim (h ⟨xs, (asStrings_exact_thm v xs).mp hv⟩)
  simp [benchmarkJoin, hn]

/-- Exact length in Unicode characters: each apostrophe adds four characters,
and unsafe words receive two enclosing quotes. -/
def quote_length_prop (s : String) : Prop :=
  (quote s).length =
    if s = "" then 2 else if safeString s then s.length
    else s.length + 4 * s.toList.count '\'' + 2

/-- An empty argument is still a shell word, namely two quote characters. -/
def quote_nonempty_prop (s : String) : Prop := quote s ≠ ""

/-- No nonempty list of arguments can disappear into the empty command. -/
def join_empty_prop (xs : List String) : Prop := join xs = "" ↔ xs = []

theorem escape_length_thm (cs : List Char) :
    (cs.flatMap escapeChar).length = cs.length + 4 * cs.count '\'' := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    by_cases hc : c = '\''
    · subst c
      simp [escapeChar, ih]
      omega
    · simp [escapeChar, hc, ih]
      omega

theorem quote_length_thm (s : String) : quote_length_prop s := by
  unfold quote_length_prop quote
  split_ifs with he hs
  · rfl
  · rfl
  · simp only [String.length_append]
    change 1 + (s.toList.flatMap escapeChar).length + 1 =
      s.toList.length + 4 * s.toList.count '\'' + 2
    rw [escape_length_thm]
    omega

theorem length_zero_thm (s : String) : s.length = 0 ↔ s = "" := by
  cases s
  simp [String.length, String.ext_iff]

theorem append_empty_iff_thm (s t : String) :
    s ++ t = "" ↔ s = "" ∧ t = "" := by
  cases s; cases t
  simp [String.ext_iff]

theorem quote_nonempty_thm (s : String) : quote_nonempty_prop s := by
  have hpos : 0 < (quote s).length := by
    rw [quote_length_thm s]
    split_ifs with he hs
    · omega
    · have hn : s.length ≠ 0 := fun h => he ((length_zero_thm s).mp h)
      omega
    · omega
  intro h
  simp [h] at hpos

theorem join_empty_thm (xs : List String) : join_empty_prop xs := by
  unfold join_empty_prop
  cases xs with
  | nil => simp [join]
  | cons s ss =>
    constructor
    · intro h
      have hq : quote s = "" := ((append_empty_iff_thm _ _).mp h).1
      exact False.elim (quote_nonempty_thm s hq)
    · intro h; cases h

/-- Total contract: exact output and quoting laws on lists of strings, and the
exact TypeError on every other dynamic value. In particular empty arguments
are retained and Unicode is not treated as ASCII-safe. -/
def Post_prop (v : PyValue) (result : Except JoinError String) : Prop :=
  (∀ xs, v = input xs →
    result = .ok (String.intercalate " " (xs.map quote)) ∧
    join_spec_prop xs ∧ join_empty_prop xs ∧ safe_join_prop xs ∧
    (∀ s ∈ xs, quote_cases_prop s ∧ escape_prop s ∧ boundary_prop s ∧
      quote_length_prop s ∧ quote_nonempty_prop s)) ∧
  (¬ Pre v → result = .error (.typeError "expected list of strings"))

/-! ## Bounded property-based tests
The corpus enumerates all character strings of length at most two over an
alphabet containing each interesting class, then all argument lists of length
at most two. These are executable checks, not substitutes for the proofs.
-/

def alphabet : List Char :=
  ['a', 'Z', '0', '_', '@', '-', ' ', '\t', '\n', '\'', '"', '\\', '$', ';', 'é', '中']

def strings : List String :=
  [""] ++ alphabet.map (fun c => String.singleton c) ++
    alphabet.flatMap (fun c => alphabet.map (fun d => String.mk [c, d]))

def argumentLists : List (List String) :=
  [[]] ++ strings.map (fun s => [s]) ++
    strings.flatMap (fun s => strings.map (fun t => [s, t]))

def appendSamples : List (List String) :=
  let words := ["", "a", " ", "'", "\"", "é", "a b", "foo'bar"]
  [[]] ++ words.map (fun s => [s]) ++
    words.flatMap (fun s => words.map (fun t => [s, t])) ++
    [["a", "b", "c"], ["", "'", "é", "a b"]]

/-- Generated counter-domain: nonlists, bad heads/tails, and nested lists. -/
def invalidInputs : List PyValue :=
  strings.map PyValue.str ++
    [.other "123", .other "None", .other "True", .other "{}"] ++
    appendSamples.flatMap (fun xs =>
      [.list (.other "123" :: xs.map PyValue.str),
       .list (xs.map PyValue.str ++ [.other "123"]),
       .list (.list [] :: xs.map PyValue.str),
       .list (.str "ok" :: .list [] :: xs.map PyValue.str)])

def dynamicInputs : List PyValue := argumentLists.map input ++ invalidInputs

def quoteCasesCheck (s : String) : Bool :=
  ((s != "") || quote s == "''") &&
  ((s == "" || !safeString s) || quote s == s) &&
  ((s == "" || safeString s) || quote s == "'" ++ escapeQuotes s ++ "'")

def escapeCheck (s : String) : Bool :=
  (escapeQuotes s).toList == s.toList.flatMap
    (fun c => if c = '\'' then ['\'', '"', '\'', '"', '\''] else [c])

def boundaryCheck (s : String) : Bool :=
  join [] == "" && join [s] == quote s

def joinSpecCheck (xs : List String) : Bool :=
  join xs == String.intercalate " " (xs.map quote)

def safeJoinCheck (xs : List String) : Bool :=
  !(xs.all (fun s => s != "" && safeString s)) ||
    join xs == String.intercalate " " xs

def appendCheck (xs ys : List String) : Bool :=
  join (xs ++ ys) ==
    (if xs.isEmpty then join ys else if ys.isEmpty then join xs
      else join xs ++ " " ++ join ys)

def quoteLengthCheck (s : String) : Bool :=
  (quote s).length ==
    (if s = "" then 2 else if safeString s then s.length
      else s.length + 4 * s.toList.count '\'' + 2)

def joinEmptyCheck (xs : List String) : Bool :=
  (join xs == "") == xs.isEmpty

def postCheck (v : PyValue) : Bool :=
  match asStrings v with
  | none => benchmarkJoin v == .error (.typeError "expected list of strings")
  | some xs =>
    benchmarkJoin v == .ok (String.intercalate " " (xs.map quote)) &&
    joinSpecCheck xs && joinEmptyCheck xs && safeJoinCheck xs &&
    xs.all (fun s => quoteCasesCheck s && escapeCheck s && boundaryCheck s &&
      quoteLengthCheck s && quote s != "")

-- PBT for quote_cases_prop (all three branches).
example : strings.all quoteCasesCheck = true := by native_decide
-- PBT for escape_prop (all positions and repeated apostrophes).
example : strings.all escapeCheck = true := by native_decide
-- PBT for boundary_prop.
example : strings.all boundaryCheck = true := by native_decide
-- PBT for join_spec_prop.
example : argumentLists.all joinSpecCheck = true := by native_decide
-- PBT for append_prop: exhaustive pairs of short argument lists.
example : appendSamples.all (fun xs =>
    appendSamples.all (appendCheck xs)) = true := by native_decide
-- PBT for safe_join_prop; includes many lists meeting the safe-word antecedent.
example : argumentLists.all safeJoinCheck = true := by native_decide
-- PBT for accepted_prop.
example : argumentLists.all (fun xs =>
    benchmarkJoin (input xs) == .ok (String.intercalate " " (xs.map quote))) = true := by
  native_decide
-- PBT for rejected_prop; preJoin is equivalent to Pre by pre_iff_thm.
example : dynamicInputs.all (fun v => preJoin v ||
    benchmarkJoin v == .error (.typeError "expected list of strings")) = true := by
  native_decide
-- Nonvacuous rejection PBT: every generated malformed value fails Pre.
example : invalidInputs.all (fun v => !preJoin v &&
    benchmarkJoin v == .error (.typeError "expected list of strings")) = true := by
  native_decide
-- PBT for quote_length_prop.
example : strings.all quoteLengthCheck = true := by native_decide
-- PBT for quote_nonempty_prop.
example : strings.all (fun s => quote s != "") = true := by native_decide
-- PBT for join_empty_prop.
example : argumentLists.all joinEmptyCheck = true := by native_decide
-- PBT for the entire Post_prop (both valid and invalid branches).
example : dynamicInputs.all postCheck = true := by native_decide
#eval (strings.length, argumentLists.length, invalidInputs.length, dynamicInputs.all postCheck)

theorem total_correctness_thm (v : PyValue) : Post_prop v (benchmarkJoin v) := by
  constructor
  · intro xs hx
    subst v
    exact ⟨accepted_thm xs, join_spec_thm xs, join_empty_thm xs, safe_join_thm xs,
      fun s _ => ⟨quote_cases_thm s, escape_thm s, boundary_thm s,
        quote_length_thm s, quote_nonempty_thm s⟩⟩
  · exact rejected_thm v

/-- In particular, the requested precondition implies the complete postcondition. -/
theorem correctness_thm (v : PyValue) : Pre v → Post_prop v (benchmarkJoin v) := by
  intro _
  exact total_correctness_thm v

/-! ## Imperative translation
All scans are explicit `Id.run` loops with mutable accumulators. A first-word
flag inserts one separator between arguments, including empty source strings.
Validation has a sticky failure state.
-/

def safeStringImperative (s : String) : Bool := Id.run do
  let mut safe := true
  for c in s.toList do
    safe := safe && safeChar c
  return safe

def escapeQuotesImperative (s : String) : String := Id.run do
  let mut acc : List Char := []
  for c in s.toList do
    acc := acc ++ escapeChar c
  return String.mk acc

def quoteImperative (s : String) : String := Id.run do
  if s = "" then return "''"
  if safeStringImperative s then return s
  let mut result := "'"
  result := result ++ escapeQuotesImperative s
  result := result ++ "'"
  return result

/-- Output accumulated so far and a flag meaning that no word has been seen. -/
def joinStep (state : String × Bool) (s : String) : String × Bool :=
  (state.1 ++ (if state.2 then "" else " ") ++ quoteImperative s, false)

def joinImperative (xs : List String) : String := Id.run do
  let mut state : String × Bool := ("", true)
  for s in xs do
    state := joinStep state s
  return state.1

def readStep (acc : Option (List String)) (v : PyValue) : Option (List String) :=
  match acc, v with
  | some xs, .str s => some (xs ++ [s])
  | _, _ => none

def readStringsImperative (vs : List PyValue) : Option (List String) := Id.run do
  let mut acc : Option (List String) := some []
  for v in vs do
    acc := readStep acc v
  return acc

def asStringsImperative (v : PyValue) : Option (List String) :=
  match v with
  | .list vs => readStringsImperative vs
  | _ => none

def benchmarkJoinImperative (v : PyValue) : Except JoinError String := Id.run do
  match asStringsImperative v with
  | none => return .error (.typeError "expected list of strings")
  | some xs => return .ok (joinImperative xs)

-- Imperative tests: all the source examples and errors.
example : benchmarkJoinImperative (input ["ls", "-l"]) = .ok "ls -l" := by native_decide
example : benchmarkJoinImperative (input ["echo", "hello world"]) =
    .ok "echo 'hello world'" := by native_decide
example : benchmarkJoinImperative (input ["cp", "", "dest"]) =
    .ok "cp '' dest" := by native_decide
example : benchmarkJoinImperative (input []) = .ok "" := by native_decide
example : benchmarkJoinImperative (input ["grep", "foo'bar"]) =
    .ok "grep 'foo'\"'\"'bar'" := by native_decide
example : benchmarkJoinImperative (.str "not a list") =
    .error (.typeError "expected list of strings") := by native_decide
example : benchmarkJoinImperative (.list [.str "ls", .other "123"]) =
    .error (.typeError "expected list of strings") := by native_decide
example : benchmarkJoinImperative (.list [.other "123", .str "ls"]) =
    .error (.typeError "expected list of strings") := by native_decide
example : benchmarkJoinImperative (input ["", "", "é", "a\nb"]) =
    .ok "'' '' 'é' 'a\nb'" := by native_decide
example : dynamicInputs.all (fun v =>
    benchmarkJoin v == benchmarkJoinImperative v) = true := by native_decide
#eval benchmarkJoinImperative (input ["grep", "foo'bar"])

/-! ## Loop invariants and equivalence -/

theorem safe_fold_thm (cs : List Char) (acc : Bool) :
    cs.foldl (fun b c => b && safeChar c) acc = (acc && cs.all safeChar) := by
  induction cs generalizing acc with
  | nil => simp
  | cons c cs ih => simp [ih, Bool.and_assoc]

theorem safeStringImperative_eq_thm (s : String) :
    safeStringImperative s = safeString s := by
  simp [safeStringImperative, safe_fold_thm, safeString]

theorem escape_fold_thm (cs acc : List Char) :
    cs.foldl (fun out c => out ++ escapeChar c) acc = acc ++ cs.flatMap escapeChar := by
  induction cs generalizing acc with
  | nil => simp
  | cons c cs ih => simp [ih, List.append_assoc]

theorem escapeQuotesImperative_eq_thm (s : String) :
    escapeQuotesImperative s = escapeQuotes s := by
  have norm : escapeQuotesImperative s =
      String.mk (s.toList.foldl (fun acc c => acc ++ escapeChar c) []) := by
    simp [escapeQuotesImperative]
  rw [norm, escape_fold_thm]
  rfl

theorem quoteImperative_eq_thm (s : String) : quoteImperative s = quote s := by
  by_cases he : s = "" <;> by_cases hs : safeString s = true <;>
    simp [quoteImperative, quote, safeStringImperative_eq_thm,
      escapeQuotesImperative_eq_thm, he, hs]

theorem join_fold_thm (xs : List String) (acc : String) :
    xs.foldl joinStep (acc, false) =
      (acc ++ xs.foldr (fun s tail => " " ++ quote s ++ tail) "", false) := by
  induction xs generalizing acc with
  | nil => simp
  | cons s ss ih =>
    simp [List.foldl_cons, joinStep, quoteImperative_eq_thm, ih, String.append_assoc]

theorem joinImperative_eq_thm (xs : List String) : joinImperative xs = join xs := by
  have norm : joinImperative xs = (xs.foldl joinStep ("", true)).1 := by
    simp [joinImperative]
  rw [norm]
  cases xs with
  | nil => rfl
  | cons s ss =>
    have hs : joinStep ("", true) s = (quote s, false) := by
      simp [joinStep, quoteImperative_eq_thm]
    rw [List.foldl_cons, hs, join_fold_thm]
    simp only [join_tail_thm]
    rfl

theorem read_fold_thm (vs : List PyValue) (acc : Option (List String)) :
    vs.foldl readStep acc =
      acc.bind (fun pre => (readStrings vs).map (pre ++ ·)) := by
  induction vs generalizing acc with
  | nil => cases acc <;> simp [readStrings]
  | cons v vs ih =>
    rw [List.foldl_cons, ih]
    cases acc with
    | none => cases v <;> simp [readStep]
    | some pre =>
      cases v <;> cases hr : readStrings vs <;>
        simp [readStep, readStrings, hr, List.append_assoc]

theorem readStringsImperative_eq_thm (vs : List PyValue) :
    readStringsImperative vs = readStrings vs := by
  simp [readStringsImperative, read_fold_thm]

theorem asStringsImperative_eq_thm (v : PyValue) :
    asStringsImperative v = asStrings v := by
  cases v <;> simp [asStringsImperative, asStrings, readStringsImperative_eq_thm]

/-- Equivalence on the entire dynamic input domain, not merely valid calls. -/
theorem equivalence_thm (v : PyValue) :
    benchmarkJoin v = benchmarkJoinImperative v := by
  cases hv : asStrings v <;>
    simp [benchmarkJoinImperative, benchmarkJoin, asStringsImperative_eq_thm,
      joinImperative_eq_thm, hv]

end ShlexJoin
end Agent
