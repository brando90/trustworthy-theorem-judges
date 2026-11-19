import Mathlib
namespace Agent

/-!
# HumanEval 17: parsing ASCII music

Python splits on the literal ASCII space and ignores empty fields.  The three
legal dictionary keys are `o`, `o|`, and `.|`, with durations 4, 2, and 1.
`parse_music` is the list-valued parser on this domain; its value 0 on an invalid
key is only a totalization.  `parse_music_checked` additionally exposes dictionary
failure rather than silently accepting such a key.  `Pre` is exactly the domain
on which the Python list comprehension returns normally.
-/

namespace humaneval_17_parse_music

/-- Nonempty fields, without trimming tabs, newlines, or other characters. -/
def tokens (music : String) : List String :=
  (music.splitOn " ").filter (fun token => token != "")

/-- The dictionary lookup, totalized outside the three legal keys. -/
def noteBeats (token : String) : Nat :=
  if token = "o" then 4 else if token = "o|" then 2 else if token = ".|" then 1 else 0

def validNote (token : String) : Prop :=
  token = "o" ∨ token = "o|" ∨ token = ".|"

instance (token : String) : Decidable (validNote token) :=
  inferInstanceAs (Decidable (token = "o" ∨ token = "o|" ∨ token = ".|"))

def parse_music (music : String) : List Nat :=
  (tokens music).map noteBeats

/-- `none` represents Python's dictionary lookup failure (`KeyError`). -/
def parse_music_checked (music : String) : Option (List Nat) :=
  if (tokens music).all (fun token => decide (validNote token)) then
    some (parse_music music)
  else none

-- The five supplied tests, the documentation example, and spacing/error cases.
example : parse_music "" = [] := by native_decide
example : parse_music "o o o o" = [4, 4, 4, 4] := by native_decide
example : parse_music ".| .| .| .|" = [1, 1, 1, 1] := by native_decide
example : parse_music "o| o| .| .| o o o o" = [2, 2, 1, 1, 4, 4, 4, 4] := by native_decide
example : parse_music "o| .| o| .| o o| o o|" = [2, 1, 2, 1, 4, 2, 4, 2] := by native_decide
example : parse_music "o o| .| o| o| .| .| .| .| o o" =
    [4, 2, 1, 2, 2, 1, 1, 1, 1, 4, 4] := by native_decide
example : parse_music "  o   o|  .| " = [4, 2, 1] := by native_decide
example : parse_music "    " = [] := by native_decide
example : parse_music_checked "o\to|" = none := by native_decide
example : parse_music_checked "o .| x" = none := by native_decide
example : parse_music_checked " o  .| " = some [4, 1] := by native_decide
#eval parse_music "o o| .| o| o| .| .| .| .| o o"
#eval parse_music_checked " o  o| .| "

/-- No dictionary lookup performed by Python fails. -/
def Pre (music : String) : Prop :=
  ∀ token ∈ tokens music, validNote token

/-- Independent, executable statement of the three dictionary entries. -/
def noteMatches (token : String) (beats : Nat) : Bool :=
  (token == "o" && beats == 4) ||
  (token == "o|" && beats == 2) ||
  (token == ".|" && beats == 1)

/-- Every nonempty input field corresponds to exactly one output, in order. -/
def parsing_prop (music : String) (result : List Nat) : Prop :=
  List.Forall₂ (fun token beats => noteMatches token beats = true) (tokens music) result

/-- Repeated spaces create no additional output entries. -/
def length_prop (music : String) (result : List Nat) : Prop :=
  result.length = (tokens music).length

/-- Every emitted duration belongs to the musical legend. -/
def beats_prop (result : List Nat) : Prop :=
  ∀ beats ∈ result, beats = 4 ∨ beats = 2 ∨ beats = 1

/-- Multiplicity of each note is preserved by the parser. -/
def counts_prop (music : String) (result : List Nat) : Prop :=
  result.count 4 = (tokens music).count "o" ∧
  result.count 2 = (tokens music).count "o|" ∧
  result.count 1 = (tokens music).count ".|"

/-- Empty output occurs exactly when every literal-space field is empty. -/
def empty_prop (music : String) (result : List Nat) : Prop :=
  result = [] ↔ ∀ token ∈ music.splitOn " ", token = ""

/-- The error-aware interface succeeds exactly on Python's normal-return domain. -/
def checked_prop (music : String) : Prop :=
  (parse_music_checked music = some (parse_music music) ↔ Pre music) ∧
  (parse_music_checked music = none ↔ ¬ Pre music)

/-- Filtering discards exactly the empty fields. -/
theorem mem_tokens_thm (music token : String) :
    token ∈ tokens music ↔ token ∈ music.splitOn " " ∧ token ≠ "" := by
  simp [tokens]

theorem noteMatches_thm {token : String} (h : validNote token) :
    noteMatches token (noteBeats token) = true := by
  rcases h with rfl | rfl | rfl <;> decide

theorem noteBeats_valid_thm {token : String} (h : validNote token) :
    noteBeats token = 4 ∨ noteBeats token = 2 ∨ noteBeats token = 1 := by
  rcases h with rfl | rfl | rfl <;> simp [noteBeats]

theorem parsing_thm (music : String) (h : Pre music) :
    parsing_prop music (parse_music music) := by
  unfold parsing_prop parse_music
  rw [List.forall₂_map_right_iff, List.forall₂_same]
  intro token ht
  exact noteMatches_thm (h token ht)

theorem length_thm (music : String) : length_prop music (parse_music music) := by
  simp [length_prop, parse_music]

theorem beats_thm (music : String) (h : Pre music) :
    beats_prop (parse_music music) := by
  intro beats hb
  obtain ⟨token, ht, rfl⟩ := List.mem_map.mp hb
  exact noteBeats_valid_thm (h token ht)

/-- A list-level counting invariant, independent of string splitting. -/
theorem counts_list_thm (notes : List String)
    (h : ∀ token ∈ notes, validNote token) :
    (notes.map noteBeats).count 4 = notes.count "o" ∧
    (notes.map noteBeats).count 2 = notes.count "o|" ∧
    (notes.map noteBeats).count 1 = notes.count ".|" := by
  induction notes with
  | nil => simp
  | cons token rest ih =>
      have ht : validNote token := h token (by simp)
      have hr : ∀ t ∈ rest, validNote t := by
        intro t hm
        exact h t (by simp [hm])
      obtain ⟨h4, h2, h1⟩ := ih hr
      rcases ht with rfl | rfl | rfl <;>
        simp [noteBeats, h4, h2, h1]

theorem counts_thm (music : String) (h : Pre music) :
    counts_prop music (parse_music music) := by
  exact counts_list_thm (tokens music) h

theorem empty_thm (music : String) : empty_prop music (parse_music music) := by
  simp [empty_prop, parse_music, tokens, List.filter_eq_nil_iff]

theorem checked_thm (music : String) : checked_prop music := by
  have hp : (tokens music).all (fun token => decide (validNote token)) = true ↔
      Pre music := by
    simp [List.all_eq_true, Pre]
  by_cases h : Pre music
  · have ha := hp.mpr h
    simp [checked_prop, parse_music_checked, ha, h]
  · have ha : (tokens music).all (fun token => decide (validNote token)) = false := by
      apply Bool.eq_false_iff.mpr
      exact fun ht => h (hp.mp ht)
    simp [checked_prop, parse_music_checked, ha, h]

/-- Full normal-return specification; order is included, not merely a multiset. -/
def Post_prop (music : String) (result : List Nat) : Prop :=
  parsing_prop music result ∧ length_prop music result ∧ beats_prop result ∧
  counts_prop music result ∧ empty_prop music result ∧ checked_prop music

-- Constructive instances expose the executable forms of the specifications.
instance (music : String) : Decidable (Pre music) := by
  unfold Pre
  infer_instance

instance (music : String) (result : List Nat) : Decidable (parsing_prop music result) := by
  unfold parsing_prop
  infer_instance

instance (music : String) (result : List Nat) : Decidable (length_prop music result) := by
  unfold length_prop
  infer_instance

instance (result : List Nat) : Decidable (beats_prop result) := by
  unfold beats_prop
  infer_instance

instance (music : String) (result : List Nat) : Decidable (counts_prop music result) := by
  unfold counts_prop
  infer_instance

instance (music : String) (result : List Nat) : Decidable (empty_prop music result) := by
  unfold empty_prop
  infer_instance

instance (music : String) : Decidable (checked_prop music) := by
  unfold checked_prop
  infer_instance

instance (music : String) (result : List Nat) : Decidable (Post_prop music result) := by
  unfold Post_prop
  infer_instance

/-! ## Bounded property-based tests

Enumerate all lists of at most five fields from the legal notes plus the empty
field: 1,365 cases, including leading/trailing/repeated spaces.  Also enumerate
all lists of at most three fields from a larger alphabet with invalid keys and
non-space whitespace.  The latter exercises unconditional and error properties.
Each `_prop`, including `Post_prop`, has its own executable check below.
-/

def fieldLists (alphabet : List String) : Nat → List (List String)
  | 0 => [[]]
  | n + 1 => (fieldLists alphabet n).flatMap
      (fun tail => alphabet.map (fun head => head :: tail))

def validSamples : List String :=
  ((List.range 6).flatMap (fieldLists ["", "o", "o|", ".|"])).map
    (String.intercalate " ")

def rawSamples : List String :=
  ((List.range 4).flatMap (fieldLists ["", "o", "o|", ".|", "x", "\t", "o\n", "oo"])).map
    (String.intercalate " ")

-- Check admissibility rather than relying on an untested generator assumption.
example : validSamples.length = 1365 := by native_decide
example : validSamples.all (fun music => decide (Pre music)) = true := by native_decide

-- PBT: parsing_prop (pointwise, order-preserving dictionary correspondence).
example : validSamples.all
    (fun music => decide (parsing_prop music (parse_music music))) = true := by
  native_decide

-- PBT: length_prop, including strings outside the normal-return domain.
example : (validSamples ++ rawSamples).all
    (fun music => decide (length_prop music (parse_music music))) = true := by
  native_decide

-- PBT: beats_prop.
example : validSamples.all
    (fun music => decide (beats_prop (parse_music music))) = true := by
  native_decide

-- PBT: counts_prop, checking all three multiplicities in every case.
example : validSamples.all
    (fun music => decide (counts_prop music (parse_music music))) = true := by
  native_decide

-- PBT: empty_prop, including invalid nonempty fields.
example : (validSamples ++ rawSamples).all
    (fun music => decide (empty_prop music (parse_music music))) = true := by
  native_decide

-- PBT: checked_prop, exercising both successful parses and dictionary errors.
example : (validSamples ++ rawSamples).all
    (fun music => decide (checked_prop music)) = true := by
  native_decide

-- PBT: the complete conjunction Post_prop.
example : validSamples.all
    (fun music => decide (Post_prop music (parse_music music))) = true := by
  native_decide

#eval (validSamples.length, rawSamples.length)
#eval validSamples.all (fun music => decide (Post_prop music (parse_music music)))

theorem correctness_thm (music : String) :
    Pre music → Post_prop music (parse_music music) := by
  intro h
  exact ⟨parsing_thm music h, length_thm music, beats_thm music h,
    counts_thm music h, empty_thm music, checked_thm music⟩

/-! ## Imperative implementation

The imperative version visits the raw fields, skips empty ones inside the loop,
and appends each duration to mutable state.  In particular it does not simply
call the functional parser.  As with the list-valued functional version, only
its behavior under `Pre` represents a successful Python return.
-/

def parse_music_imperative (music : String) : List Nat := Id.run do
  let mut result : List Nat := []
  for token in music.splitOn " " do
    if token != "" then
      result := result ++ [noteBeats token]
  return result

example : parse_music_imperative "" = [] := by native_decide
example : parse_music_imperative "o o o o" = [4, 4, 4, 4] := by native_decide
example : parse_music_imperative ".| .| .| .|" = [1, 1, 1, 1] := by native_decide
example : parse_music_imperative "o| o| .| .| o o o o" =
    [2, 2, 1, 1, 4, 4, 4, 4] := by native_decide
example : parse_music_imperative "o| .| o| .| o o| o o|" =
    [2, 1, 2, 1, 4, 2, 4, 2] := by native_decide
example : parse_music_imperative "o o| .| o| o| .| .| .| .| o o" =
    [4, 2, 1, 2, 2, 1, 1, 1, 1, 4, 4] := by native_decide
example : parse_music_imperative "  o   o|  .| " = [4, 2, 1] := by native_decide
example : parse_music_imperative "    " = [] := by native_decide
example : (validSamples ++ rawSamples).all
    (fun music => parse_music music == parse_music_imperative music) = true := by
  native_decide
#eval parse_music_imperative "o o| .| o| o| .| .| .| .| o o"

/-- Loop invariant: the old accumulator followed by the parsed remaining fields. -/
theorem foldl_notes_thm (fields : List String) (acc : List Nat) :
    fields.foldl
      (fun result token => if token != "" then result ++ [noteBeats token] else result) acc =
    acc ++ (fields.filter (fun token => token != "")).map noteBeats := by
  induction fields generalizing acc with
  | nil => simp
  | cons token rest ih =>
      by_cases h : token = ""
      · subst token
        simpa using ih acc
      · simpa [List.foldl_cons, h, List.append_assoc] using
          ih (acc ++ [noteBeats token])

/-- Equality holds for every string, even outside the successful-parse domain. -/
theorem equivalence_thm (music : String) :
    parse_music music = parse_music_imperative music := by
  unfold parse_music_imperative
  change parse_music music =
    (forIn (music.splitOn " ") ([] : List Nat)
      (fun token result => if token != "" then
        ForInStep.yield (result ++ [noteBeats token]) else ForInStep.yield result) : Id (List Nat))
  have step_eq (token : String) (result : List Nat) :
      (if token != "" then ForInStep.yield (result ++ [noteBeats token])
        else ForInStep.yield result) =
      ForInStep.yield (if token != "" then result ++ [noteBeats token] else result) := by
    split <;> rfl
  simp_rw [step_eq]
  have hfold :
      (forIn (music.splitOn " ") ([] : List Nat)
        (fun token result => ForInStep.yield
          (if token != "" then result ++ [noteBeats token] else result)) : Id (List Nat)) =
      (music.splitOn " ").foldl
        (fun result token => if token != "" then result ++ [noteBeats token] else result) [] :=
    List.forIn_pure_yield_eq_foldl (m := Id) (l := music.splitOn " ")
      (fun (token : String) (result : List Nat) =>
        if token != "" then result ++ [noteBeats token] else result) []
  rw [hfold, foldl_notes_thm]
  simp [parse_music, tokens]

end humaneval_17_parse_music
end Agent
