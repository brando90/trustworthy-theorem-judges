import Mathlib
namespace Agent

/-!
# Safe eval input filter

A translation of the MIT 6.858 example `safe_eval_input`.  The Python code
only checks text: it does not parse or evaluate an expression.  It returns
`true` exactly when none of `;`, `(`, `)`, and the contiguous substring `__`
occurs.  In particular, a single underscore is permitted.  No claim is made
that every accepted string is a valid expression or safe for a general evaluator.

Strings are modelled by their Unicode character lists; substring membership
is contiguous list infix membership.  All strings are admissible.  The proofs
below are kernel checked; `native_decide` is used only for executable tests.
-/

namespace UnsafeEvalInjectionSafe

/-- The four forbidden substrings, in the same order as the Python program. -/
def dangerousTokens : List String := [";", "(", ")", "__"]

/-- Contiguous substring occurrence, not subsequence or character-set membership. -/
def Contains (needle text : String) : Prop :=
  needle.toList.IsInfix text.toList

instance (needle text : String) : Decidable (Contains needle text) :=
  inferInstanceAs (Decidable (needle.toList.IsInfix text.toList))

/-- Executable Python-style `needle in text`. -/
def containsSubstring (needle text : String) : Bool :=
  decide (Contains needle text)

/-- Functional translation of `all(c not in input_str for c in [...])`. -/
def safe_eval_input (input_str : String) : Bool :=
  dangerousTokens.all (fun token => !containsSubstring token input_str)

-- The five unit tests from the source program.
example : safe_eval_input "hello" = true := by native_decide
example : safe_eval_input "42" = true := by native_decide
example : safe_eval_input ";badstuff()" = false := by native_decide
example : safe_eval_input "__import__" = false := by native_decide
example : safe_eval_input "(evil)" = false := by native_decide

-- Boundary cases distinguish two adjacent underscores from one underscore.
example : safe_eval_input "" = true := by native_decide
example : safe_eval_input "_" = true := by native_decide
example : safe_eval_input "a_b_c" = true := by native_decide
example : safe_eval_input "a__b" = false := by native_decide
example : safe_eval_input "λ + 42\n" = true := by native_decide
example : safe_eval_input "\";\"" = false := by native_decide

#eval ["hello", "42", ";badstuff()", "__import__", "(evil)"].map safe_eval_input

/-- Python accepts any string argument; there is no further precondition. -/
def Pre (_input_str : String) : Prop := True

/-- Exact agreement with the generator passed to Python's `all`. -/
theorem safe_iff_no_token_thm (s : String) :
    safe_eval_input s = true ↔
      ∀ token ∈ dangerousTokens, ¬Contains token s := by
  simp [safe_eval_input, List.all_eq_true, containsSubstring]

/-- Exact acceptance: the three single characters and adjacent underscores
are absent.  This includes completeness, so harmless strings are not rejected. -/
def acceptance_prop (s : String) : Prop :=
  safe_eval_input s = true ↔
    ';' ∉ s.toList ∧ '(' ∉ s.toList ∧ ')' ∉ s.toList ∧
      ¬Contains "__" s

theorem acceptance_thm (s : String) : acceptance_prop s := by
  have singleton_infix (c : Char) (xs : List Char) :
      [c].IsInfix xs ↔ c ∈ xs := by
    constructor
    · intro h
      exact List.singleton_sublist.mp h.sublist
    · intro h
      obtain ⟨left, right, rfl⟩ := List.mem_iff_append.mp h
      exact ⟨left, right, by simp⟩
  unfold acceptance_prop
  rw [safe_iff_no_token_thm]
  simp [dangerousTokens, Contains, String.toList, singleton_infix]

/-- Rejection has a forbidden-substring witness, and every such witness
forces rejection. -/
def rejection_prop (s : String) : Prop :=
  safe_eval_input s = false ↔
    ∃ token ∈ dangerousTokens, Contains token s

theorem rejection_thm (s : String) : rejection_prop s := by
  simp [rejection_prop, safe_eval_input, List.all_eq_false, containsSubstring]

/-- Rejected text remains rejected when surrounded by arbitrary text. -/
def contextRejection_prop (s : String) : Prop :=
  safe_eval_input s = false →
    ∀ before after : String, safe_eval_input (before ++ s ++ after) = false

theorem contextRejection_thm (s : String) : contextRejection_prop s := by
  intro hs before after
  obtain ⟨token, htoken, hoccurs⟩ := (rejection_thm s).mp hs
  apply (rejection_thm (before ++ s ++ after)).mpr
  refine ⟨token, htoken, ?_⟩
  apply List.IsInfix.trans hoccurs
  change s.toList.IsInfix (before.toList ++ s.toList ++ after.toList)
  exact List.infix_append before.toList s.toList after.toList

/-- A contiguous substring of accepted text is accepted.  The converse
for concatenation is deliberately not asserted: `"_" ++ "_"` is rejected. -/
def substringSafety_prop (s : String) : Prop :=
  safe_eval_input s = true →
    ∀ t : String, t.toList.IsInfix s.toList → safe_eval_input t = true

theorem substringSafety_thm (s : String) : substringSafety_prop s := by
  intro hs t ht
  apply (safe_iff_no_token_thm t).mpr
  intro token htoken hoccurs
  exact (safe_iff_no_token_thm s).mp hs token htoken
    (List.IsInfix.trans hoccurs ht)

/-- An explicit injection-rejection corollary, with arbitrary surrounding text. -/
theorem embeddedDanger_thm (before after token : String)
    (htoken : token ∈ dangerousTokens) :
    safe_eval_input (before ++ token ++ after) = false := by
  apply (rejection_thm (before ++ token ++ after)).mpr
  refine ⟨token, htoken, ?_⟩
  change token.toList.IsInfix (before.toList ++ token.toList ++ after.toList)
  exact List.infix_append before.toList token.toList after.toList

/-- The empty input passes the filter, even though it is not a Python expression. -/
theorem empty_thm : safe_eval_input "" = true := by decide

/-- The post-condition combines the exact result specifications and their
preservation properties. -/
def Post_prop (s : String) : Prop :=
  acceptance_prop s ∧ rejection_prop s ∧
    contextRejection_prop s ∧ substringSafety_prop s

/-! ## Bounded property-based tests

Exhaustively generate all strings of length at most three over an alphabet
containing every dangerous character, an ordinary letter, a digit, whitespace,
and a non-ASCII character.  Add longer regression inputs.  These executable
Boolean checks are evidence, not the proofs above.  The universal string
quantifiers in the preservation properties are tested over bounded contexts
and candidate substrings, without narrowing the corresponding theorem domains.
-/

def pbtAlphabet : List Char := ['a', '4', ';', '(', ')', '_', ' ', 'λ']

def pbtCharLists : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 => [] :: pbtAlphabet.flatMap (fun c => (pbtCharLists n).map (c :: ·))

def pbtInputs : List String :=
  (pbtCharLists 3).map String.mk ++
    ["hello", "42", ";badstuff()", "__import__", "(evil)", "a_b_c", "a__b", "\";\"", "\n", "é😊"]

def pbtContexts : List String := (pbtCharLists 1).map String.mk

/-- Executable counterpart of the right side of `acceptance_prop`. -/
def acceptanceSpecB (s : String) : Bool :=
  !(s.toList.contains ';') && !(s.toList.contains '(') &&
    !(s.toList.contains ')') && !containsSubstring "__" s

/-- Executable counterpart of the existential in `rejection_prop`. -/
def rejectionSpecB (s : String) : Bool :=
  dangerousTokens.any (fun token => containsSubstring token s)

def acceptanceTestB (s : String) : Bool :=
  safe_eval_input s == acceptanceSpecB s

def rejectionTestB (s : String) : Bool :=
  (!safe_eval_input s) == rejectionSpecB s

def contextRejectionTestB (s : String) : Bool :=
  pbtContexts.all (fun before => pbtContexts.all (fun after =>
    safe_eval_input s || !safe_eval_input (before ++ s ++ after)))

def substringSafetyTestB (s : String) : Bool :=
  pbtInputs.all (fun t =>
    !(safe_eval_input s && containsSubstring t s) || safe_eval_input t)

-- PBT for acceptance_prop (both soundness and completeness).
example : pbtInputs.all acceptanceTestB = true := by native_decide
-- PBT for rejection_prop (both directions of the equivalence).
example : pbtInputs.all rejectionTestB = true := by native_decide
-- PBT for contextRejection_prop, including cases where rejection is required.
example : pbtInputs.all contextRejectionTestB = true := by native_decide
-- PBT for substringSafety_prop, including empty and nonempty infixes.
example : pbtInputs.all substringSafetyTestB = true := by native_decide
-- PBT for Post_prop: conjunction of all four executable property checks.
example : pbtInputs.all (fun s =>
    acceptanceTestB s && rejectionTestB s &&
      contextRejectionTestB s && substringSafetyTestB s) = true := by native_decide

-- Additional PBT for embeddedDanger_thm: every token, at every bounded context.
example : pbtContexts.all (fun before => pbtContexts.all (fun after =>
    dangerousTokens.all (fun token =>
      !safe_eval_input (before ++ token ++ after)))) = true := by native_decide
-- PBT for the list-oriented characterization safe_iff_no_token_thm.
example : pbtInputs.all (fun s => (safe_eval_input s) ==
    !(dangerousTokens.any (fun token => containsSubstring token s))) = true := by
  native_decide

#eval (pbtInputs.length, pbtInputs.all (fun s =>
  acceptanceTestB s && rejectionTestB s &&
    contextRejectionTestB s && substringSafetyTestB s))

/-- Correctness on the full input domain, with no unproved assumptions. -/
theorem correctness_thm (s : String) : Pre s → Post_prop s := by
  intro _
  exact ⟨acceptance_thm s, rejection_thm s,
    contextRejection_thm s, substringSafety_thm s⟩

/-- Imperative version: accumulate the four tests in mutable Boolean state.
Each test is pure, so retaining a false accumulator has the same result as
Python's short-circuiting `all`. -/
def safe_eval_input_imperative (input_str : String) : Bool := Id.run do
  let mut accepted := true
  for token in dangerousTokens do
    accepted := accepted && !containsSubstring token input_str
  return accepted

example : safe_eval_input_imperative "hello" = true := by native_decide
example : safe_eval_input_imperative "42" = true := by native_decide
example : safe_eval_input_imperative ";badstuff()" = false := by native_decide
example : safe_eval_input_imperative "__import__" = false := by native_decide
example : safe_eval_input_imperative "(evil)" = false := by native_decide
example : safe_eval_input_imperative "" = true := by native_decide
example : safe_eval_input_imperative "a_b" = true := by native_decide

#eval ["hello", "42", ";badstuff()", "__import__", "(evil)"].map safe_eval_input_imperative

-- Bounded equivalence test, in addition to the universal proof below.
example : pbtInputs.all (fun s =>
    safe_eval_input s == safe_eval_input_imperative s) = true := by native_decide

/-- Functional/imperative equivalence for every string, not only the tests. -/
theorem equivalence_thm (s : String) :
    safe_eval_input s = safe_eval_input_imperative s := by
  simp [safe_eval_input, safe_eval_input_imperative, dangerousTokens,
    List.all_cons, Bool.and_assoc]

end UnsafeEvalInjectionSafe
end Agent
