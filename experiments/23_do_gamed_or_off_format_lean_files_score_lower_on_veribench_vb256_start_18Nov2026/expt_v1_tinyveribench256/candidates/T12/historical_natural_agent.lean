import Mathlib
namespace Agent

/-!
# Safe TLS: no compression before encryption (CRIME mitigation)

Lean 4 translation of the Python program `158_unsafeTLSCompression_safe.py`.

The Python function `safe_tls_send(cookie, attacker_guess)` builds the HTTP request
body `"PyZoobar={attacker_guess}&secret_cookie={cookie}"`, applies **no** compression
before encryption, and returns the raw length of that body.  Because every character
is always transmitted, the returned length depends only on the *lengths* of the
attacker's guess and of the cookie, never on whether the guess matches (or is a
prefix of) the cookie: the CRIME length oracle is eliminated.

Contents:
* `safeTlsSend` – functional implementation;
* `check` – translation of the Python test harness, and unit tests;
* `Pre`, the `_prop` properties with their theorems, and `Post_prop`;
* property-based tests (randomised via `Plausible`, and bounded/exhaustive);
* the correctness theorem `Pre → Post_prop`;
* `safeTlsSendImp` – an imperative implementation (`Id.run do`, mutable state and a
  character-counting loop) with its tests and the equivalence theorem.
-/

namespace «158_unsafeTLSCompression_safe»

/-! ## Functional implementation -/

/-- Safe TLS send: build the request body
`"PyZoobar={attackerGuess}&secret_cookie={cookie}"` **without** compressing it and
return its raw (uncompressed) length.  Every character is always sent, so the
result cannot leak whether the guess matches the cookie. -/
def safeTlsSend (cookie attackerGuess : String) : Nat :=
  let requestBody : String := "PyZoobar=" ++ attackerGuess ++ "&secret_cookie=" ++ cookie
  requestBody.length

/-- Number of characters contributed by the fixed request structure
(`"PyZoobar="` and `"&secret_cookie="`), i.e. `9 + 15 = 24`. -/
def structuralOverhead : Nat := "PyZoobar=".length + "&secret_cookie=".length

/-- Translation of the Python `check` harness: `true` iff every assertion passes. -/
def check (candidate : String → String → Nat) : Bool :=
  let cookie := "abc123"
  -- 1) same-length guesses, matching vs non-matching, must give the same length
  let fullMatch := candidate cookie "abc123"
  let noMatch := candidate cookie "xyz000"
  let partialMatch := candidate cookie "abc"
  let wrong3chars := candidate cookie "xyz"
  -- 2) length varies only with the input size
  let shorterLen := candidate cookie "ab"
  let longerLen := candidate cookie "abcde"
  -- 3) empty cookie edge case
  let emptyLen := candidate "" "xyz"
  (fullMatch == noMatch) && (partialMatch == wrong3chars) &&
    decide (shorterLen < longerLen) && decide (emptyLen ≥ 0)

/-! ## Unit tests (mirroring the Python `check`) -/

example : safeTlsSend "abc123" "abc123" = 36 := by native_decide
example : safeTlsSend "abc123" "abc123" = safeTlsSend "abc123" "xyz000" := by native_decide
example : safeTlsSend "abc123" "abc" = safeTlsSend "abc123" "xyz" := by native_decide
example : safeTlsSend "abc123" "abc" = 33 := by native_decide
example : safeTlsSend "abc123" "ab" < safeTlsSend "abc123" "abcde" := by native_decide
example : safeTlsSend "abc123" "ab" = 32 := by native_decide
example : safeTlsSend "abc123" "abcde" = 35 := by native_decide
example : safeTlsSend "" "xyz" ≥ 0 := by native_decide
example : safeTlsSend "" "xyz" = 27 := by native_decide
example : safeTlsSend "" "" = 24 := by native_decide
example : structuralOverhead = 24 := by native_decide
example : check safeTlsSend = true := by native_decide

#eval safeTlsSend "abc123" "abc123"   -- 36
#eval safeTlsSend "abc123" "xyz000"   -- 36
#eval safeTlsSend "abc123" "abc"      -- 33
#eval safeTlsSend "abc123" "xyz"      -- 33
#eval safeTlsSend "abc123" "ab"       -- 32
#eval safeTlsSend "abc123" "abcde"    -- 35
#eval safeTlsSend "" "xyz"            -- 27
#eval check safeTlsSend               -- true

/-- The Python test harness succeeds on `safeTlsSend` (kernel-checked). -/
theorem check_safeTlsSend : check safeTlsSend = true := by decide

/-! ## Pre-condition -/

/-- Pre-condition: `safe_tls_send` accepts every cookie and every attacker guess. -/
def Pre (cookie attackerGuess : String) : Prop := True

/-! ## Properties -/

/-- Exact length: the fixed structure plus the full guess plus the full cookie.
Nothing is ever compressed away. -/
def length_formula_prop : Prop :=
  ∀ cookie attackerGuess : String,
    safeTlsSend cookie attackerGuess =
      "PyZoobar=".length + attackerGuess.length + "&secret_cookie=".length + cookie.length

theorem length_formula_thm : length_formula_prop := by
  intro cookie attackerGuess
  unfold safeTlsSend
  simp only [String.length_append]

/-- Numeric form of the exact length: `24 + |guess| + |cookie|`. -/
def length_formula_numeric_prop : Prop :=
  ∀ cookie attackerGuess : String,
    safeTlsSend cookie attackerGuess = 24 + attackerGuess.length + cookie.length

theorem length_formula_numeric_thm : length_formula_numeric_prop := by
  intro cookie attackerGuess
  rw [length_formula_thm cookie attackerGuess]
  have h1 : "PyZoobar=".length = 9 := by decide
  have h2 : "&secret_cookie=".length = 15 := by decide
  rw [h1, h2]
  omega

/-- No CRIME oracle: two guesses of the same length (whether or not either matches
the cookie) are transmitted with exactly the same length. -/
def no_oracle_prop : Prop :=
  ∀ cookie guess₁ guess₂ : String, guess₁.length = guess₂.length →
    safeTlsSend cookie guess₁ = safeTlsSend cookie guess₂

theorem no_oracle_thm : no_oracle_prop := by
  intro cookie guess₁ guess₂ h
  rw [length_formula_thm cookie guess₁, length_formula_thm cookie guess₂, h]

/-- The cookie's *content* is irrelevant as well: only its length matters. -/
def cookie_content_irrelevant_prop : Prop :=
  ∀ cookie₁ cookie₂ attackerGuess : String, cookie₁.length = cookie₂.length →
    safeTlsSend cookie₁ attackerGuess = safeTlsSend cookie₂ attackerGuess

theorem cookie_content_irrelevant_thm : cookie_content_irrelevant_prop := by
  intro cookie₁ cookie₂ attackerGuess h
  rw [length_formula_thm cookie₁ attackerGuess, length_formula_thm cookie₂ attackerGuess, h]

/-- The result is a function of the two lengths only. -/
def depends_only_on_lengths_prop : Prop :=
  ∀ cookie₁ cookie₂ guess₁ guess₂ : String,
    cookie₁.length = cookie₂.length → guess₁.length = guess₂.length →
      safeTlsSend cookie₁ guess₁ = safeTlsSend cookie₂ guess₂

theorem depends_only_on_lengths_thm : depends_only_on_lengths_prop := by
  intro cookie₁ cookie₂ guess₁ guess₂ hc hg
  rw [no_oracle_thm cookie₁ guess₁ guess₂ hg, cookie_content_irrelevant_thm cookie₁ cookie₂ guess₂ hc]

/-- A partial match (a prefix of the cookie) is transmitted with exactly the same
length as any non-matching guess of the same length. -/
def prefix_match_prop : Prop :=
  ∀ cookie guess other : String,
    guess.isPrefixOf cookie = true → guess.length = other.length →
      safeTlsSend cookie guess = safeTlsSend cookie other

theorem prefix_match_thm : prefix_match_prop := by
  intro cookie guess other _ h
  exact no_oracle_thm cookie guess other h

/-- Length scales with input size: a strictly shorter guess is transmitted strictly
shorter, regardless of match quality. -/
def length_scales_prop : Prop :=
  ∀ cookie guess₁ guess₂ : String, guess₁.length < guess₂.length →
    safeTlsSend cookie guess₁ < safeTlsSend cookie guess₂

theorem length_scales_thm : length_scales_prop := by
  intro cookie guess₁ guess₂ h
  rw [length_formula_thm cookie guess₁, length_formula_thm cookie guess₂]
  omega

/-- Monotonicity in the guess length (non-strict form). -/
def length_monotone_prop : Prop :=
  ∀ cookie guess₁ guess₂ : String, guess₁.length ≤ guess₂.length →
    safeTlsSend cookie guess₁ ≤ safeTlsSend cookie guess₂

theorem length_monotone_thm : length_monotone_prop := by
  intro cookie guess₁ guess₂ h
  rw [length_formula_thm cookie guess₁, length_formula_thm cookie guess₂]
  omega

/-- Growing the guess by `k` characters grows the transmission by exactly `k`. -/
def length_additive_prop : Prop :=
  ∀ cookie guess extra : String,
    safeTlsSend cookie (guess ++ extra) = safeTlsSend cookie guess + extra.length

theorem length_additive_thm : length_additive_prop := by
  intro cookie guess extra
  rw [length_formula_thm cookie (guess ++ extra), length_formula_thm cookie guess,
    String.length_append]
  omega

/-- Non-negativity of the transmitted length (edge case of the Python check). -/
def nonneg_prop : Prop :=
  ∀ cookie attackerGuess : String, 0 ≤ safeTlsSend cookie attackerGuess

theorem nonneg_thm : nonneg_prop := by
  intro cookie attackerGuess
  exact Nat.zero_le _

/-- The transmitted length is never below the structural overhead. -/
def structural_lower_bound_prop : Prop :=
  ∀ cookie attackerGuess : String, structuralOverhead ≤ safeTlsSend cookie attackerGuess

theorem structural_lower_bound_thm : structural_lower_bound_prop := by
  intro cookie attackerGuess
  unfold structuralOverhead
  rw [length_formula_thm cookie attackerGuess]
  omega

/-- Empty cookie: the length is still determined by the structure and the guess. -/
def empty_cookie_prop : Prop :=
  ∀ attackerGuess : String,
    safeTlsSend "" attackerGuess = structuralOverhead + attackerGuess.length

theorem empty_cookie_thm : empty_cookie_prop := by
  intro attackerGuess
  unfold structuralOverhead
  rw [length_formula_thm "" attackerGuess]
  have h0 : "".length = 0 := by decide
  rw [h0]
  omega

/-! ## Post-condition -/

/-- Post-condition for `result = safeTlsSend cookie attackerGuess`: the exact
uncompressed length, the absence of a length oracle (for guesses and cookies),
length scaling with input size, and the structural lower bound / non-negativity. -/
def Post_prop (cookie attackerGuess : String) (result : Nat) : Prop :=
  result = "PyZoobar=".length + attackerGuess.length + "&secret_cookie=".length + cookie.length ∧
  result = 24 + attackerGuess.length + cookie.length ∧
  (∀ guess : String, guess.length = attackerGuess.length → safeTlsSend cookie guess = result) ∧
  (∀ cookie' : String, cookie'.length = cookie.length → safeTlsSend cookie' attackerGuess = result) ∧
  (∀ guess : String, guess.length < attackerGuess.length → safeTlsSend cookie guess < result) ∧
  (∀ guess : String, attackerGuess.length < guess.length → result < safeTlsSend cookie guess) ∧
  structuralOverhead ≤ result ∧
  0 ≤ result

/-! ## Property-based tests -/

-- Randomised PBTs (Plausible).  Compilation fails if a counterexample is found.

-- length_formula_prop
#eval Plausible.Testable.check (∀ cookie attackerGuess : String,
  safeTlsSend cookie attackerGuess =
    "PyZoobar=".length + attackerGuess.length + "&secret_cookie=".length + cookie.length)

-- length_formula_numeric_prop
#eval Plausible.Testable.check (∀ cookie attackerGuess : String,
  safeTlsSend cookie attackerGuess = 24 + attackerGuess.length + cookie.length)

-- no_oracle_prop (direct form, with many retries so that same-length pairs are found;
-- and a constructive form where the second guess is built with the same length)
#eval Plausible.Testable.check (∀ cookie guess₁ guess₂ : String,
  guess₁.length = guess₂.length → safeTlsSend cookie guess₁ = safeTlsSend cookie guess₂)
  { numRetries := 3000 }
#eval Plausible.Testable.check (∀ cookie guess : String, ∀ c : Char,
  safeTlsSend cookie guess = safeTlsSend cookie (String.mk (List.replicate guess.length c)))

-- cookie_content_irrelevant_prop (direct and constructive forms)
#eval Plausible.Testable.check (∀ cookie₁ cookie₂ attackerGuess : String,
  cookie₁.length = cookie₂.length →
    safeTlsSend cookie₁ attackerGuess = safeTlsSend cookie₂ attackerGuess)
  { numRetries := 3000 }
#eval Plausible.Testable.check (∀ cookie attackerGuess : String, ∀ c : Char,
  safeTlsSend cookie attackerGuess =
    safeTlsSend (String.mk (List.replicate cookie.length c)) attackerGuess)

-- depends_only_on_lengths_prop (direct form; the double precondition is rarely met by
-- random strings, so this check may report "Gave up" -- a constructive randomised form
-- and an exhaustive bounded test are given as well)
#eval Plausible.Testable.check (∀ cookie₁ cookie₂ guess₁ guess₂ : String,
  cookie₁.length = cookie₂.length → guess₁.length = guess₂.length →
    safeTlsSend cookie₁ guess₁ = safeTlsSend cookie₂ guess₂)
#eval Plausible.Testable.check (∀ cookie guess : String, ∀ a b : Char,
  safeTlsSend cookie guess =
    safeTlsSend (String.mk (List.replicate cookie.length a))
      (String.mk (List.replicate guess.length b)))

-- prefix_match_prop (direct form; random guesses are rarely prefixes of the cookie, so
-- this check may report "Gave up" -- a constructive form where the guess is the prefix
-- of length `n` of the cookie and the other guess has the same length, and an
-- exhaustive bounded test, are given as well)
#eval Plausible.Testable.check (∀ cookie guess other : String,
  guess.isPrefixOf cookie = true → guess.length = other.length →
    safeTlsSend cookie guess = safeTlsSend cookie other)
#eval Plausible.Testable.check (∀ cookie : String, ∀ n : Nat, ∀ c : Char,
  safeTlsSend cookie (String.mk (cookie.toList.take n)) =
    safeTlsSend cookie (String.mk (List.replicate (cookie.toList.take n).length c)))

-- length_scales_prop (direct form, and a constructive form with a longer guess)
#eval Plausible.Testable.check (∀ cookie guess₁ guess₂ : String,
  guess₁.length < guess₂.length → safeTlsSend cookie guess₁ < safeTlsSend cookie guess₂)
  { numRetries := 3000 }
#eval Plausible.Testable.check (∀ cookie guess : String, ∀ c : Char,
  safeTlsSend cookie guess < safeTlsSend cookie (guess.push c))

-- length_monotone_prop (direct form, and a constructive form)
#eval Plausible.Testable.check (∀ cookie guess₁ guess₂ : String,
  guess₁.length ≤ guess₂.length → safeTlsSend cookie guess₁ ≤ safeTlsSend cookie guess₂)
  { numRetries := 3000 }
#eval Plausible.Testable.check (∀ cookie guess extra : String,
  safeTlsSend cookie guess ≤ safeTlsSend cookie (guess ++ extra))

-- length_additive_prop
#eval Plausible.Testable.check (∀ cookie guess extra : String,
  safeTlsSend cookie (guess ++ extra) = safeTlsSend cookie guess + extra.length)

-- nonneg_prop
#eval Plausible.Testable.check (∀ cookie attackerGuess : String,
  0 ≤ safeTlsSend cookie attackerGuess)

-- structural_lower_bound_prop
#eval Plausible.Testable.check (∀ cookie attackerGuess : String,
  structuralOverhead ≤ safeTlsSend cookie attackerGuess)

-- empty_cookie_prop
#eval Plausible.Testable.check (∀ attackerGuess : String,
  safeTlsSend "" attackerGuess = structuralOverhead + attackerGuess.length)

-- Bounded / exhaustive PBTs over a fixed corpus of strings (same-length pairs are
-- plentiful here, so the implications are exercised many times).

/-- Corpus of strings for the bounded property tests. -/
def sampleStrings : List String :=
  ["", "a", "x", "ab", "xy", "abc", "xyz", "ab1", "abcde", "xyzde", "abc12", "abc123",
   "xyz000", "zzzzzz", "secret", "PyZoobar=", "&secret_cookie=", "1234567"]

/-- Executable form of `Post_prop` on the implementation, for a given corpus. -/
def postCheck (cookie attackerGuess guess cookie' : String) : Bool :=
  let result := safeTlsSend cookie attackerGuess
  decide (result =
      "PyZoobar=".length + attackerGuess.length + "&secret_cookie=".length + cookie.length) &&
  decide (result = 24 + attackerGuess.length + cookie.length) &&
  decide (guess.length = attackerGuess.length → safeTlsSend cookie guess = result) &&
  decide (cookie'.length = cookie.length → safeTlsSend cookie' attackerGuess = result) &&
  decide (guess.length < attackerGuess.length → safeTlsSend cookie guess < result) &&
  decide (attackerGuess.length < guess.length → result < safeTlsSend cookie guess) &&
  decide (structuralOverhead ≤ result) && decide (0 ≤ result)

-- Post_prop (randomised: `postCheck` is the executable Boolean form of every conjunct)
#eval Plausible.Testable.check (∀ cookie attackerGuess guess cookie' : String,
  postCheck cookie attackerGuess guess cookie' = true)

-- length_formula_prop / length_formula_numeric_prop
example : (sampleStrings.all fun cookie => sampleStrings.all fun guess =>
    safeTlsSend cookie guess ==
      "PyZoobar=".length + guess.length + "&secret_cookie=".length + cookie.length) = true := by
  native_decide
example : (sampleStrings.all fun cookie => sampleStrings.all fun guess =>
    safeTlsSend cookie guess == 24 + guess.length + cookie.length) = true := by native_decide

-- no_oracle_prop
example : (sampleStrings.all fun cookie => sampleStrings.all fun g₁ => sampleStrings.all fun g₂ =>
    decide (g₁.length = g₂.length → safeTlsSend cookie g₁ = safeTlsSend cookie g₂)) = true := by
  native_decide

-- cookie_content_irrelevant_prop
example : (sampleStrings.all fun c₁ => sampleStrings.all fun c₂ => sampleStrings.all fun g =>
    decide (c₁.length = c₂.length → safeTlsSend c₁ g = safeTlsSend c₂ g)) = true := by
  native_decide

-- depends_only_on_lengths_prop
example : (sampleStrings.all fun c₁ => sampleStrings.all fun c₂ =>
    sampleStrings.all fun g₁ => sampleStrings.all fun g₂ =>
      decide (c₁.length = c₂.length → g₁.length = g₂.length →
        safeTlsSend c₁ g₁ = safeTlsSend c₂ g₂)) = true := by
  native_decide

-- prefix_match_prop
example : (sampleStrings.all fun cookie => sampleStrings.all fun g => sampleStrings.all fun o =>
    decide (g.isPrefixOf cookie = true → g.length = o.length →
      safeTlsSend cookie g = safeTlsSend cookie o)) = true := by
  native_decide

-- length_scales_prop / length_monotone_prop
example : (sampleStrings.all fun cookie => sampleStrings.all fun g₁ => sampleStrings.all fun g₂ =>
    decide (g₁.length < g₂.length → safeTlsSend cookie g₁ < safeTlsSend cookie g₂)) = true := by
  native_decide
example : (sampleStrings.all fun cookie => sampleStrings.all fun g₁ => sampleStrings.all fun g₂ =>
    decide (g₁.length ≤ g₂.length → safeTlsSend cookie g₁ ≤ safeTlsSend cookie g₂)) = true := by
  native_decide

-- length_additive_prop
example : (sampleStrings.all fun cookie => sampleStrings.all fun g => sampleStrings.all fun e =>
    safeTlsSend cookie (g ++ e) == safeTlsSend cookie g + e.length) = true := by
  native_decide

-- nonneg_prop / structural_lower_bound_prop
example : (sampleStrings.all fun cookie => sampleStrings.all fun g =>
    decide (0 ≤ safeTlsSend cookie g) && decide (structuralOverhead ≤ safeTlsSend cookie g)) =
    true := by
  native_decide

-- empty_cookie_prop
example : (sampleStrings.all fun g =>
    safeTlsSend "" g == structuralOverhead + g.length) = true := by native_decide

-- Post_prop (bounded, exhaustive over the corpus)
example : (sampleStrings.all fun cookie => sampleStrings.all fun attackerGuess =>
    sampleStrings.all fun guess => sampleStrings.all fun cookie' =>
      postCheck cookie attackerGuess guess cookie') = true := by
  native_decide

-- Bounded PBT parameterised by guess length: for every length `n < 40`, a matching
-- prefix-style guess (`'a'` repeated) and a non-matching guess (`'z'` repeated)
-- transmit the same length, namely `24 + n + 6` for the cookie `"abc123"`.
example : ((List.range 40).all fun n =>
    safeTlsSend "abc123" (String.mk (List.replicate n 'a')) ==
      safeTlsSend "abc123" (String.mk (List.replicate n 'z')) &&
    safeTlsSend "abc123" (String.mk (List.replicate n 'a')) == 24 + n + 6) = true := by
  native_decide

/-! ## Correctness theorem -/

/-- `Pre → Post`: for every cookie and every attacker guess, the result of
`safeTlsSend` satisfies the post-condition. -/
theorem safeTlsSend_correct (cookie attackerGuess : String) (hpre : Pre cookie attackerGuess) :
    Post_prop cookie attackerGuess (safeTlsSend cookie attackerGuess) := by
  refine ⟨length_formula_thm cookie attackerGuess, length_formula_numeric_thm cookie attackerGuess,
    ?_, ?_, ?_, ?_, structural_lower_bound_thm cookie attackerGuess, nonneg_thm cookie attackerGuess⟩
  · intro guess h
    exact no_oracle_thm cookie guess attackerGuess h
  · intro cookie' h
    exact cookie_content_irrelevant_thm cookie' cookie attackerGuess h
  · intro guess h
    exact length_scales_thm cookie guess attackerGuess h
  · intro guess h
    exact length_scales_thm cookie attackerGuess guess h

/-! ## Imperative implementation -/

/-- Imperative version of `safe_tls_send`: the request body is assembled piece by
piece in a mutable variable (never compressed), then every character that will be
transmitted is counted by a loop. -/
def safeTlsSendImp (cookie attackerGuess : String) : Nat := Id.run do
  let mut requestBody : String := "PyZoobar="
  requestBody := requestBody ++ attackerGuess
  requestBody := requestBody ++ "&secret_cookie="
  requestBody := requestBody ++ cookie
  let mut transmitted : Nat := 0
  for _ in requestBody.toList do
    transmitted := transmitted + 1
  return transmitted

/-! ## Imperative tests -/

example : safeTlsSendImp "abc123" "abc123" = 36 := by native_decide
example : safeTlsSendImp "abc123" "abc123" = safeTlsSendImp "abc123" "xyz000" := by native_decide
example : safeTlsSendImp "abc123" "abc" = safeTlsSendImp "abc123" "xyz" := by native_decide
example : safeTlsSendImp "abc123" "ab" < safeTlsSendImp "abc123" "abcde" := by native_decide
example : safeTlsSendImp "" "xyz" ≥ 0 := by native_decide
example : safeTlsSendImp "" "xyz" = 27 := by native_decide
example : check safeTlsSendImp = true := by native_decide
example : (sampleStrings.all fun cookie => sampleStrings.all fun g =>
    safeTlsSendImp cookie g == safeTlsSend cookie g) = true := by native_decide

#eval safeTlsSendImp "abc123" "abc123"   -- 36
#eval safeTlsSendImp "abc123" "xyz000"   -- 36
#eval safeTlsSendImp "abc123" "abc"      -- 33
#eval safeTlsSendImp "abc123" "ab"       -- 32
#eval safeTlsSendImp "abc123" "abcde"    -- 35
#eval safeTlsSendImp "" "xyz"            -- 27
#eval check safeTlsSendImp               -- true
#eval Plausible.Testable.check (∀ cookie attackerGuess : String,
  safeTlsSendImp cookie attackerGuess = safeTlsSend cookie attackerGuess)

/-! ## Equivalence theorem -/

/-- The counting loop adds the length of the traversed list to the accumulator. -/
theorem count_loop (l : List Char) (acc : Nat) :
    Id.run (forIn (m := Id) l acc fun _ r => do
        pure PUnit.unit
        pure (ForInStep.yield (r + 1))) = acc + l.length := by
  induction l generalizing acc with
  | nil => rfl
  | cons c cs ih =>
    rw [List.forIn_cons]
    show Id.run (forIn cs (acc + 1) _) = _
    rw [ih, List.length_cons]
    omega

/-- Functional and imperative implementations agree on every input. -/
theorem safeTlsSendImp_eq_safeTlsSend (cookie attackerGuess : String) :
    safeTlsSendImp cookie attackerGuess = safeTlsSend cookie attackerGuess := by
  unfold safeTlsSendImp safeTlsSend
  show Id.run (forIn (m := Id) _ 0 fun _ r => do
      pure PUnit.unit
      pure (ForInStep.yield (r + 1))) = _
  rw [count_loop, Nat.zero_add]
  rfl

/-- Consequently the imperative implementation also satisfies the post-condition. -/
theorem safeTlsSendImp_correct (cookie attackerGuess : String) (hpre : Pre cookie attackerGuess) :
    Post_prop cookie attackerGuess (safeTlsSendImp cookie attackerGuess) := by
  rw [safeTlsSendImp_eq_safeTlsSend]
  exact safeTlsSend_correct cookie attackerGuess hpre

/-- The Python test harness also succeeds on the imperative implementation. -/
theorem check_safeTlsSendImp : check safeTlsSendImp = true := by
  unfold check
  simp only [safeTlsSendImp_eq_safeTlsSend]
  exact check_safeTlsSend

end «158_unsafeTLSCompression_safe»
end Agent
