import Mathlib
namespace Agent

/-!
# Nonce-based TLS key derivation (integer model)

Translation of `safe_key_gen` and its Python `check` function. `Int` preserves
Python's unbounded signed inputs; remainder by the positive modulus is Euclidean.

Freshness is necessarily modular: arbitrary distinct Python integers can differ
by 2^32 and give the same key. We prove exact separation modulo 2^32, including
injectivity for distinct 32-bit nonces/sessions, rather than claiming impossible
injectivity on all integers. Every integer in [0, 2^32) is an attainable key.
The function consumes a nonce; it does not implement or verify a random generator.
These arithmetic facts alone do not establish cryptographic unpredictability or
that enumerating a 32-bit space is computationally infeasible.
-/

namespace SafePredictableKeyGen

def modulus : Int := 2 ^ 32

def multiplier : Int := 1000000007

/-- Exact translation of the Python integer expression. -/
def safe_key_gen (session_id fresh_nonce : Int) : Int :=
  (session_id * multiplier + fresh_nonce) % modulus

/-- The six checks from the Python source, including all four bounds checks. -/
def check (candidate : Int → Int → Int) : Bool :=
  decide (candidate 1 100 ≠ candidate 1 200) &&
  decide (candidate 1 100 ≠ candidate 2 100) &&
  decide (candidate 1 100 = candidate 1 100) &&
  decide (candidate 0 0 ≠ candidate 0 1) &&
  decide (candidate 5 999999 ≠ candidate 5 1000000) &&
  ([(0, 0), (1, 1), (100, 200), (2 ^ 16, 2 ^ 16)] : List (Int × Int)).all
    (fun p => decide (0 ≤ candidate p.1 p.2 ∧ candidate p.1 p.2 < modulus))

-- Unit tests reproduce every assertion, not just the aggregate Boolean.
example : safe_key_gen 1 100 ≠ safe_key_gen 1 200 := by native_decide
example : safe_key_gen 1 100 ≠ safe_key_gen 2 100 := by native_decide
example : safe_key_gen 1 100 = safe_key_gen 1 100 := by native_decide
example : safe_key_gen 0 0 ≠ safe_key_gen 0 1 := by native_decide
example : safe_key_gen 5 999999 ≠ safe_key_gen 5 1000000 := by native_decide
example : 0 ≤ safe_key_gen 0 0 ∧ safe_key_gen 0 0 < 2 ^ 32 := by native_decide
example : 0 ≤ safe_key_gen 1 1 ∧ safe_key_gen 1 1 < 2 ^ 32 := by native_decide
example : 0 ≤ safe_key_gen 100 200 ∧ safe_key_gen 100 200 < 2 ^ 32 := by native_decide
example : 0 ≤ safe_key_gen (2 ^ 16) (2 ^ 16) ∧
    safe_key_gen (2 ^ 16) (2 ^ 16) < 2 ^ 32 := by native_decide
example : check safe_key_gen = true := by native_decide
-- Negative inputs and wrapping are allowed by Python as well.
example : safe_key_gen 0 (-1) = 4294967295 := by native_decide
example : safe_key_gen 0 0 = safe_key_gen 0 (2 ^ 32) := by native_decide
#eval safe_key_gen 1 100
#eval check safe_key_gen
#eval if check safe_key_gen then "All tests passed." else "Candidate failed tests"

/-- No restriction on either Python integer argument. -/
def Pre (_session_id _fresh_nonce : Int) : Prop := True

def bounded_prop (s n : Int) : Prop :=
  0 ≤ safe_key_gen s n ∧ safe_key_gen s n < modulus

theorem bounded_thm (s n : Int) : bounded_prop s n := by
  unfold bounded_prop safe_key_gen
  constructor
  · exact Int.emod_nonneg _ (by norm_num [modulus])
  · exact Int.emod_lt_of_pos _ (by norm_num [modulus])

def deterministic_prop (s n : Int) : Prop :=
  safe_key_gen s n = safe_key_gen s n

theorem deterministic_thm (s n : Int) : deterministic_prop s n := by
  rfl

/-- Equal keys for one session occur exactly for congruent nonces. -/
def nonce_freshness_prop (s n₁ n₂ : Int) : Prop :=
  safe_key_gen s n₁ = safe_key_gen s n₂ ↔ n₁ % modulus = n₂ % modulus

theorem nonce_freshness_thm (s n₁ n₂ : Int) : nonce_freshness_prop s n₁ n₂ := by
  change Int.ModEq modulus (s * multiplier + n₁) (s * multiplier + n₂) ↔
    Int.ModEq modulus n₁ n₂
  exact ⟨Int.ModEq.add_left_cancel' _, fun h => h.add_left _⟩

/-- Odd multiplication is a permutation of the residues modulo 2^32. -/
def session_separation_prop (s₁ s₂ n : Int) : Prop :=
  safe_key_gen s₁ n = safe_key_gen s₂ n ↔ s₁ % modulus = s₂ % modulus

theorem session_separation_thm (s₁ s₂ n : Int) :
    session_separation_prop s₁ s₂ n := by
  change Int.ModEq modulus (s₁ * multiplier + n) (s₂ * multiplier + n) ↔
    Int.ModEq modulus s₁ s₂
  constructor
  · intro h
    have hc := Int.ModEq.add_right_cancel' n h
    have hm : 0 < modulus := by norm_num [modulus]
    have hg : Int.gcd modulus multiplier = 1 := by
      norm_num [modulus, multiplier, Int.gcd]
    simpa [hg] using Int.ModEq.cancel_right_div_gcd hm hc
  · intro h
    exact (h.mul_right multiplier).add_right n

/-- The usual distinct-nonce statement on canonical 32-bit representatives.
The implementation itself still accepts all integers. -/
theorem distinct_nonces_thm (s n₁ n₂ : Int)
    (h₁ : 0 ≤ n₁ ∧ n₁ < modulus) (h₂ : 0 ≤ n₂ ∧ n₂ < modulus)
    (hne : n₁ ≠ n₂) : safe_key_gen s n₁ ≠ safe_key_gen s n₂ := by
  intro h
  have hm := (nonce_freshness_thm s n₁ n₂).mp h
  rw [Int.emod_eq_of_lt h₁.1 h₁.2, Int.emod_eq_of_lt h₂.1 h₂.2] at hm
  exact hne hm

/-- The multiplier also separates distinct canonical session identifiers. -/
theorem distinct_sessions_thm (s₁ s₂ n : Int)
    (h₁ : 0 ≤ s₁ ∧ s₁ < modulus) (h₂ : 0 ≤ s₂ ∧ s₂ < modulus)
    (hne : s₁ ≠ s₂) : safe_key_gen s₁ n ≠ safe_key_gen s₂ n := by
  intro h
  have hm := (session_separation_thm s₁ s₂ n).mp h
  rw [Int.emod_eq_of_lt h₁.1 h₁.2, Int.emod_eq_of_lt h₂.1 h₂.2] at hm
  exact hne hm

def zero_session_prop (n : Int) : Prop := safe_key_gen 0 n = n % modulus

theorem zero_session_thm (n : Int) : zero_session_prop n := by
  simp [zero_session_prop, safe_key_gen]

/-- Adjacent nonces differ even at a wraparound, for every integer session. -/
def adjacent_nonce_prop (s n : Int) : Prop :=
  safe_key_gen s n ≠ safe_key_gen s (n + 1)

theorem adjacent_nonce_thm (s n : Int) : adjacent_nonce_prop s n := by
  unfold adjacent_nonce_prop
  intro h
  have hmod := (nonce_freshness_thm s n (n + 1)).mp h
  norm_num [modulus] at hmod
  omega

/-- Exactly the 32-bit nonnegative integers are fixed by the zero-session map.
Thus every one of the 2^32 possible outputs is attained by the explicit input
(session_id, fresh_nonce) = (0, k). -/
def output_space_prop (k : Int) : Prop :=
  safe_key_gen 0 k = k ↔ 0 ≤ k ∧ k < modulus

theorem output_space_thm (k : Int) : output_space_prop k := by
  unfold output_space_prop
  constructor
  · intro h
    simpa only [bounded_prop, h] using bounded_thm 0 k
  · intro h
    simpa [safe_key_gen] using Int.emod_eq_of_lt h.1 h.2

/-- A kernel-checked proof of all original checks (independent of native tests). -/
theorem check_thm : check safe_key_gen = true := by
  norm_num [check, safe_key_gen, modulus, multiplier]

/-- The result and its relationship to every other session/nonce. No hidden
restriction to the bounded test set is present in this specification. -/
def Post_prop (s n : Int) : Prop :=
  bounded_prop s n ∧
  deterministic_prop s n ∧
  (∀ otherNonce : Int, nonce_freshness_prop s n otherNonce) ∧
  (∀ otherSession : Int, session_separation_prop s otherSession n) ∧
  zero_session_prop n ∧
  adjacent_nonce_prop s n ∧
  output_space_prop n ∧
  check safe_key_gen = true

/-! ## Property-based tests

Each test below is the executable form of its named property. All small signed
inputs are tested exhaustively; additional samples cover the original examples,
wraparound, congruent inputs, and integers much larger than machine words. The
universal clauses in `Post_prop` are tested over the same finite sample set,
not used as a substitute for their unrestricted proofs.
-/

def testInputs : List Int :=
  (List.range 25).map (fun k => (k : Int) - 12) ++
  [100, 200, 999999, 1000000, 2 ^ 16, -(2 ^ 16), multiplier, -multiplier,
   modulus - 1, modulus, modulus + 1, -modulus - 1, -modulus, -modulus + 1,
   2 * modulus + 17, -2 * modulus - 17, 2 ^ 80, -(2 ^ 80)]

-- PBT: bounded_prop.
example : testInputs.all (fun s => testInputs.all (fun n =>
    decide (0 ≤ safe_key_gen s n ∧ safe_key_gen s n < modulus))) = true := by
  native_decide

-- PBT: deterministic_prop.
example : testInputs.all (fun s => testInputs.all (fun n =>
    decide (safe_key_gen s n = safe_key_gen s n))) = true := by
  native_decide

-- PBT: nonce_freshness_prop; both congruent and noncongruent nonces occur.
example : testInputs.all (fun s => testInputs.all (fun n₁ =>
    testInputs.all (fun n₂ => decide
      (safe_key_gen s n₁ = safe_key_gen s n₂ ↔
       n₁ % modulus = n₂ % modulus)))) = true := by
  native_decide

-- PBT: session_separation_prop, including negative session identifiers.
example : testInputs.all (fun s₁ => testInputs.all (fun s₂ =>
    testInputs.all (fun n => decide
      (safe_key_gen s₁ n = safe_key_gen s₂ n ↔
       s₁ % modulus = s₂ % modulus)))) = true := by
  native_decide

-- PBT: the canonical 32-bit distinctness corollaries.
example : testInputs.all (fun s => testInputs.all (fun a =>
    testInputs.all (fun b => decide
      ((0 ≤ a ∧ a < modulus) → (0 ≤ b ∧ b < modulus) → a ≠ b →
       safe_key_gen s a ≠ safe_key_gen s b)))) = true := by
  native_decide
example : testInputs.all (fun n => testInputs.all (fun a =>
    testInputs.all (fun b => decide
      ((0 ≤ a ∧ a < modulus) → (0 ≤ b ∧ b < modulus) → a ≠ b →
       safe_key_gen a n ≠ safe_key_gen b n)))) = true := by
  native_decide

-- PBT: zero_session_prop.
example : testInputs.all (fun n =>
    decide (safe_key_gen 0 n = n % modulus)) = true := by
  native_decide

-- PBT: adjacent_nonce_prop, also covering the large-nonce Python check.
example : testInputs.all (fun s => testInputs.all (fun n =>
    decide (safe_key_gen s n ≠ safe_key_gen s (n + 1)))) = true := by
  native_decide

-- PBT: output_space_prop, with explicit witnesses (session, nonce) = (0, k).
example : testInputs.all (fun k =>
    decide (safe_key_gen 0 k = k ↔ 0 ≤ k ∧ k < modulus)) = true := by
  native_decide

-- PBT: the conjunction Post_prop, with bounded samples of its universal clauses.
example : testInputs.all (fun s => testInputs.all (fun n =>
    decide (0 ≤ safe_key_gen s n ∧ safe_key_gen s n < modulus) &&
    decide (safe_key_gen s n = safe_key_gen s n) &&
    testInputs.all (fun otherNonce => decide
      (safe_key_gen s n = safe_key_gen s otherNonce ↔
       n % modulus = otherNonce % modulus)) &&
    testInputs.all (fun otherSession => decide
      (safe_key_gen s n = safe_key_gen otherSession n ↔
       s % modulus = otherSession % modulus)) &&
    decide (safe_key_gen 0 n = n % modulus) &&
    decide (safe_key_gen s n ≠ safe_key_gen s (n + 1)) &&
    decide (safe_key_gen 0 n = n ↔ 0 ≤ n ∧ n < modulus) &&
    check safe_key_gen)) = true := by
  native_decide

#eval testInputs.length
#eval testInputs.all (fun s => testInputs.all (fun n =>
  decide (0 ≤ safe_key_gen s n ∧ safe_key_gen s n < modulus)))

/-- Correctness for the entire Python input domain, not just the PBT samples. -/
theorem correctness_thm (s n : Int) : Pre s n → Post_prop s n := by
  intro _
  exact ⟨bounded_thm s n, deterministic_thm s n,
    fun otherNonce => nonce_freshness_thm s n otherNonce,
    fun otherSession => session_separation_thm s otherSession n,
    zero_session_thm n, adjacent_nonce_thm s n, output_space_thm n, check_thm⟩

/-! ## Imperative translation -/

/-- The same sequence of integer operations using mutable state. -/
def safe_key_gen_imp (session_id fresh_nonce : Int) : Int := Id.run do
  let mut mixed := session_id
  mixed := mixed * multiplier
  mixed := mixed + fresh_nonce
  mixed := mixed % modulus
  return mixed

-- Imperative tests include every original assertion via the same check function.
example : check safe_key_gen_imp = true := by native_decide
example : safe_key_gen_imp 1 100 = 1000000107 := by native_decide
example : safe_key_gen_imp 0 (-1) = 4294967295 := by native_decide
example : safe_key_gen_imp 0 (2 ^ 32) = 0 := by native_decide
example : testInputs.all (fun s => testInputs.all (fun n =>
    decide (safe_key_gen s n = safe_key_gen_imp s n))) = true := by
  native_decide
#eval safe_key_gen_imp 1 100
#eval check safe_key_gen_imp

/-- Kernel reduction proves equality for all signed integer inputs. -/
theorem functional_imperative_equiv_thm (s n : Int) :
    safe_key_gen s n = safe_key_gen_imp s n := by
  rfl

end SafePredictableKeyGen
end Agent
