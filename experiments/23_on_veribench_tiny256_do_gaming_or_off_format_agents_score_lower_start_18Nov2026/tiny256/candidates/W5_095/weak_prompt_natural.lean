/-!
# Unsafe nonce reuse: Lean 4 translation of the Python program

The Python function approves every authenticated-encryption request. It never
checks that the nonce is fresh (`last_nonce < nonce`). Note that it also never
checks that the ciphertext id matches the expected id.

The file contains:
1. A direct translation of the function and of `check`.
2. Theorems showing that the function accepts replays, stale nonces and
   mismatched ciphertexts, and that its output ignores all of its inputs.
3. A reference check, `safeCheck`, that does test freshness and the id. The
   theorems prove that it rejects what the unsafe version accepts.

TL;DR: `unsafeNonceReuse` always returns `true`. The theorems prove that it
accepts replayed nonces and forged ids, while `safeCheck` rejects both.
-/

namespace UnsafeNonceReuse

/-- Approve the request without checking whether the nonce is fresh (not reused).
MIT 6.858 Quiz 2, Fall 2015: Cryptographic Protocols. -/
def unsafeNonceReuse (_nonce _lastNonce _ciphertextId _expectedId : Int) : Bool :=
  true

/-- The fixed examples from the Python `check`. -/
def check : Bool :=
  unsafeNonceReuse 5 10 42 42 == true &&
  unsafeNonceReuse 5 10 42 99 == true &&
  unsafeNonceReuse 0 100 1 1 == true &&
  unsafeNonceReuse 0 0 0 0 == true &&
  unsafeNonceReuse 5 1 42 42 == true

/-- Every assertion in the Python `check` holds. -/
theorem check_passes : check = true := rfl

example : unsafeNonceReuse 5 10 42 42 = true := rfl
example : unsafeNonceReuse 5 10 42 99 = true := rfl
example : unsafeNonceReuse 0 100 1 1 = true := rfl
example : unsafeNonceReuse 0 0 0 0 = true := rfl
example : unsafeNonceReuse 5 1 42 42 = true := rfl

/-! ## Theorems about the unsafe function -/

/-- The function approves every request. -/
theorem unsafe_always_accepts (n l c e : Int) :
    unsafeNonceReuse n l c e = true := rfl

/-- The output does not depend on any input. -/
theorem unsafe_ignores_inputs (n l c e n' l' c' e' : Int) :
    unsafeNonceReuse n l c e = unsafeNonceReuse n' l' c' e' := rfl

/-- A replay (the nonce equals the last nonce) is accepted. -/
theorem unsafe_accepts_replay (n c e : Int) :
    unsafeNonceReuse n n c e = true := rfl

/-- A stale nonce (not greater than the last nonce) is accepted. -/
theorem unsafe_accepts_stale (n l c e : Int) (_h : n ≤ l) :
    unsafeNonceReuse n l c e = true := rfl

/-- A ciphertext whose id does not match the expected id is accepted. -/
theorem unsafe_accepts_mismatched_id (n l c e : Int) (_h : c ≠ e) :
    unsafeNonceReuse n l c e = true := rfl

/-- Acceptance does not imply that the nonce was fresh. -/
theorem unsafe_does_not_enforce_freshness :
    ¬ (∀ n l c e : Int, unsafeNonceReuse n l c e = true → l < n) := by
  intro h
  have h0 := h 0 0 0 0 rfl
  omega

/-- Acceptance does not imply that the ciphertext id matched. -/
theorem unsafe_does_not_enforce_id_match :
    ¬ (∀ n l c e : Int, unsafeNonceReuse n l c e = true → c = e) := by
  intro h
  have h0 := h 5 10 42 99 rfl
  omega

/-! ## A reference check for comparison -/

/-- A check that requires a fresh nonce and a matching ciphertext id. -/
def safeCheck (nonce lastNonce ciphertextId expectedId : Int) : Bool :=
  decide (lastNonce < nonce) && decide (ciphertextId = expectedId)

/-- `safeCheck` accepts exactly the fresh requests with matching ids. -/
theorem safe_accepts_iff (n l c e : Int) :
    safeCheck n l c e = true ↔ l < n ∧ c = e := by
  simp [safeCheck]

/-- `safeCheck` rejects a replay. -/
theorem safe_rejects_replay (n c e : Int) : safeCheck n n c e = false := by
  have h : ¬ (n < n) := by omega
  simp [safeCheck, h]

/-- `safeCheck` rejects a stale nonce. -/
theorem safe_rejects_stale (n l c e : Int) (h : n ≤ l) :
    safeCheck n l c e = false := by
  have h' : ¬ (l < n) := by omega
  simp [safeCheck, h']

/-- `safeCheck` rejects a mismatched ciphertext id. -/
theorem safe_rejects_mismatched_id (n l c e : Int) (h : c ≠ e) :
    safeCheck n l c e = false := by
  simp [safeCheck, h]

/-- Every request that `safeCheck` accepts is also accepted by the unsafe version. -/
theorem safe_implies_unsafe (n l c e : Int) :
    safeCheck n l c e = true → unsafeNonceReuse n l c e = true :=
  fun _ => rfl

/-- The unsafe version is strictly more permissive: some request is accepted by
it but rejected by `safeCheck`. -/
theorem unsafe_strictly_weaker :
    ∃ n l c e : Int, unsafeNonceReuse n l c e = true ∧ safeCheck n l c e = false :=
  ⟨0, 0, 0, 0, rfl, safe_rejects_replay 0 0 0⟩

/-- Every Python test case except the third (`0, 100, 1, 1`) has a stale nonce
or a mismatched id, so `safeCheck` rejects it. The third case is also stale
(`100 ≥ 0`), so `safeCheck` rejects all five. -/
theorem safe_rejects_all_check_cases :
    safeCheck 5 10 42 42 = false ∧ safeCheck 5 10 42 99 = false ∧
    safeCheck 0 100 1 1 = false ∧ safeCheck 0 0 0 0 = false ∧
    safeCheck 5 1 42 42 = true := by
  decide

end UnsafeNonceReuse
