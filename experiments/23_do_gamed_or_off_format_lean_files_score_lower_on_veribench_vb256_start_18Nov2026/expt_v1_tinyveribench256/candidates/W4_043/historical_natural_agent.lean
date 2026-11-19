import Mathlib
namespace Agent

/-!
# Shared-key deniable authentication

Translation of the Python MAC example. `Int` models Python's unbounded integers;
remainder modulo the positive integer 100003 also agrees for negative inputs.
Both Alice and Bob possess the same key, so they compute identical tags. The
third-party function is the source program's explicit no-key policy, not a
cryptographic hardness claim about this deliberately simple arithmetic MAC.

No inputs are excluded. An adjacent wrong key is always rejected, generalizing
the source test (7 versus 8). Arbitrary distinct keys need not be rejected:
keys differing by 100003 collide. No such stronger security claim is made.
-/

namespace UnsafeDeniableAuthSafe

/-! ## Functional implementation and the Python assertion harness -/

def safe_deniable_auth (msg shared_key : Int) : Int :=
  (msg + 31 * shared_key) % 100003

def verify_safe (msg tag shared_key : Int) : Bool :=
  decide (tag = (msg + 31 * shared_key) % 100003)

def third_party_verifiable (_msg _shared_key : Int) : Bool := false

def bob_can_forge (msg shared_key : Int) : Int :=
  (msg + 31 * shared_key) % 100003

/-- Boolean translation of all assertions in `check`; a failed assertion
corresponds to `false`, while successful completion corresponds to `true`. -/
def check (candidate : Int → Int → Int) : Bool :=
  let tag := candidate 42 7
  verify_safe 42 tag 7 &&
  !third_party_verifiable 42 7 &&
  !third_party_verifiable 999 12345 &&
  (bob_can_forge 42 7 == candidate 42 7) &&
  (bob_can_forge 999 12345 == candidate 999 12345) &&
  !verify_safe 42 tag 8 &&
  (candidate 0 0 == 0) &&
  (candidate 99 100 == candidate 99 100)

/-! ## Unit tests -/

example : safe_deniable_auth 42 7 = 259 := by native_decide
example : verify_safe 42 (safe_deniable_auth 42 7) 7 = true := by native_decide
example : third_party_verifiable 42 7 = false := by native_decide
example : third_party_verifiable 999 12345 = false := by native_decide
example : bob_can_forge 42 7 = safe_deniable_auth 42 7 := by native_decide
example : bob_can_forge 999 12345 = safe_deniable_auth 999 12345 := by native_decide
example : safe_deniable_auth 999 12345 = 83685 := by native_decide
example : verify_safe 42 (safe_deniable_auth 42 7) 8 = false := by native_decide
example : safe_deniable_auth 0 0 = 0 := by native_decide
example : safe_deniable_auth 99 100 = safe_deniable_auth 99 100 := by native_decide
example : safe_deniable_auth (-1) 0 = 100002 := by native_decide
example : safe_deniable_auth 0 (-1) = 99972 := by native_decide
example : check safe_deniable_auth = true := by native_decide

#eval safe_deniable_auth 42 7
#eval safe_deniable_auth 999 12345
#eval check safe_deniable_auth

/-! ## Preconditions and proven properties -/

/-- Python accepts every integer message and key. -/
def Pre (_msg _shared_key : Int) : Prop := True

def recipient_verification_prop (msg shared_key : Int) : Prop :=
  verify_safe msg (safe_deniable_auth msg shared_key) shared_key = true

theorem recipient_verification_thm (msg shared_key : Int) :
    recipient_verification_prop msg shared_key := by
  simp [recipient_verification_prop, verify_safe, safe_deniable_auth]

def third_party_nonverifiable_prop (msg shared_key : Int) : Prop :=
  third_party_verifiable msg shared_key = false

theorem third_party_nonverifiable_thm (msg shared_key : Int) :
    third_party_nonverifiable_prop msg shared_key := by
  rfl

/-- Equality of the observable tags is the source's indistinguishability claim. -/
def bob_forgery_prop (msg shared_key : Int) : Prop :=
  bob_can_forge msg shared_key = safe_deniable_auth msg shared_key

theorem bob_forgery_thm (msg shared_key : Int) :
    bob_forgery_prop msg shared_key := by
  rfl

/-- In particular, this rejects key 8 for the tag produced using key 7. -/
def wrong_key_prop (msg shared_key : Int) : Prop :=
  verify_safe msg (safe_deniable_auth msg shared_key) (shared_key + 1) = false

theorem wrong_key_thm (msg shared_key : Int) :
    wrong_key_prop msg shared_key := by
  simp only [wrong_key_prop, verify_safe, safe_deniable_auth,
    decide_eq_false_iff_not]
  omega

/-- General zero-key law, including the source's zero-message/zero-key edge. -/
def zero_key_prop (msg : Int) : Prop :=
  safe_deniable_auth msg 0 = msg % 100003

theorem zero_key_thm (msg : Int) : zero_key_prop msg := by
  simp [zero_key_prop, safe_deniable_auth]

theorem zero_input_thm : safe_deniable_auth 0 0 = 0 := by
  rfl

def determinism_prop (msg shared_key : Int) : Prop :=
  safe_deniable_auth msg shared_key = safe_deniable_auth msg shared_key

theorem determinism_thm (msg shared_key : Int) :
    determinism_prop msg shared_key := by
  rfl

/-- Positive-modulus Python remainder is always a canonical nonnegative tag. -/
def tag_range_prop (msg shared_key : Int) : Prop :=
  0 ≤ safe_deniable_auth msg shared_key ∧
  safe_deniable_auth msg shared_key < 100003

theorem tag_range_thm (msg shared_key : Int) :
    tag_range_prop msg shared_key := by
  unfold tag_range_prop safe_deniable_auth
  constructor
  · exact Int.emod_nonneg _ (by norm_num)
  · exact Int.emod_lt_of_pos _ (by norm_num)

/-- Kernel-checked proof of the complete, original finite check harness. -/
theorem python_check_thm : check safe_deniable_auth = true := by
  decide

/-! ## Postcondition -/

def Post_prop (msg shared_key : Int) : Prop :=
  recipient_verification_prop msg shared_key ∧
  third_party_nonverifiable_prop msg shared_key ∧
  bob_forgery_prop msg shared_key ∧
  wrong_key_prop msg shared_key ∧
  zero_key_prop msg ∧
  determinism_prop msg shared_key ∧
  tag_range_prop msg shared_key ∧
  safe_deniable_auth 0 0 = 0 ∧
  check safe_deniable_auth = true

/-! ## Bounded property-based tests

Each test below checks an executable form of the named property. The finite
sample contains every integer from -20 to 20, plus positive and negative
modulus boundaries and the source examples. These tests do not justify any
of the universal theorems.
-/

def testInts : List Int :=
  (List.range 41).map (fun n => (n : Int) - 20) ++
  [-200006, -100004, -100003, -100002, 42, 99, 100, 999, 12345,
    100002, 100003, 100004, 200006]

-- PBT: recipient_verification_prop
example : testInts.all (fun msg => testInts.all (fun key =>
    verify_safe msg (safe_deniable_auth msg key) key)) = true := by
  native_decide

-- PBT: third_party_nonverifiable_prop
example : testInts.all (fun msg => testInts.all (fun key =>
    !third_party_verifiable msg key)) = true := by
  native_decide

-- PBT: bob_forgery_prop
example : testInts.all (fun msg => testInts.all (fun key =>
    bob_can_forge msg key == safe_deniable_auth msg key)) = true := by
  native_decide

-- PBT: wrong_key_prop (adjacent keys, including negative keys)
example : testInts.all (fun msg => testInts.all (fun key =>
    !verify_safe msg (safe_deniable_auth msg key) (key + 1))) = true := by
  native_decide

-- PBT: zero_key_prop
example : testInts.all (fun msg =>
    safe_deniable_auth msg 0 == msg % 100003) = true := by
  native_decide

-- PBT: determinism_prop
example : testInts.all (fun msg => testInts.all (fun key =>
    safe_deniable_auth msg key == safe_deniable_auth msg key)) = true := by
  native_decide

-- PBT: tag_range_prop
example : testInts.all (fun msg => testInts.all (fun key =>
    decide (0 ≤ safe_deniable_auth msg key ∧
      safe_deniable_auth msg key < 100003))) = true := by
  native_decide

-- PBT: Post_prop, checking every conjunct together on each input pair.
example : testInts.all (fun msg => testInts.all (fun key =>
    verify_safe msg (safe_deniable_auth msg key) key &&
    !third_party_verifiable msg key &&
    (bob_can_forge msg key == safe_deniable_auth msg key) &&
    !verify_safe msg (safe_deniable_auth msg key) (key + 1) &&
    (safe_deniable_auth msg 0 == msg % 100003) &&
    (safe_deniable_auth msg key == safe_deniable_auth msg key) &&
    decide (0 ≤ safe_deniable_auth msg key ∧
      safe_deniable_auth msg key < 100003) &&
    (safe_deniable_auth 0 0 == 0) &&
    check safe_deniable_auth)) = true := by
  native_decide

#eval testInts.all (fun msg => testInts.all (fun key =>
  verify_safe msg (safe_deniable_auth msg key) key &&
  !third_party_verifiable msg key &&
  (bob_can_forge msg key == safe_deniable_auth msg key)))

/-! ## Correctness -/

theorem correctness_thm (msg shared_key : Int) :
    Pre msg shared_key → Post_prop msg shared_key := by
  intro _
  exact ⟨recipient_verification_thm msg shared_key,
    third_party_nonverifiable_thm msg shared_key,
    bob_forgery_thm msg shared_key,
    wrong_key_thm msg shared_key,
    zero_key_thm msg,
    determinism_thm msg shared_key,
    tag_range_thm msg shared_key,
    zero_input_thm,
    python_check_thm⟩

/-! ## Imperative implementation -/

/-- The same unbounded integer arithmetic, expressed as mutable updates. -/
def safe_deniable_auth_imperative (msg shared_key : Int) : Int := Id.run do
  let mut tag := shared_key
  tag := 31 * tag
  tag := msg + tag
  tag := tag % 100003
  return tag

/-! ## Imperative tests -/

example : safe_deniable_auth_imperative 42 7 = 259 := by native_decide
example : safe_deniable_auth_imperative 999 12345 = 83685 := by native_decide
example : safe_deniable_auth_imperative 0 0 = 0 := by native_decide
example : safe_deniable_auth_imperative (-1) 0 = 100002 := by native_decide
example : check safe_deniable_auth_imperative = true := by native_decide

-- Bounded functional/imperative equivalence test on signed inputs.
example : testInts.all (fun msg => testInts.all (fun key =>
    safe_deniable_auth msg key == safe_deniable_auth_imperative msg key)) = true := by
  native_decide

#eval safe_deniable_auth_imperative 42 7
#eval check safe_deniable_auth_imperative

/-! ## Functional/imperative equivalence -/

theorem functional_imperative_equivalence_thm (msg shared_key : Int) :
    safe_deniable_auth msg shared_key =
      safe_deniable_auth_imperative msg shared_key := by
  rfl

theorem functional_imperative_extensional_thm :
    safe_deniable_auth = safe_deniable_auth_imperative := by
  funext msg shared_key
  exact functional_imperative_equivalence_thm msg shared_key

end UnsafeDeniableAuthSafe
end Agent
