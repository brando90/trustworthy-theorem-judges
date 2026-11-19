import Mathlib
namespace Agent

/-!
# Unsafe out-of-band authentication

Translation of the Python `unsafe_oob_auth` example from messaging security.
The function returns `true` for every message identifier and verification flag.
In particular, it accepts unverified messages: this formalization describes the
vulnerability rather than repairing it or claiming authentication is provided.

`Int` models Python's unrestricted integer identifiers, including negative ones.
No precondition requires an identifier to be positive or verification to occur.
The functional and mutable implementations have the same unconditional result.
-/

namespace UnsafeOobAuth

/-! ## Functional implementation -/

def unsafe_oob_auth (_msg_id : Int) (_has_oob_verification : Bool) : Bool :=
  true

/-! ## Unit tests and the Python check routine -/

example : unsafe_oob_auth 1 true = true := by native_decide
example : unsafe_oob_auth 1 false = true := by native_decide
example : unsafe_oob_auth 99 false = true := by native_decide
example : unsafe_oob_auth (-1) false = true := by native_decide

/-- Execute the three assertions from Python, retaining their error messages. -/
def check : IO Unit := do
  unless unsafe_oob_auth 1 true == true do
    throw (IO.userError "verified msg rejected")
  unless unsafe_oob_auth 1 false == true do
    throw (IO.userError "vuln: unverified msg accepted")
  unless unsafe_oob_auth 99 false == true do
    throw (IO.userError "vuln: any msg accepted")
  IO.println "All tests passed."

#eval unsafe_oob_auth 1 true
#eval unsafe_oob_auth 1 false
#eval unsafe_oob_auth 99 false
#eval check

/-! ## Unrestricted precondition -/

/-- Every integer identifier and both verification flags are admissible. -/
def Pre (_msg_id : Int) (_has_oob_verification : Bool) : Prop := True

/-! ## Properties and kernel-checked proofs -/

/-- The exact return value, not merely acceptance of the sample identifiers. -/
def always_accepts_prop (msg_id : Int) (has_oob_verification : Bool) : Prop :=
  unsafe_oob_auth msg_id has_oob_verification = true

theorem always_accepts_thm (msg_id : Int) (has_oob_verification : Bool) :
    always_accepts_prop msg_id has_oob_verification := by
  rfl

/-- The vulnerability: absence of OOB verification never causes rejection. -/
def unverified_accepted_prop (msg_id : Int) : Prop :=
  unsafe_oob_auth msg_id false = true

theorem unverified_accepted_thm (msg_id : Int) :
    unverified_accepted_prop msg_id := by
  rfl

/-- Changing the verification flag cannot affect the result. -/
def verification_independent_prop (msg_id : Int) (b₁ b₂ : Bool) : Prop :=
  unsafe_oob_auth msg_id b₁ = unsafe_oob_auth msg_id b₂

theorem verification_independent_thm (msg_id : Int) (b₁ b₂ : Bool) :
    verification_independent_prop msg_id b₁ b₂ := by
  rfl

/-- Changing the message identifier cannot affect the result either. -/
def message_id_independent_prop (msg₁ msg₂ : Int) (b : Bool) : Prop :=
  unsafe_oob_auth msg₁ b = unsafe_oob_auth msg₂ b

theorem message_id_independent_thm (msg₁ msg₂ : Int) (b : Bool) :
    message_id_independent_prop msg₁ msg₂ b := by
  rfl

/-! ## Conjunctive post-condition -/

def Post_prop (msg_id : Int) (has_oob_verification : Bool) : Prop :=
  always_accepts_prop msg_id has_oob_verification ∧
  unverified_accepted_prop msg_id ∧
  (∀ b : Bool, verification_independent_prop msg_id has_oob_verification b) ∧
  (∀ other_id : Int, message_id_independent_prop msg_id other_id has_oob_verification)

/-! ## Property-based tests

These checks use executable equalities on the implementation, not theorem
proofs. The post-condition check samples all its universally quantified inputs;
it is the universal closure of the unfolded conjunction in `Post_prop`.
-/

-- PBT for always_accepts_prop.
#eval Plausible.Testable.check
  (∀ (msg_id : Int) (b : Bool), unsafe_oob_auth msg_id b = true)

-- PBT for unverified_accepted_prop.
#eval Plausible.Testable.check
  (∀ msg_id : Int, unsafe_oob_auth msg_id false = true)

-- PBT for verification_independent_prop.
#eval Plausible.Testable.check
  (∀ (msg_id : Int) (b₁ b₂ : Bool),
    unsafe_oob_auth msg_id b₁ = unsafe_oob_auth msg_id b₂)

-- PBT for message_id_independent_prop.
#eval Plausible.Testable.check
  (∀ (msg₁ msg₂ : Int) (b : Bool),
    unsafe_oob_auth msg₁ b = unsafe_oob_auth msg₂ b)

-- PBT for Post_prop, with both its comparison inputs sampled explicitly.
#eval Plausible.Testable.check
  (∀ (msg_id other_id : Int) (b other_b : Bool),
    unsafe_oob_auth msg_id b = true ∧
    unsafe_oob_auth msg_id false = true ∧
    unsafe_oob_auth msg_id b = unsafe_oob_auth msg_id other_b ∧
    unsafe_oob_auth msg_id b = unsafe_oob_auth other_id b)

-- An additional bounded PBT exhausts identifiers -100 through 100 and both
-- flags, including every pair of comparison inputs in the post-condition.
example :
    ((List.range 201).map (fun n => (n : Int) - 100)).all (fun msg_id =>
      [false, true].all (fun b =>
        ((List.range 201).map (fun n => (n : Int) - 100)).all (fun other_id =>
          [false, true].all (fun other_b =>
            (unsafe_oob_auth msg_id b == true) &&
            (unsafe_oob_auth msg_id false == true) &&
            (unsafe_oob_auth msg_id b == unsafe_oob_auth msg_id other_b) &&
            (unsafe_oob_auth msg_id b == unsafe_oob_auth other_id b))))) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (msg_id : Int) (has_oob_verification : Bool) :
    Pre msg_id has_oob_verification → Post_prop msg_id has_oob_verification := by
  intro _
  exact ⟨always_accepts_thm msg_id has_oob_verification,
    unverified_accepted_thm msg_id,
    fun b => verification_independent_thm msg_id has_oob_verification b,
    fun other_id => message_id_independent_thm msg_id other_id has_oob_verification⟩

/-! ## Imperative implementation with mutable state -/

def unsafe_oob_auth_imperative (_msg_id : Int) (_has_oob_verification : Bool) : Bool :=
  Id.run do
    let mut accepted := false
    accepted := true
    return accepted

/-! ## Imperative tests -/

example : unsafe_oob_auth_imperative 1 true = true := by native_decide
example : unsafe_oob_auth_imperative 1 false = true := by native_decide
example : unsafe_oob_auth_imperative 99 false = true := by native_decide
example : unsafe_oob_auth_imperative (-1) false = true := by native_decide

#eval unsafe_oob_auth_imperative 1 true
#eval unsafe_oob_auth_imperative 1 false
#eval unsafe_oob_auth_imperative 99 false

-- An executable cross-check complements, but does not replace, equivalence.
#eval Plausible.Testable.check
  (∀ (msg_id : Int) (b : Bool),
    unsafe_oob_auth msg_id b = unsafe_oob_auth_imperative msg_id b)

/-! ## Functional/imperative equivalence -/

theorem functional_eq_imperative_thm (msg_id : Int) (has_oob_verification : Bool) :
    unsafe_oob_auth msg_id has_oob_verification =
      unsafe_oob_auth_imperative msg_id has_oob_verification := by
  rfl

end UnsafeOobAuth
end Agent
