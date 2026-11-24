import Mathlib
namespace Agent

/-!
# Unsafe key server acceptance

Lean 4 formalization of the Python module `96_unsafeKeyServer`.

The Python function

```python
def unsafe_key_server_accept(server_key: int, expected_key: int) -> bool:
    return True
```

models a messaging client that encrypts a message with whatever key the central
key server hands back, *without* verifying that the server did not substitute an
attacker-controlled key (MIT 6.858 Lecture 17: Messaging Security).

The interesting content of the program is precisely that the decision is a
constant: it does not depend on either argument, so a mismatched (attacker)
key is accepted exactly as readily as the genuine one.  The theorems below
state that constancy, the three concrete test cases of `check()`, and the fact
that this behaviour is *not* the behaviour of a key-verifying client.
-/

namespace UnsafeKeyServer

/-! ## Functional implementation -/

/-- The vulnerable acceptance check: returns `true` no matter what key the
server returned and no matter which key was expected. -/
def unsafeKeyServerAccept (_serverKey _expectedKey : Int) : Bool := true

/-- The *secure* check the client should have performed: only accept the key
returned by the server when it equals the expected (out-of-band verified) key. -/
def secureKeyServerAccept (serverKey expectedKey : Int) : Bool :=
  serverKey == expectedKey

/-! ## Unit tests (mirroring Python `check()`) -/

-- normal case
example : unsafeKeyServerAccept 42 42 = true := by native_decide
-- vuln: wrong key accepted
example : unsafeKeyServerAccept 99 42 = true := by native_decide
-- vuln: attacker key accepted
example : unsafeKeyServerAccept 0 42 = true := by native_decide

#eval unsafeKeyServerAccept 42 42
#eval unsafeKeyServerAccept 99 42
#eval unsafeKeyServerAccept 0 42

/-! ## Pre-condition -/

/-- The Python function is total: every pair of integer keys is a legal input. -/
def Pre (_serverKey _expectedKey : Int) : Prop := True

/-! ## Properties -/

/-- The result is always `true`. -/
def alwaysAccepts_prop (serverKey expectedKey : Int) : Prop :=
  unsafeKeyServerAccept serverKey expectedKey = true

/-- The result never depends on the arguments: the function is constant. -/
def constant_prop : Prop :=
  ∀ s₁ e₁ s₂ e₂ : Int,
    unsafeKeyServerAccept s₁ e₁ = unsafeKeyServerAccept s₂ e₂

/-- The vulnerability: a key different from the expected one is still accepted. -/
def acceptsSubstitutedKey_prop : Prop :=
  ∀ s e : Int, s ≠ e → unsafeKeyServerAccept s e = true

/-- The function is never `false`, i.e. no key is ever rejected. -/
def neverRejects_prop (serverKey expectedKey : Int) : Prop :=
  unsafeKeyServerAccept serverKey expectedKey ≠ false

/-- The unsafe check is *not* the secure check: it differs on some input, so it
cannot be implementing key verification. -/
def notSecure_prop : Prop :=
  ¬ (∀ s e : Int, unsafeKeyServerAccept s e = secureKeyServerAccept s e)

/-- On matching keys the unsafe check happens to agree with the secure one;
the two only diverge when the server substituted a key. -/
def agreesOnMatch_prop : Prop :=
  ∀ s e : Int, s = e → unsafeKeyServerAccept s e = secureKeyServerAccept s e

/-- The three assertions of the Python `check()` function. -/
def checkTests_prop : Prop :=
  unsafeKeyServerAccept 42 42 = true ∧
  unsafeKeyServerAccept 99 42 = true ∧
  unsafeKeyServerAccept 0 42 = true

/-! ## Theorems -/

theorem alwaysAccepts_thm (serverKey expectedKey : Int) :
    alwaysAccepts_prop serverKey expectedKey := by sorry

theorem constant_thm : constant_prop := by sorry

theorem acceptsSubstitutedKey_thm : acceptsSubstitutedKey_prop := by sorry

theorem neverRejects_thm (serverKey expectedKey : Int) :
    neverRejects_prop serverKey expectedKey := by sorry

theorem notSecure_thm : notSecure_prop := by sorry

theorem agreesOnMatch_thm : agreesOnMatch_prop := by sorry

theorem checkTests_thm : checkTests_prop := by sorry

/-! ## Post-condition and correctness -/

/-- Full post-condition: everything that holds of the returned value. -/
def Post_prop (serverKey expectedKey : Int) : Prop :=
  alwaysAccepts_prop serverKey expectedKey ∧
  neverRejects_prop serverKey expectedKey ∧
  constant_prop ∧
  acceptsSubstitutedKey_prop ∧
  agreesOnMatch_prop ∧
  notSecure_prop ∧
  checkTests_prop

/-- Correctness: the pre-condition implies the post-condition. -/
theorem correctness_thm (serverKey expectedKey : Int) :
    Pre serverKey expectedKey → Post_prop serverKey expectedKey := by sorry

/-! ## Imperative implementation -/

/-- Imperative rendering: the client stores the key it received from the server
and flips its `accepted` flag to `true` without ever comparing it against
`expectedKey`. -/
def unsafeKeyServerAcceptImp (serverKey _expectedKey : Int) : Bool := Id.run do
  let mut accepted : Bool := false
  let mut keyInUse : Int := 0
  -- the key handed back by the (possibly compromised) server is taken as-is
  keyInUse := serverKey
  -- no verification step against `expectedKey` happens here
  accepted := true
  let _ := keyInUse
  return accepted

/-! ## Imperative tests -/

example : unsafeKeyServerAcceptImp 42 42 = true := by native_decide
example : unsafeKeyServerAcceptImp 99 42 = true := by native_decide
example : unsafeKeyServerAcceptImp 0 42 = true := by native_decide

#eval unsafeKeyServerAcceptImp 42 42
#eval unsafeKeyServerAcceptImp 99 42
#eval unsafeKeyServerAcceptImp 0 42

/-! ## Equivalence of the two implementations -/

theorem funcImp_equiv_thm (serverKey expectedKey : Int) :
    unsafeKeyServerAccept serverKey expectedKey
      = unsafeKeyServerAcceptImp serverKey expectedKey := by sorry

/-- The imperative version inherits the full post-condition. -/
theorem imp_correctness_thm (serverKey expectedKey : Int) :
    Pre serverKey expectedKey → unsafeKeyServerAcceptImp serverKey expectedKey = true := by sorry

end UnsafeKeyServer
end Agent
