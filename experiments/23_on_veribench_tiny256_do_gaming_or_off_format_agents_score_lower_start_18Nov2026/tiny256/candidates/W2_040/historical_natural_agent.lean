import Mathlib
namespace Agent

/-!
# Safe bare Keybase lookup

Translation of the Python safe lookup and client acceptance check. External
identity-proof verification is represented by its supplied Boolean outcome:
only a successful verification permits returning the server's claimed key.
`Int` preserves Python's arbitrary-precision signed integer domain, and
`Option Int` distinguishes `None` from every key, including zero.

The `check` function encodes the conjunction of the Python test assertions.
Bounded property-based tests are executable evidence; all named theorems
below have independent kernel-checked proofs.
-/

namespace SafeBareKeybaseLookup

/-! ## Functional implementation -/

def safe_bare_lookup (server_key : Int) (external_proofs_valid : Bool) : Option Int :=
  if external_proofs_valid then some server_key else none

def client_accepts (server_key : Int) (proofs_valid : Bool) : Bool :=
  (safe_bare_lookup server_key proofs_valid).isSome

/-- Boolean encoding of the assertion successes in Python's `check`.
As in Python, only the first four assertions use the supplied candidate;
the remaining assertions exercise `client_accepts` itself. -/
def check (candidate : Int → Bool → Option Int) : Bool :=
  (candidate 1234 true == some 1234) &&
  (candidate 1234 false == none) &&
  (candidate 0 true == some 0) &&
  (candidate 9999 false == none) &&
  (client_accepts 100 true == true) &&
  (client_accepts 9999 false == false) &&
  ([0, 1, 100, 9999] : List Int).all (fun k =>
    (client_accepts k true == true) && (client_accepts k false == false))

/-! ## Unit tests (including all Python assertions) -/

example : safe_bare_lookup 1234 true = some 1234 := by native_decide
example : safe_bare_lookup 1234 false = none := by native_decide
example : safe_bare_lookup 0 true = some 0 := by native_decide
example : safe_bare_lookup 9999 false = none := by native_decide
example : client_accepts 100 true = true := by native_decide
example : client_accepts 9999 false = false := by native_decide
example : ([0, 1, 100, 9999] : List Int).all (fun k =>
    (client_accepts k true == true) && (client_accepts k false == false)) = true := by
  native_decide
example : check safe_bare_lookup = true := by native_decide
example : safe_bare_lookup (-1234) true = some (-1234) := by native_decide
example : safe_bare_lookup (-1234) false = none := by native_decide

#eval safe_bare_lookup 1234 true
#eval safe_bare_lookup 1234 false
#eval safe_bare_lookup 0 true
#eval client_accepts 9999 false
#eval check safe_bare_lookup

/-! ## Preconditions and properties -/

/-- Every integer key and both proof-verification outcomes are admissible. -/
def Pre (_server_key : Int) (_proofs_valid : Bool) : Prop := True

/-- Successful verification returns the original key without alteration. -/
def valid_proofs_prop (k : Int) (b : Bool) : Prop :=
  b = true → safe_bare_lookup k b = some k

theorem valid_proofs_thm (k : Int) (b : Bool) : valid_proofs_prop k b := by
  cases b <;> simp [valid_proofs_prop, safe_bare_lookup]

/-- Failed verification rejects the claimed key. -/
def invalid_proofs_prop (k : Int) (b : Bool) : Prop :=
  b = false → safe_bare_lookup k b = none

theorem invalid_proofs_thm (k : Int) (b : Bool) : invalid_proofs_prop k b := by
  cases b <;> simp [invalid_proofs_prop, safe_bare_lookup]

/-- A key is returned exactly when proofs pass, and it is exactly the supplied key. -/
def returned_key_prop (k : Int) (b : Bool) : Prop :=
  ∀ returnedKey : Int,
    safe_bare_lookup k b = some returnedKey ↔ b = true ∧ returnedKey = k

theorem returned_key_thm (k : Int) (b : Bool) : returned_key_prop k b := by
  cases b <;> simp [returned_key_prop, safe_bare_lookup, eq_comm]

/-- Absence of a key is equivalent to unsuccessful verification. -/
def rejection_prop (k : Int) (b : Bool) : Prop :=
  safe_bare_lookup k b = none ↔ b = false

theorem rejection_thm (k : Int) (b : Bool) : rejection_prop k b := by
  cases b <;> simp [rejection_prop, safe_bare_lookup]

/-- Acceptance depends only on proof validity, not on the integer's value. -/
def acceptance_prop (k : Int) (b : Bool) : Prop :=
  client_accepts k b = b

theorem acceptance_thm (k : Int) (b : Bool) : acceptance_prop k b := by
  cases b <;> simp [acceptance_prop, client_accepts, safe_bare_lookup]

/-! ## Postcondition -/

def Post_prop (k : Int) (b : Bool) : Prop :=
  valid_proofs_prop k b ∧
  invalid_proofs_prop k b ∧
  returned_key_prop k b ∧
  rejection_prop k b ∧
  acceptance_prop k b

/-! ## Bounded property-based tests

Exhaust all keys in [-32, 32], additional signed/public-example keys, and
both Boolean inputs. For returned-key characterization, also exhaust the
same bounded set of proposed return values. These are Boolean counterparts
of the properties, not proofs of their universal statements.
-/

def pbtKeys : List Int :=
  (List.range 65).map (fun n => (n : Int) - 32) ++
    [-9999, -1234, 100, 1234, 9999]

def pbtFlags : List Bool := [false, true]

-- PBT for valid_proofs_prop: executable implication.
example : pbtKeys.all (fun k => pbtFlags.all (fun b =>
    (!b) || (safe_bare_lookup k b == some k))) = true := by
  native_decide

-- PBT for invalid_proofs_prop: executable implication.
example : pbtKeys.all (fun k => pbtFlags.all (fun b =>
    b || (safe_bare_lookup k b == none))) = true := by
  native_decide

-- PBT for returned_key_prop, including unequal proposed return keys.
example : pbtKeys.all (fun k => pbtFlags.all (fun b =>
    pbtKeys.all (fun returnedKey =>
      (safe_bare_lookup k b == some returnedKey) ==
        (b && (returnedKey == k))))) = true := by
  native_decide

-- PBT for rejection_prop.
example : pbtKeys.all (fun k => pbtFlags.all (fun b =>
    (safe_bare_lookup k b == none) == (!b))) = true := by
  native_decide

-- PBT for acceptance_prop.
example : pbtKeys.all (fun k => pbtFlags.all (fun b =>
    client_accepts k b == b)) = true := by
  native_decide

/-- Executable bounded counterpart of the full postcondition. -/
def postCheck (k : Int) (b : Bool) : Bool :=
  ((!b) || (safe_bare_lookup k b == some k)) &&
  (b || (safe_bare_lookup k b == none)) &&
  pbtKeys.all (fun returnedKey =>
    (safe_bare_lookup k b == some returnedKey) == (b && (returnedKey == k))) &&
  ((safe_bare_lookup k b == none) == (!b)) &&
  (client_accepts k b == b)

-- PBT for Post_prop. Pre is True, so no generated inputs are discarded.
example : pbtKeys.all (fun k => pbtFlags.all (postCheck k)) = true := by
  native_decide

#eval pbtKeys.all (fun k => pbtFlags.all (postCheck k))

/-! ## Correctness -/

theorem correctness_thm (k : Int) (b : Bool) : Pre k b → Post_prop k b := by
  intro _
  exact ⟨valid_proofs_thm k b, invalid_proofs_thm k b,
    returned_key_thm k b, rejection_thm k b, acceptance_thm k b⟩

/-! ## Imperative implementation -/

def safe_bare_lookup_imperative (server_key : Int)
    (external_proofs_valid : Bool) : Option Int := Id.run do
  let mut result : Option Int := none
  if external_proofs_valid then
    result := some server_key
  return result

def client_accepts_imperative (server_key : Int) (proofs_valid : Bool) : Bool := Id.run do
  let mut accepted := false
  let result := safe_bare_lookup_imperative server_key proofs_valid
  if result.isSome then
    accepted := true
  return accepted

/-! ## Imperative tests -/

example : safe_bare_lookup_imperative 1234 true = some 1234 := by native_decide
example : safe_bare_lookup_imperative 1234 false = none := by native_decide
example : safe_bare_lookup_imperative 0 true = some 0 := by native_decide
example : safe_bare_lookup_imperative 9999 false = none := by native_decide
example : client_accepts_imperative 100 true = true := by native_decide
example : client_accepts_imperative 9999 false = false := by native_decide
example : ([0, 1, 100, 9999] : List Int).all (fun k =>
    (client_accepts_imperative k true == true) &&
    (client_accepts_imperative k false == false)) = true := by native_decide
example : check safe_bare_lookup_imperative = true := by native_decide

-- Bounded equivalence tests exercise both implementations at every sampled input.
example : pbtKeys.all (fun k => pbtFlags.all (fun b =>
    (safe_bare_lookup k b == safe_bare_lookup_imperative k b) &&
    (client_accepts k b == client_accepts_imperative k b))) = true := by
  native_decide

#eval safe_bare_lookup_imperative 1234 true
#eval safe_bare_lookup_imperative 9999 false
#eval client_accepts_imperative 0 true
#eval check safe_bare_lookup_imperative

/-! ## Functional/imperative equivalence -/

theorem lookup_equivalence_thm (k : Int) (b : Bool) :
    safe_bare_lookup k b = safe_bare_lookup_imperative k b := by
  cases b <;> rfl

theorem client_equivalence_thm (k : Int) (b : Bool) :
    client_accepts k b = client_accepts_imperative k b := by
  cases b <;> rfl

end SafeBareKeybaseLookup
end Agent
