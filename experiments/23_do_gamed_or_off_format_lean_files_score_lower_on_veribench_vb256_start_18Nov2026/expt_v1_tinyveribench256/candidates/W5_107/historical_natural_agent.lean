import Mathlib
namespace Agent

/-!
# Unsafe service authorization (MIT 6.858, Lecture 5 / OKWS)

This is a translation of `unsafe_service_auth` and its six Python checks.
`Int` models arbitrary Python integers, `Std.HashMap Int String` models a finite
Python dictionary (including replacement of an existing key), and `Option String`
models `str | None`. In particular, an empty string is a successful result, not
`None`. Database lookup is read-only.

The token is deliberately unused. The specification describes the vulnerability,
not a repaired authorization mechanism: every caller, including zero, negative,
and unknown tokens, can retrieve every present row. A missing query is the only
reason to return `none`; it is not an authorization failure. Token independence
and the present-row theorem together express the failure of service separation.
All theorems quantify over arbitrary integers, strings, and finite databases.
-/

namespace UnsafeServiceAuth

abbrev Database := Std.HashMap Int String

/-- Direct translation of `return db.get(query_id)`: there is no token check. -/
def unsafe_service_auth (_token queryId : Int) (db : Database) : Option String :=
  db[queryId]?

/-- The database in the Python test harness. -/
def sampleDb : Database :=
  (({} : Database).insert 1 "alice@example.com").insert 2 "secret_password_hash"
    |>.insert 3 "user_profile"

/-- Executable translation of the six assertions in Python's `check`. -/
def check (candidate : Int → Int → Database → Option String) : Bool :=
  candidate 100 1 sampleDb == some "alice@example.com" &&
  candidate 100 2 sampleDb == some "secret_password_hash" &&
  candidate 999 3 sampleDb == some "user_profile" &&
  candidate 0 1 sampleDb == some "alice@example.com" &&
  candidate 100 99 sampleDb == none &&
  candidate 100 1 ({} : Database) == none

-- 1. Normal access.
example : unsafe_service_auth 100 1 sampleDb = some "alice@example.com" := by
  native_decide
-- 2. Cross-service password access is allowed (the vulnerability).
example : unsafe_service_auth 100 2 sampleDb = some "secret_password_hash" := by
  native_decide
-- 3. An unknown token is accepted.
example : unsafe_service_auth 999 3 sampleDb = some "user_profile" := by
  native_decide
-- 4. Even the unauthenticated token is accepted.
example : unsafe_service_auth 0 1 sampleDb = some "alice@example.com" := by
  native_decide
-- 5. Ordinary not-found behavior.
example : unsafe_service_auth 100 99 sampleDb = none := by native_decide
-- 6. An empty database.
example : unsafe_service_auth 100 1 ({} : Database) = none := by native_decide
example : check unsafe_service_auth = true := by native_decide
-- Python integers are not restricted to Nat, and a stored empty string is data.
example : unsafe_service_auth (-999) (-7) (({} : Database).insert (-7) "") =
    some "" := by native_decide

#eval check unsafe_service_auth
#eval unsafe_service_auth 100 2 sampleDb
#eval unsafe_service_auth 100 99 sampleDb

/-- Every well-typed call is admissible; no token or query is filtered. -/
def Pre (_token _queryId : Int) (_db : Database) : Prop := True

/-- The output is precisely the optional database lookup. -/
def lookup_prop (token queryId : Int) (db : Database) : Prop :=
  unsafe_service_auth token queryId db = db[queryId]?

theorem lookup_thm (token queryId : Int) (db : Database) :
    lookup_prop token queryId db := by
  rfl

/-- Replacing the caller's token, arbitrarily, never changes the result. -/
def token_independent_prop (token queryId : Int) (db : Database) : Prop :=
  ∀ otherToken : Int,
    unsafe_service_auth token queryId db = unsafe_service_auth otherToken queryId db

theorem token_independent_thm (token queryId : Int) (db : Database) :
    token_independent_prop token queryId db := by
  intro otherToken
  rfl

/-- Every stored row is returned to every token, with its exact stored value. -/
def present_prop (token queryId : Int) (db : Database) : Prop :=
  ∀ h : queryId ∈ db,
    unsafe_service_auth token queryId db = some (db[queryId]'h)

theorem present_thm (token queryId : Int) (db : Database) :
    present_prop token queryId db := by
  intro h
  exact Std.HashMap.getElem?_eq_some_getElem h

/-- `none` means precisely that the query key is absent, not that access was denied. -/
def not_found_prop (token queryId : Int) (db : Database) : Prop :=
  unsafe_service_auth token queryId db = none ↔ queryId ∉ db

theorem not_found_thm (token queryId : Int) (db : Database) :
    not_found_prop token queryId db := by
  constructor
  · intro hnone hmem
    have hsome := Std.HashMap.getElem?_eq_some_getElem (m := db) hmem
    change db[queryId]? = none at hnone
    rw [hnone] at hsome
    cases hsome
  · intro hmissing
    exact Std.HashMap.getElem?_eq_none hmissing

/-- Empty databases return `none` for every query and every token. -/
def empty_prop (token queryId : Int) : Prop :=
  unsafe_service_auth token queryId ({} : Database) = none

theorem empty_thm (token queryId : Int) : empty_prop token queryId := by
  exact Std.HashMap.getElem?_empty

/-- An arbitrary stored string is accessible, even when it replaces an old row.
There is no restriction on which token may read the inserted query. -/
def inserted_row_prop (token queryId : Int) (db : Database) : Prop :=
  ∀ value : String,
    unsafe_service_auth token queryId (db.insert queryId value) = some value

theorem inserted_row_thm (token queryId : Int) (db : Database) :
    inserted_row_prop token queryId db := by
  intro value
  exact Std.HashMap.getElem?_insert_self

/-- Full behavioral postcondition, including the intentional security defect. -/
def Post_prop (token queryId : Int) (db : Database) : Prop :=
  lookup_prop token queryId db ∧
  token_independent_prop token queryId db ∧
  present_prop token queryId db ∧
  not_found_prop token queryId db ∧
  empty_prop token queryId ∧
  inserted_row_prop token queryId db

/-! ## Bounded property-based tests

These tests exhaust all insertion histories of length at most two over the key
and value alphabets below, and also use the original three-row database. Histories
include repeated keys, so overwriting is exercised as well as empty databases,
missing queries, and stored empty strings. Caller samples include negative, zero,
known, unknown, and very large integers. These finite tests are evidence only;
the proofs above and below are unrestricted and do not depend on these tests.
-/

def pbtTokens : List Int :=
  [-1000, -1, 0, 1, 100, 999, 100000000000000000000]

def pbtKeys : List Int := [-1, 0, 1, 2, 3]

def pbtQueries : List Int := [-7, -1, 0, 1, 2, 3, 99, 100000000000000000000]

def pbtValues : List String := ["", "public", "secret_password_hash", "user_profile"]

def pbtRows : List (Int × String) :=
  pbtKeys.flatMap fun key => pbtValues.map fun value => (key, value)

def pbtDatabases : List Database :=
  [({} : Database), sampleDb] ++
  pbtRows.map (fun row => ({} : Database).insert row.1 row.2) ++
  pbtRows.flatMap (fun first => pbtRows.map fun second =>
    (({} : Database).insert first.1 first.2).insert second.1 second.2)

def allInputs (test : Int → Int → Database → Bool) : Bool :=
  pbtDatabases.all fun db =>
    pbtTokens.all fun token => pbtQueries.all fun queryId => test token queryId db

/-- Executable form of `lookup_prop`. -/
def lookupCheck (token queryId : Int) (db : Database) : Bool :=
  unsafe_service_auth token queryId db == db[queryId]?

/-- Bounded executable form of the universal token in `token_independent_prop`. -/
def tokenIndependentCheck (token queryId : Int) (db : Database) : Bool :=
  pbtTokens.all fun otherToken =>
    unsafe_service_auth token queryId db == unsafe_service_auth otherToken queryId db

/-- Executable form of `present_prop`: `getD` agrees with the stored value under
`contains`; its fallback is never used when the implication's premise holds. -/
def presentCheck (token queryId : Int) (db : Database) : Bool :=
  if db.contains queryId then
    unsafe_service_auth token queryId db == some (db.getD queryId "")
  else true

/-- Executable equivalence corresponding to `not_found_prop`. -/
def notFoundCheck (token queryId : Int) (db : Database) : Bool :=
  (unsafe_service_auth token queryId db == none) == (!db.contains queryId)

/-- Executable form of `empty_prop`. -/
def emptyCheck (token queryId : Int) : Bool :=
  unsafe_service_auth token queryId ({} : Database) == none

/-- Bounded executable form of the universal string in `inserted_row_prop`. -/
def insertedRowCheck (token queryId : Int) (db : Database) : Bool :=
  pbtValues.all fun value =>
    unsafe_service_auth token queryId (db.insert queryId value) == some value

/-- Executable conjunction corresponding to `Post_prop`. -/
def postCheck (token queryId : Int) (db : Database) : Bool :=
  lookupCheck token queryId db &&
  tokenIndependentCheck token queryId db &&
  presentCheck token queryId db &&
  notFoundCheck token queryId db &&
  emptyCheck token queryId &&
  insertedRowCheck token queryId db

-- A separate PBT for each property and for the entire postcondition.
example : allInputs lookupCheck = true := by native_decide
example : allInputs tokenIndependentCheck = true := by native_decide
example : allInputs presentCheck = true := by native_decide
example : allInputs notFoundCheck = true := by native_decide
example : (pbtTokens.all fun token =>
    pbtQueries.all fun queryId => emptyCheck token queryId) = true := by native_decide
example : allInputs insertedRowCheck = true := by native_decide
example : allInputs postCheck = true := by native_decide

#eval ("PBT database histories", pbtDatabases.length)
#eval ("All bounded postcondition checks passed", allInputs postCheck)

/-- Correctness means faithful unsafe behavior, not enforcement of authorization. -/
theorem correctness_thm (token queryId : Int) (db : Database) :
    Pre token queryId db → Post_prop token queryId db := by
  intro _
  exact ⟨lookup_thm token queryId db,
    token_independent_thm token queryId db,
    present_thm token queryId db,
    not_found_thm token queryId db,
    empty_thm token queryId,
    inserted_row_thm token queryId db⟩

/-- Imperative read-only lookup with a mutable result. The token remains unused. -/
def unsafe_service_auth_imperative (_token queryId : Int) (db : Database) :
    Option String := Id.run do
  let mut result : Option String := none
  if let some value := db[queryId]? then
    result := some value
  return result

-- The imperative version passes all six source assertions too.
example : unsafe_service_auth_imperative 100 1 sampleDb =
    some "alice@example.com" := by native_decide
example : unsafe_service_auth_imperative 100 2 sampleDb =
    some "secret_password_hash" := by native_decide
example : unsafe_service_auth_imperative 999 3 sampleDb =
    some "user_profile" := by native_decide
example : unsafe_service_auth_imperative 0 1 sampleDb =
    some "alice@example.com" := by native_decide
example : unsafe_service_auth_imperative 100 99 sampleDb = none := by native_decide
example : unsafe_service_auth_imperative 100 1 ({} : Database) = none := by
  native_decide
example : check unsafe_service_auth_imperative = true := by native_decide
example : unsafe_service_auth_imperative (-999) (-7)
    (({} : Database).insert (-7) "") = some "" := by native_decide

#eval check unsafe_service_auth_imperative
#eval unsafe_service_auth_imperative 0 2 sampleDb

-- Bounded equivalence test, in addition to the unrestricted proof below.
example : allInputs (fun token queryId db =>
    unsafe_service_auth token queryId db ==
      unsafe_service_auth_imperative token queryId db) = true := by native_decide

/-- Equality as functions: both implementations agree on every possible input. -/
theorem functional_eq_imperative_thm :
    unsafe_service_auth = unsafe_service_auth_imperative := by
  funext token queryId db
  cases h : db[queryId]? <;>
    simp [unsafe_service_auth, unsafe_service_auth_imperative, h]

end UnsafeServiceAuth
end Agent
