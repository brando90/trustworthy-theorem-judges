import Mathlib
namespace Agent

/-!
# Safe service authorization (OKWS privilege separation)

Translation of `safe_service_auth`: a token-to-query whitelist gates database
lookup. Unknown tokens and disallowed queries return `none`; authorized queries
return the database lookup, which can itself be `none`.

Python's arbitrary-precision integer keys are modeled by `Int`, and its optional
string result by `Option String`. Finite dictionaries are association lists with
first-binding lookup. A Python dictionary is represented by its distinct-key
entries in any order. Duplicate-key lists also have a well-defined interpretation
(the first binding wins), so no validity assumption is needed for the proofs.
Query lists may contain duplicates, and all integer keys, including negatives,
are admitted. Strings, including the empty string, are returned unchanged.

The examples and bounded property-based tests use `native_decide` only as tests.
All named theorems have ordinary kernel-checked proofs.
-/

namespace UnsafeServiceAuthSafe

abbrev Permissions := List (Int × List Int)
abbrev Database := List (Int × String)

/-- The observable dictionary operation corresponding to Python's `dict.get`. -/
def lookup {α : Type} (key : Int) : List (Int × α) → Option α
  | [] => none
  | (k, value) :: rest => if key = k then some value else lookup key rest

/-- Functional translation: the database is consulted only after authorization. -/
def safe_service_auth (token query_id : Int) (allowed : Permissions)
    (db : Database) : Option String :=
  match lookup token allowed with
  | none => none
  | some queries =>
      if query_id ∈ queries then lookup query_id db else none

/-! ## Unit tests and the original Python check harness -/

def testDb : Database :=
  [(1, "alice@example.com"), (2, "secret_password_hash"), (3, "user_profile")]

def testPerm : Permissions := [(100, [1, 3]), (200, [2])]

def check (candidate : Int → Int → Permissions → Database → Option String) : Bool :=
  (candidate 100 1 testPerm testDb == some "alice@example.com") &&
  (candidate 100 3 testPerm testDb == some "user_profile") &&
  (candidate 100 2 testPerm testDb == none) &&
  (candidate 999 1 testPerm testDb == none) &&
  (candidate 0 1 testPerm testDb == none) &&
  (candidate 200 2 testPerm testDb == some "secret_password_hash") &&
  (candidate 200 1 testPerm testDb == none) &&
  (candidate 100 1 [] testDb == none) &&
  (candidate 100 99 testPerm testDb == none)

example : safe_service_auth 100 1 testPerm testDb = some "alice@example.com" := by
  native_decide
example : safe_service_auth 100 3 testPerm testDb = some "user_profile" := by
  native_decide
example : safe_service_auth 100 2 testPerm testDb = none := by native_decide
example : safe_service_auth 999 1 testPerm testDb = none := by native_decide
example : safe_service_auth 0 1 testPerm testDb = none := by native_decide
example : safe_service_auth 200 2 testPerm testDb = some "secret_password_hash" := by
  native_decide
example : safe_service_auth 200 1 testPerm testDb = none := by native_decide
example : safe_service_auth 100 1 [] testDb = none := by native_decide
example : safe_service_auth 100 99 testPerm testDb = none := by native_decide

-- The source's query 99 is not actually whitelisted. This additionally tests
-- a genuinely authorized query that is absent from the database.
example : safe_service_auth 100 99 [(100, [99])] testDb = none := by native_decide
example : safe_service_auth 100 1 [(100, [])] testDb = none := by native_decide
example : safe_service_auth (-7) (-2) [(-7, [-2, -2])] [(-2, "")] = some "" := by
  native_decide
example : check safe_service_auth = true := by native_decide

#eval check safe_service_auth
#eval safe_service_auth 100 1 testPerm testDb
#eval safe_service_auth 100 2 testPerm testDb
#eval safe_service_auth 100 99 [(100, [99])] testDb

/-! ## Precondition and semantic properties -/

/-- The source is total on all inputs of its annotated types. -/
def Pre (_token _query_id : Int) (_allowed : Permissions) (_db : Database) : Prop := True

/-- Unknown services are denied, regardless of the database. -/
def unknown_token_prop (token query_id : Int) (allowed : Permissions)
    (db : Database) : Prop :=
  lookup token allowed = none → safe_service_auth token query_id allowed db = none

theorem unknown_token_thm (token query_id : Int) (allowed : Permissions)
    (db : Database) : unknown_token_prop token query_id allowed db := by
  intro h
  simp [safe_service_auth, h]

/-- A known token cannot issue any query outside its whitelist. -/
def unauthorized_query_prop (token query_id : Int) (allowed : Permissions)
    (db : Database) : Prop :=
  ∀ queries, lookup token allowed = some queries → query_id ∉ queries →
    safe_service_auth token query_id allowed db = none

theorem unauthorized_query_thm (token query_id : Int) (allowed : Permissions)
    (db : Database) : unauthorized_query_prop token query_id allowed db := by
  intro queries htoken hquery
  simp [safe_service_auth, htoken, hquery]

/-- Authorization returns exactly `db.get`, not an invented or altered value. -/
def authorized_access_prop (token query_id : Int) (allowed : Permissions)
    (db : Database) : Prop :=
  ∀ queries, lookup token allowed = some queries → query_id ∈ queries →
    safe_service_auth token query_id allowed db = lookup query_id db

theorem authorized_access_thm (token query_id : Int) (allowed : Permissions)
    (db : Database) : authorized_access_prop token query_id allowed db := by
  intro queries htoken hquery
  simp [safe_service_auth, htoken, hquery]

/-- An empty permission table denies every token and query. -/
def empty_permissions_prop (token query_id : Int) (db : Database) : Prop :=
  safe_service_auth token query_id [] db = none

theorem empty_permissions_thm (token query_id : Int) (db : Database) :
    empty_permissions_prop token query_id db := by
  simp [empty_permissions_prop, safe_service_auth, lookup]

/-- A missing database entry cannot become a successful result, even if authorized. -/
def missing_query_prop (token query_id : Int) (allowed : Permissions)
    (db : Database) : Prop :=
  lookup query_id db = none → safe_service_auth token query_id allowed db = none

theorem missing_query_thm (token query_id : Int) (allowed : Permissions)
    (db : Database) : missing_query_prop token query_id allowed db := by
  intro hdb
  unfold safe_service_auth
  cases htoken : lookup token allowed with
  | none => rfl
  | some queries =>
      by_cases hquery : query_id ∈ queries <;> simp [hquery, hdb]

/-- Exact success criterion, including both authorization and the returned value. -/
def success_iff_prop (token query_id : Int) (allowed : Permissions)
    (db : Database) (value : String) : Prop :=
  safe_service_auth token query_id allowed db = some value ↔
    ∃ queries, lookup token allowed = some queries ∧ query_id ∈ queries ∧
      lookup query_id db = some value

theorem success_iff_thm (token query_id : Int) (allowed : Permissions)
    (db : Database) (value : String) : success_iff_prop token query_id allowed db value := by
  unfold success_iff_prop safe_service_auth
  cases htoken : lookup token allowed with
  | none => simp
  | some queries =>
      by_cases hquery : query_id ∈ queries <;> simp [hquery]

/-- Exact failure criterion: unknown service, disallowed query, or missing row. -/
def denial_iff_prop (token query_id : Int) (allowed : Permissions)
    (db : Database) : Prop :=
  safe_service_auth token query_id allowed db = none ↔
    lookup token allowed = none ∨
      (∃ queries, lookup token allowed = some queries ∧ query_id ∉ queries) ∨
      lookup query_id db = none

theorem denial_iff_thm (token query_id : Int) (allowed : Permissions)
    (db : Database) : denial_iff_prop token query_id allowed db := by
  unfold denial_iff_prop safe_service_auth
  cases htoken : lookup token allowed with
  | none => simp
  | some queries =>
      by_cases hquery : query_id ∈ queries <;> simp [hquery]

/-- The postcondition collects all branches and the exact success/failure criteria. -/
def Post_prop (token query_id : Int) (allowed : Permissions) (db : Database) : Prop :=
  unknown_token_prop token query_id allowed db ∧
  unauthorized_query_prop token query_id allowed db ∧
  authorized_access_prop token query_id allowed db ∧
  empty_permissions_prop token query_id db ∧
  missing_query_prop token query_id allowed db ∧
  (∀ value, success_iff_prop token query_id allowed db value) ∧
  denial_iff_prop token query_id allowed db

/-! ## Bounded property-based tests

All named properties above are executable for finite inputs. The checks below
are their Boolean forms; the list-valued witness in the propositions is obtained
by lookup rather than by attempting to enumerate all lists.

We exhaust all permission dictionaries with keys drawn from {-1, 1}, each
whitelist being any list of length at most two over {-1, 0, 1}. We also exhaust
all databases with keys drawn from {-1, 0, 1} and values drawn from {"", "value"}.
Tokens and queries range over {-2, -1, 0, 1, 2}. Thus each four-input property is
tested on 132300 combinations, including unknown tokens, missing rows, duplicate
whitelist entries, empty tables/lists/strings, and negative integer keys.
-/

def smallKeys : List Int := [-1, 0, 1]

def smallQueryLists : List (List Int) :=
  [[]] ++ smallKeys.map (fun q => [q]) ++
    smallKeys.flatMap (fun q => smallKeys.map (fun r => [q, r]))

/-- Enumerate every distinct-key dictionary on a subset of `keys`. -/
def smallTables {α : Type} (keys : List Int) (values : List α) : List (List (Int × α)) :=
  match keys with
  | [] => [[]]
  | k :: ks =>
      (smallTables ks values).flatMap (fun rest =>
        rest :: values.map (fun value => (k, value) :: rest))

def smallPermissions : List Permissions := smallTables [-1, 1] smallQueryLists
def smallDatabases : List Database := smallTables smallKeys ["", "value"]
def sampleInts : List Int := [-2, -1, 0, 1, 2]
def sampleValues : List String := ["", "value", "not in the database"]

def allSmallInputs (p : Int → Int → Permissions → Database → Bool) : Bool :=
  sampleInts.all (fun token => sampleInts.all (fun query_id =>
    smallPermissions.all (fun allowed => smallDatabases.all (fun db =>
      p token query_id allowed db))))

/-- Executable whitelist membership, not a second authorization implementation. -/
def authorizedB (token query_id : Int) (allowed : Permissions) : Bool :=
  match lookup token allowed with
  | none => false
  | some queries => decide (query_id ∈ queries)

def unknownTokenCheck (token query_id : Int) (allowed : Permissions) (db : Database) : Bool :=
  if lookup token allowed == none then safe_service_auth token query_id allowed db == none
  else true

def unauthorizedQueryCheck (token query_id : Int) (allowed : Permissions)
    (db : Database) : Bool :=
  match lookup token allowed with
  | none => true
  | some queries =>
      if query_id ∈ queries then true else safe_service_auth token query_id allowed db == none

def authorizedAccessCheck (token query_id : Int) (allowed : Permissions)
    (db : Database) : Bool :=
  match lookup token allowed with
  | none => true
  | some queries =>
      if query_id ∈ queries then
        safe_service_auth token query_id allowed db == lookup query_id db
      else true

def emptyPermissionsCheck (token query_id : Int) (db : Database) : Bool :=
  safe_service_auth token query_id [] db == none

def missingQueryCheck (token query_id : Int) (allowed : Permissions) (db : Database) : Bool :=
  if lookup query_id db == none then safe_service_auth token query_id allowed db == none
  else true

def successIffCheck (token query_id : Int) (allowed : Permissions)
    (db : Database) (value : String) : Bool :=
  (safe_service_auth token query_id allowed db == some value) ==
    (authorizedB token query_id allowed && (lookup query_id db == some value))

def denialIffCheck (token query_id : Int) (allowed : Permissions) (db : Database) : Bool :=
  (safe_service_auth token query_id allowed db == none) ==
    (!authorizedB token query_id allowed || (lookup query_id db == none))

/-- Bounded Boolean form of Post, including success at every sampled value. -/
def postCheck (token query_id : Int) (allowed : Permissions) (db : Database) : Bool :=
  unknownTokenCheck token query_id allowed db &&
  unauthorizedQueryCheck token query_id allowed db &&
  authorizedAccessCheck token query_id allowed db &&
  emptyPermissionsCheck token query_id db &&
  missingQueryCheck token query_id allowed db &&
  sampleValues.all (fun value => successIffCheck token query_id allowed db value) &&
  denialIffCheck token query_id allowed db

-- PBT: unknown_token_prop
example : allSmallInputs unknownTokenCheck = true := by native_decide
-- PBT: unauthorized_query_prop
example : allSmallInputs unauthorizedQueryCheck = true := by native_decide
-- PBT: authorized_access_prop
example : allSmallInputs authorizedAccessCheck = true := by native_decide
-- PBT: empty_permissions_prop
example : (sampleInts.all (fun token => sampleInts.all (fun query_id =>
    smallDatabases.all (fun db => emptyPermissionsCheck token query_id db)))) = true := by
  native_decide
-- PBT: missing_query_prop
example : allSmallInputs missingQueryCheck = true := by native_decide
-- PBT: success_iff_prop, in both directions and for matching/nonmatching values
example : allSmallInputs (fun token query_id allowed db =>
    sampleValues.all (fun value => successIffCheck token query_id allowed db value)) = true := by
  native_decide
-- PBT: denial_iff_prop, in both directions
example : allSmallInputs denialIffCheck = true := by native_decide
-- PBT: Post_prop (the full conjunction, with values bounded as above)
example : allSmallInputs postCheck = true := by native_decide
#eval allSmallInputs postCheck

/-! ## Correctness -/

theorem safe_service_auth_correct (token query_id : Int) (allowed : Permissions)
    (db : Database) : Pre token query_id allowed db → Post_prop token query_id allowed db := by
  intro _
  exact ⟨unknown_token_thm token query_id allowed db,
    unauthorized_query_thm token query_id allowed db,
    authorized_access_thm token query_id allowed db,
    empty_permissions_thm token query_id db,
    missing_query_thm token query_id allowed db,
    fun value => success_iff_thm token query_id allowed db value,
    denial_iff_thm token query_id allowed db⟩

/-! ## Imperative implementation and tests -/

/-- A mutable authorization flag gates assignment of the database result. -/
def safe_service_auth_imperative (token query_id : Int) (allowed : Permissions)
    (db : Database) : Option String := Id.run do
  let mut result : Option String := none
  let mut authorized : Bool := false
  match lookup token allowed with
  | none => pure ()
  | some queries =>
      if query_id ∈ queries then
        authorized := true
  if authorized then
    result := lookup query_id db
  return result

example : check safe_service_auth_imperative = true := by native_decide
example : safe_service_auth_imperative 100 99 [(100, [99])] testDb = none := by
  native_decide
example : safe_service_auth_imperative 100 1 [(100, [])] testDb = none := by
  native_decide
example : safe_service_auth_imperative (-7) (-2) [(-7, [-2, -2])] [(-2, "")] = some "" := by
  native_decide
#eval check safe_service_auth_imperative
#eval safe_service_auth_imperative 200 2 testPerm testDb

-- Additional bounded PBT for equivalence, independent of the proof below.
example : allSmallInputs (fun token query_id allowed db =>
    safe_service_auth token query_id allowed db ==
      safe_service_auth_imperative token query_id allowed db) = true := by
  native_decide

/-! ## Functional/imperative equivalence on the entire input domain -/

theorem functional_imperative_equiv (token query_id : Int) (allowed : Permissions)
    (db : Database) :
    safe_service_auth token query_id allowed db =
      safe_service_auth_imperative token query_id allowed db := by
  cases htoken : lookup token allowed with
  | none => simp [safe_service_auth, safe_service_auth_imperative, htoken]
  | some queries =>
      by_cases hquery : query_id ∈ queries <;>
        simp [safe_service_auth, safe_service_auth_imperative, htoken, hquery]

end UnsafeServiceAuthSafe
end Agent
