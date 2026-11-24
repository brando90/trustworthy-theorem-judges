import Mathlib
namespace Agent

/-!
# Unsafe per-user ticket lookup

Translation of the MIT 6.858 / OKWS example. A service fetches the requested
user's record without checking either the service token or the per-user ticket.
This file describes the vulnerability; it does not repair it or assume that a
ticket is valid. In particular, no relationship to the user whose HTTP request
is being handled is imposed.

Python's unbounded integers are modeled by `Int`, finite dictionaries by
`Std.HashMap Int String`, and `str | None` by `Option String`. Hash-map insertion
has the usual dictionary overwrite semantics. All finite dictionaries, integer
credentials, and user IDs are admissible, including negative integers.

The named theorems use kernel-checked proofs. `native_decide` is used only in
executable examples, including exhaustive bounded property-based tests.
-/

namespace UnsafePerUserTicket

abbrev Database := Std.HashMap Int String

/-- The original function: `return db.get(user_id)`. Both credentials are ignored. -/
def unsafePerUserTicket (_serviceToken userId _ticket : Int)
    (db : Database) : Option String :=
  db[userId]?

/-! ## Unit tests: the five assertions from Python -/

def sampleDB : Database :=
  ((∅ : Database).insert 1 "alice_profile").insert 2 "bob_profile"
    |>.insert 3 "carol_profile"

/-- Executable counterpart of the Python `check` function. -/
def check (candidate : Int → Int → Int → Database → Option String) : Bool :=
  candidate 100 1 999 sampleDB == some "alice_profile" &&
  candidate 100 2 0 sampleDB == some "bob_profile" &&
  candidate 100 3 777 sampleDB == some "carol_profile" &&
  candidate 100 99 999 sampleDB == none &&
  candidate 100 1 999 (∅ : Database) == none

example : unsafePerUserTicket 100 1 999 sampleDB = some "alice_profile" := by
  native_decide
example : unsafePerUserTicket 100 2 0 sampleDB = some "bob_profile" := by
  native_decide
example : unsafePerUserTicket 100 3 777 sampleDB = some "carol_profile" := by
  native_decide
example : unsafePerUserTicket 100 99 999 sampleDB = none := by
  native_decide
example : unsafePerUserTicket 100 1 999 (∅ : Database) = none := by
  native_decide
example : check unsafePerUserTicket = true := by native_decide

#eval unsafePerUserTicket 100 1 999 sampleDB
#eval unsafePerUserTicket 100 2 0 sampleDB
#eval unsafePerUserTicket 100 3 777 sampleDB
#eval unsafePerUserTicket 100 99 999 sampleDB
#eval unsafePerUserTicket 100 1 999 (∅ : Database)
#eval check unsafePerUserTicket

/-! ## Preconditions and properties -/

/-- Python performs no credential validation and requires no extra condition. -/
def Pre (_serviceToken _userId _ticket : Int) (_db : Database) : Prop := True

/-- The return value is exactly the optional dictionary lookup. -/
def lookup_prop (s u t : Int) (db : Database) : Prop :=
  unsafePerUserTicket s u t db = db[u]?

theorem lookup_thm (s u t : Int) (db : Database) : lookup_prop s u t db := by sorry

/-- Changing a ticket cannot change the result, even for arbitrary forged tickets. -/
def ticket_ignored_prop (s u t otherTicket : Int) (db : Database) : Prop :=
  unsafePerUserTicket s u t db = unsafePerUserTicket s u otherTicket db

theorem ticket_ignored_thm (s u t otherTicket : Int) (db : Database) :
    ticket_ignored_prop s u t otherTicket db := by sorry

/-- The Python body also does not inspect the service token. -/
def service_ignored_prop (s otherService u t : Int) (db : Database) : Prop :=
  unsafePerUserTicket s u t db = unsafePerUserTicket otherService u t db

theorem service_ignored_thm (s otherService u t : Int) (db : Database) :
    service_ignored_prop s otherService u t db := by sorry

/-- Any stored record is returned for every credential pair: no valid ticket is needed. -/
def present_prop (s u t : Int) (db : Database) (value : String) : Prop :=
  db[u]? = some value → unsafePerUserTicket s u t db = some value

theorem present_thm (s u t : Int) (db : Database) (value : String) :
    present_prop s u t db value := by sorry

/-- `None` means exactly that the user is absent, not that authorization failed. -/
def missing_prop (s u t : Int) (db : Database) : Prop :=
  unsafePerUserTicket s u t db = none ↔ u ∉ db

theorem missing_thm (s u t : Int) (db : Database) : missing_prop s u t db := by sorry

/-- An empty database always returns `None`, independently of both credentials. -/
def empty_prop (s u t : Int) : Prop :=
  unsafePerUserTicket s u t (∅ : Database) = none

theorem empty_thm (s u t : Int) : empty_prop s u t := by sorry

/-- Inserting or overwriting a user's record exposes it with every possible ticket. -/
def inserted_user_prop (s u t : Int) (db : Database) (value : String) : Prop :=
  unsafePerUserTicket s u t (db.insert u value) = some value

theorem inserted_user_thm (s u t : Int) (db : Database) (value : String) :
    inserted_user_prop s u t db value := by sorry

/-- Repeated queries can read an arbitrary list of users with one unchanged ticket. -/
def bulk_read_prop (s t : Int) (users : List Int) (db : Database) : Prop :=
  users.map (fun u => unsafePerUserTicket s u t db) =
    users.map (fun u => db[u]?)

theorem bulk_read_thm (s t : Int) (users : List Int) (db : Database) :
    bulk_read_prop s t users db := by sorry

/-! ## Postcondition -/

/-- Full behavioral specification, with no credential-validity assumption. -/
def Post_prop (s u t : Int) (db : Database) : Prop :=
  lookup_prop s u t db ∧
  (∀ otherTicket, ticket_ignored_prop s u t otherTicket db) ∧
  (∀ otherService, service_ignored_prop s otherService u t db) ∧
  (∀ value, present_prop s u t db value) ∧
  missing_prop s u t db ∧
  empty_prop s u t ∧
  (∀ value, inserted_user_prop s u t db value) ∧
  (∀ users, bulk_read_prop s t users db)

/-! ## Bounded property-based tests

Hash maps do not need a Plausible sampler: these tests exhaust Cartesian
products of explicit finite domains. Dictionaries vary over empty maps,
singletons, every two-key/two-value combination in the small domains, an
overwritten key, and the original example. Inputs include absent and negative
IDs, invalid/forged credentials, and empty/Unicode strings.

Each `_prop` has its own executable Boolean check below. For universally
quantified components of `Post_prop`, the bounded test enumerates the bound
variable too. The theorem statements above and below remain unrestricted.
-/

def testUserIds : List Int := [-3, -1, 0, 1, 2, 3, 99]
def testCredentials : List Int := [-1, 0, 100, 777, 999]
def testKeys : List Int := [-1, 0, 1]
def testValues : List String := ["", "bob_profile", "λ-data"]

def testDBs : List Database :=
  [∅, sampleDB, ((∅ : Database).insert 1 "old").insert 1 "new"] ++
  testKeys.flatMap (fun k => testValues.map (fun v => (∅ : Database).insert k v)) ++
  testKeys.flatMap (fun k₁ => testKeys.flatMap (fun k₂ =>
    testValues.flatMap (fun v₁ => testValues.map (fun v₂ =>
      ((∅ : Database).insert k₁ v₁).insert k₂ v₂))))

def testUserLists : List (List Int) :=
  [[], testUserIds, [1, 2, 3], [99, -1, 1, 1]] ++
  testKeys.flatMap (fun u => testKeys.map (fun v => [u, v]))

/-- Exhaust all database, service-token, user-ID, and ticket combinations. -/
def forAllCalls (p : Int → Int → Int → Database → Bool) : Bool :=
  testDBs.all (fun db => testCredentials.all (fun s => testUserIds.all (fun u =>
    testCredentials.all (fun t => p s u t db))))

def lookupPBT : Bool := forAllCalls (fun s u t db =>
  unsafePerUserTicket s u t db == db[u]?)

def ticketIgnoredPBT : Bool := forAllCalls (fun s u t db =>
  testCredentials.all (fun otherTicket =>
    unsafePerUserTicket s u t db == unsafePerUserTicket s u otherTicket db))

def serviceIgnoredPBT : Bool := forAllCalls (fun s u t db =>
  testCredentials.all (fun otherService =>
    unsafePerUserTicket s u t db == unsafePerUserTicket otherService u t db))

def presentPBT : Bool := forAllCalls (fun s u t db =>
  (testValues ++ ["alice_profile", "carol_profile", "new"]).all (fun value =>
    decide (db[u]? = some value → unsafePerUserTicket s u t db = some value)))

def missingPBT : Bool := forAllCalls (fun s u t db =>
  (unsafePerUserTicket s u t db == none) == !(db.contains u))

def emptyPBT : Bool := testCredentials.all (fun s => testUserIds.all (fun u =>
  testCredentials.all (fun t => unsafePerUserTicket s u t (∅ : Database) == none)))

def insertedUserPBT : Bool := forAllCalls (fun s u t db =>
  testValues.all (fun value =>
    unsafePerUserTicket s u t (db.insert u value) == some value))

def bulkReadPBT : Bool := testDBs.all (fun db => testCredentials.all (fun s =>
  testCredentials.all (fun t => testUserLists.all (fun users =>
    users.map (fun u => unsafePerUserTicket s u t db) ==
      users.map (fun u => db[u]?)))))

/-- Pointwise conjunction of all postcondition components, bounded at every quantifier. -/
def postPBT : Bool := forAllCalls (fun s u t db =>
  (unsafePerUserTicket s u t db == db[u]?) &&
  testCredentials.all (fun t' =>
    unsafePerUserTicket s u t db == unsafePerUserTicket s u t' db) &&
  testCredentials.all (fun s' =>
    unsafePerUserTicket s u t db == unsafePerUserTicket s' u t db) &&
  (testValues ++ ["alice_profile", "carol_profile", "new"]).all (fun value =>
    decide (db[u]? = some value → unsafePerUserTicket s u t db = some value)) &&
  ((unsafePerUserTicket s u t db == none) == !(db.contains u)) &&
  (unsafePerUserTicket s u t (∅ : Database) == none) &&
  testValues.all (fun value =>
    unsafePerUserTicket s u t (db.insert u value) == some value) &&
  testUserLists.all (fun users =>
    users.map (fun v => unsafePerUserTicket s v t db) ==
      users.map (fun v => db[v]?)))

-- lookup_prop
example : lookupPBT = true := by native_decide
-- ticket_ignored_prop
example : ticketIgnoredPBT = true := by native_decide
-- service_ignored_prop
example : serviceIgnoredPBT = true := by native_decide
-- present_prop
example : presentPBT = true := by native_decide
-- missing_prop
example : missingPBT = true := by native_decide
-- empty_prop
example : emptyPBT = true := by native_decide
-- inserted_user_prop
example : insertedUserPBT = true := by native_decide
-- bulk_read_prop
example : bulkReadPBT = true := by native_decide
-- Post_prop
example : postPBT = true := by native_decide

#eval [("lookup", lookupPBT), ("ticket ignored", ticketIgnoredPBT),
  ("service ignored", serviceIgnoredPBT), ("present", presentPBT),
  ("missing", missingPBT), ("empty", emptyPBT), ("inserted", insertedUserPBT),
  ("bulk read", bulkReadPBT), ("postcondition", postPBT)]

/-! ## Correctness -/

theorem correctness_thm (s u t : Int) (db : Database) :
    Pre s u t db → Post_prop s u t db := by sorry

/-! ## Imperative implementation and tests -/

/-- Mutable result register, with no authorization branch. -/
def unsafePerUserTicketImperative (_serviceToken userId _ticket : Int)
    (db : Database) : Option String := Id.run do
  let mut result : Option String := none
  result := db[userId]?
  return result

example : unsafePerUserTicketImperative 100 1 999 sampleDB = some "alice_profile" := by
  native_decide
example : unsafePerUserTicketImperative 100 2 0 sampleDB = some "bob_profile" := by
  native_decide
example : unsafePerUserTicketImperative 100 3 777 sampleDB = some "carol_profile" := by
  native_decide
example : unsafePerUserTicketImperative 100 99 999 sampleDB = none := by
  native_decide
example : unsafePerUserTicketImperative 100 1 999 (∅ : Database) = none := by
  native_decide
example : check unsafePerUserTicketImperative = true := by native_decide

-- Bounded equivalence test over the same varied maps and integer inputs.
example : forAllCalls (fun s u t db =>
    unsafePerUserTicket s u t db == unsafePerUserTicketImperative s u t db) = true := by
  native_decide

#eval check unsafePerUserTicketImperative
#eval [1, 2, 3, 99].map (fun u => unsafePerUserTicketImperative 100 u 0 sampleDB)

/-- Equality for every input, not just for the five regression tests. -/
theorem functional_eq_imperative_thm (s u t : Int) (db : Database) :
    unsafePerUserTicket s u t db = unsafePerUserTicketImperative s u t db := by sorry

end UnsafePerUserTicket
end Agent
