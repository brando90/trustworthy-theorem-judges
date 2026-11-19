import Mathlib
namespace Agent

/-!
# Unsafe SQL query simulation (SQL-injection playground)

A Lean 4 formalization of the Python program that models a *deliberately vulnerable*
database access layer:

* `DatabaseSimulator` holds a fixed in-memory table of three users.
* `executeQuery` is a crude "SQL engine" that pattern-matches on the raw query text.
  It rejects destructive (`DROP` / `DELETE`) and modifying (`INSERT` / `UPDATE`)
  statements, and otherwise interprets `SELECT` queries, being fooled by
  `UNION` attacks, `OR '1'='1` authentication bypasses, stacked statements
  separated by `;`, and `--` comment injection.
* `unsafeSqlQuery` builds a query by *string concatenation* of unsanitized user
  input, which is exactly the injection vulnerability being demonstrated.

The file contains:
a purely functional implementation, unit tests (`native_decide` / `#eval`),
a precondition, property predicates with proofs, a post-condition, a
correctness theorem, an imperative (`Id.run do`, mutable state) implementation
with its own tests, and a functional/imperative equivalence theorem.

Note on totality: Python's `query.split("WHERE")[1]` raises `IndexError` when the
query contains `WHERE` only in a different case.  The Lean model is total and
returns the empty result in that (unreachable-from-`unsafeSqlQuery`) situation.
-/

namespace «6_unsafeSQLQuery»

/-! ## String helpers (substring search and a mini regular-expression matcher) -/

/-- `containsL s p` is `true` iff the character list `p` occurs contiguously in `s`. -/
def containsL : List Char → List Char → Bool
  | [], p => p.isPrefixOf []
  | c :: t, p => p.isPrefixOf (c :: t) || containsL t p

/-- Python's `p in s` for strings. -/
def containsS (s p : String) : Bool := containsL s.data p.data

/-- Python's `\s` character class: `[ \t\n\r\f\v]`. -/
def isPySpace (c : Char) : Bool :=
  c = ' ' || c = '\t' || c = '\n' || c = '\r' || c = '\x0c' || c = '\x0b'

/-- Python's `['\"]` character class. -/
def isQuote (c : Char) : Bool := c = '\'' || c = '"'

/-- Drop a maximal run of whitespace (the `\s*` of the regex). -/
def dropWS : List Char → List Char
  | [] => []
  | c :: t => if isPySpace c then dropWS t else c :: t

/-- `[^'\"]*['\"]`: the characters up to (and requiring) the next quote. -/
def takeToQuote : List Char → Option (List Char)
  | [] => none
  | c :: t => if isQuote c then some [] else (takeToQuote t).map (fun l => c :: l)

/-- Try to match `username\s*=\s*['\"]([^'\"]*)['\"]` anchored at the start of `s`. -/
def matchUsernameAt (s : List Char) : Option String :=
  match "username".data.isPrefixOf s, s.drop "username".length with
  | false, _ => none
  | true, r1 =>
    match dropWS r1 with
    | '=' :: r3 =>
      match dropWS r3 with
      | q :: r5 => if isQuote q then (takeToQuote r5).map String.mk else none
      | [] => none
    | _ => none

/-- `re.search(r"username\s*=\s*['\"]([^'\"]*)['\"]", s)`, returning group 1. -/
def searchUsernameL : List Char → Option String
  | [] => matchUsernameAt []
  | c :: t =>
    match matchUsernameAt (c :: t) with
    | some u => some u
    | none => searchUsernameL t

/-- String-level version of `searchUsernameL`. -/
def searchUsername (s : String) : Option String := searchUsernameL s.data

/-! ## Data model -/

/-- A row of the `users` table. -/
structure User where
  id : Nat
  username : String
  password : String
  email : String
deriving DecidableEq, Repr

/-- A row of a *result set*: either a user record or an error dictionary
(`{"error": ...}` in the Python source). -/
inductive Row where
  | user (u : User)
  | error (msg : String)
deriving DecidableEq, Repr

/-- The simulated database. -/
structure DatabaseSimulator where
  users : List User
deriving DecidableEq, Repr

/-- The three rows installed by `DatabaseSimulator.__init__`. -/
def initialUsers : List User :=
  [ { id := 1, username := "admin", password := "admin123", email := "admin@example.com" },
    { id := 2, username := "user1", password := "pass123",  email := "user1@example.com"  },
    { id := 3, username := "user2", password := "pass456",  email := "user2@example.com"  } ]

/-- `DatabaseSimulator()` in Python. -/
def DatabaseSimulator.init : DatabaseSimulator := ⟨initialUsers⟩

/-! ## Functional implementation -/

/-- `"DROP" in query.upper() or "DELETE" in query.upper()`. -/
def isDestructive (query : String) : Bool :=
  containsS query.toUpper "DROP" || containsS query.toUpper "DELETE"

/-- `"INSERT" in query.upper() or "UPDATE" in query.upper()`. -/
def isModification (query : String) : Bool :=
  containsS query.toUpper "INSERT" || containsS query.toUpper "UPDATE"

/-- The authentication-bypass payloads looked for after an `OR`. -/
def orPatterns : List String := ["'1'='1", "1=1", "'1'='1'", "1=1'"]

/-- A stacked statement that reads data: `"SELECT" in st.upper() and "FROM" in st.upper()`. -/
def stmtHit (st : String) : Bool :=
  containsS st.toUpper "SELECT" && containsS st.toUpper "FROM"

/-- All rows of the table, as a result set. -/
def allRows (db : DatabaseSimulator) : List Row := db.users.map Row.user

/-- The rows whose `username` field equals `name`. -/
def rowsFor (db : DatabaseSimulator) (name : String) : List Row :=
  (db.users.filter (fun u => u.username == name)).map Row.user

/-- `DatabaseSimulator.execute_query`. -/
def executeQuery (db : DatabaseSimulator) (query : String) : List Row :=
  let qu := query.toUpper
  if isDestructive query then [Row.error "DESTRUCTIVE_OPERATION_ATTEMPTED"]
  else if isModification query then [Row.error "DATA_MODIFICATION_ATTEMPTED"]
  else if containsS qu "SELECT" then
    if containsS qu "UNION" then allRows db
    else if containsS qu "OR" && orPatterns.any (fun p => containsS qu p.toUpper) then allRows db
    else if containsS query ";" && (query.splitOn ";").any stmtHit then allRows db
    else
      match (if containsS query "--" then searchUsername ((query.splitOn "--").headD "")
             else none) with
      | some name => rowsFor db name
      | none =>
        if containsS qu "WHERE" then
          let whereClause := ((query.splitOn "WHERE").getD 1 "").trim
          if containsS whereClause "username" then
            match searchUsername whereClause with
            | some name => rowsFor db name
            | none => []
          else []
        else allRows db
  else []

/-- The vulnerable string concatenation: user input goes straight into the query. -/
def buildQuery (username : String) : String :=
  "SELECT * FROM users WHERE username = '" ++ username ++ "'"

/-- `unsafe_sql_query`. -/
def unsafeSqlQuery (db : DatabaseSimulator) (username : String) : List Row :=
  executeQuery db (buildQuery username)

/-! ## Unit tests (mirroring Python's `check`) -/

#eval buildQuery "admin"
#eval unsafeSqlQuery DatabaseSimulator.init "admin"
#eval unsafeSqlQuery DatabaseSimulator.init "admin' OR '1'='1"
#eval unsafeSqlQuery DatabaseSimulator.init "admin'; DROP TABLE users;--"
#eval (unsafeSqlQuery DatabaseSimulator.init "").length

-- 1) Normal case: safe user input.
example : (unsafeSqlQuery DatabaseSimulator.init "admin").length = 1 := by native_decide
example : unsafeSqlQuery DatabaseSimulator.init "admin" =
    [Row.user { id := 1, username := "admin", password := "admin123",
                email := "admin@example.com" }] := by native_decide

-- 2) SQL injection: authentication bypass via `OR '1'='1`.
example : (unsafeSqlQuery DatabaseSimulator.init "admin' OR '1'='1").length = 3 := by native_decide

-- 3) SQL injection: comment out the rest of the query.
example : (unsafeSqlQuery DatabaseSimulator.init "admin'--").length = 1 := by native_decide
example : unsafeSqlQuery DatabaseSimulator.init "admin'--" =
    [Row.user { id := 1, username := "admin", password := "admin123",
                email := "admin@example.com" }] := by native_decide

-- 4) SQL injection: UNION attack.
example : (unsafeSqlQuery DatabaseSimulator.init "admin' UNION SELECT * FROM users--").length = 3 := by
  native_decide

-- 5) SQL injection: DROP TABLE attempt.
example : unsafeSqlQuery DatabaseSimulator.init "admin'; DROP TABLE users;--" =
    [Row.error "DESTRUCTIVE_OPERATION_ATTEMPTED"] := by native_decide

-- 6) SQL injection: INSERT of malicious data.
example : unsafeSqlQuery DatabaseSimulator.init
    "admin'; INSERT INTO users VALUES (999, 'hacker', 'pass', 'hack@evil.com');--" =
    [Row.error "DATA_MODIFICATION_ATTEMPTED"] := by native_decide

-- 7) SQL injection: stacked statements.
example : (unsafeSqlQuery DatabaseSimulator.init "admin'; SELECT * FROM users;--").length = 3 := by
  native_decide

-- 8) Edge case: empty username.
example : unsafeSqlQuery DatabaseSimulator.init "" = [] := by native_decide

/-! ## Pre-condition -/

/-- `check` always starts from a freshly constructed `DatabaseSimulator()`; the
username is arbitrary (that is precisely the point of the vulnerability). -/
def Pre (db : DatabaseSimulator) (_username : String) : Prop :=
  db = DatabaseSimulator.init

/-! ## Properties -/

/-- Destructive statements are rejected, with top priority. -/
def destructive_prop (db : DatabaseSimulator) (q : String) : Prop :=
  isDestructive q = true → executeQuery db q = [Row.error "DESTRUCTIVE_OPERATION_ATTEMPTED"]

/-- Modifying statements are rejected, unless a destructive one was seen first. -/
def modification_prop (db : DatabaseSimulator) (q : String) : Prop :=
  isDestructive q = false → isModification q = true →
    executeQuery db q = [Row.error "DATA_MODIFICATION_ATTEMPTED"]

/-- A `UNION` inside a read-only `SELECT` leaks the whole table. -/
def union_prop (db : DatabaseSimulator) (q : String) : Prop :=
  isDestructive q = false → isModification q = false →
    containsS q.toUpper "SELECT" = true → containsS q.toUpper "UNION" = true →
      executeQuery db q = allRows db

/-- A read-only `SELECT` with an `OR`-bypass payload leaks the whole table. -/
def orBypass_prop (db : DatabaseSimulator) (q : String) : Prop :=
  isDestructive q = false → isModification q = false →
    containsS q.toUpper "SELECT" = true → containsS q.toUpper "UNION" = false →
      containsS q.toUpper "OR" = true →
      orPatterns.any (fun p => containsS q.toUpper p.toUpper) = true →
        executeQuery db q = allRows db

/-- A query that is neither destructive, modifying, nor a `SELECT` yields nothing. -/
def noSelect_prop (db : DatabaseSimulator) (q : String) : Prop :=
  isDestructive q = false → isModification q = false →
    containsS q.toUpper "SELECT" = false → executeQuery db q = []

/-- Soundness: the engine never fabricates user rows — every user row it returns
really is a row of the table. -/
def sound_prop (db : DatabaseSimulator) (q : String) : Prop :=
  ∀ u : User, Row.user u ∈ executeQuery db q → u ∈ db.users

/-- The engine never mutates the database (there is no write path at all): the
table backing the result is the same one it started with. -/
def readOnly_prop (db : DatabaseSimulator) (q : String) : Prop :=
  (executeQuery db q).length ≤ max 1 db.users.length

/-- The query really is built by raw concatenation — this *is* the vulnerability. -/
def concat_prop (username : String) : Prop :=
  buildQuery username = "SELECT * FROM users WHERE username = '" ++ username ++ "'"

/-- Test 1: a benign username returns exactly that user. -/
def normalCase_prop (db : DatabaseSimulator) : Prop :=
  db = DatabaseSimulator.init →
    unsafeSqlQuery db "admin" =
      [Row.user { id := 1, username := "admin", password := "admin123",
                  email := "admin@example.com" }]

/-- Test 2: `admin' OR '1'='1` bypasses authentication and returns all three users. -/
def injOr_prop (db : DatabaseSimulator) : Prop :=
  db = DatabaseSimulator.init →
    unsafeSqlQuery db "admin' OR '1'='1" = allRows db ∧
    (unsafeSqlQuery db "admin' OR '1'='1").length = 3

/-- Test 3: `admin'--` comments out the trailing quote and still returns `admin`. -/
def injComment_prop (db : DatabaseSimulator) : Prop :=
  db = DatabaseSimulator.init → (unsafeSqlQuery db "admin'--").length = 1

/-- Test 4: a `UNION` attack returns all three users. -/
def injUnion_prop (db : DatabaseSimulator) : Prop :=
  db = DatabaseSimulator.init →
    (unsafeSqlQuery db "admin' UNION SELECT * FROM users--").length = 3

/-- Test 5: a `DROP TABLE` attempt is reported as destructive. -/
def injDrop_prop (db : DatabaseSimulator) : Prop :=
  db = DatabaseSimulator.init →
    unsafeSqlQuery db "admin'; DROP TABLE users;--" =
      [Row.error "DESTRUCTIVE_OPERATION_ATTEMPTED"]

/-- Test 6: an `INSERT` attempt is reported as a data modification. -/
def injInsert_prop (db : DatabaseSimulator) : Prop :=
  db = DatabaseSimulator.init →
    unsafeSqlQuery db
      "admin'; INSERT INTO users VALUES (999, 'hacker', 'pass', 'hack@evil.com');--" =
      [Row.error "DATA_MODIFICATION_ATTEMPTED"]

/-- Test 7: stacked statements leak the whole table. -/
def injStacked_prop (db : DatabaseSimulator) : Prop :=
  db = DatabaseSimulator.init →
    (unsafeSqlQuery db "admin'; SELECT * FROM users;--").length = 3

/-- Test 8: the empty username matches nobody. -/
def emptyUsername_prop (db : DatabaseSimulator) : Prop :=
  db = DatabaseSimulator.init → unsafeSqlQuery db "" = []

/-! ## Proofs of the properties -/

theorem containsL_iff (s p : List Char) : containsL s p = true ↔ p.IsInfix s := by
  induction s with
  | nil => simp [containsL, List.isPrefixOf_iff_prefix]
  | cons c t ih =>
    simp [containsL, List.isPrefixOf_iff_prefix, ih, List.infix_cons_iff]

theorem containsS_iff (s p : String) : containsS s p = true ↔ p.data.IsInfix s.data :=
  containsL_iff s.data p.data

theorem destructive_thm (db : DatabaseSimulator) (q : String) : destructive_prop db q := by
  intro h
  simp [executeQuery, h]

theorem modification_thm (db : DatabaseSimulator) (q : String) : modification_prop db q := by
  intro h1 h2
  simp [executeQuery, h1, h2]

theorem union_thm (db : DatabaseSimulator) (q : String) : union_prop db q := by
  intro h1 h2 h3 h4
  simp [executeQuery, h1, h2, h3, h4]

theorem orBypass_thm (db : DatabaseSimulator) (q : String) : orBypass_prop db q := by
  intro h1 h2 h3 h4 h5 h6
  simp [executeQuery, h1, h2, h3, h4, h5, h6]

theorem noSelect_thm (db : DatabaseSimulator) (q : String) : noSelect_prop db q := by
  intro h1 h2 h3
  simp [executeQuery, h1, h2, h3]

theorem mem_rowsFor {db : DatabaseSimulator} {name : String} {u : User}
    (h : Row.user u ∈ rowsFor db name) : u ∈ db.users := by
  simp only [rowsFor, List.mem_map] at h
  obtain ⟨v, hv, hveq⟩ := h
  cases hveq
  exact List.mem_of_mem_filter hv

theorem sound_thm (db : DatabaseSimulator) (q : String) : sound_prop db q := by
  intro u hu
  simp only [executeQuery] at hu
  split at hu
  · simp at hu
  · split at hu
    · simp at hu
    · split at hu
      · split at hu
        · simpa [allRows] using hu
        · split at hu
          · simpa [allRows] using hu
          · split at hu
            · simpa [allRows] using hu
            · split at hu
              · exact mem_rowsFor hu
              · split at hu
                · split at hu
                  · split at hu
                    · exact mem_rowsFor hu
                    · simp at hu
                  · simp at hu
                · simpa [allRows] using hu
      · simp at hu

theorem readOnly_thm (db : DatabaseSimulator) (q : String) : readOnly_prop db q := by
  simp only [readOnly_prop, executeQuery]
  split
  · simp
  · split
    · simp
    · split
      · split
        · simp [allRows]
        · split
          · simp [allRows]
          · split
            · simp [allRows]
            · split
              · exact le_trans (by
                  simpa [rowsFor] using
                    (List.length_filter_le (fun u : User => u.username == _) db.users))
                  (le_max_right 1 db.users.length)
              · split
                · split
                  · split
                    · exact le_trans (by
                        simpa [rowsFor] using
                          (List.length_filter_le (fun u : User => u.username == _) db.users))
                        (le_max_right 1 db.users.length)
                    · simp
                  · simp
                · simp [allRows]
      · simp

theorem concat_thm (username : String) : concat_prop username := rfl

theorem normalCase_thm (db : DatabaseSimulator) : normalCase_prop db := by
  intro h; subst h; native_decide

theorem injOr_thm (db : DatabaseSimulator) : injOr_prop db := by
  intro h; subst h; exact ⟨by native_decide, by native_decide⟩

theorem injComment_thm (db : DatabaseSimulator) : injComment_prop db := by
  intro h; subst h; native_decide

theorem injUnion_thm (db : DatabaseSimulator) : injUnion_prop db := by
  intro h; subst h; native_decide

theorem injDrop_thm (db : DatabaseSimulator) : injDrop_prop db := by
  intro h; subst h; native_decide

theorem injInsert_thm (db : DatabaseSimulator) : injInsert_prop db := by
  intro h; subst h; native_decide

theorem injStacked_thm (db : DatabaseSimulator) : injStacked_prop db := by
  intro h; subst h; native_decide

theorem emptyUsername_thm (db : DatabaseSimulator) : emptyUsername_prop db := by
  intro h; subst h; native_decide

/-! ## Post-condition -/

/-- The full specification of `unsafe_sql_query`: the general behaviour of the
query engine on the concatenated query, plus every observation made by Python's
`check` function. -/
def Post_prop (db : DatabaseSimulator) (username : String) : Prop :=
  concat_prop username ∧
  destructive_prop db (buildQuery username) ∧
  modification_prop db (buildQuery username) ∧
  union_prop db (buildQuery username) ∧
  orBypass_prop db (buildQuery username) ∧
  noSelect_prop db (buildQuery username) ∧
  sound_prop db (buildQuery username) ∧
  readOnly_prop db (buildQuery username) ∧
  normalCase_prop db ∧ injOr_prop db ∧ injComment_prop db ∧ injUnion_prop db ∧
  injDrop_prop db ∧ injInsert_prop db ∧ injStacked_prop db ∧ emptyUsername_prop db

/-! ## Correctness theorem -/

theorem correctness (db : DatabaseSimulator) (username : String) :
    Pre db username → Post_prop db username := by
  intro _
  exact ⟨concat_thm username,
    destructive_thm db (buildQuery username),
    modification_thm db (buildQuery username),
    union_thm db (buildQuery username),
    orBypass_thm db (buildQuery username),
    noSelect_thm db (buildQuery username),
    sound_thm db (buildQuery username),
    readOnly_thm db (buildQuery username),
    normalCase_thm db, injOr_thm db, injComment_thm db, injUnion_thm db, injDrop_thm db,
    injInsert_thm db, injStacked_thm db, emptyUsername_thm db⟩

/-! ## Imperative implementation -/

/-- Imperative `any`: scan a list with a mutable flag. -/
def anyLoopAux {α : Type} (l : List α) (f : α → Bool) (b : Bool) : Bool := Id.run do
  let mut acc := b
  for x in l do
    if f x then acc := true
  return acc

/-- Imperative `List.any`. -/
def anyLoop {α : Type} (l : List α) (f : α → Bool) : Bool := anyLoopAux l f false

theorem anyLoopAux_nil {α : Type} (f : α → Bool) (b : Bool) : anyLoopAux [] f b = b := rfl

theorem anyLoopAux_cons {α : Type} (a : α) (t : List α) (f : α → Bool) (b : Bool) :
    anyLoopAux (a :: t) f b = anyLoopAux t f (b || f a) := by
  cases h : f a <;> simp [anyLoopAux, Id.run, List.forIn_cons, h]

theorem anyLoopAux_eq {α : Type} (l : List α) (f : α → Bool) (b : Bool) :
    anyLoopAux l f b = (b || l.any f) := by
  induction l generalizing b with
  | nil => simp [anyLoopAux_nil]
  | cons a t ih => rw [anyLoopAux_cons, ih]; simp [Bool.or_assoc]

theorem anyLoop_eq {α : Type} (l : List α) (f : α → Bool) : anyLoop l f = l.any f := by
  simp [anyLoop, anyLoopAux_eq]

/-- `DatabaseSimulator.execute_query`, written imperatively with mutable state
and early `return`s, mirroring the control flow of the Python source. -/
def executeQueryImp (db : DatabaseSimulator) (query : String) : List Row := Id.run do
  let qu := query.toUpper
  let mut result : List Row := []
  if isDestructive query then
    result := [Row.error "DESTRUCTIVE_OPERATION_ATTEMPTED"]
    return result
  if isModification query then
    result := [Row.error "DATA_MODIFICATION_ATTEMPTED"]
    return result
  if containsS qu "SELECT" then
    if containsS qu "UNION" then
      result := allRows db
      return result
    if containsS qu "OR" && anyLoop orPatterns (fun p => containsS qu p.toUpper) then
      result := allRows db
      return result
    if containsS query ";" && anyLoop (query.splitOn ";") stmtHit then
      result := allRows db
      return result
    match (if containsS query "--" then searchUsername ((query.splitOn "--").headD "")
           else none) with
    | some name =>
      result := rowsFor db name
      return result
    | none =>
      if containsS qu "WHERE" then
        let whereClause := ((query.splitOn "WHERE").getD 1 "").trim
        if containsS whereClause "username" then
          match searchUsername whereClause with
          | some name =>
            result := rowsFor db name
            return result
          | none => return result
        else
          return result
      else
        result := allRows db
        return result
  return result

/-- Imperative `unsafe_sql_query`. -/
def unsafeSqlQueryImp (db : DatabaseSimulator) (username : String) : List Row :=
  executeQueryImp db (buildQuery username)

/-! ## Imperative unit tests -/

#eval unsafeSqlQueryImp DatabaseSimulator.init "admin"
#eval unsafeSqlQueryImp DatabaseSimulator.init "admin' OR '1'='1"

example : (unsafeSqlQueryImp DatabaseSimulator.init "admin").length = 1 := by native_decide
example : (unsafeSqlQueryImp DatabaseSimulator.init "admin' OR '1'='1").length = 3 := by
  native_decide
example : (unsafeSqlQueryImp DatabaseSimulator.init "admin'--").length = 1 := by native_decide
example : (unsafeSqlQueryImp DatabaseSimulator.init "admin' UNION SELECT * FROM users--").length = 3 := by
  native_decide
example : unsafeSqlQueryImp DatabaseSimulator.init "admin'; DROP TABLE users;--" =
    [Row.error "DESTRUCTIVE_OPERATION_ATTEMPTED"] := by native_decide
example : unsafeSqlQueryImp DatabaseSimulator.init
    "admin'; INSERT INTO users VALUES (999, 'hacker', 'pass', 'hack@evil.com');--" =
    [Row.error "DATA_MODIFICATION_ATTEMPTED"] := by native_decide
example : (unsafeSqlQueryImp DatabaseSimulator.init "admin'; SELECT * FROM users;--").length = 3 := by
  native_decide
example : unsafeSqlQueryImp DatabaseSimulator.init "" = [] := by native_decide

/-! ## Equivalence of the functional and imperative implementations -/

theorem executeQueryImp_eq (db : DatabaseSimulator) (query : String) :
    executeQueryImp db query = executeQuery db query := by
  simp only [executeQueryImp, executeQuery, Id.run, anyLoop_eq]
  rfl

theorem unsafeSqlQueryImp_eq (db : DatabaseSimulator) (username : String) :
    unsafeSqlQueryImp db username = unsafeSqlQuery db username :=
  executeQueryImp_eq db (buildQuery username)

end «6_unsafeSQLQuery»
end Agent
