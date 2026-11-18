import Mathlib
namespace Agent

/-!
# Safe post creation by authenticated username

Translation of MIT 6.858 Quiz 1 (Spring 2020), Question 13's safe post
service. The server checks the supplied token before appending a post.

`TokenDB` represents a Python dictionary by its `get` operation: `none`
means that the username is absent, and `some t` is its stored string token.
Every Python dictionary has this representation; no enumeration or
finiteness assumption is needed because the program performs one lookup.
Authentication means equality with the token stored for the *claimed*
username. It does not assume token uniqueness, nonempty strings, or a
cryptographic ownership property not present in the Python program.
-/

namespace UnsafePostAuthoritySafe

abbrev Post := String × String
abbrev TokenDB := String → Option String
abbrev Candidate := List Post → String → String → String → TokenDB → Option (List Post)

/-- Check the claimed user's token, then append exactly one post on success. -/
def safe_make_post (posts : List Post) (username content token : String)
    (valid_tokens : TokenDB) : Option (List Post) :=
  if valid_tokens username = some token then
    some (posts ++ [(username, content)])
  else
    none

/-! ## Unit tests: the six assertions from Python -/

def exampleTokens : TokenDB := fun username =>
  if username = "alice" then some "tok_alice"
  else if username = "bob" then some "tok_bob"
  else none

/-- Executable translation of Python's `check`, also used for the imperative code. -/
def check (candidate : Candidate) : Bool :=
  (candidate [] "alice" "Hello world" "tok_alice" exampleTokens ==
    some [("alice", "Hello world")]) &&
  (candidate [] "alice" "Forged post" "wrong_token" exampleTokens == none) &&
  (candidate [] "alice" "Forged" "" exampleTokens == none) &&
  (candidate [] "alice" "Forged" "tok_bob" exampleTokens == none) &&
  (candidate [] "bob" "Bob's post" "tok_bob" exampleTokens ==
    some [("bob", "Bob's post")]) &&
  (candidate [] "eve" "Eve's post" "tok_eve" exampleTokens == none)

example : safe_make_post [] "alice" "Hello world" "tok_alice" exampleTokens =
    some [("alice", "Hello world")] := by native_decide

example : safe_make_post [] "alice" "Forged post" "wrong_token" exampleTokens =
    none := by native_decide

example : safe_make_post [] "alice" "Forged" "" exampleTokens =
    none := by native_decide

example : safe_make_post [] "alice" "Forged" "tok_bob" exampleTokens =
    none := by native_decide

example : safe_make_post [] "bob" "Bob's post" "tok_bob" exampleTokens =
    some [("bob", "Bob's post")] := by native_decide

example : safe_make_post [] "eve" "Eve's post" "tok_eve" exampleTokens =
    none := by native_decide

example : check safe_make_post = true := by native_decide

-- A nonempty history is preserved, including repeated posts.
example : safe_make_post [("alice", "Hello world"), ("bob", "old")]
    "alice" "Hello world" "tok_alice" exampleTokens =
    some [("alice", "Hello world"), ("bob", "old"), ("alice", "Hello world")] := by
  native_decide

-- Empty tokens are not inherently invalid: they are rejected only on a mismatch.
example : safe_make_post [] "" "" "" (fun _ => some "") =
    some [("", "")] := by native_decide

-- An absent dictionary entry is different from an entry containing "".
example : safe_make_post [] "" "" "" (fun _ => none) = none := by native_decide

#eval check safe_make_post
#eval safe_make_post [] "alice" "Hello world" "tok_alice" exampleTokens
#eval safe_make_post [] "alice" "Forged" "tok_bob" exampleTokens

/-! ## Preconditions and semantic properties -/

/-- The Python function is total on its typed domain; no extra assumptions. -/
def Pre (_posts : List Post) (_username _content _token : String)
    (_valid_tokens : TokenDB) : Prop := True

/-- A matching token always succeeds and appends exactly the supplied post. -/
def authorized_append_prop (posts : List Post) (username content token : String)
    (valid_tokens : TokenDB) : Prop :=
  valid_tokens username = some token →
    safe_make_post posts username content token valid_tokens =
      some (posts ++ [(username, content)])

theorem authorized_append_thm (posts : List Post) (username content token : String)
    (valid_tokens : TokenDB) :
    authorized_append_prop posts username content token valid_tokens := by
  intro h
  simp [safe_make_post, h]

/-- Rejection occurs exactly when the claimed user's token does not match. -/
def rejection_iff_prop (posts : List Post) (username content token : String)
    (valid_tokens : TokenDB) : Prop :=
  safe_make_post posts username content token valid_tokens = none ↔
    valid_tokens username ≠ some token

theorem rejection_iff_thm (posts : List Post) (username content token : String)
    (valid_tokens : TokenDB) :
    rejection_iff_prop posts username content token valid_tokens := by
  unfold rejection_iff_prop
  by_cases h : valid_tokens username = some token <;>
    simp [safe_make_post, h]

/-- Any successful result certifies authentication and the exact output list. -/
def success_iff_prop (posts : List Post) (username content token : String)
    (valid_tokens : TokenDB) : Prop :=
  ∀ result : List Post,
    safe_make_post posts username content token valid_tokens = some result ↔
      valid_tokens username = some token ∧ result = posts ++ [(username, content)]

theorem success_iff_thm (posts : List Post) (username content token : String)
    (valid_tokens : TokenDB) :
    success_iff_prop posts username content token valid_tokens := by
  intro result
  by_cases h : valid_tokens username = some token <;>
    simp [safe_make_post, h, eq_comm]

/-- All existing posts remain the unchanged prefix, in their original order. -/
def history_preserved_prop (posts : List Post) (username content token : String)
    (valid_tokens : TokenDB) : Prop :=
  ∀ result : List Post,
    safe_make_post posts username content token valid_tokens = some result →
      result.take posts.length = posts

theorem history_preserved_thm (posts : List Post) (username content token : String)
    (valid_tokens : TokenDB) :
    history_preserved_prop posts username content token valid_tokens := by
  intro result hresult
  obtain ⟨_, rfl⟩ := (success_iff_thm posts username content token valid_tokens result).mp hresult
  simp

/-- Success adds exactly one post, with the claimed username and unmodified content. -/
def one_new_post_prop (posts : List Post) (username content token : String)
    (valid_tokens : TokenDB) : Prop :=
  ∀ result : List Post,
    safe_make_post posts username content token valid_tokens = some result →
      result.length = posts.length + 1 ∧
      result.drop posts.length = [(username, content)]

theorem one_new_post_thm (posts : List Post) (username content token : String)
    (valid_tokens : TokenDB) :
    one_new_post_prop posts username content token valid_tokens := by
  intro result hresult
  obtain ⟨_, rfl⟩ := (success_iff_thm posts username content token valid_tokens result).mp hresult
  simp

/-- An unknown user cannot authenticate with any string, even the empty string. -/
def unknown_user_prop (posts : List Post) (username content token : String)
    (valid_tokens : TokenDB) : Prop :=
  valid_tokens username = none →
    safe_make_post posts username content token valid_tokens = none

theorem unknown_user_thm (posts : List Post) (username content token : String)
    (valid_tokens : TokenDB) :
    unknown_user_prop posts username content token valid_tokens := by
  intro h
  simp [safe_make_post, h]

/-- The full contract, with no restriction on histories, names, contents or tokens. -/
def Post_prop (posts : List Post) (username content token : String)
    (valid_tokens : TokenDB) : Prop :=
  authorized_append_prop posts username content token valid_tokens ∧
  rejection_iff_prop posts username content token valid_tokens ∧
  success_iff_prop posts username content token valid_tokens ∧
  history_preserved_prop posts username content token valid_tokens ∧
  one_new_post_prop posts username content token valid_tokens ∧
  unknown_user_prop posts username content token valid_tokens

/-! ## Bounded property-based tests

The dictionary type is a function, so we use exhaustive bounded tests rather
than a sampler for arbitrary functions. Each property is checked over all
12,288 combinations: 64 dictionaries × 4 histories × 4 usernames × 3 contents
× 4 submitted tokens. Every dictionary over alice/bob/eve with values drawn
from {absent, empty, tok_alice, tok_bob} is included. This covers successful
and rejected calls, unknown users, shared credentials, cross-user tokens,
empty strings, nonempty histories, and repeated posts. The bounded test
inputs do not restrict the domains of the theorems above.

The checks for properties quantified over the output list inspect the actual
Option result. In the `none` branch the success iff additionally checks that
authentication failed; in the `some` branch it checks authentication and the
exact list. Thus the check does not merely test an implication on success.
-/

def sampleHistories : List (List Post) :=
  [[], [("bob", "old")], [("alice", "first"), ("bob", "second")],
    [("alice", "Hello world")]]

def sampleUsers : List String := ["alice", "bob", "eve", ""]
def sampleContents : List String := ["", "Hello world", "Unicode: λ"]
def sampleTokens : List String := ["", "tok_alice", "tok_bob", "wrong_token"]
def sampleStoredTokens : List (Option String) :=
  [none, some "", some "tok_alice", some "tok_bob"]

def sampleTables : List TokenDB := do
  let alice ← sampleStoredTokens
  let bob ← sampleStoredTokens
  let eve ← sampleStoredTokens
  pure (fun username =>
    if username = "alice" then alice
    else if username = "bob" then bob
    else if username = "eve" then eve
    else none)

abbrev PropertyCheck := List Post → String → String → String → TokenDB → Bool

def boundedCheck (p : PropertyCheck) : Bool :=
  sampleTables.all fun ts =>
    sampleHistories.all fun posts =>
      sampleUsers.all fun username =>
        sampleContents.all fun content =>
          sampleTokens.all fun token => p posts username content token ts

/-- Executable form of `authorized_append_prop`. -/
def authorizedAppendCheck : PropertyCheck := fun posts username content token ts =>
  if ts username = some token then
    decide (safe_make_post posts username content token ts =
      some (posts ++ [(username, content)]))
  else true

/-- Executable form of `rejection_iff_prop`. -/
def rejectionCheck : PropertyCheck := fun posts username content token ts =>
  decide ((safe_make_post posts username content token ts = none) ↔
    ts username ≠ some token)

/-- Executable form of `success_iff_prop`, avoiding enumeration of all lists. -/
def successCheck : PropertyCheck := fun posts username content token ts =>
  match safe_make_post posts username content token ts with
  | none => decide (ts username ≠ some token)
  | some result => decide (ts username = some token ∧
      result = posts ++ [(username, content)])

/-- Executable form of `history_preserved_prop`. -/
def historyCheck : PropertyCheck := fun posts username content token ts =>
  match safe_make_post posts username content token ts with
  | none => true
  | some result => decide (result.take posts.length = posts)

/-- Executable form of `one_new_post_prop`. -/
def oneNewPostCheck : PropertyCheck := fun posts username content token ts =>
  match safe_make_post posts username content token ts with
  | none => true
  | some result => decide (result.length = posts.length + 1 ∧
      result.drop posts.length = [(username, content)])

/-- Executable form of `unknown_user_prop`. -/
def unknownUserCheck : PropertyCheck := fun posts username content token ts =>
  if ts username = none then
    decide (safe_make_post posts username content token ts = none)
  else true

/-- Executable form of the conjunction `Post_prop`. -/
def postCheck : PropertyCheck := fun posts username content token ts =>
  authorizedAppendCheck posts username content token ts &&
  rejectionCheck posts username content token ts &&
  successCheck posts username content token ts &&
  historyCheck posts username content token ts &&
  oneNewPostCheck posts username content token ts &&
  unknownUserCheck posts username content token ts

-- PBT: authorized_append_prop
example : boundedCheck authorizedAppendCheck = true := by native_decide
-- PBT: rejection_iff_prop
example : boundedCheck rejectionCheck = true := by native_decide
-- PBT: success_iff_prop
example : boundedCheck successCheck = true := by native_decide
-- PBT: history_preserved_prop
example : boundedCheck historyCheck = true := by native_decide
-- PBT: one_new_post_prop
example : boundedCheck oneNewPostCheck = true := by native_decide
-- PBT: unknown_user_prop
example : boundedCheck unknownUserCheck = true := by native_decide
-- PBT: Post_prop
example : boundedCheck postCheck = true := by native_decide

#eval ("bounded post-condition", boundedCheck postCheck)

/-! ## Correctness -/

theorem safe_make_post_correct (posts : List Post) (username content token : String)
    (valid_tokens : TokenDB) :
    Pre posts username content token valid_tokens →
      Post_prop posts username content token valid_tokens := by
  intro _
  exact ⟨authorized_append_thm posts username content token valid_tokens,
    rejection_iff_thm posts username content token valid_tokens,
    success_iff_thm posts username content token valid_tokens,
    history_preserved_thm posts username content token valid_tokens,
    one_new_post_thm posts username content token valid_tokens,
    unknown_user_thm posts username content token valid_tokens⟩

/-! ## Imperative version: reject early, otherwise update a local mutable list -/

def safe_make_post_imp (posts : List Post) (username content token : String)
    (valid_tokens : TokenDB) : Option (List Post) := Id.run do
  let mut updated := posts
  if valid_tokens username ≠ some token then
    return none
  let newPost : Post := (username, content)
  updated := updated ++ [newPost]
  return some updated

/-! ## Imperative tests -/

-- This runs all six original assertions against the imperative implementation.
example : check safe_make_post_imp = true := by native_decide

example : safe_make_post_imp [("bob", "old")] "alice" "new" "tok_alice"
    exampleTokens = some [("bob", "old"), ("alice", "new")] := by native_decide

example : safe_make_post_imp [("bob", "old")] "alice" "new" "tok_bob"
    exampleTokens = none := by native_decide

example : safe_make_post_imp [] "" "" "" (fun _ => some "") =
    some [("", "")] := by native_decide

-- Compare both implementations on all bounded input combinations as well.
example : boundedCheck (fun posts username content token ts =>
    decide (safe_make_post posts username content token ts =
      safe_make_post_imp posts username content token ts)) = true := by
  native_decide

#eval check safe_make_post_imp
#eval safe_make_post_imp [("bob", "old")] "alice" "new" "tok_alice" exampleTokens

/-! ## Functional / imperative equivalence, for every input -/

theorem functional_eq_imperative (posts : List Post) (username content token : String)
    (valid_tokens : TokenDB) :
    safe_make_post posts username content token valid_tokens =
      safe_make_post_imp posts username content token valid_tokens := by
  by_cases h : valid_tokens username = some token <;>
    simp [safe_make_post, safe_make_post_imp, h]

end UnsafePostAuthoritySafe
end Agent
