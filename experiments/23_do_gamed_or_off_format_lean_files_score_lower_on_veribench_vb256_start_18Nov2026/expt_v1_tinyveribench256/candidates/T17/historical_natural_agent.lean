import Mathlib
namespace Agent

/-!
# Unsafe post creation: forging posts under any username

Lean 4 formalization of the Python program `unsafe_make_post`
(MIT 6.858 Quiz 1, Spring 2020 — Question 13, Lab 2: Privilege Separation).

The Zoobar post service exposes `rpc_make_post(username, content, token)` but never
verifies that `token` authenticates `username`.  Consequently any caller — including an
attacker who controls the dynamic container — can append a post attributed to an
arbitrary user.

A post is modelled as a pair `(creator, content) : String × String`, and the database as
a `List Post`.  `unsafeMakePost` appends the new post unconditionally; the token argument
is discarded.  The theorems below pin down exactly this behaviour, including the security
defect: the result is *independent of the token*, so a wrong or empty credential is
accepted just like a valid one.
-/

namespace UnsafePostAuthority

/-- A post is a pair `(creator, content)`. -/
abbrev Post : Type := String × String

/-! ## Functional implementation -/

/-- Append a new post to the list.

Vulnerability: `_token` is never checked against `username`, so an arbitrary caller can
claim an arbitrary identity. -/
def unsafeMakePost (posts : List Post) (username content : String) (_token : String) :
    List Post :=
  posts ++ [(username, content)]

/-! ## Unit tests (mirroring the Python `check` function) -/

-- 1) Normal operation: legitimate user creates a post.
example : unsafeMakePost [] "alice" "Hello world" "valid_token_alice"
    = [("alice", "Hello world")] := by native_decide

-- 2) Vulnerability trigger: a forged post with a wrong token is accepted.
example : ("alice", "Forged post") ∈
    unsafeMakePost (unsafeMakePost [] "alice" "Hello world" "valid_token_alice")
      "alice" "Forged post" "wrong_token" := by native_decide

-- 3) Impersonation of another user with no token at all.
example : unsafeMakePost [] "bob" "Impersonated!" "" = [("bob", "Impersonated!")] := by
  native_decide

-- 4) Multiple posts accumulate correctly.
example :
    (unsafeMakePost (unsafeMakePost [] "alice" "Post 1" "t1") "bob" "Post 2" "t2").length
      = 2 := by native_decide

#eval unsafeMakePost [] "alice" "Hello world" "valid_token_alice"
#eval unsafeMakePost [("alice", "Hello world")] "alice" "Forged post" "wrong_token"
#eval unsafeMakePost [] "bob" "Impersonated!" ""

/-! ## Pre-condition -/

/-- The Python function imposes no requirement whatsoever on its inputs: it is total and
accepts every database, username, content and token.  This vacuous pre-condition *is* the
faithful specification (and is itself the bug: no credential is demanded). -/
def Pre (_posts : List Post) (_username _content _token : String) : Prop := True

/-! ## Properties -/

/-- The new post is appended at the end of the database. -/
def appends_prop (posts : List Post) (username content token : String) : Prop :=
  unsafeMakePost posts username content token = posts ++ [(username, content)]

theorem appends_thm (posts : List Post) (username content token : String) :
    appends_prop posts username content token := by
  rfl

/-- The token argument is completely ignored: any two tokens give the same result.
This is the security defect — no authentication is performed. -/
def tokenIgnored_prop (posts : List Post) (username content t₁ t₂ : String) : Prop :=
  unsafeMakePost posts username content t₁ = unsafeMakePost posts username content t₂

theorem tokenIgnored_thm (posts : List Post) (username content t₁ t₂ : String) :
    tokenIgnored_prop posts username content t₁ t₂ := by
  rfl

/-- Forgery: for *every* user and *every* token (in particular a wrong one, or the empty
string), the post is accepted and recorded as authored by that user. -/
def forgeable_prop (posts : List Post) (username content token : String) : Prop :=
  (username, content) ∈ unsafeMakePost posts username content token

theorem forgeable_thm (posts : List Post) (username content token : String) :
    forgeable_prop posts username content token := by
  simp [forgeable_prop, unsafeMakePost]

/-- Concrete instance of the exploit from the Python `check`: Mallory posts as "alice"
with a bogus token, and the forged post lands in the database. -/
theorem exploit_thm :
    ("alice", "Forged post") ∈
      unsafeMakePost [("alice", "Hello world")] "alice" "Forged post" "wrong_token" := by
  decide

/-- Exactly one post is added per call. -/
def lengthIncrement_prop (posts : List Post) (username content token : String) : Prop :=
  (unsafeMakePost posts username content token).length = posts.length + 1

theorem lengthIncrement_thm (posts : List Post) (username content token : String) :
    lengthIncrement_prop posts username content token := by
  simp [lengthIncrement_prop, unsafeMakePost]

/-- Existing posts are preserved: the old database is a prefix of the new one, so nothing
is dropped or modified. -/
def preservesHistory_prop (posts : List Post) (username content token : String) : Prop :=
  posts <+: unsafeMakePost posts username content token ∧
    ∀ p ∈ posts, p ∈ unsafeMakePost posts username content token

theorem preservesHistory_thm (posts : List Post) (username content token : String) :
    preservesHistory_prop posts username content token := by
  constructor
  · exact ⟨[(username, content)], rfl⟩
  · intro p hp
    simp [unsafeMakePost, hp]

/-- Nothing else is created: every post in the result is either an old post or the newly
submitted one. -/
def noSpuriousPosts_prop (posts : List Post) (username content token : String) : Prop :=
  ∀ p ∈ unsafeMakePost posts username content token, p ∈ posts ∨ p = (username, content)

theorem noSpuriousPosts_thm (posts : List Post) (username content token : String) :
    noSpuriousPosts_prop posts username content token := by
  intro p hp
  simpa [noSpuriousPosts_prop, unsafeMakePost] using hp

/-- The last entry of the result is the freshly submitted post. -/
def lastIsNew_prop (posts : List Post) (username content token : String) : Prop :=
  (unsafeMakePost posts username content token).getLast?  = some (username, content)

theorem lastIsNew_thm (posts : List Post) (username content token : String) :
    lastIsNew_prop posts username content token := by
  simp [lastIsNew_prop, unsafeMakePost]

/-! ## Post-condition -/

/-- Full post-condition: the conjunction of all the properties above. -/
def Post_prop (posts : List Post) (username content token : String) : Prop :=
  appends_prop posts username content token ∧
  (∀ t' : String, tokenIgnored_prop posts username content token t') ∧
  forgeable_prop posts username content token ∧
  lengthIncrement_prop posts username content token ∧
  preservesHistory_prop posts username content token ∧
  noSpuriousPosts_prop posts username content token ∧
  lastIsNew_prop posts username content token

/-- Correctness: the (vacuous) pre-condition implies the full post-condition. -/
theorem correctness_thm (posts : List Post) (username content token : String)
    (_h : Pre posts username content token) :
    Post_prop posts username content token :=
  ⟨appends_thm posts username content token,
   fun t' => tokenIgnored_thm posts username content token t',
   forgeable_thm posts username content token,
   lengthIncrement_thm posts username content token,
   preservesHistory_thm posts username content token,
   noSpuriousPosts_thm posts username content token,
   lastIsNew_thm posts username content token⟩

/-! ## Imperative implementation -/

/-- Imperative version: rebuild the database into a mutable accumulator, then push the
new (unauthenticated) post. -/
def unsafeMakePostImp (posts : List Post) (username content : String) (_token : String) :
    List Post :=
  Id.run do
    let mut acc : List Post := []
    for p in posts do
      acc := acc ++ [p]
    acc := acc ++ [(username, content)]
    return acc

/-! ### Imperative tests -/

example : unsafeMakePostImp [] "alice" "Hello world" "valid_token_alice"
    = [("alice", "Hello world")] := by native_decide

example : unsafeMakePostImp [] "bob" "Impersonated!" "" = [("bob", "Impersonated!")] := by
  native_decide

example :
    (unsafeMakePostImp (unsafeMakePostImp [] "alice" "Post 1" "t1") "bob" "Post 2"
      "t2").length = 2 := by native_decide

#eval unsafeMakePostImp [("alice", "Hello world")] "alice" "Forged post" "wrong_token"

/-! ## Equivalence of the two implementations -/

/-- The `for` loop only copies the input list, element by element, onto the accumulator. -/
private theorem flatten_map_singleton {α : Type} (l : List α) :
    (l.map (fun x => [x])).flatten = l := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

/-- Functional and imperative implementations agree on all inputs. -/
theorem unsafeMakePost_eq_imp (posts : List Post) (username content token : String) :
    unsafeMakePost posts username content token
      = unsafeMakePostImp posts username content token := by
  simp [unsafeMakePost, unsafeMakePostImp, Id.run, flatten_map_singleton]
  rfl

end UnsafePostAuthority
end Agent
