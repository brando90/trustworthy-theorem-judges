import Mathlib
namespace Agent

/-!
# Safe OAuth redirect validation

Translation of `safe_oauth_redirect` and its Python checks. Acceptance is exact
string membership in the supplied allowlist. The `client_id` parameter is unused:
the caller is responsible for supplying the requesting client's registered list.
There is no URL parsing, normalization, or additional nonempty-string check.
All strings and all finite lists of strings are admissible, including duplicates.
-/

namespace UnsafeOAuthRedirectSafe

/-- Functional translation of Python's `redirect_url in allowed_urls`. -/
def safe_oauth_redirect (redirect_url : String) (_client_id : String)
    (allowed_urls : List String) : Bool :=
  allowed_urls.contains redirect_url

/-! ## Unit tests -/

def allowed : List String :=
  ["https://rp1.example.com/cb", "https://rp2.example.com/cb"]

example : safe_oauth_redirect "https://rp1.example.com/cb" "rp1" allowed = true := by
  native_decide
example : safe_oauth_redirect "https://rp2.example.com/cb" "rp2" allowed = true := by
  native_decide
example : safe_oauth_redirect "https://evil.com/steal" "rp1" allowed = false := by
  native_decide
example : safe_oauth_redirect "https://rp3.com/cb" "rp1" allowed = false := by
  native_decide
example : safe_oauth_redirect "" "rp1" allowed = false := by
  native_decide

-- These edge cases distinguish exact membership from extra URL validation.
example : safe_oauth_redirect "" "" [""] = true := by native_decide
example : safe_oauth_redirect "https://rp1.example.com/cb" "another-client" allowed = true := by
  native_decide
example : safe_oauth_redirect "https://rp1.example.com/cb/" "rp1" allowed = false := by
  native_decide
example : safe_oauth_redirect "https://rp1.example.com/cb" "rp1" [] = false := by
  native_decide
example : safe_oauth_redirect "x" "rp1" ["x", "x"] = true := by native_decide

/-- Executable counterpart of Python's `check`, including all five assertions. -/
def check : IO Unit := do
  let results := [
    safe_oauth_redirect "https://rp1.example.com/cb" "rp1" allowed,
    safe_oauth_redirect "https://rp2.example.com/cb" "rp2" allowed,
    !(safe_oauth_redirect "https://evil.com/steal" "rp1" allowed),
    !(safe_oauth_redirect "https://rp3.com/cb" "rp1" allowed),
    !(safe_oauth_redirect "" "rp1" allowed)]
  if results.all id then
    IO.println "All tests passed."
  else
    throw (IO.userError "redirect validation test failed")

#eval check

/-! ## Preconditions and universally quantified specifications -/

/-- The Python function imposes no extra precondition on its typed inputs. -/
def Pre (_redirect_url _client_id : String) (_allowed_urls : List String) : Prop := True

/-- An accepted URL must actually be registered in the supplied list. -/
def soundness_prop (redirect_url client_id : String) (allowed_urls : List String) : Prop :=
  safe_oauth_redirect redirect_url client_id allowed_urls = true → redirect_url ∈ allowed_urls

theorem soundness_thm (redirect_url client_id : String) (allowed_urls : List String) :
    soundness_prop redirect_url client_id allowed_urls := by
  simp [soundness_prop, safe_oauth_redirect]

/-- Every registered URL is accepted, regardless of its spelling or the client ID. -/
def completeness_prop (redirect_url client_id : String) (allowed_urls : List String) : Prop :=
  redirect_url ∈ allowed_urls → safe_oauth_redirect redirect_url client_id allowed_urls = true

theorem completeness_thm (redirect_url client_id : String) (allowed_urls : List String) :
    completeness_prop redirect_url client_id allowed_urls := by
  simp [completeness_prop, safe_oauth_redirect]

/-- Rejection occurs exactly for URLs absent from the allowlist. -/
def rejection_prop (redirect_url client_id : String) (allowed_urls : List String) : Prop :=
  safe_oauth_redirect redirect_url client_id allowed_urls = false ↔ redirect_url ∉ allowed_urls

theorem rejection_thm (redirect_url client_id : String) (allowed_urls : List String) :
    rejection_prop redirect_url client_id allowed_urls := by
  simp [rejection_prop, safe_oauth_redirect]

/-- `client_id` is not consulted; the supplied allowlist determines authorization. -/
def client_independence_prop (redirect_url client_id : String)
    (allowed_urls : List String) : Prop :=
  ∀ other_client_id : String,
    safe_oauth_redirect redirect_url client_id allowed_urls =
      safe_oauth_redirect redirect_url other_client_id allowed_urls

theorem client_independence_thm (redirect_url client_id : String)
    (allowed_urls : List String) :
    client_independence_prop redirect_url client_id allowed_urls := by
  intro other_client_id
  rfl

/-- Full behavioral contract, without adding any URL syntax restrictions. -/
def Post_prop (redirect_url client_id : String) (allowed_urls : List String) : Prop :=
  soundness_prop redirect_url client_id allowed_urls ∧
  completeness_prop redirect_url client_id allowed_urls ∧
  rejection_prop redirect_url client_id allowed_urls ∧
  client_independence_prop redirect_url client_id allowed_urls

/-! ## Bounded property-based tests

Exhaust all URL/client combinations and all allowlists of length at most two
from the corpus, plus a longer duplicate-containing list. In particular these
cover absent/present URLs, empty lists and strings, duplicates, list order,
trailing slashes, and case-sensitive matching. Membership in the executable
specification is `decide (url ∈ urls)`, separate from the Boolean implementation.
Each universally quantified client-independence check is bounded to the client
corpus here; the theorems above are not bounded.
-/

def urlCases : List String :=
  ["", "https://rp1.example.com/cb", "https://rp2.example.com/cb",
   "https://evil.com/steal", "https://rp3.com/cb",
   "https://rp1.example.com/cb/", "https://RP1.example.com/cb", "not a URL"]

def clientCases : List String := ["", "rp1", "rp2", "unknown-client"]

def allowlistCases : List (List String) :=
  [[]] ++ urlCases.map (fun u => [u]) ++
  urlCases.flatMap (fun u => urlCases.map (fun v => [u, v])) ++
  [allowed ++ allowed]

def boundedCheck (p : String → String → List String → Bool) : Bool :=
  urlCases.all fun u => clientCases.all fun c => allowlistCases.all fun xs => p u c xs

def soundnessCheck (u c : String) (xs : List String) : Bool :=
  !(safe_oauth_redirect u c xs) || decide (u ∈ xs)

def completenessCheck (u c : String) (xs : List String) : Bool :=
  !(decide (u ∈ xs)) || safe_oauth_redirect u c xs

def rejectionCheck (u c : String) (xs : List String) : Bool :=
  (!(safe_oauth_redirect u c xs)) == (!(decide (u ∈ xs)))

def clientIndependenceCheck (u c : String) (xs : List String) : Bool :=
  clientCases.all fun other => safe_oauth_redirect u c xs == safe_oauth_redirect u other xs

def postCheck (u c : String) (xs : List String) : Bool :=
  soundnessCheck u c xs && completenessCheck u c xs &&
  rejectionCheck u c xs && clientIndependenceCheck u c xs

-- PBT for soundness_prop.
example : boundedCheck soundnessCheck = true := by native_decide
-- PBT for completeness_prop.
example : boundedCheck completenessCheck = true := by native_decide
-- PBT for rejection_prop.
example : boundedCheck rejectionCheck = true := by native_decide
-- PBT for client_independence_prop.
example : boundedCheck clientIndependenceCheck = true := by native_decide
-- PBT for the conjunction Post_prop.
example : boundedCheck postCheck = true := by native_decide

#eval [("soundness", boundedCheck soundnessCheck),
       ("completeness", boundedCheck completenessCheck),
       ("rejection", boundedCheck rejectionCheck),
       ("client independence", boundedCheck clientIndependenceCheck),
       ("postcondition", boundedCheck postCheck)]

/-! ## Correctness -/

theorem correctness_thm (redirect_url client_id : String) (allowed_urls : List String) :
    Pre redirect_url client_id allowed_urls → Post_prop redirect_url client_id allowed_urls := by
  intro _
  exact ⟨soundness_thm redirect_url client_id allowed_urls,
    completeness_thm redirect_url client_id allowed_urls,
    rejection_thm redirect_url client_id allowed_urls,
    client_independence_thm redirect_url client_id allowed_urls⟩

/-! ## Imperative implementation and tests -/

/-- Scan the allowlist, accumulating whether any exact string match was found. -/
def safe_oauth_redirect_imperative (redirect_url : String) (_client_id : String)
    (allowed_urls : List String) : Bool := Id.run do
  let mut found := false
  for url in allowed_urls do
    found := found || (url == redirect_url)
  return found

example : safe_oauth_redirect_imperative "https://rp1.example.com/cb" "rp1" allowed = true := by
  native_decide
example : safe_oauth_redirect_imperative "https://rp2.example.com/cb" "rp2" allowed = true := by
  native_decide
example : safe_oauth_redirect_imperative "https://evil.com/steal" "rp1" allowed = false := by
  native_decide
example : safe_oauth_redirect_imperative "https://rp3.com/cb" "rp1" allowed = false := by
  native_decide
example : safe_oauth_redirect_imperative "" "rp1" allowed = false := by native_decide
example : safe_oauth_redirect_imperative "" "" [""] = true := by native_decide
example : safe_oauth_redirect_imperative "x" "c" [] = false := by native_decide
example : safe_oauth_redirect_imperative "x" "c" ["x", "x"] = true := by native_decide

#eval [safe_oauth_redirect_imperative "https://rp1.example.com/cb" "rp1" allowed,
       safe_oauth_redirect_imperative "https://rp2.example.com/cb" "rp2" allowed,
       safe_oauth_redirect_imperative "https://evil.com/steal" "rp1" allowed,
       safe_oauth_redirect_imperative "https://rp3.com/cb" "rp1" allowed,
       safe_oauth_redirect_imperative "" "rp1" allowed]

example : boundedCheck (fun u c xs =>
    safe_oauth_redirect u c xs == safe_oauth_redirect_imperative u c xs) = true := by
  native_decide

/-! ## Functional/imperative equivalence -/

/-- Loop invariant: scanning preserves an earlier match and records any new match. -/
private theorem scan_invariant (redirect_url : String) (urls : List String) (found : Bool) :
    urls.foldl (fun b url => b || (url == redirect_url)) found =
      (found || urls.contains redirect_url) := by
  induction urls generalizing found with
  | nil => simp
  | cons url urls ih =>
      rw [List.foldl_cons, ih, List.contains_cons, Bool.or_assoc]
      rw [Bool.beq_comm (a := url) (b := redirect_url)]

theorem functional_imperative_equivalence_thm (redirect_url client_id : String)
    (allowed_urls : List String) :
    safe_oauth_redirect redirect_url client_id allowed_urls =
      safe_oauth_redirect_imperative redirect_url client_id allowed_urls := by
  simp [safe_oauth_redirect, safe_oauth_redirect_imperative, scan_invariant]

end UnsafeOAuthRedirectSafe
end Agent
