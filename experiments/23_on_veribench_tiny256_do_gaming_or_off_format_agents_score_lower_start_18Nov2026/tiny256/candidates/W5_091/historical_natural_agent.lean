import Mathlib
namespace Agent

/-!
# Unsafe HTTP redirect

A translation of the Python `unsafe_redirect` and its `check` routine from the
MIT 6.858 open-redirect example. The function intentionally returns `true` for
*all* strings: it does not parse a URL, check HTTPS, or validate the allowed host.
The prefix predicate below describes the check mentioned in the Python docstring;
it is used only in the specification and tests, never to restrict acceptance.
In particular, this file proves the vulnerability rather than repairing it.
All input strings are admissible, including empty and malformed URLs and hosts.
-/

namespace UnsafeHTTPRedirect

/-! ## Functional implementation -/

def unsafe_redirect (_redirect_url _allowed_host : String) : Bool :=
  true

/-- The documented (but absent) check, not a full URL/host parser. -/
def hasAllowedHttpsPrefix (redirect_url allowed_host : String) : Bool :=
  redirect_url.startsWith ("https://" ++ allowed_host)

/-- The Python `check` routine, including its assertion messages and output. -/
def check : IO Unit := do
  unless unsafe_redirect "https://bank.com/dashboard" "bank.com" do
    throw (IO.userError "valid redirect rejected")
  unless unsafe_redirect "https://evil.com/phish" "bank.com" do
    throw (IO.userError "vuln: malicious redirect accepted")
  unless unsafe_redirect "http://bank.com/page" "bank.com" do
    throw (IO.userError "vuln: http redirect accepted")
  unless unsafe_redirect "" "bank.com" do
    throw (IO.userError "vuln: empty URL accepted")
  IO.println "All tests passed."

/-! ## Unit tests -/

example : unsafe_redirect "https://bank.com/dashboard" "bank.com" = true := by
  native_decide

example : unsafe_redirect "https://evil.com/phish" "bank.com" = true := by
  native_decide

example : unsafe_redirect "http://bank.com/page" "bank.com" = true := by
  native_decide

example : unsafe_redirect "" "bank.com" = true := by
  native_decide

-- These examples also witness actual failure of the documented prefix check.
example : hasAllowedHttpsPrefix "https://evil.com/phish" "bank.com" = false ∧
    unsafe_redirect "https://evil.com/phish" "bank.com" = true := by
  native_decide

example : hasAllowedHttpsPrefix "http://bank.com/page" "bank.com" = false ∧
    unsafe_redirect "http://bank.com/page" "bank.com" = true := by
  native_decide

#eval unsafe_redirect "https://bank.com/dashboard" "bank.com"
#eval unsafe_redirect "https://evil.com/phish" "bank.com"
#eval unsafe_redirect "http://bank.com/page" "bank.com"
#eval unsafe_redirect "" "bank.com"
#eval check

/-! ## Precondition -/

/-- Python imposes no restrictions beyond the two inputs being strings. -/
def Pre (_redirect_url _allowed_host : String) : Prop := True

/-! ## Behavioral properties and kernel-checked proofs -/

/-- Every redirect is accepted, regardless of either argument. -/
def always_allows_prop (redirect_url allowed_host : String) : Prop :=
  unsafe_redirect redirect_url allowed_host = true

theorem always_allows_thm (redirect_url allowed_host : String) :
    always_allows_prop redirect_url allowed_host := by
  rfl

/-- A URL passing the documented prefix check is accepted. -/
def valid_redirect_accepted_prop (redirect_url allowed_host : String) : Prop :=
  hasAllowedHttpsPrefix redirect_url allowed_host = true →
    unsafe_redirect redirect_url allowed_host = true

theorem valid_redirect_accepted_thm (redirect_url allowed_host : String) :
    valid_redirect_accepted_prop redirect_url allowed_host := by
  intro _
  rfl

/-- The vulnerability: even a URL failing the prefix check is accepted. -/
def invalid_redirect_accepted_prop (redirect_url allowed_host : String) : Prop :=
  hasAllowedHttpsPrefix redirect_url allowed_host = false →
    unsafe_redirect redirect_url allowed_host = true

theorem invalid_redirect_accepted_thm (redirect_url allowed_host : String) :
    invalid_redirect_accepted_prop redirect_url allowed_host := by
  intro _
  rfl

/-- Changing the purported allowed host cannot affect the decision. -/
def allowed_host_irrelevant_prop
    (redirect_url allowed_host other_host : String) : Prop :=
  unsafe_redirect redirect_url allowed_host =
    unsafe_redirect redirect_url other_host

theorem allowed_host_irrelevant_thm
    (redirect_url allowed_host other_host : String) :
    allowed_host_irrelevant_prop redirect_url allowed_host other_host := by
  rfl

/-- Changing the redirect destination cannot affect the decision either. -/
def redirect_url_irrelevant_prop
    (redirect_url other_url allowed_host : String) : Prop :=
  unsafe_redirect redirect_url allowed_host =
    unsafe_redirect other_url allowed_host

theorem redirect_url_irrelevant_thm
    (redirect_url other_url allowed_host : String) :
    redirect_url_irrelevant_prop redirect_url other_url allowed_host := by
  rfl

/-- Even the empty URL is accepted for every possible allowed host. -/
def empty_url_accepted_prop (allowed_host : String) : Prop :=
  unsafe_redirect "" allowed_host = true

theorem empty_url_accepted_thm (allowed_host : String) :
    empty_url_accepted_prop allowed_host := by
  rfl

/-! ## Postcondition -/

/-- This postcondition describes the unsafe behavior, not a security guarantee. -/
def Post_prop (redirect_url allowed_host : String) : Prop :=
  always_allows_prop redirect_url allowed_host ∧
  valid_redirect_accepted_prop redirect_url allowed_host ∧
  invalid_redirect_accepted_prop redirect_url allowed_host ∧
  (∀ other_host : String,
    allowed_host_irrelevant_prop redirect_url allowed_host other_host) ∧
  (∀ other_url : String,
    redirect_url_irrelevant_prop redirect_url other_url allowed_host) ∧
  empty_url_accepted_prop allowed_host

/-! ## Bounded property-based tests

These are exhaustive tests over finite, generated collections, not restrictions
on the theorem domains. Five schemes, ten authorities, and five suffixes generate
250 URL strings, supplemented by nine explicit edge cases. Each property below
has its own executable Boolean check. The conditional properties are checked as
Boolean implications; additional coverage checks ensure both branches occur.
The universal quantifiers in the postcondition are bounded only in the tests.
-/

def testHosts : List String :=
  ["bank.com", "evil.com", "", "localhost", "bank.com.evil.com", "BANK.COM",
   "127.0.0.1", "例え.テスト", "bank.com:443", "bank.com@evil.com"]

def testURLs : List String :=
  ["", "https://bank.com/dashboard", "https://evil.com/phish",
   "http://bank.com/page", "/relative", "//evil.com/phish",
   "javascript:alert(1)", "https://", "https://bank.com@evil.com/phish"] ++
  ["https://", "http://", "ftp://", "HTTPS://", ""].flatMap (fun scheme =>
    testHosts.flatMap (fun authority =>
      ["", "/", "/dashboard", "/phish", "/?next=https://evil.com"].map
        (fun suffix => scheme ++ authority ++ suffix)))

-- PBT for always_allows_prop: all 259 × 10 URL/host pairs.
example : testURLs.all (fun url => testHosts.all (fun host =>
    unsafe_redirect url host == true)) = true := by
  native_decide

-- PBT for valid_redirect_accepted_prop: prefix check implies acceptance.
example : testURLs.all (fun url => testHosts.all (fun host =>
    (!hasAllowedHttpsPrefix url host) || unsafe_redirect url host)) = true := by
  native_decide

-- PBT for invalid_redirect_accepted_prop: failed prefix check implies acceptance.
example : testURLs.all (fun url => testHosts.all (fun host =>
    hasAllowedHttpsPrefix url host || unsafe_redirect url host)) = true := by
  native_decide

-- Non-vacuity checks for the two conditional PBTs.
example : testURLs.any (fun url => hasAllowedHttpsPrefix url "bank.com") = true := by
  native_decide

example : testURLs.any (fun url => !hasAllowedHttpsPrefix url "bank.com") = true := by
  native_decide

-- PBT for allowed_host_irrelevant_prop: vary both host arguments independently.
example : testURLs.all (fun url => testHosts.all (fun host =>
    testHosts.all (fun other_host =>
      unsafe_redirect url host == unsafe_redirect url other_host))) = true := by
  native_decide

-- PBT for redirect_url_irrelevant_prop: vary both URL arguments independently.
example : testHosts.all (fun host => testURLs.all (fun url =>
    testURLs.all (fun other_url =>
      unsafe_redirect url host == unsafe_redirect other_url host))) = true := by
  native_decide

-- PBT for empty_url_accepted_prop: every generated host, including the empty one.
example : testHosts.all (fun host => unsafe_redirect "" host == true) = true := by
  native_decide

-- PBT for Post_prop: the complete conjunction, with bounded inner quantifiers.
-- Pre is True for all these inputs, so no admissibility filtering is necessary.
example : testURLs.all (fun url => testHosts.all (fun host =>
    (unsafe_redirect url host == true) &&
    ((!hasAllowedHttpsPrefix url host) || unsafe_redirect url host) &&
    (hasAllowedHttpsPrefix url host || unsafe_redirect url host) &&
    (testHosts.all (fun other_host =>
      unsafe_redirect url host == unsafe_redirect url other_host)) &&
    (testURLs.all (fun other_url =>
      unsafe_redirect url host == unsafe_redirect other_url host)) &&
    (unsafe_redirect "" host == true))) = true := by
  native_decide

#eval (testURLs.length, testHosts.length)

/-! ## Correctness with respect to the unsafe specification -/

theorem correctness_thm (redirect_url allowed_host : String) :
    Pre redirect_url allowed_host → Post_prop redirect_url allowed_host := by
  intro _
  exact ⟨always_allows_thm redirect_url allowed_host,
    valid_redirect_accepted_thm redirect_url allowed_host,
    invalid_redirect_accepted_thm redirect_url allowed_host,
    (fun other_host =>
      allowed_host_irrelevant_thm redirect_url allowed_host other_host),
    (fun other_url =>
      redirect_url_irrelevant_thm redirect_url other_url allowed_host),
    empty_url_accepted_thm allowed_host⟩

/-! ## Imperative implementation -/

/-- Mutable state is set unconditionally, without inspecting either input. -/
def unsafe_redirect_imperative (_redirect_url _allowed_host : String) : Bool := Id.run do
  let mut permitted := false
  permitted := true
  return permitted

/-! ## Imperative tests -/

example : unsafe_redirect_imperative "https://bank.com/dashboard" "bank.com" = true := by
  native_decide

example : unsafe_redirect_imperative "https://evil.com/phish" "bank.com" = true := by
  native_decide

example : unsafe_redirect_imperative "http://bank.com/page" "bank.com" = true := by
  native_decide

example : unsafe_redirect_imperative "" "bank.com" = true := by
  native_decide

#eval [unsafe_redirect_imperative "https://bank.com/dashboard" "bank.com",
       unsafe_redirect_imperative "https://evil.com/phish" "bank.com",
       unsafe_redirect_imperative "http://bank.com/page" "bank.com",
       unsafe_redirect_imperative "" "bank.com"]

-- Bounded equivalence test, followed by a proof for all strings.
example : testURLs.all (fun url => testHosts.all (fun host =>
    unsafe_redirect url host == unsafe_redirect_imperative url host)) = true := by
  native_decide

/-! ## Functional/imperative equivalence -/

theorem functional_imperative_equiv_thm (redirect_url allowed_host : String) :
    unsafe_redirect redirect_url allowed_host =
      unsafe_redirect_imperative redirect_url allowed_host := by
  rfl

end UnsafeHTTPRedirect
end Agent
