import Mathlib
namespace Agent

/-!
# HTTPS redirect prefix check

A translation of the Python `safe_redirect` function and its checks. Strings
are compared as sequences of Unicode characters, with literal, case-sensitive
prefix matching. This is not a URL parser or an exact hostname comparison.
For example, `https://bank.com.evil/phish` passes for the host `bank.com`, just
as it does in the Python source. No hostname-boundary guarantee is asserted.

Every string is admissible, including an empty allowed host. The specification
characterizes acceptance by an arbitrary suffix after `https://` and that
host. General proofs are kernel-checked; `native_decide` is used only in tests.
-/

namespace UnsafeHTTPRedirectSafe

/-- Python's `redirect_url.startswith("https://" + allowed_host)`, implemented
as a prefix comparison of character lists (not URL normalization). -/
def safe_redirect (redirect_url allowed_host : String) : Bool :=
  ("https://" ++ allowed_host).data.isPrefixOf redirect_url.data

-- All six original Python assertions.
example : safe_redirect "https://bank.com/dashboard" "bank.com" = true := by native_decide
example : safe_redirect "https://bank.com/" "bank.com" = true := by native_decide
example : safe_redirect "https://evil.com/phish" "bank.com" = false := by native_decide
example : safe_redirect "http://bank.com/page" "bank.com" = false := by native_decide
example : safe_redirect "" "bank.com" = false := by native_decide
example : safe_redirect "https://evilbank.com/phish" "bank.com" = false := by native_decide

-- Edge cases document the literal semantics, including its security limitations.
example : safe_redirect "https://bank.com" "bank.com" = true := by native_decide
example : safe_redirect "https://bank.com.evil/phish" "bank.com" = true := by native_decide
example : safe_redirect "https://bank.com@evil.com/" "bank.com" = true := by native_decide
example : safe_redirect "HTTPS://bank.com/" "bank.com" = false := by native_decide
example : safe_redirect "https://BANK.COM/" "bank.com" = false := by native_decide
example : safe_redirect "https://" "" = true := by native_decide
example : safe_redirect "https://例え.テスト/残高" "例え.テスト" = true := by native_decide

/-- Executable version of the Python `check` assertions. -/
def check : Bool :=
  safe_redirect "https://bank.com/dashboard" "bank.com" &&
  safe_redirect "https://bank.com/" "bank.com" &&
  !safe_redirect "https://evil.com/phish" "bank.com" &&
  !safe_redirect "http://bank.com/page" "bank.com" &&
  !safe_redirect "" "bank.com" &&
  !safe_redirect "https://evilbank.com/phish" "bank.com"

example : check = true := by native_decide
#eval if check then "All tests passed." else "Tests failed."
#eval safe_redirect "https://bank.com/dashboard" "bank.com"
#eval safe_redirect "https://evil.com/phish" "bank.com"

/-- There are no restrictions on the input strings. -/
def Pre (_redirect_url _allowed_host : String) : Prop := True

/-- Bridge from the executable character-prefix operation to string append. -/
private theorem prefix_iff_suffix (p s : String) :
    p.data.isPrefixOf s.data = true ↔ ∃ t : String, s = p ++ t := by
  cases p with
  | mk p =>
    cases s with
    | mk s =>
      simp only [List.isPrefixOf_iff_prefix, List.IsPrefix]
      constructor
      · rintro ⟨t, ht⟩
        exact ⟨String.mk t, congrArg String.mk ht.symm⟩
      · rintro ⟨⟨t⟩, ht⟩
        exact ⟨t, (congrArg String.data ht).symm⟩

/-- Exact acceptance criterion, in both directions, with an unrestricted suffix. -/
def prefix_spec_prop (url host : String) : Prop :=
  safe_redirect url host = true ↔ ∃ suffix : String, url = ("https://" ++ host) ++ suffix

theorem prefix_spec_thm (url host : String) : prefix_spec_prop url host := by
  exact prefix_iff_suffix _ _

/-- Exactly those strings without the required prefix are rejected. -/
def reject_mismatch_prop (url host : String) : Prop :=
  safe_redirect url host = false ↔ ¬ ∃ suffix : String, url = ("https://" ++ host) ++ suffix

theorem reject_mismatch_thm (url host : String) : reject_mismatch_prop url host := by
  unfold reject_mismatch_prop
  have spec := prefix_spec_thm url host
  unfold prefix_spec_prop at spec
  rw [← spec]
  cases safe_redirect url host <;> simp

/-- Every accepted redirect starts with the literal HTTPS scheme. -/
def https_only_prop (url host : String) : Prop :=
  safe_redirect url host = true → ∃ suffix : String, url = "https://" ++ suffix

theorem https_only_thm (url host : String) : https_only_prop url host := by
  intro ok
  obtain ⟨suffix, rfl⟩ := (prefix_spec_thm url host).1 ok
  exact ⟨host ++ suffix, String.append_assoc _ _ _⟩

/-- Acceptance requires enough characters for both the HTTPS prefix and the host. -/
def length_bound_prop (url host : String) : Prop :=
  safe_redirect url host = true → 8 + host.length ≤ url.length

theorem length_bound_thm (url host : String) : length_bound_prop url host := by
  intro ok
  obtain ⟨suffix, rfl⟩ := (prefix_spec_thm url host).1 ok
  simp only [String.length_append]
  change 8 + host.length ≤ 8 + host.length + suffix.length
  omega

/-- Every continuation of the required prefix is accepted, including the empty one. -/
def valid_redirect_prop (host suffix : String) : Prop :=
  safe_redirect (("https://" ++ host) ++ suffix) host = true

theorem valid_redirect_thm (host suffix : String) : valid_redirect_prop host suffix := by
  exact (prefix_spec_thm _ _).2 ⟨suffix, rfl⟩

/-- HTTP is rejected regardless of its tail and regardless of the allowed host. -/
def http_rejected_prop (tail host : String) : Prop :=
  safe_redirect ("http://" ++ tail) host = false

theorem http_rejected_thm (tail host : String) : http_rejected_prop tail host := by
  simp [http_rejected_prop, safe_redirect, String.data_append, List.isPrefixOf]

/-- An empty URL is rejected even when the allowed host itself is empty. -/
def empty_rejected_prop (host : String) : Prop := safe_redirect "" host = false

theorem empty_rejected_thm (host : String) : empty_rejected_prop host := by
  simp [empty_rejected_prop, safe_redirect, String.data_append]

/-- Appending to an accepted URL cannot destroy its initial prefix. -/
def append_stable_prop (url host tail : String) : Prop :=
  safe_redirect url host = true → safe_redirect (url ++ tail) host = true

theorem append_stable_thm (url host tail : String) : append_stable_prop url host tail := by
  intro ok
  obtain ⟨suffix, rfl⟩ := (prefix_spec_thm url host).1 ok
  exact (prefix_spec_thm _ _).2 ⟨suffix ++ tail, String.append_assoc _ _ _⟩

/-- With no allowed-host characters, the check is exactly the HTTPS-prefix check. -/
def empty_host_prop (url : String) : Prop :=
  safe_redirect url "" = true ↔ ∃ suffix : String, url = "https://" ++ suffix

theorem empty_host_thm (url : String) : empty_host_prop url := by
  simpa [empty_host_prop, prefix_spec_prop] using prefix_spec_thm url ""

/-- Pointwise semantics together with the general continuation and rejection laws. -/
def Post_prop (url host : String) : Prop :=
  prefix_spec_prop url host ∧
  reject_mismatch_prop url host ∧
  https_only_prop url host ∧
  length_bound_prop url host ∧
  (∀ suffix : String, valid_redirect_prop host suffix) ∧
  (∀ tail : String, http_rejected_prop tail host) ∧
  empty_rejected_prop host ∧
  (∀ tail : String, append_stable_prop url host tail) ∧
  empty_host_prop url

/-! ## Bounded property-based tests

The generators combine hosts and suffixes with several schemes, exercising
both successful and unsuccessful cases rather than relying on rare successful
random prefixes. They include empty strings, case differences, Unicode,
embedded NUL, and suffixes that are not URL-path delimiters.

Each `_prop` has its own test below. Existential string-prefix specifications
have the executable form `p.data == url.data.take p.length`, by
`List.isPrefixOf_iff_prefix` and `List.prefix_iff_eq_take`. Thus the spec tests
compare against a character slice instead of repeating the implementation.
Universal suffix/tail clauses in the postcondition are tested by instantiating
them over the generated suffix family. These tests are not used in any proof.
-/

private def testHosts : List String :=
  ["", "bank.com", "evil.com", "evilbank.com", "BANK.COM", "bank.com.evil",
   "localhost", "例え.テスト", "é", "é", "@", String.singleton (Char.ofNat 0)] ++
  (List.range 6).map (fun n => "h" ++ toString n ++ ".test")

private def testSuffixes : List String :=
  ["", "/", "/dashboard", "/phish", "?x=1", "#top", ".evil/phish",
   "@evil.com", "例", "🔒", "\n", String.singleton (Char.ofNat 0)] ++
  (List.range 6).map (fun n => "/path/" ++ toString n)

private def testUrls : List String :=
  ["", "https:", "https:/", "https://", "http://", "//bank.com", "javascript:alert(1)",
   "\nhttps://bank.com/"] ++
  testHosts.flatMap (fun host => testSuffixes.flatMap (fun suffix =>
    ["https://" ++ host ++ suffix, "http://" ++ host ++ suffix,
     "HTTPS://" ++ host ++ suffix]))

private def hasPrefixCheck (needle url : String) : Bool :=
  needle.data == url.data.take needle.length

private def prefixSpecCheck (url host : String) : Bool :=
  safe_redirect url host == hasPrefixCheck ("https://" ++ host) url

private def rejectMismatchCheck (url host : String) : Bool :=
  (safe_redirect url host == false) == !hasPrefixCheck ("https://" ++ host) url

private def httpsOnlyCheck (url host : String) : Bool :=
  !safe_redirect url host || hasPrefixCheck "https://" url

private def lengthBoundCheck (url host : String) : Bool :=
  !safe_redirect url host || decide (8 + host.length ≤ url.length)

private def validRedirectCheck (host suffix : String) : Bool :=
  safe_redirect (("https://" ++ host) ++ suffix) host

private def httpRejectedCheck (tail host : String) : Bool :=
  !safe_redirect ("http://" ++ tail) host

private def emptyRejectedCheck (host : String) : Bool := !safe_redirect "" host

private def appendStableCheck (url host tail : String) : Bool :=
  !safe_redirect url host || safe_redirect (url ++ tail) host

private def emptyHostCheck (url : String) : Bool :=
  safe_redirect url "" == hasPrefixCheck "https://" url

-- PBT: prefix_spec_prop.
example : testUrls.all (fun url => testHosts.all (prefixSpecCheck url)) = true := by
  native_decide

-- PBT: reject_mismatch_prop.
example : testUrls.all (fun url => testHosts.all (rejectMismatchCheck url)) = true := by
  native_decide

-- PBT: https_only_prop.
example : testUrls.all (fun url => testHosts.all (httpsOnlyCheck url)) = true := by
  native_decide

-- PBT: length_bound_prop.
example : testUrls.all (fun url => testHosts.all (lengthBoundCheck url)) = true := by
  native_decide

-- PBT: valid_redirect_prop, including accepted URLs for every generated host.
example : testHosts.all (fun host => testSuffixes.all (validRedirectCheck host)) = true := by
  native_decide

-- PBT: http_rejected_prop with arbitrary generated tails.
example : testUrls.all (fun tail => testHosts.all (httpRejectedCheck tail)) = true := by
  native_decide

-- PBT: empty_rejected_prop.
example : testHosts.all emptyRejectedCheck = true := by native_decide

-- PBT: append_stable_prop, with both true and false antecedents.
example : testUrls.all (fun url => testHosts.all (fun host =>
    testSuffixes.all (appendStableCheck url host))) = true := by native_decide

-- PBT: empty_host_prop.
example : testUrls.all emptyHostCheck = true := by native_decide

/-- Boolean form of all postcondition clauses, with its quantified tail instantiated. -/
private def postCheck (url host tail : String) : Bool :=
  prefixSpecCheck url host && rejectMismatchCheck url host &&
  httpsOnlyCheck url host && lengthBoundCheck url host &&
  validRedirectCheck host tail && httpRejectedCheck tail host &&
  emptyRejectedCheck host && appendStableCheck url host tail && emptyHostCheck url

private def postTests : Bool :=
  testUrls.all (fun url => testHosts.all (fun host => testSuffixes.all (postCheck url host)))

-- PBT: Post_prop, including all universal clauses over the bounded tail family.
example : postTests = true := by native_decide
#eval (testUrls.length, testHosts.length, testSuffixes.length)
#eval postTests

/-- Total correctness on the full Python string domain; tests are not proof premises. -/
theorem correctness_thm (url host : String) : Pre url host → Post_prop url host := by
  intro _
  exact ⟨prefix_spec_thm url host, reject_mismatch_thm url host,
    https_only_thm url host, length_bound_thm url host,
    valid_redirect_thm host, fun tail => http_rejected_thm tail host,
    empty_rejected_thm host, append_stable_thm url host, empty_host_thm url⟩

/-- Imperative translation: build the expected prefix, then update a mutable result. -/
def safe_redirect_imperative (redirect_url allowed_host : String) : Bool := Id.run do
  let mut expected := "https://"
  expected := expected ++ allowed_host
  let mut permitted := false
  if expected.data.isPrefixOf redirect_url.data then
    permitted := true
  return permitted

-- All six original assertions also hold for the imperative implementation.
example : safe_redirect_imperative "https://bank.com/dashboard" "bank.com" = true := by
  native_decide
example : safe_redirect_imperative "https://bank.com/" "bank.com" = true := by native_decide
example : safe_redirect_imperative "https://evil.com/phish" "bank.com" = false := by native_decide
example : safe_redirect_imperative "http://bank.com/page" "bank.com" = false := by native_decide
example : safe_redirect_imperative "" "bank.com" = false := by native_decide
example : safe_redirect_imperative "https://evilbank.com/phish" "bank.com" = false := by
  native_decide
example : safe_redirect_imperative "https://bank.com.evil/phish" "bank.com" = true := by
  native_decide
example : safe_redirect_imperative "https://" "" = true := by native_decide

#eval safe_redirect_imperative "https://bank.com/dashboard" "bank.com"
#eval safe_redirect_imperative "http://bank.com/page" "bank.com"

-- Bounded equivalence check in addition to the unrestricted proof below.
example : testUrls.all (fun url => testHosts.all (fun host =>
    safe_redirect url host == safe_redirect_imperative url host)) = true := by native_decide

/-- Both implementations return exactly the same Boolean on every pair of strings. -/
theorem functional_imperative_equivalence_thm (url host : String) :
    safe_redirect url host = safe_redirect_imperative url host := by
  change ("https://" ++ host).data.isPrefixOf url.data =
    (if ("https://" ++ host).data.isPrefixOf url.data then true else false)
  cases ("https://" ++ host).data.isPrefixOf url.data <;> rfl

end UnsafeHTTPRedirectSafe
end Agent
