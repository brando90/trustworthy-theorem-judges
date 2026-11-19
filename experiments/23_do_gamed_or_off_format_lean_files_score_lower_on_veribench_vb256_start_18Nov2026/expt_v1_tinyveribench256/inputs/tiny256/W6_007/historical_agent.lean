import Mathlib
namespace Agent

/-!
# Unsafe session cookie without enforcement of the Secure flag

Translation of the MIT 6.858 web-security example. The function deliberately
returns `true` for every URL and every cookie flag value: in particular, even a
cookie marked Secure is sent to an HTTP URL. This models the supplied vulnerable
program, not a repaired browser policy. `Int` models Python's unbounded signed
integer flags, and no validity restriction is imposed on the URL string.

The Boolean `check` harness represents successful completion of the five Python
assertions; `false` represents an assertion failure. Bounded property-based tests
are executable evidence, separate from the universally quantified kernel proofs.
-/

namespace UnsafeInsecureCookieSecure

-- Implementation and flag constants.
def SECURE_FLAG : Int := 0x01

def HTTPONLY_FLAG : Int := 0x02

def unsafe_session_cookie (_url : String) (_cookie_flags : Int) : Bool :=
  true

def check (candidate : String → Int → Bool) : Bool :=
  candidate "https://bensbank.com/" (Int.lor SECURE_FLAG HTTPONLY_FLAG) &&
  candidate "http://bensbank.com/" (Int.lor SECURE_FLAG HTTPONLY_FLAG) &&
  candidate "http://bensbank.com/" 0 &&
  candidate "https://bensbank.com/account" SECURE_FLAG &&
  candidate "http://bensbank.com/login" HTTPONLY_FLAG

-- Unit tests: the five assertions in the Python source, without repairing them.
example : Int.lor SECURE_FLAG HTTPONLY_FLAG = 3 := by native_decide

example : unsafe_session_cookie "https://bensbank.com/"
    (Int.lor SECURE_FLAG HTTPONLY_FLAG) = true := by native_decide

example : unsafe_session_cookie "http://bensbank.com/"
    (Int.lor SECURE_FLAG HTTPONLY_FLAG) = true := by native_decide

example : unsafe_session_cookie "http://bensbank.com/" 0 = true := by
  native_decide

example : unsafe_session_cookie "https://bensbank.com/account" SECURE_FLAG = true := by
  native_decide

example : unsafe_session_cookie "http://bensbank.com/login" HTTPONLY_FLAG = true := by
  native_decide

example : check unsafe_session_cookie = true := by native_decide

#eval check unsafe_session_cookie
#eval if check unsafe_session_cookie then "All tests passed." else "Candidate failed insecure cookie tests"

-- Precondition: every string and every signed integer are admissible.
def Pre (_url : String) (_cookie_flags : Int) : Prop := True

-- Every request transmits the cookie, not merely the five fixed test requests.
def always_transmitted_prop (url : String) (cookie_flags : Int) : Prop :=
  unsafe_session_cookie url cookie_flags = true

theorem always_transmitted_thm (url : String) (cookie_flags : Int) :
    always_transmitted_prop url cookie_flags := by
  rfl

-- Neither Secure nor HttpOnly (nor any other flag bits) affect the result.
def flags_ignored_prop (url : String) (flags other_flags : Int) : Prop :=
  unsafe_session_cookie url flags = unsafe_session_cookie url other_flags

theorem flags_ignored_thm (url : String) (flags other_flags : Int) :
    flags_ignored_prop url flags other_flags := by
  rfl

-- The scheme, host, path, and even URL validity are ignored.
def url_ignored_prop (url other_url : String) (cookie_flags : Int) : Prop :=
  unsafe_session_cookie url cookie_flags = unsafe_session_cookie other_url cookie_flags

theorem url_ignored_thm (url other_url : String) (cookie_flags : Int) :
    url_ignored_prop url other_url cookie_flags := by
  rfl

-- Explicit vulnerability: every HTTP-prefixed request transmits the cookie,
-- including flags containing SECURE_FLAG. The suffix is wholly unrestricted.
def http_leak_prop (suffix : String) (cookie_flags : Int) : Prop :=
  unsafe_session_cookie ("http://" ++ suffix) cookie_flags = true

theorem http_leak_thm (suffix : String) (cookie_flags : Int) :
    http_leak_prop suffix cookie_flags := by
  rfl

-- Ordinary HTTPS transmission is preserved as well.
def https_transmitted_prop (suffix : String) (cookie_flags : Int) : Prop :=
  unsafe_session_cookie ("https://" ++ suffix) cookie_flags = true

theorem https_transmitted_thm (suffix : String) (cookie_flags : Int) :
    https_transmitted_prop suffix cookie_flags := by
  rfl

-- Kernel proof that the translated assertion harness succeeds.
theorem check_unsafe_session_cookie_thm : check unsafe_session_cookie = true := by
  rfl

-- Postcondition includes universal independence of both input arguments and
-- explicitly records HTTP leakage, HTTPS transmission, and the source checks.
def Post_prop (url : String) (cookie_flags : Int) : Prop :=
  always_transmitted_prop url cookie_flags ∧
  (∀ other_flags : Int, flags_ignored_prop url cookie_flags other_flags) ∧
  (∀ other_url : String, url_ignored_prop url other_url cookie_flags) ∧
  http_leak_prop url cookie_flags ∧
  https_transmitted_prop url cookie_flags ∧
  check unsafe_session_cookie = true

/-! ## Bounded property-based tests

Strings have no finite exhaustive domain. These tests enumerate a varied finite
corpus of strings and all flag integers from -32 through 32. Comparison properties
use the Cartesian product of the corresponding samples. These bounds apply only
to tests, never to the specifications or theorems.
-/

def testUrls : List String :=
  ["", "bensbank.com/", "https://bensbank.com/", "http://bensbank.com/",
   "https://bensbank.com/account", "http://bensbank.com/login",
   "ftp://bensbank.com/", "HTTP://bensbank.com/", "not a URL",
   "http://example.org/?q=1#fragment", "https://example.org/λ"]

def testFlags : List Int :=
  (List.range 65).map (fun n => (n : Int) - 32)

-- PBT for always_transmitted_prop.
example : testUrls.all (fun url => testFlags.all (fun flags =>
    unsafe_session_cookie url flags == true)) = true := by
  native_decide

-- PBT for flags_ignored_prop, including negative and unknown flag bits.
example : testUrls.all (fun url => testFlags.all (fun flags =>
    testFlags.all (fun other_flags =>
      unsafe_session_cookie url flags == unsafe_session_cookie url other_flags))) = true := by
  native_decide

-- PBT for url_ignored_prop, including different schemes and malformed URLs.
example : testUrls.all (fun url => testUrls.all (fun other_url =>
    testFlags.all (fun flags =>
      unsafe_session_cookie url flags == unsafe_session_cookie other_url flags))) = true := by
  native_decide

-- PBT for http_leak_prop.
example : testUrls.all (fun suffix => testFlags.all (fun flags =>
    unsafe_session_cookie ("http://" ++ suffix) flags == true)) = true := by
  native_decide

-- PBT for https_transmitted_prop.
example : testUrls.all (fun suffix => testFlags.all (fun flags =>
    unsafe_session_cookie ("https://" ++ suffix) flags == true)) = true := by
  native_decide

-- PBT for Post_prop: its universally quantified comparison arguments are
-- enumerated over the same finite samples, and every conjunct is checked.
def postTest : Bool :=
  testUrls.all (fun url => testFlags.all (fun flags =>
    (unsafe_session_cookie url flags == true) &&
    testFlags.all (fun other_flags =>
      unsafe_session_cookie url flags == unsafe_session_cookie url other_flags) &&
    testUrls.all (fun other_url =>
      unsafe_session_cookie url flags == unsafe_session_cookie other_url flags) &&
    (unsafe_session_cookie ("http://" ++ url) flags == true) &&
    (unsafe_session_cookie ("https://" ++ url) flags == true) &&
    check unsafe_session_cookie))

example : postTest = true := by native_decide
#eval postTest

-- Correctness describes the vulnerable behavior; it does not assert security.
theorem correctness_thm (url : String) (cookie_flags : Int) :
    Pre url cookie_flags → Post_prop url cookie_flags := by
  intro _
  exact ⟨always_transmitted_thm url cookie_flags,
    (fun other_flags => flags_ignored_thm url cookie_flags other_flags),
    (fun other_url => url_ignored_thm url other_url cookie_flags),
    http_leak_thm url cookie_flags,
    https_transmitted_thm url cookie_flags,
    check_unsafe_session_cookie_thm⟩

-- Imperative implementation: the result is assigned unconditionally, without
-- inspecting either argument. No Secure or URL-scheme check is introduced.
def unsafe_session_cookie_imp (_url : String) (_cookie_flags : Int) : Bool := Id.run do
  let mut transmitted := false
  transmitted := true
  return transmitted

-- Imperative tests mirror all five source assertions.
example : unsafe_session_cookie_imp "https://bensbank.com/"
    (Int.lor SECURE_FLAG HTTPONLY_FLAG) = true := by native_decide

example : unsafe_session_cookie_imp "http://bensbank.com/"
    (Int.lor SECURE_FLAG HTTPONLY_FLAG) = true := by native_decide

example : unsafe_session_cookie_imp "http://bensbank.com/" 0 = true := by
  native_decide

example : unsafe_session_cookie_imp "https://bensbank.com/account" SECURE_FLAG = true := by
  native_decide

example : unsafe_session_cookie_imp "http://bensbank.com/login" HTTPONLY_FLAG = true := by
  native_decide

example : check unsafe_session_cookie_imp = true := by native_decide
#eval check unsafe_session_cookie_imp

-- A bounded equivalence test supplements, but does not replace, the proof below.
example : testUrls.all (fun url => testFlags.all (fun flags =>
    unsafe_session_cookie url flags == unsafe_session_cookie_imp url flags)) = true := by
  native_decide

-- Extensional equality covers every URL and every signed integer flag value.
theorem functional_eq_imperative_thm :
    unsafe_session_cookie = unsafe_session_cookie_imp := by
  funext url cookie_flags
  rfl

end UnsafeInsecureCookieSecure
end Agent
