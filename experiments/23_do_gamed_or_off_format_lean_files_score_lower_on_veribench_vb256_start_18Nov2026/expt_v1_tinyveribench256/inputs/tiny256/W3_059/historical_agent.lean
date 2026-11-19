import Mathlib
namespace Agent

/-!
# Session cookies protected by the Secure flag

Translation of the MIT 6.858 Web Security example.  A cookie whose Secure bit
is set is transmitted exactly when the URL starts with the case-sensitive
prefix `https://`.  With no Secure bit, the Python function transmits the
cookie regardless of scheme (the legacy, insecure branch).

Flags use `Int`, preserving Python's unbounded signed-integer domain and
bitwise semantics; no nonnegativity assumption is imposed.  Strings are
checked as strings, not parsed or normalized as URLs.  HTTPONLY is a distinct
flag and is not consulted by the transmission decision.
-/

namespace SafeSessionCookie

def SECURE_FLAG : Int := 0x01

def HTTPONLY_FLAG : Int := 0x02

/-- The mask used by Python's `(cookie_flags & SECURE_FLAG) != 0`. -/
def secureMask (cookie_flags : Int) : Int := Int.land cookie_flags SECURE_FLAG

/-- Functional translation, including the unconditional legacy branch. -/
def safe_session_cookie (url : String) (cookie_flags : Int) : Bool :=
  if secureMask cookie_flags ≠ 0 then url.startsWith "https://" else true

-- The five assertions in Python's `check`.
example : safe_session_cookie "https://bensbank.com/"
    (Int.lor SECURE_FLAG HTTPONLY_FLAG) = true := by native_decide
example : safe_session_cookie "http://bensbank.com/"
    (Int.lor SECURE_FLAG HTTPONLY_FLAG) = false := by native_decide
example : safe_session_cookie "http://bensbank.com/" 0 = true := by native_decide
example : safe_session_cookie "https://bensbank.com/account" SECURE_FLAG = true := by
  native_decide
example : safe_session_cookie "http://bensbank.com/login" SECURE_FLAG = false := by
  native_decide

/-- Executable counterpart of the source's `check(candidate)`. -/
def check (candidate : String → Int → Bool) : Bool :=
  candidate "https://bensbank.com/" (Int.lor SECURE_FLAG HTTPONLY_FLAG) &&
  !(candidate "http://bensbank.com/" (Int.lor SECURE_FLAG HTTPONLY_FLAG)) &&
  candidate "http://bensbank.com/" 0 &&
  candidate "https://bensbank.com/account" SECURE_FLAG &&
  !(candidate "http://bensbank.com/login" SECURE_FLAG)

#eval check safe_session_cookie
#eval safe_session_cookie "http://bensbank.com/" (-1)

/-- All strings and all Python integers are admissible. -/
def Pre (_url : String) (_cookie_flags : Int) : Prop := True

/-- A Secure cookie's decision is exactly the HTTPS-prefix check. -/
def secure_scheme_prop (url : String) (flags : Int) : Prop :=
  secureMask flags ≠ 0 →
    safe_session_cookie url flags = url.startsWith "https://"

theorem secure_scheme_thm (url : String) (flags : Int) :
    secure_scheme_prop url flags := by
  intro h
  simp [safe_session_cookie, h]

/-- Secure cookies cannot be sent to any non-HTTPS string, not just one host. -/
def secure_withheld_prop (url : String) (flags : Int) : Prop :=
  secureMask flags ≠ 0 → url.startsWith "https://" = false →
    safe_session_cookie url flags = false

theorem secure_withheld_thm (url : String) (flags : Int) :
    secure_withheld_prop url flags := by
  intro h hs
  simp [safe_session_cookie, h, hs]

/-- The no-Secure branch is unconditional, including for invalid URLs. -/
def legacy_transmit_prop (url : String) (flags : Int) : Prop :=
  secureMask flags = 0 → safe_session_cookie url flags = true

theorem legacy_transmit_thm (url : String) (flags : Int) :
    legacy_transmit_prop url flags := by
  intro h
  simp [safe_session_cookie, h]

/-- HTTPS URLs transmit with or without the Secure bit. -/
def https_transmit_prop (url : String) (flags : Int) : Prop :=
  url.startsWith "https://" = true → safe_session_cookie url flags = true

theorem https_transmit_thm (url : String) (flags : Int) :
    https_transmit_prop url flags := by
  intro hs
  simp [safe_session_cookie, hs]

/-- Exact characterization: the legacy branch OR an HTTPS prefix. -/
def transmit_iff_prop (url : String) (flags : Int) : Prop :=
  safe_session_cookie url flags = true ↔
    secureMask flags = 0 ∨ url.startsWith "https://" = true

theorem transmit_iff_thm (url : String) (flags : Int) :
    transmit_iff_prop url flags := by
  unfold transmit_iff_prop
  by_cases h : secureMask flags = 0 <;> simp [safe_session_cookie, h]

/-- Exact characterization of withholding, including its converse. -/
def withheld_iff_prop (url : String) (flags : Int) : Prop :=
  safe_session_cookie url flags = false ↔
    secureMask flags ≠ 0 ∧ url.startsWith "https://" = false

theorem withheld_iff_thm (url : String) (flags : Int) :
    withheld_iff_prop url flags := by
  unfold withheld_iff_prop
  by_cases h : secureMask flags = 0 <;> simp [safe_session_cookie, h]

/-- Flags with the same masked Secure bit have identical behavior. -/
def mask_invariance_prop (url : String) (flags otherFlags : Int) : Prop :=
  secureMask flags = secureMask otherFlags →
    safe_session_cookie url flags = safe_session_cookie url otherFlags

theorem mask_invariance_thm (url : String) (flags otherFlags : Int) :
    mask_invariance_prop url flags otherFlags := by
  intro h
  simp only [safe_session_cookie, h]

/-- The complete pointwise contract, without assumptions on URL syntax. -/
def Post_prop (url : String) (flags : Int) : Prop :=
  secure_scheme_prop url flags ∧
  secure_withheld_prop url flags ∧
  legacy_transmit_prop url flags ∧
  https_transmit_prop url flags ∧
  transmit_iff_prop url flags ∧
  withheld_iff_prop url flags ∧
  (∀ otherFlags, mask_invariance_prop url flags otherFlags)

/-!
## Bounded property-based tests

These are finite-product tests, not proofs of the universal properties above.
URLs are generated from a varied set of scheme-like prefixes and suffixes;
flags exhaust every integer in [-32, 32] and also include large signed values.
Every executable property has a separate Boolean test below.  Implications
are encoded as `!antecedent || consequent`, and equivalences as Bool equality.
-/

def urlPrefixes : List String :=
  ["https://", "http://", "HTTPS://", "Http://", "https:/", "https:",
   "httpsx://", " https://", "ftp://", "//", "", "xhttps://"]

def urlSuffixes : List String :=
  ["", "bensbank.com/", "bensbank.com/account", "bensbank.com/login",
   "evil.example/?next=https://bensbank.com/", "例え.test/π", "/", "https://"]

def testUrls : List String :=
  urlPrefixes.flatMap fun pre => urlSuffixes.map fun tail => pre ++ tail

def testFlags : List Int :=
  (List.range 65).map (fun n => (n : Int) - 32) ++
    [2^80, 2^80 + 1, -(2^80), -(2^80) - 1]

def allInputs (p : String → Int → Bool) : Bool :=
  testUrls.all fun url => testFlags.all fun flags => p url flags

-- PBT for secure_scheme_prop.
def secureSchemeTest (url : String) (flags : Int) : Bool :=
  (secureMask flags == 0) ||
    (safe_session_cookie url flags == url.startsWith "https://")
example : allInputs secureSchemeTest = true := by native_decide

-- PBT for secure_withheld_prop.
def secureWithheldTest (url : String) (flags : Int) : Bool :=
  (secureMask flags == 0) || url.startsWith "https://" ||
    !safe_session_cookie url flags
example : allInputs secureWithheldTest = true := by native_decide

-- PBT for legacy_transmit_prop.
def legacyTransmitTest (url : String) (flags : Int) : Bool :=
  (secureMask flags != 0) || safe_session_cookie url flags
example : allInputs legacyTransmitTest = true := by native_decide

-- PBT for https_transmit_prop.
def httpsTransmitTest (url : String) (flags : Int) : Bool :=
  !(url.startsWith "https://") || safe_session_cookie url flags
example : allInputs httpsTransmitTest = true := by native_decide

-- PBT for transmit_iff_prop.
def transmitIffTest (url : String) (flags : Int) : Bool :=
  safe_session_cookie url flags ==
    ((secureMask flags == 0) || url.startsWith "https://")
example : allInputs transmitIffTest = true := by native_decide

-- PBT for withheld_iff_prop.
def withheldIffTest (url : String) (flags : Int) : Bool :=
  (!safe_session_cookie url flags) ==
    ((secureMask flags != 0) && !(url.startsWith "https://"))
example : allInputs withheldIffTest = true := by native_decide

-- PBT for mask_invariance_prop, over two independently enumerated flags.
def maskInvarianceTest (url : String) (flags otherFlags : Int) : Bool :=
  (secureMask flags != secureMask otherFlags) ||
    (safe_session_cookie url flags == safe_session_cookie url otherFlags)
example : allInputs (fun url flags =>
    testFlags.all (maskInvarianceTest url flags)) = true := by native_decide

-- PBT for the conjunction Post_prop; its universally quantified component
-- is exhaustively checked over the same finite testFlags domain.
def postTest (url : String) (flags : Int) : Bool :=
  secureSchemeTest url flags && secureWithheldTest url flags &&
  legacyTransmitTest url flags && httpsTransmitTest url flags &&
  transmitIffTest url flags && withheldIffTest url flags &&
  testFlags.all (maskInvarianceTest url flags)
example : allInputs postTest = true := by native_decide
#eval allInputs postTest

/-- Every admissible input satisfies the whole contract. -/
theorem correctness_thm (url : String) (flags : Int) :
    Pre url flags → Post_prop url flags := by
  intro _
  exact ⟨secure_scheme_thm url flags, secure_withheld_thm url flags,
    legacy_transmit_thm url flags, https_transmit_thm url flags,
    transmit_iff_thm url flags, withheld_iff_thm url flags,
    mask_invariance_thm url flags⟩

/-- Imperative translation with an explicitly mutable transmission decision. -/
def safe_session_cookie_imperative (url : String) (cookie_flags : Int) : Bool := Id.run do
  let mut transmit := true
  if secureMask cookie_flags ≠ 0 then
    transmit := url.startsWith "https://"
  return transmit

-- Imperative versions of all five original assertions.
example : safe_session_cookie_imperative "https://bensbank.com/"
    (Int.lor SECURE_FLAG HTTPONLY_FLAG) = true := by native_decide
example : safe_session_cookie_imperative "http://bensbank.com/"
    (Int.lor SECURE_FLAG HTTPONLY_FLAG) = false := by native_decide
example : safe_session_cookie_imperative "http://bensbank.com/" 0 = true := by
  native_decide
example : safe_session_cookie_imperative "https://bensbank.com/account"
    SECURE_FLAG = true := by native_decide
example : safe_session_cookie_imperative "http://bensbank.com/login"
    SECURE_FLAG = false := by native_decide
#eval check safe_session_cookie_imperative

-- Bounded PBT for the functional/imperative correspondence.
example : allInputs (fun url flags =>
    safe_session_cookie url flags == safe_session_cookie_imperative url flags) = true := by
  native_decide

theorem functional_imperative_equiv_thm (url : String) (flags : Int) :
    safe_session_cookie url flags = safe_session_cookie_imperative url flags := by
  by_cases h : secureMask flags ≠ 0 <;>
    simp [safe_session_cookie, safe_session_cookie_imperative, h]

end SafeSessionCookie
end Agent
