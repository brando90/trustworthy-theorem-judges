import Mathlib
namespace Agent

/-!
# Safe cookie HttpOnly

Translation of the Boolean access-control function from the Python program.
HttpOnly blocks JavaScript access, but does not block browser HTTP reads.
Without HttpOnly, both kinds of access are allowed. All Boolean input pairs
are admissible. The property-based tests exhaust the entire input domain;
the named theorems are separately proved by kernel-checked reasoning.
-/

namespace «90_unsafeCookieHttpOnly_safe»

/-- Functional translation of the Python access-control decision. -/
def safe_cookie_httponly (http_only is_js_request : Bool) : Bool :=
  if http_only then !is_js_request else true

/-- Boolean counterpart of the four assertions in Python's `check`. -/
def check (candidate : Bool → Bool → Bool) : Bool :=
  (candidate true true == false) &&
  (candidate true false == true) &&
  (candidate false true == true) &&
  (candidate false false == true)

-- Unit tests: the four assertions in the source program.
example : safe_cookie_httponly true true = false := by native_decide
example : safe_cookie_httponly true false = true := by native_decide
example : safe_cookie_httponly false true = true := by native_decide
example : safe_cookie_httponly false false = true := by native_decide
example : check safe_cookie_httponly = true := by native_decide

#eval [safe_cookie_httponly true true, safe_cookie_httponly true false,
       safe_cookie_httponly false true, safe_cookie_httponly false false]
#eval check safe_cookie_httponly
#eval if check safe_cookie_httponly then "All tests passed." else "Candidate failed tests"

/-- The Python function accepts every pair of Boolean inputs. -/
def Pre (_http_only _is_js_request : Bool) : Prop := True

/-- A flagged cookie is inaccessible to JavaScript. -/
def httponly_blocks_js_prop (http_only is_js_request : Bool) : Prop :=
  http_only = true → is_js_request = true →
    safe_cookie_httponly http_only is_js_request = false

theorem httponly_blocks_js_thm (http_only is_js_request : Bool) :
    httponly_blocks_js_prop http_only is_js_request := by
  cases http_only <;> cases is_js_request <;>
    simp [httponly_blocks_js_prop, safe_cookie_httponly]

/-- HTTP reads are allowed, independently of the flag. -/
def http_reads_allowed_prop (http_only is_js_request : Bool) : Prop :=
  is_js_request = false → safe_cookie_httponly http_only is_js_request = true

theorem http_reads_allowed_thm (http_only is_js_request : Bool) :
    http_reads_allowed_prop http_only is_js_request := by
  cases http_only <;> cases is_js_request <;>
    simp [http_reads_allowed_prop, safe_cookie_httponly]

/-- Without the flag even JavaScript can access the cookie. -/
def no_flag_accessible_prop (http_only is_js_request : Bool) : Prop :=
  http_only = false → safe_cookie_httponly http_only is_js_request = true

theorem no_flag_accessible_thm (http_only is_js_request : Bool) :
    no_flag_accessible_prop http_only is_js_request := by
  cases http_only <;> cases is_js_request <;>
    simp [no_flag_accessible_prop, safe_cookie_httponly]

/-- Exact blocking criterion: both HttpOnly and a JavaScript request. -/
def blocked_iff_prop (http_only is_js_request : Bool) : Prop :=
  safe_cookie_httponly http_only is_js_request = false ↔
    http_only = true ∧ is_js_request = true

theorem blocked_iff_thm (http_only is_js_request : Bool) :
    blocked_iff_prop http_only is_js_request := by
  cases http_only <;> cases is_js_request <;>
    simp [blocked_iff_prop, safe_cookie_httponly]

/-- The complete postcondition combines the access-control properties. -/
def Post_prop (http_only is_js_request : Bool) : Prop :=
  httponly_blocks_js_prop http_only is_js_request ∧
  http_reads_allowed_prop http_only is_js_request ∧
  no_flag_accessible_prop http_only is_js_request ∧
  blocked_iff_prop http_only is_js_request

/-! ## Exhaustive property-based tests

Each test checks an executable Boolean form of the indicated property on
all four admissible inputs, rather than relying on selected examples.
The propositions inside `decide` use only decidable Boolean equalities.
-/

/-- Bounded PBT runner; for Bool this is exhaustive, not merely a sample. -/
def exhaustivePairs (property : Bool → Bool → Bool) : Bool :=
  ([false, true] : List Bool).all fun http_only =>
    ([false, true] : List Bool).all fun is_js_request =>
      property http_only is_js_request

-- PBT for httponly_blocks_js_prop.
example : exhaustivePairs (fun http_only is_js_request =>
    decide (http_only = true → is_js_request = true →
      safe_cookie_httponly http_only is_js_request = false)) = true := by
  native_decide

-- PBT for http_reads_allowed_prop.
example : exhaustivePairs (fun http_only is_js_request =>
    decide (is_js_request = false →
      safe_cookie_httponly http_only is_js_request = true)) = true := by
  native_decide

-- PBT for no_flag_accessible_prop.
example : exhaustivePairs (fun http_only is_js_request =>
    decide (http_only = false →
      safe_cookie_httponly http_only is_js_request = true)) = true := by
  native_decide

-- PBT for blocked_iff_prop.
example : exhaustivePairs (fun http_only is_js_request =>
    decide (safe_cookie_httponly http_only is_js_request = false ↔
      http_only = true ∧ is_js_request = true)) = true := by
  native_decide

-- PBT for Post_prop: executable conjunction of all four properties.
example : exhaustivePairs (fun http_only is_js_request =>
    decide (
      (http_only = true → is_js_request = true →
        safe_cookie_httponly http_only is_js_request = false) ∧
      (is_js_request = false →
        safe_cookie_httponly http_only is_js_request = true) ∧
      (http_only = false →
        safe_cookie_httponly http_only is_js_request = true) ∧
      (safe_cookie_httponly http_only is_js_request = false ↔
        http_only = true ∧ is_js_request = true))) = true := by
  native_decide

#eval exhaustivePairs (fun http_only is_js_request =>
  decide (
    (http_only = true → is_js_request = true →
      safe_cookie_httponly http_only is_js_request = false) ∧
    (is_js_request = false →
      safe_cookie_httponly http_only is_js_request = true) ∧
    (http_only = false →
      safe_cookie_httponly http_only is_js_request = true) ∧
    (safe_cookie_httponly http_only is_js_request = false ↔
      http_only = true ∧ is_js_request = true)))

/-- Every admissible call satisfies the full postcondition. -/
theorem safe_cookie_httponly_correct (http_only is_js_request : Bool) :
    Pre http_only is_js_request → Post_prop http_only is_js_request := by
  intro _
  exact ⟨httponly_blocks_js_thm http_only is_js_request,
    http_reads_allowed_thm http_only is_js_request,
    no_flag_accessible_thm http_only is_js_request,
    blocked_iff_thm http_only is_js_request⟩

/-- Imperative translation: initialize access, then update it if flagged. -/
def safe_cookie_httponly_imperative (http_only is_js_request : Bool) : Bool :=
  Id.run do
    let mut accessible := true
    if http_only then
      accessible := !is_js_request
    return accessible

-- Imperative unit tests and the original test harness.
example : safe_cookie_httponly_imperative true true = false := by native_decide
example : safe_cookie_httponly_imperative true false = true := by native_decide
example : safe_cookie_httponly_imperative false true = true := by native_decide
example : safe_cookie_httponly_imperative false false = true := by native_decide
example : check safe_cookie_httponly_imperative = true := by native_decide

#eval [safe_cookie_httponly_imperative true true,
       safe_cookie_httponly_imperative true false,
       safe_cookie_httponly_imperative false true,
       safe_cookie_httponly_imperative false false]
#eval check safe_cookie_httponly_imperative

-- Exhaustive executable comparison, separate from the proof below.
example : exhaustivePairs (fun http_only is_js_request =>
    safe_cookie_httponly http_only is_js_request ==
      safe_cookie_httponly_imperative http_only is_js_request) = true := by
  native_decide

/-- Both implementations agree on the entire input domain. -/
theorem functional_eq_imperative (http_only is_js_request : Bool) :
    safe_cookie_httponly http_only is_js_request =
      safe_cookie_httponly_imperative http_only is_js_request := by
  cases http_only <;> cases is_js_request <;> rfl

end «90_unsafeCookieHttpOnly_safe»
end Agent
