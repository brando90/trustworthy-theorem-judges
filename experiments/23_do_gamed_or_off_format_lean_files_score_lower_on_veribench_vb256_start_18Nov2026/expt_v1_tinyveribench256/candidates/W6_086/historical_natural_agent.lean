import Mathlib
namespace Agent

/-!
# Unsafe TLS certificate-name validation

Translation of `unsafe_tls_cert_name` and its Python test suite. Python's
unbounded integers are modelled by `Int`. The function deliberately returns
`true` for every input: even a certificate for a different server is accepted.
The specification records this vulnerability, not secure TLS validation.

The bounded property-based tests include negative integers, zero, and the
original test values. They supplement the universally quantified kernel proofs.
-/

namespace UnsafeTlsCertName

/-- Deliberately ignores both names, exactly as in the Python implementation. -/
def unsafe_tls_cert_name (_server_name _cert_name : Int) : Bool :=
  true

/-- Boolean form of the conjunction of assertions in Python's `check`. -/
def check (candidate : Int → Int → Bool) : Bool :=
  candidate 100 100 &&
  candidate 200 200 &&
  candidate 0 0 &&
  candidate 100 200 &&
  candidate 500 999 &&
  candidate 0 999 &&
  candidate 999 0

-- Unit tests: all seven assertions from the Python source.
example : unsafe_tls_cert_name 100 100 = true := by native_decide
example : unsafe_tls_cert_name 200 200 = true := by native_decide
example : unsafe_tls_cert_name 0 0 = true := by native_decide
example : unsafe_tls_cert_name 100 200 = true := by native_decide
example : unsafe_tls_cert_name 500 999 = true := by native_decide
example : unsafe_tls_cert_name 0 999 = true := by native_decide
example : unsafe_tls_cert_name 999 0 = true := by native_decide
example : check unsafe_tls_cert_name = true := by native_decide

-- Python integers are not restricted to the nonnegative test fixtures.
example : unsafe_tls_cert_name (-100) 200 = true := by native_decide
example : unsafe_tls_cert_name 100 (-200) = true := by native_decide

#eval check unsafe_tls_cert_name
#eval if check unsafe_tls_cert_name then "All tests passed." else "Tests failed."

/-- Every pair of Python integers is admissible; no name relation is required. -/
def Pre (_server_name _cert_name : Int) : Prop := True

/-- The exact return-value contract, on all integer inputs. -/
def always_accepts_prop (server_name cert_name : Int) : Prop :=
  unsafe_tls_cert_name server_name cert_name = true

theorem always_accepts_thm (server_name cert_name : Int) :
    always_accepts_prop server_name cert_name := by
  rfl

/-- Matching certificate names are accepted. -/
def matching_names_prop (server_name cert_name : Int) : Prop :=
  server_name = cert_name → unsafe_tls_cert_name server_name cert_name = true

theorem matching_names_thm (server_name cert_name : Int) :
    matching_names_prop server_name cert_name := by
  intro _
  rfl

/-- The vulnerability: unequal certificate names are also accepted. -/
def mismatched_names_prop (server_name cert_name : Int) : Prop :=
  server_name ≠ cert_name → unsafe_tls_cert_name server_name cert_name = true

theorem mismatched_names_thm (server_name cert_name : Int) :
    mismatched_names_prop server_name cert_name := by
  intro _
  rfl

/-- The postcondition records unconditional acceptance and both name cases. -/
def Post_prop (server_name cert_name : Int) : Prop :=
  always_accepts_prop server_name cert_name ∧
  matching_names_prop server_name cert_name ∧
  mismatched_names_prop server_name cert_name

-- Property-based tests: exhaustive Cartesian products of a signed range and
-- the original nonzero fixtures. These are evidence, not theorem proofs.
def pbtNames : List Int :=
  ((List.range 41).map (fun n => (n : Int) - 20)) ++ [100, 200, 500, 999]

-- PBT for always_accepts_prop, in executable Boolean form.
example :
    pbtNames.all (fun server_name =>
      pbtNames.all (fun cert_name =>
        unsafe_tls_cert_name server_name cert_name)) = true := by
  native_decide

-- PBT for matching_names_prop. Every sampled name also has a matching partner.
example :
    pbtNames.all (fun server_name =>
      pbtNames.all (fun cert_name =>
        decide (server_name = cert_name →
          unsafe_tls_cert_name server_name cert_name = true))) = true := by
  native_decide

-- PBT for mismatched_names_prop, including negative/positive mismatches.
example :
    pbtNames.all (fun server_name =>
      pbtNames.all (fun cert_name =>
        decide (server_name ≠ cert_name →
          unsafe_tls_cert_name server_name cert_name = true))) = true := by
  native_decide

-- PBT for Post_prop: the executable conjunction of all its component claims.
-- Pre is True, so all sampled pairs are admissible.
example :
    pbtNames.all (fun server_name =>
      pbtNames.all (fun cert_name =>
        decide (
          unsafe_tls_cert_name server_name cert_name = true ∧
          (server_name = cert_name →
            unsafe_tls_cert_name server_name cert_name = true) ∧
          (server_name ≠ cert_name →
            unsafe_tls_cert_name server_name cert_name = true)))) = true := by
  native_decide

/-- Correctness means fidelity to the unsafe Python behavior, not TLS security. -/
theorem correctness_thm (server_name cert_name : Int) :
    Pre server_name cert_name → Post_prop server_name cert_name := by
  intro _
  exact ⟨always_accepts_thm server_name cert_name,
    matching_names_thm server_name cert_name,
    mismatched_names_thm server_name cert_name⟩

/-- Imperative version: overwrite the mutable result without inspecting names. -/
def unsafe_tls_cert_name_imperative (_server_name _cert_name : Int) : Bool := Id.run do
  let mut accepted : Bool := false
  accepted := true
  return accepted

-- Imperative tests, reproducing the same seven source assertions.
example : unsafe_tls_cert_name_imperative 100 100 = true := by native_decide
example : unsafe_tls_cert_name_imperative 200 200 = true := by native_decide
example : unsafe_tls_cert_name_imperative 0 0 = true := by native_decide
example : unsafe_tls_cert_name_imperative 100 200 = true := by native_decide
example : unsafe_tls_cert_name_imperative 500 999 = true := by native_decide
example : unsafe_tls_cert_name_imperative 0 999 = true := by native_decide
example : unsafe_tls_cert_name_imperative 999 0 = true := by native_decide
example : check unsafe_tls_cert_name_imperative = true := by native_decide
example : unsafe_tls_cert_name_imperative (-100) 200 = true := by native_decide

#eval check unsafe_tls_cert_name_imperative
#eval unsafe_tls_cert_name_imperative 500 999

/-- The two implementations agree for every pair of unbounded integers. -/
theorem functional_eq_imperative_thm (server_name cert_name : Int) :
    unsafe_tls_cert_name server_name cert_name =
      unsafe_tls_cert_name_imperative server_name cert_name := by
  rfl

end UnsafeTlsCertName
end Agent
