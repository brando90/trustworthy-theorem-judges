import Mathlib

/-!
# Unsafe TLS version downgrade

The server selects the minimum of its maximum supported version and the maximum
version visible in the client's offer. Versions 0 through 4 represent SSL 3.0
through TLS 1.3. `Int` preserves the Python function's behavior on all integers,
including values outside that conventional range.

There is no check binding the visible offer to the client's true capability.
Consequently, an attacker can force a strictly weaker negotiated version by
presenting an offer below both endpoints' true capabilities. The theorems describe
this unsafe behavior faithfully; they do not assert downgrade resistance.
-/

namespace UnsafeTlsDowngrade

/- Functional implementation. -/

def unsafe_tls_downgrade (client_offered_max server_max : Int) : Int :=
  min client_offered_max server_max

/-- Boolean counterpart of the six assertions in the Python test harness. -/
def check (candidate : Int → Int → Int) : Bool :=
  candidate 4 4 == 4 &&
  candidate 1 4 == 1 &&
  candidate 4 2 == 2 &&
  candidate 3 3 == 3 &&
  candidate 4 0 == 0 &&
  decide (candidate 2 4 ≥ candidate 1 4)

/- Unit tests, including every assertion in the source. -/

example : unsafe_tls_downgrade 4 4 = 4 := by native_decide
example : unsafe_tls_downgrade 1 4 = 1 := by native_decide
example : unsafe_tls_downgrade 4 2 = 2 := by native_decide
example : unsafe_tls_downgrade 3 3 = 3 := by native_decide
example : unsafe_tls_downgrade 4 0 = 0 := by native_decide
example : unsafe_tls_downgrade 2 4 ≥ unsafe_tls_downgrade 1 4 := by native_decide
example : unsafe_tls_downgrade (-2) 4 = -2 := by native_decide
example : unsafe_tls_downgrade 7 9 = 7 := by native_decide
example : check unsafe_tls_downgrade = true := by native_decide

#eval unsafe_tls_downgrade 1 4
#eval check unsafe_tls_downgrade
#eval if check unsafe_tls_downgrade then IO.println "All tests passed."
      else throw (IO.userError "Candidate failed tests")

/-- The Python function accepts every pair of integers. -/
def Pre (_client_offered_max _server_max : Int) : Prop := True

/- Properties and their proofs. -/

/-- The exact result is the highest common version of the visible offer. -/
def highest_common_prop (offered server result : Int) : Prop :=
  result = min offered server

theorem highest_common_thm (offered server : Int) :
    highest_common_prop offered server (unsafe_tls_downgrade offered server) := by
  rfl

def bounds_prop (offered server result : Int) : Prop :=
  result ≤ offered ∧ result ≤ server

theorem bounds_thm (offered server : Int) :
    bounds_prop offered server (unsafe_tls_downgrade offered server) := by
  exact ⟨min_le_left offered server, min_le_right offered server⟩

def selection_prop (offered server result : Int) : Prop :=
  result = offered ∨ result = server

theorem selection_thm (offered server : Int) :
    selection_prop offered server (unsafe_tls_downgrade offered server) := by
  rcases le_total offered server with h | h
  · exact Or.inl (min_eq_left h)
  · exact Or.inr (min_eq_right h)

/-- Whichever endpoint has the lower maximum determines the result. -/
def limiting_endpoint_prop (offered server result : Int) : Prop :=
  (offered ≤ server → result = offered) ∧
  (server ≤ offered → result = server)

theorem limiting_endpoint_thm (offered server : Int) :
    limiting_endpoint_prop offered server (unsafe_tls_downgrade offered server) := by
  exact ⟨fun h => min_eq_left h, fun h => min_eq_right h⟩

/-- A version is at most the result exactly when both visible limits permit it. -/
def greatest_common_prop (offered server version : Int) : Prop :=
  version ≤ unsafe_tls_downgrade offered server ↔
    version ≤ offered ∧ version ≤ server

theorem greatest_common_thm (offered server version : Int) :
    greatest_common_prop offered server version := by
  exact le_min_iff

def offer_monotone_prop (lower higher server : Int) : Prop :=
  lower ≤ higher →
    unsafe_tls_downgrade lower server ≤ unsafe_tls_downgrade higher server

theorem offer_monotone_thm (lower higher server : Int) :
    offer_monotone_prop lower higher server := by
  intro h
  exact min_le_min_right server h

def server_monotone_prop (offered lower higher : Int) : Prop :=
  lower ≤ higher →
    unsafe_tls_downgrade offered lower ≤ unsafe_tls_downgrade offered higher

theorem server_monotone_thm (offered lower higher : Int) :
    server_monotone_prop offered lower higher := by
  intro h
  exact min_le_min_left offered h

/-- Stripping the offer below the true common maximum forces that weaker version. -/
def downgrade_prop (tampered true_client server : Int) : Prop :=
  tampered < min true_client server →
    unsafe_tls_downgrade tampered server = tampered ∧
    unsafe_tls_downgrade tampered server < unsafe_tls_downgrade true_client server

theorem downgrade_thm (tampered true_client server : Int) :
    downgrade_prop tampered true_client server := by
  intro h
  have hserver : tampered ≤ server :=
    le_of_lt (lt_of_lt_of_le h (min_le_right true_client server))
  change min tampered server = tampered ∧
    min tampered server < min true_client server
  rw [min_eq_left hserver]
  exact ⟨rfl, h⟩

/-- The result satisfies the exact negotiation rule and its endpoint constraints. -/
def Post_prop (offered server result : Int) : Prop :=
  highest_common_prop offered server result ∧
  bounds_prop offered server result ∧
  selection_prop offered server result ∧
  limiting_endpoint_prop offered server result

/-
Property-based tests: exhaustively check the executable form of every `_prop`
above and of `Post_prop`. The domain -10 through 14 includes all TLS labels,
equal inputs, negative integers, and integers above the conventional labels.
Each pair test checks 625 cases; each triple test checks 15,625 cases.
Implications are decidable and include both admissible and vacuous cases.
These bounded checks supplement the unrestricted integer proofs.
-/

private def pbtInputs : List Int :=
  (List.range 25).map (fun n => (n : Int) - 10)

-- PBT for highest_common_prop.
example : pbtInputs.all (fun offered => pbtInputs.all (fun server =>
    decide (unsafe_tls_downgrade offered server = min offered server))) = true := by
  native_decide

-- PBT for bounds_prop.
example : pbtInputs.all (fun offered => pbtInputs.all (fun server =>
    let result := unsafe_tls_downgrade offered server
    decide (result ≤ offered ∧ result ≤ server))) = true := by
  native_decide

-- PBT for selection_prop.
example : pbtInputs.all (fun offered => pbtInputs.all (fun server =>
    let result := unsafe_tls_downgrade offered server
    decide (result = offered ∨ result = server))) = true := by
  native_decide

-- PBT for limiting_endpoint_prop.
example : pbtInputs.all (fun offered => pbtInputs.all (fun server =>
    let result := unsafe_tls_downgrade offered server
    decide ((offered ≤ server → result = offered) ∧
      (server ≤ offered → result = server)))) = true := by
  native_decide

-- PBT for greatest_common_prop.
example : pbtInputs.all (fun offered => pbtInputs.all (fun server =>
    pbtInputs.all (fun version =>
      decide (version ≤ unsafe_tls_downgrade offered server ↔
        version ≤ offered ∧ version ≤ server)))) = true := by
  native_decide

-- PBT for offer_monotone_prop.
example : pbtInputs.all (fun lower => pbtInputs.all (fun higher =>
    pbtInputs.all (fun server =>
      decide (lower ≤ higher →
        unsafe_tls_downgrade lower server ≤
          unsafe_tls_downgrade higher server)))) = true := by
  native_decide

-- PBT for server_monotone_prop.
example : pbtInputs.all (fun offered => pbtInputs.all (fun lower =>
    pbtInputs.all (fun higher =>
      decide (lower ≤ higher →
        unsafe_tls_downgrade offered lower ≤
          unsafe_tls_downgrade offered higher)))) = true := by
  native_decide

-- PBT for downgrade_prop.
example : pbtInputs.all (fun tampered => pbtInputs.all (fun true_client =>
    pbtInputs.all (fun server =>
      decide (tampered < min true_client server →
        unsafe_tls_downgrade tampered server = tampered ∧
        unsafe_tls_downgrade tampered server <
          unsafe_tls_downgrade true_client server)))) = true := by
  native_decide

-- PBT for Post_prop, with its entire conjunction expanded into executable checks.
example : pbtInputs.all (fun offered => pbtInputs.all (fun server =>
    let result := unsafe_tls_downgrade offered server
    decide (result = min offered server ∧
      (result ≤ offered ∧ result ≤ server) ∧
      (result = offered ∨ result = server) ∧
      ((offered ≤ server → result = offered) ∧
        (server ≤ offered → result = server))))) = true := by
  native_decide

/- Correctness: every accepted input satisfies the post-condition. -/

theorem correctness_thm (offered server : Int) :
    Pre offered server → Post_prop offered server (unsafe_tls_downgrade offered server) := by
  intro _
  exact ⟨highest_common_thm offered server, bounds_thm offered server,
    selection_thm offered server, limiting_endpoint_thm offered server⟩

/- Imperative implementation using mutable state. -/

def unsafe_tls_downgrade_imperative (client_offered_max server_max : Int) : Int := Id.run do
  let mut negotiated := client_offered_max
  if server_max < negotiated then
    negotiated := server_max
  return negotiated

/- Imperative tests. -/

example : unsafe_tls_downgrade_imperative 4 4 = 4 := by native_decide
example : unsafe_tls_downgrade_imperative 1 4 = 1 := by native_decide
example : unsafe_tls_downgrade_imperative 4 2 = 2 := by native_decide
example : unsafe_tls_downgrade_imperative 3 3 = 3 := by native_decide
example : unsafe_tls_downgrade_imperative 4 0 = 0 := by native_decide
example : unsafe_tls_downgrade_imperative 2 4 ≥
    unsafe_tls_downgrade_imperative 1 4 := by native_decide
example : unsafe_tls_downgrade_imperative (-2) 4 = -2 := by native_decide
example : unsafe_tls_downgrade_imperative 7 9 = 7 := by native_decide
example : check unsafe_tls_downgrade_imperative = true := by native_decide

#eval unsafe_tls_downgrade_imperative 1 4
#eval check unsafe_tls_downgrade_imperative

/- Equivalence holds on the complete Python integer domain. -/

theorem functional_imperative_equiv_thm (offered server : Int) :
    unsafe_tls_downgrade offered server =
      unsafe_tls_downgrade_imperative offered server := by
  by_cases h : server < offered
  · simp [unsafe_tls_downgrade, unsafe_tls_downgrade_imperative, h,
      min_eq_right (le_of_lt h)]
  · have hle : offered ≤ server := by omega
    simp [unsafe_tls_downgrade, unsafe_tls_downgrade_imperative, h,
      min_eq_left hle]

end UnsafeTlsDowngrade
