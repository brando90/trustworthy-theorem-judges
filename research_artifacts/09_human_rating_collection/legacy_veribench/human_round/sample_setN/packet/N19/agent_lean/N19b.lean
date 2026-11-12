import Mathlib

/-!
# Unsafe TLS version downgrade

Translation of the Python `unsafe_tls_downgrade` program. The server chooses
`min client_offered_max server_max`, using only the offer that it actually sees.
There is no check binding that offer to the client's true capability.

The conventional versions are 0 = SSL 3.0, 1 = TLS 1.0, 2 = TLS 1.1,
3 = TLS 1.2, and 4 = TLS 1.3. We use `Int`, not a bounded version enumeration:
the Python function is total on integers, including values outside 0 through 4.
The downgrade property compares an attacker-stripped offer with the true client
capability; it does not add a security check to the implementation.

All named theorems have kernel-checked proofs. `native_decide` is used only for
executable tests. Bounded PBTs include negative inputs and all conventional TLS
versions; the theorems themselves remain universally quantified over `Int`.
-/

namespace UnsafeTlsDowngrade

/-! ## Functional implementation -/

def unsafe_tls_downgrade (client_offered_max server_max : Int) : Int :=
  min client_offered_max server_max

/-- The six assertions in the Python `check`, expressed as a Boolean. -/
def check (candidate : Int → Int → Int) : Bool :=
  (candidate 4 4 == 4) &&
  (candidate 1 4 == 1) &&
  (candidate 4 2 == 2) &&
  (candidate 3 3 == 3) &&
  (candidate 4 0 == 0) &&
  decide (candidate 2 4 ≥ candidate 1 4)

/-! ## Unit tests -/

-- No attack: TLS 1.3 is negotiated.
example : unsafe_tls_downgrade 4 4 = 4 := by native_decide
-- An attacker strips the visible offer to TLS 1.0.
example : unsafe_tls_downgrade 1 4 = 1 := by native_decide
-- The server caps the result.
example : unsafe_tls_downgrade 4 2 = 2 := by native_decide
-- Equal versions negotiate that version.
example : unsafe_tls_downgrade 3 3 = 3 := by native_decide
-- A legacy-only server chooses SSL 3.0.
example : unsafe_tls_downgrade 4 0 = 0 := by native_decide
-- More visible client capability cannot reduce the negotiated version.
example : unsafe_tls_downgrade 2 4 ≥ unsafe_tls_downgrade 1 4 := by native_decide
example : check unsafe_tls_downgrade = true := by native_decide

-- Preserve Python's integer semantics beyond the conventional version range.
example : unsafe_tls_downgrade (-2) 4 = -2 := by native_decide
example : unsafe_tls_downgrade 4 (-3) = -3 := by native_decide
example : unsafe_tls_downgrade 9 7 = 7 := by native_decide

#eval unsafe_tls_downgrade 4 4
#eval unsafe_tls_downgrade 1 4
#eval check unsafe_tls_downgrade
#eval if check unsafe_tls_downgrade then "All tests passed." else "Candidate failed tests"

/-! ## Precondition and properties -/

/-- Python's integer minimum has no additional input precondition. -/
def Pre (_client_offered_max _server_max : Int) : Prop := True

/-- Exact behavior, including which input is selected in each order case. -/
def negotiation_prop (client server : Int) : Prop :=
  unsafe_tls_downgrade client server = if client ≤ server then client else server

theorem negotiation_thm (client server : Int) : negotiation_prop client server := by
  unfold negotiation_prop unsafe_tls_downgrade
  by_cases h : client ≤ server
  · simp [h]
  · simp [h, min_eq_right (le_of_not_ge h)]

/-- The result is common to both visible maxima, and no common version is higher. -/
def highest_common_prop (client server : Int) : Prop :=
  unsafe_tls_downgrade client server ≤ client ∧
  unsafe_tls_downgrade client server ≤ server ∧
  ∀ version : Int,
    version ≤ client → version ≤ server → version ≤ unsafe_tls_downgrade client server

theorem highest_common_thm (client server : Int) : highest_common_prop client server := by
  unfold highest_common_prop unsafe_tls_downgrade
  exact ⟨min_le_left _ _, min_le_right _ _, fun _ hc hs => le_min hc hs⟩

/-- Increasing the offer cannot decrease the selected version. -/
def offer_monotone_prop (lower upper server : Int) : Prop :=
  lower ≤ upper → unsafe_tls_downgrade lower server ≤ unsafe_tls_downgrade upper server

theorem offer_monotone_thm (lower upper server : Int) :
    offer_monotone_prop lower upper server := by
  unfold offer_monotone_prop unsafe_tls_downgrade
  intro h
  exact min_le_min h le_rfl

/-- Increasing server capability cannot decrease the selected version. -/
def server_monotone_prop (client lower upper : Int) : Prop :=
  lower ≤ upper → unsafe_tls_downgrade client lower ≤ unsafe_tls_downgrade client upper

theorem server_monotone_thm (client lower upper : Int) :
    server_monotone_prop client lower upper := by
  unfold server_monotone_prop unsafe_tls_downgrade
  intro h
  exact min_le_min le_rfl h

/--
Stripping the offer cannot improve negotiation. If the stripped offer is below
the actual highest common version, the server accepts that stripped version,
strictly below what the true client and server could have negotiated.
`true_client` is used only in the specification, not by the server function.
-/
def downgrade_prop (true_client server stripped : Int) : Prop :=
  stripped ≤ true_client →
    unsafe_tls_downgrade stripped server ≤ unsafe_tls_downgrade true_client server ∧
    (stripped < min true_client server →
      unsafe_tls_downgrade stripped server = stripped ∧
      unsafe_tls_downgrade stripped server < unsafe_tls_downgrade true_client server)

theorem downgrade_thm (true_client server stripped : Int) :
    downgrade_prop true_client server stripped := by
  unfold downgrade_prop
  intro hstrip
  constructor
  · exact offer_monotone_thm stripped true_client server hstrip
  · intro hstrict
    have hs : stripped ≤ server :=
      le_trans (le_of_lt hstrict) (min_le_right true_client server)
    have hresult : unsafe_tls_downgrade stripped server = stripped := min_eq_left hs
    refine ⟨hresult, ?_⟩
    rw [hresult]
    exact hstrict

/-! ## Postcondition -/

/-- All semantic properties, with auxiliary versions universally quantified. -/
def Post_prop (client server : Int) : Prop :=
  negotiation_prop client server ∧
  highest_common_prop client server ∧
  (∀ lower : Int, offer_monotone_prop lower client server) ∧
  (∀ upper : Int, server_monotone_prop client server upper) ∧
  (∀ stripped : Int, downgrade_prop client server stripped)

/-! ## Property-based tests

Exhaustive bounded testing is used rather than random sampling. Each input and
auxiliary version ranges over all integers from -6 to 10, so these tests include
both orders, equality, negative inputs, the full TLS range, and larger values.
The Boolean checks below are executable forms of the corresponding properties.
Only the tests bound universal quantifiers; no theorem or specification is
restricted to this finite domain.
-/

private def testVersions : List Int :=
  (List.range 17).map (fun n => (n : Int) - 6)

private def negotiationCheck (client server : Int) : Bool :=
  decide (unsafe_tls_downgrade client server =
    if client ≤ server then client else server)

private def highestCommonCheck (client server : Int) : Bool :=
  decide (unsafe_tls_downgrade client server ≤ client ∧
    unsafe_tls_downgrade client server ≤ server) &&
  testVersions.all (fun version =>
    decide (version ≤ client → version ≤ server →
      version ≤ unsafe_tls_downgrade client server))

private def offerMonotoneCheck (lower upper server : Int) : Bool :=
  decide (lower ≤ upper →
    unsafe_tls_downgrade lower server ≤ unsafe_tls_downgrade upper server)

private def serverMonotoneCheck (client lower upper : Int) : Bool :=
  decide (lower ≤ upper →
    unsafe_tls_downgrade client lower ≤ unsafe_tls_downgrade client upper)

private def downgradeCheck (true_client server stripped : Int) : Bool :=
  decide (stripped ≤ true_client →
    unsafe_tls_downgrade stripped server ≤ unsafe_tls_downgrade true_client server ∧
    (stripped < min true_client server →
      unsafe_tls_downgrade stripped server = stripped ∧
      unsafe_tls_downgrade stripped server < unsafe_tls_downgrade true_client server))

-- PBT for negotiation_prop: all 17² pairs.
example : testVersions.all (fun client => testVersions.all (fun server =>
    negotiationCheck client server)) = true := by native_decide

-- PBT for highest_common_prop: both bounds and all 17³ maximality instances.
example : testVersions.all (fun client => testVersions.all (fun server =>
    highestCommonCheck client server)) = true := by native_decide

-- PBT for offer_monotone_prop: all 17³ triples, including admissible inequalities.
example : testVersions.all (fun lower => testVersions.all (fun upper =>
    testVersions.all (fun server => offerMonotoneCheck lower upper server))) = true := by
  native_decide

-- PBT for server_monotone_prop: all 17³ triples.
example : testVersions.all (fun client => testVersions.all (fun lower =>
    testVersions.all (fun upper => serverMonotoneCheck client lower upper))) = true := by
  native_decide

-- PBT for downgrade_prop: tests both nonincrease and the strict downgrade clause.
example : testVersions.all (fun true_client => testVersions.all (fun server =>
    testVersions.all (fun stripped => downgradeCheck true_client server stripped))) = true := by
  native_decide

/-- Bounded executable counterpart of the complete Post_prop conjunction. -/
private def postCheck (client server : Int) : Bool :=
  negotiationCheck client server &&
  highestCommonCheck client server &&
  testVersions.all (fun lower => offerMonotoneCheck lower client server) &&
  testVersions.all (fun upper => serverMonotoneCheck client server upper) &&
  testVersions.all (fun stripped => downgradeCheck client server stripped)

-- PBT for Post_prop. Pre is True, so every tested pair is admissible.
example : testVersions.all (fun client => testVersions.all (fun server =>
    postCheck client server)) = true := by native_decide

#eval testVersions.all (fun client => testVersions.all (fun server => postCheck client server))

/-! ## Correctness: unrestricted integer inputs satisfy the postcondition -/

theorem correctness_thm (client server : Int) : Pre client server → Post_prop client server := by
  intro _hpre
  exact ⟨negotiation_thm client server,
    highest_common_thm client server,
    fun lower => offer_monotone_thm lower client server,
    fun upper => server_monotone_thm client server upper,
    fun stripped => downgrade_thm client server stripped⟩

/-! ## Imperative implementation -/

/-- Keep a mutable selected version, lowering it only if the server caps it. -/
def unsafe_tls_downgrade_imperative (client_offered_max server_max : Int) : Int :=
  Id.run do
    let mut negotiated := client_offered_max
    if server_max < negotiated then
      negotiated := server_max
    return negotiated

/-! ## Imperative tests -/

example : unsafe_tls_downgrade_imperative 4 4 = 4 := by native_decide
example : unsafe_tls_downgrade_imperative 1 4 = 1 := by native_decide
example : unsafe_tls_downgrade_imperative 4 2 = 2 := by native_decide
example : unsafe_tls_downgrade_imperative 3 3 = 3 := by native_decide
example : unsafe_tls_downgrade_imperative 4 0 = 0 := by native_decide
example : unsafe_tls_downgrade_imperative 2 4 ≥ unsafe_tls_downgrade_imperative 1 4 := by
  native_decide
example : check unsafe_tls_downgrade_imperative = true := by native_decide
example : unsafe_tls_downgrade_imperative (-2) 4 = -2 := by native_decide
example : unsafe_tls_downgrade_imperative 4 (-3) = -3 := by native_decide

#eval unsafe_tls_downgrade_imperative 1 4
#eval check unsafe_tls_downgrade_imperative
#eval if check unsafe_tls_downgrade_imperative then "All tests passed." else "Candidate failed tests"

-- Additional bounded regression check of the two implementations.
example : testVersions.all (fun client => testVersions.all (fun server =>
    decide (unsafe_tls_downgrade client server =
      unsafe_tls_downgrade_imperative client server))) = true := by native_decide

/-! ## Functional / imperative equivalence -/

theorem functional_imperative_equivalence_thm (client server : Int) :
    unsafe_tls_downgrade client server = unsafe_tls_downgrade_imperative client server := by
  by_cases h : server < client
  · simp [unsafe_tls_downgrade, unsafe_tls_downgrade_imperative,
      h, min_eq_right (le_of_lt h)]
  · simp [unsafe_tls_downgrade, unsafe_tls_downgrade_imperative,
      h, min_eq_left (le_of_not_gt h)]

end UnsafeTlsDowngrade
