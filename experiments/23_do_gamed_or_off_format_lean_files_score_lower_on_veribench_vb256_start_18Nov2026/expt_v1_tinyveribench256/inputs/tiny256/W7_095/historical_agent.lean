import Mathlib
namespace Agent

/-!
# Unsafe TLS cipher-suite downgrade

Translation of the Python `unsafe_cipher_downgrade` program from the TLS
cipher-downgrade example (MIT 6.858, Lecture 14). Cipher ranks are integers and
larger ranks represent stronger ciphers. The server selects the minimum of its
maximum rank and the *visible*, potentially attacker-modified client offer.
There is no authenticated original offer or integrity check in this function.

`Int` preserves Python's arbitrary-precision integer domain, including negative
values: although the illustrative TLS ranks are 0 through 4, the Python function
does not enforce that range. Consequently `Pre` imposes no restrictions.

The general theorems show that stripping an offer cannot increase the result,
and that an offer strictly below both original limits forces a strict downgrade.
Bounded property-based tests are executable evidence only; the named theorems
are proved separately by kernel-checked order reasoning.
-/

namespace UnsafeCipherDowngrade

/-! ## Functional implementation -/

/-- Negotiate using only the received offer, with no integrity validation. -/
def unsafe_cipher_downgrade (client_offered_cipher server_max_cipher : Int) : Int :=
  min client_offered_cipher server_max_cipher

/-! ## Original Python unit tests -/

/-- Executable translation of all six assertions in Python's `check`. -/
def check (candidate : Int → Int → Int) : Bool :=
  decide (
    candidate 4 4 = 4 ∧
    candidate 1 4 = 1 ∧
    candidate 4 2 = 2 ∧
    candidate 3 3 = 3 ∧
    candidate 0 4 = 0 ∧
    candidate 1 4 ≤ candidate 2 4)

-- No attack: a strong offer and a strong server negotiate a strong cipher.
example : unsafe_cipher_downgrade 4 4 = 4 := by native_decide
-- Vulnerability: the attacker-stripped offer forces a weak cipher.
example : unsafe_cipher_downgrade 1 4 = 1 := by native_decide
-- The server caps the result.
example : unsafe_cipher_downgrade 4 2 = 2 := by native_decide
-- Matching ranks.
example : unsafe_cipher_downgrade 3 3 = 3 := by native_decide
-- Extreme downgrade.
example : unsafe_cipher_downgrade 0 4 = 0 := by native_decide
-- Increasing the visible offer does not reduce the negotiated rank.
example : unsafe_cipher_downgrade 2 4 ≥ unsafe_cipher_downgrade 1 4 := by
  native_decide
example : check unsafe_cipher_downgrade = true := by native_decide

-- Python does not restrict inputs to nonnegative ranks or ranks at most four.
example : unsafe_cipher_downgrade (-3) 4 = -3 := by native_decide
example : unsafe_cipher_downgrade 4 (-2) = -2 := by native_decide
example : unsafe_cipher_downgrade (-5) (-2) = -5 := by native_decide
example : unsafe_cipher_downgrade 12 8 = 8 := by native_decide

#eval [unsafe_cipher_downgrade 4 4, unsafe_cipher_downgrade 1 4,
  unsafe_cipher_downgrade 4 2, unsafe_cipher_downgrade 3 3,
  unsafe_cipher_downgrade 0 4]
#eval check unsafe_cipher_downgrade
#eval if check unsafe_cipher_downgrade then "All tests passed."
  else "Candidate failed tests"

/-! ## Precondition -/

/-- All Python integer inputs are admissible, including attacker-modified ones. -/
def Pre (_client_offered_cipher _server_max_cipher : Int) : Prop := True

/-! ## Properties and kernel-checked proofs -/

/-- Exact correspondence to Python's integer `min`. -/
def minimum_prop (client server : Int) : Prop :=
  unsafe_cipher_downgrade client server = min client server

theorem minimum_thm (client server : Int) : minimum_prop client server := by
  rfl

/-- The result never exceeds either of the two visible limits. -/
def bounds_prop (client server : Int) : Prop :=
  unsafe_cipher_downgrade client server ≤ client ∧
  unsafe_cipher_downgrade client server ≤ server

theorem bounds_thm (client server : Int) : bounds_prop client server := by
  exact ⟨min_le_left client server, min_le_right client server⟩

/-- Every rank permitted by both limits is below the selected rank. -/
def strongest_common_prop (client server common : Int) : Prop :=
  common ≤ client → common ≤ server →
    common ≤ unsafe_cipher_downgrade client server

theorem strongest_common_thm (client server common : Int) :
    strongest_common_prop client server common := by
  intro hClient hServer
  exact le_min hClient hServer

/-- Any visible offer below the server limit is accepted, however weak it is. -/
def offer_selected_prop (client server : Int) : Prop :=
  client ≤ server → unsafe_cipher_downgrade client server = client

theorem offer_selected_thm (client server : Int) :
    offer_selected_prop client server := by
  intro h
  exact min_eq_left h

/-- A server with the lower limit determines the selected rank. -/
def server_caps_prop (client server : Int) : Prop :=
  server ≤ client → unsafe_cipher_downgrade client server = server

theorem server_caps_thm (client server : Int) : server_caps_prop client server := by
  intro h
  exact min_eq_right h

/-- Equal offers/limits are returned unchanged, including the no-attack case. -/
def match_prop (rank : Int) : Prop :=
  unsafe_cipher_downgrade rank rank = rank

theorem match_thm (rank : Int) : match_prop rank := by
  exact min_self rank

/-- A larger visible client offer cannot reduce the negotiated rank. -/
def monotonicity_prop (lessVisible moreVisible server : Int) : Prop :=
  lessVisible ≤ moreVisible →
    unsafe_cipher_downgrade lessVisible server ≤
      unsafe_cipher_downgrade moreVisible server

theorem monotonicity_thm (lessVisible moreVisible server : Int) :
    monotonicity_prop lessVisible moreVisible server := by
  intro h
  change min lessVisible server ≤ min moreVisible server
  exact le_min (le_trans (min_le_left lessVisible server) h)
    (min_le_right lessVisible server)

/-- Stripping an offer to a server-supported weak rank forces exactly that rank,
without making the negotiated rank stronger than the original negotiation. -/
def downgrade_prop (original stripped server : Int) : Prop :=
  stripped ≤ original → stripped ≤ server →
    unsafe_cipher_downgrade stripped server = stripped ∧
    unsafe_cipher_downgrade stripped server ≤
      unsafe_cipher_downgrade original server

theorem downgrade_thm (original stripped server : Int) :
    downgrade_prop original stripped server := by
  intro hOriginal hServer
  exact ⟨offer_selected_thm stripped server hServer,
    monotonicity_thm stripped original server hOriginal⟩

/-- If the attacker offers a rank below both original limits, the downgrade is
strict, not merely a non-increase. No authentication rejects this modified offer. -/
def strict_downgrade_prop (original stripped server : Int) : Prop :=
  stripped < original → stripped < server →
    unsafe_cipher_downgrade stripped server <
      unsafe_cipher_downgrade original server

theorem strict_downgrade_thm (original stripped server : Int) :
    strict_downgrade_prop original stripped server := by
  intro hOriginal hServer
  change min stripped server < min original server
  rw [min_eq_left (le_of_lt hServer)]
  exact lt_min hOriginal hServer

/-! ## Postcondition -/

/-- Full specification at a given offer and server limit. The quantifiers are
unrestricted integers, not the bounded sample domain used by the tests below. -/
def Post_prop (client server : Int) : Prop :=
  minimum_prop client server ∧
  bounds_prop client server ∧
  offer_selected_prop client server ∧
  server_caps_prop client server ∧
  match_prop client ∧
  (∀ common : Int, strongest_common_prop client server common) ∧
  (∀ smaller : Int, monotonicity_prop smaller client server) ∧
  (∀ stripped : Int, downgrade_prop client stripped server) ∧
  (∀ stripped : Int, strict_downgrade_prop client stripped server)

/-! ## Property-based tests

Exhaustively sample every combination of ranks in [-10, 10], together with two
large signed outliers. All samples satisfy `Pre`. Implications are decidable,
and samples exercise both their active and inactive branches. Each property has
its own Boolean test over the implementation. The postcondition test expands its
universal quantifiers over the same finite sample set; it is not a proof of the
unrestricted postcondition and is not used by any theorem.
-/

def cipherSamples : List Int :=
  (List.range 21).map (fun n => (n : Int) - 10) ++ [-1000000, 1000000]

-- PBT: minimum_prop.
example : cipherSamples.all (fun client =>
    cipherSamples.all (fun server =>
      decide (unsafe_cipher_downgrade client server = min client server))) = true := by
  native_decide

-- PBT: bounds_prop.
example : cipherSamples.all (fun client =>
    cipherSamples.all (fun server =>
      decide (unsafe_cipher_downgrade client server ≤ client ∧
        unsafe_cipher_downgrade client server ≤ server))) = true := by
  native_decide

-- PBT: strongest_common_prop (all triples of sample integers).
example : cipherSamples.all (fun client =>
    cipherSamples.all (fun server =>
      cipherSamples.all (fun common =>
        decide (common ≤ client → common ≤ server →
          common ≤ unsafe_cipher_downgrade client server)))) = true := by
  native_decide

-- PBT: offer_selected_prop, including arbitrarily weak signed sample offers.
example : cipherSamples.all (fun client =>
    cipherSamples.all (fun server =>
      decide (client ≤ server →
        unsafe_cipher_downgrade client server = client))) = true := by
  native_decide

-- PBT: server_caps_prop.
example : cipherSamples.all (fun client =>
    cipherSamples.all (fun server =>
      decide (server ≤ client →
        unsafe_cipher_downgrade client server = server))) = true := by
  native_decide

-- PBT: match_prop.
example : cipherSamples.all (fun rank =>
    decide (unsafe_cipher_downgrade rank rank = rank)) = true := by
  native_decide

-- PBT: monotonicity_prop.
example : cipherSamples.all (fun lessVisible =>
    cipherSamples.all (fun moreVisible =>
      cipherSamples.all (fun server =>
        decide (lessVisible ≤ moreVisible →
          unsafe_cipher_downgrade lessVisible server ≤
            unsafe_cipher_downgrade moreVisible server)))) = true := by
  native_decide

-- PBT: downgrade_prop.
example : cipherSamples.all (fun original =>
    cipherSamples.all (fun stripped =>
      cipherSamples.all (fun server =>
        decide (stripped ≤ original → stripped ≤ server →
          unsafe_cipher_downgrade stripped server = stripped ∧
          unsafe_cipher_downgrade stripped server ≤
            unsafe_cipher_downgrade original server)))) = true := by
  native_decide

-- PBT: strict_downgrade_prop.
example : cipherSamples.all (fun original =>
    cipherSamples.all (fun stripped =>
      cipherSamples.all (fun server =>
        decide (stripped < original → stripped < server →
          unsafe_cipher_downgrade stripped server <
            unsafe_cipher_downgrade original server)))) = true := by
  native_decide

/-- Boolean finite-sample expansion of all conjuncts in `Post_prop`. -/
def boundedPostCheck (client server : Int) : Bool :=
  decide (unsafe_cipher_downgrade client server = min client server ∧
    (unsafe_cipher_downgrade client server ≤ client ∧
      unsafe_cipher_downgrade client server ≤ server) ∧
    (client ≤ server → unsafe_cipher_downgrade client server = client) ∧
    (server ≤ client → unsafe_cipher_downgrade client server = server) ∧
    unsafe_cipher_downgrade client client = client) &&
  cipherSamples.all (fun common =>
    decide (common ≤ client → common ≤ server →
      common ≤ unsafe_cipher_downgrade client server)) &&
  cipherSamples.all (fun smaller =>
    decide (smaller ≤ client → unsafe_cipher_downgrade smaller server ≤
      unsafe_cipher_downgrade client server)) &&
  cipherSamples.all (fun stripped =>
    decide (stripped ≤ client → stripped ≤ server →
      unsafe_cipher_downgrade stripped server = stripped ∧
      unsafe_cipher_downgrade stripped server ≤
        unsafe_cipher_downgrade client server)) &&
  cipherSamples.all (fun stripped =>
    decide (stripped < client → stripped < server →
      unsafe_cipher_downgrade stripped server <
        unsafe_cipher_downgrade client server))

-- PBT: the full Post_prop, with each universal integer variable sampled.
example : cipherSamples.all (fun client =>
    cipherSamples.all (fun server => boundedPostCheck client server)) = true := by
  native_decide

#eval cipherSamples.all (fun client =>
  cipherSamples.all (fun server => boundedPostCheck client server))

/-! ## Correctness on the full Python input domain -/

theorem correctness_thm (client server : Int) :
    Pre client server → Post_prop client server := by
  intro _
  exact ⟨minimum_thm client server,
    bounds_thm client server,
    offer_selected_thm client server,
    server_caps_thm client server,
    match_thm client,
    fun common => strongest_common_thm client server common,
    fun smaller => monotonicity_thm smaller client server,
    fun stripped => downgrade_thm client stripped server,
    fun stripped => strict_downgrade_thm client stripped server⟩

/-! ## Imperative implementation -/

/-- Start with the received offer, then cap the mutable negotiated rank at the
server limit. As in Python, there is no check against an authenticated offer. -/
def unsafe_cipher_downgrade_imp
    (client_offered_cipher server_max_cipher : Int) : Int := Id.run do
  let mut negotiated := client_offered_cipher
  if server_max_cipher < negotiated then
    negotiated := server_max_cipher
  return negotiated

/-! ## Imperative tests -/

example : unsafe_cipher_downgrade_imp 4 4 = 4 := by native_decide
example : unsafe_cipher_downgrade_imp 1 4 = 1 := by native_decide
example : unsafe_cipher_downgrade_imp 4 2 = 2 := by native_decide
example : unsafe_cipher_downgrade_imp 3 3 = 3 := by native_decide
example : unsafe_cipher_downgrade_imp 0 4 = 0 := by native_decide
example : unsafe_cipher_downgrade_imp 2 4 ≥ unsafe_cipher_downgrade_imp 1 4 := by
  native_decide
example : check unsafe_cipher_downgrade_imp = true := by native_decide
example : unsafe_cipher_downgrade_imp (-3) 4 = -3 := by native_decide
example : unsafe_cipher_downgrade_imp 4 (-2) = -2 := by native_decide
example : unsafe_cipher_downgrade_imp (-5) (-2) = -5 := by native_decide
example : unsafe_cipher_downgrade_imp 12 8 = 8 := by native_decide

#eval check unsafe_cipher_downgrade_imp
#eval if check unsafe_cipher_downgrade_imp then "All tests passed."
  else "Candidate failed tests"

-- Additional PBT: functional/imperative agreement on every sampled pair.
example : cipherSamples.all (fun client =>
    cipherSamples.all (fun server =>
      decide (unsafe_cipher_downgrade client server =
        unsafe_cipher_downgrade_imp client server))) = true := by
  native_decide

/-! ## Kernel-checked functional/imperative equivalence -/

theorem functional_eq_imperative (client server : Int) :
    unsafe_cipher_downgrade client server =
      unsafe_cipher_downgrade_imp client server := by
  by_cases h : server < client
  · simp [unsafe_cipher_downgrade, unsafe_cipher_downgrade_imp, h,
      min_eq_right (le_of_lt h)]
  · have hClient : client ≤ server := by omega
    simp [unsafe_cipher_downgrade, unsafe_cipher_downgrade_imp, h,
      min_eq_left hClient]

end UnsafeCipherDowngrade
end Agent
