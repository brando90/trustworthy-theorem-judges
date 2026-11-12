/-!
# VeriBench -- Unsafe TLS Version Downgrade
Every stated theorem is PROVEN (no `sorry`) -- this is the expected standard.
-/

namespace UnsafeTlsDowngrade

/--
An unsafe TLS server picks the highest common version from
`client_offered_max` and `server_max` -- the minimum of the two.
The vulnerability is the lack of a check that `client_offered_max` matches
the client's true capability.  An on-path attacker stripping strong versions
from the ClientHello leaves the server oblivious and it happily picks the
highest common version of the tampered offer.
-/
def unsafeTlsDowngrade (clientOfferedMax : Nat) (serverMax : Nat) : Nat :=
  min clientOfferedMax serverMax

-- Properties

def noAttack_prop (client server : Nat) : Prop :=
  unsafeTlsDowngrade client server = client
-- "No attack" means client and server share the strongest version (here client=server=4 → 4)
-- If client ≤ server, min is client, so this holds when server ≥ client.

def vulnerability_prop (attackerOffer : Nat) (serverMax : Nat) : Prop :=
  unsafeTlsDowngrade attackerOffer serverMax = attackerOffer
-- "Vulnerability": when the attacker strips the client offer down, the server picks the stripped offer.

def serverCaps_prop (client : Nat) (serverCap : Nat) : Prop :=
  unsafeTlsDowngrade client serverCap = serverCap
-- "Server caps the result": when serverCap ≤ client, min is serverCap.

def monotonicity_prop (a b : Nat) (serverMax : Nat) : Prop :=
  unsafeTlsDowngrade a serverMax ≤ unsafeTlsDowngrade b serverMax
-- "Monotone in offer": more visible offer ≥ less visible offer.

-- Theorems

@[simp] theorem noAttack_thm (client server : Nat) (h : client ≤ server) : noAttack_prop client server := by
  unfold noAttack_prop unsafeTlsDowngrade
  -- min client server = client when client ≤ server
  exact Nat.min_eq_left h

@[simp] theorem vulnerability_thm (attackerOffer serverMax : Nat) (h : attackerOffer ≤ serverMax) : vulnerability_prop attackerOffer serverMax := by
  unfold vulnerability_prop unsafeTlsDowngrade
  -- min attackerOffer serverMax = attackerOffer when attackerOffer ≤ serverMax
  exact Nat.min_eq_left h

@[simp] theorem serverCaps_thm (client serverCap : Nat) (h : serverCap ≤ client) : serverCaps_prop client serverCap := by
  unfold serverCaps_prop unsafeTlsDowngrade
  -- min client serverCap = serverCap when serverCap ≤ client
  exact Nat.min_eq_right h

@[simp] theorem monotonicity_thm (a b serverMax : Nat) (h : a ≤ b) : monotonicity_prop a b serverMax := by
  unfold monotonicity_prop unsafeTlsDowngrade
  -- Need: min a serverMax ≤ min b serverMax given a ≤ b
  -- Use: min a serverMax ≤ a ≤ b and min a serverMax ≤ serverMax
  -- So by Nat.le_min, min a serverMax ≤ min b serverMax
  apply Nat.le_min
  · -- min a serverMax ≤ b
    exact le_trans (Nat.min_le_left _ _) h
  · -- min a serverMax ≤ serverMax
    exact Nat.min_le_right _ _

-- Correctness: the server's behavior matches the specification
def Pre (_clientOfferedMax _serverMax : Nat) : Prop := True

def Post_prop (clientOfferedMax serverMax : Nat) : Prop :=
  unsafeTlsDowngrade clientOfferedMax serverMax = min clientOfferedMax serverMax

theorem correctness_thm (clientOfferedMax serverMax : Nat) (_hPre : Pre clientOfferedMax serverMax) :
  Post_prop clientOfferedMax serverMax := by
  unfold Post_prop unsafeTlsDowngrade
  rfl

-- Test suite (mirrors the Python `check` function)

example : unsafeTlsDowngrade 4 4 = 4 := by native_decide
example : unsafeTlsDowngrade 1 4 = 1 := by native_decide
example : unsafeTlsDowngrade 4 2 = 2 := by native_decide
example : unsafeTlsDowngrade 3 3 = 3 := by native_decide
example : unsafeTlsDowngrade 4 0 = 0 := by native_decide
example : unsafeTlsDowngrade 2 4 ≥ unsafeTlsDowngrade 1 4 := by native_decide

end UnsafeTlsDowngrade