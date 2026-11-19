import Mathlib
namespace Agent

/-!
# Safe TLS heartbeat length checking

Translation of the Python Heartbleed mitigation: reject a claimed length
larger than the actual payload length, and otherwise echo the claimed length.
In particular, rejection returns zero, not the minimum of the two lengths.

`Int` preserves Python's arbitrary-precision signed integer input domain.
There is no extra runtime check for negative lengths. Consequently `Pre` is
unrestricted; byte-count safety properties explicitly state the relevant
nonnegativity assumptions rather than changing the program's behavior.
-/

namespace SafeHeartbeatLengthTrust

/-! ## Functional implementation -/

def safe_heartbeat (payload_len claimed_len : Int) : Int :=
  if claimed_len > payload_len then 0 else claimed_len

/-! ## Unit tests: the seven Python assertions -/

example : safe_heartbeat 3 3 = 3 := by native_decide
example : safe_heartbeat 1 65535 = 0 := by native_decide
example : safe_heartbeat 10 5 = 5 := by native_decide
example : safe_heartbeat 0 1 = 0 := by native_decide
example : safe_heartbeat 0 0 = 0 := by native_decide
example : safe_heartbeat 1000 1000 = 1000 := by native_decide
example : safe_heartbeat 5 6 = 0 := by native_decide

/-- Boolean counterpart of the success of every assertion in Python's `check`. -/
def check (candidate : Int → Int → Int) : Bool :=
  (candidate 3 3 == 3) &&
  (candidate 1 65535 == 0) &&
  (candidate 10 5 == 5) &&
  (candidate 0 1 == 0) &&
  (candidate 0 0 == 0) &&
  (candidate 1000 1000 == 1000) &&
  (candidate 5 6 == 0)

#eval check safe_heartbeat

-- Signed-input regressions: these inputs are not silently clamped to naturals.
example : safe_heartbeat (-5) (-10) = -10 := by native_decide
example : safe_heartbeat (-5) (-4) = 0 := by native_decide
example : safe_heartbeat 3 (-1) = -1 := by native_decide
#eval (safe_heartbeat (-5) (-10), safe_heartbeat (-5) (-4))

/-! ## Precondition -/

/-- The Python function is defined on every pair of integers. -/
def Pre (_payload_len _claimed_len : Int) : Prop := True

/-! ## Behavioral and safety properties -/

/-- Every oversized claim is rejected, including the Heartbleed attack. -/
def rejection_prop (payload_len claimed_len : Int) : Prop :=
  payload_len < claimed_len → safe_heartbeat payload_len claimed_len = 0

theorem rejection_thm (payload_len claimed_len : Int) :
    rejection_prop payload_len claimed_len := by
  unfold rejection_prop
  intro h
  simp [safe_heartbeat, h]

/-- Every claim within the payload is echoed exactly, including equality. -/
def acceptance_prop (payload_len claimed_len : Int) : Prop :=
  claimed_len ≤ payload_len →
    safe_heartbeat payload_len claimed_len = claimed_len

theorem acceptance_thm (payload_len claimed_len : Int) :
    acceptance_prop payload_len claimed_len := by
  unfold acceptance_prop
  intro h
  simp [safe_heartbeat, not_lt_of_ge h]

/-- A nonnegative payload is never over-read, for any signed claim. -/
def no_overread_prop (payload_len claimed_len : Int) : Prop :=
  0 ≤ payload_len → safe_heartbeat payload_len claimed_len ≤ payload_len

theorem no_overread_thm (payload_len claimed_len : Int) :
    no_overread_prop payload_len claimed_len := by
  unfold no_overread_prop
  intro hp
  by_cases h : payload_len < claimed_len
  · simpa [safe_heartbeat, h] using hp
  · have hc : claimed_len ≤ payload_len := by omega
    simpa [safe_heartbeat, h] using hc

/-- A nonnegative claimed byte count produces a nonnegative result. -/
def nonnegative_prop (payload_len claimed_len : Int) : Prop :=
  0 ≤ claimed_len → 0 ≤ safe_heartbeat payload_len claimed_len

theorem nonnegative_thm (payload_len claimed_len : Int) :
    nonnegative_prop payload_len claimed_len := by
  unfold nonnegative_prop
  intro hc
  by_cases h : payload_len < claimed_len
  · simp [safe_heartbeat, h]
  · simpa [safe_heartbeat, h] using hc

/-- For a nonnegative claim, no more than the claimed bytes are returned. -/
def echo_bound_prop (payload_len claimed_len : Int) : Prop :=
  0 ≤ claimed_len → safe_heartbeat payload_len claimed_len ≤ claimed_len

theorem echo_bound_thm (payload_len claimed_len : Int) :
    echo_bound_prop payload_len claimed_len := by
  unfold echo_bound_prop
  intro hc
  by_cases h : payload_len < claimed_len
  · simpa [safe_heartbeat, h] using hc
  · simp [safe_heartbeat, h]

/-- Zero means either rejection or a zero claim; it need not mean rejection. -/
def zero_iff_prop (payload_len claimed_len : Int) : Prop :=
  safe_heartbeat payload_len claimed_len = 0 ↔
    payload_len < claimed_len ∨ claimed_len = 0

theorem zero_iff_thm (payload_len claimed_len : Int) :
    zero_iff_prop payload_len claimed_len := by
  unfold zero_iff_prop
  by_cases h : payload_len < claimed_len <;> simp [safe_heartbeat, h]

/-! ## Post-condition -/

/-- Exact branch behavior together with the byte-count safety guarantees. -/
def Post_prop (payload_len claimed_len : Int) : Prop :=
  rejection_prop payload_len claimed_len ∧
  acceptance_prop payload_len claimed_len ∧
  no_overread_prop payload_len claimed_len ∧
  nonnegative_prop payload_len claimed_len ∧
  echo_bound_prop payload_len claimed_len ∧
  zero_iff_prop payload_len claimed_len

/-! ## Property-based tests

These bounded PBTs exhaustively check every pair in a signed range augmented
with larger positive and negative lengths, including the attack length.
Each test uses the executable form of its named property. They are tests,
not dependencies of any theorem, and do not require `Decidable` instances
for the named proposition definitions.
-/

def pbtLengths : List Int :=
  (List.range 65).map (fun n => (n : Int) - 32) ++
    [-65535, -1000, 1000, 65535]

-- PBT for rejection_prop.
example :
    (pbtLengths.all fun p => pbtLengths.all fun c =>
      decide (p < c → safe_heartbeat p c = 0)) = true := by
  native_decide

-- PBT for acceptance_prop.
example :
    (pbtLengths.all fun p => pbtLengths.all fun c =>
      decide (c ≤ p → safe_heartbeat p c = c)) = true := by
  native_decide

-- PBT for no_overread_prop.
example :
    (pbtLengths.all fun p => pbtLengths.all fun c =>
      decide (0 ≤ p → safe_heartbeat p c ≤ p)) = true := by
  native_decide

-- PBT for nonnegative_prop.
example :
    (pbtLengths.all fun p => pbtLengths.all fun c =>
      decide (0 ≤ c → 0 ≤ safe_heartbeat p c)) = true := by
  native_decide

-- PBT for echo_bound_prop.
example :
    (pbtLengths.all fun p => pbtLengths.all fun c =>
      decide (0 ≤ c → safe_heartbeat p c ≤ c)) = true := by
  native_decide

-- PBT for zero_iff_prop.
example :
    (pbtLengths.all fun p => pbtLengths.all fun c =>
      decide (safe_heartbeat p c = 0 ↔ p < c ∨ c = 0)) = true := by
  native_decide

-- PBT for the entire Post_prop. Pre is True for all these signed inputs.
example :
    (pbtLengths.all fun p => pbtLengths.all fun c =>
      let result := safe_heartbeat p c
      decide ((p < c → result = 0) ∧
        (c ≤ p → result = c) ∧
        (0 ≤ p → result ≤ p) ∧
        (0 ≤ c → 0 ≤ result) ∧
        (0 ≤ c → result ≤ c) ∧
        (result = 0 ↔ p < c ∨ c = 0))) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (payload_len claimed_len : Int) :
    Pre payload_len claimed_len → Post_prop payload_len claimed_len := by
  intro _hpre
  exact ⟨rejection_thm payload_len claimed_len,
    acceptance_thm payload_len claimed_len,
    no_overread_thm payload_len claimed_len,
    nonnegative_thm payload_len claimed_len,
    echo_bound_thm payload_len claimed_len,
    zero_iff_thm payload_len claimed_len⟩

/-! ## Imperative implementation -/

/-- Mutable-state version of the same reject-or-echo control flow. -/
def safe_heartbeat_imp (payload_len claimed_len : Int) : Int := Id.run do
  let mut result : Int := claimed_len
  if claimed_len > payload_len then
    result := 0
  return result

/-! ## Imperative tests -/

example : safe_heartbeat_imp 3 3 = 3 := by native_decide
example : safe_heartbeat_imp 1 65535 = 0 := by native_decide
example : safe_heartbeat_imp 10 5 = 5 := by native_decide
example : safe_heartbeat_imp 0 1 = 0 := by native_decide
example : safe_heartbeat_imp 0 0 = 0 := by native_decide
example : safe_heartbeat_imp 1000 1000 = 1000 := by native_decide
example : safe_heartbeat_imp 5 6 = 0 := by native_decide
example : safe_heartbeat_imp (-5) (-10) = -10 := by native_decide
example : safe_heartbeat_imp (-5) (-4) = 0 := by native_decide
example : safe_heartbeat_imp 3 (-1) = -1 := by native_decide

#eval check safe_heartbeat_imp
#eval (safe_heartbeat_imp (-5) (-10), safe_heartbeat_imp (-5) (-4))

-- Also compare the implementations on the full bounded PBT input grid.
example :
    (pbtLengths.all fun p => pbtLengths.all fun c =>
      decide (safe_heartbeat p c = safe_heartbeat_imp p c)) = true := by
  native_decide

/-! ## Functional/imperative equivalence -/

theorem equivalence_thm (payload_len claimed_len : Int) :
    safe_heartbeat payload_len claimed_len =
      safe_heartbeat_imp payload_len claimed_len := by
  by_cases h : payload_len < claimed_len <;>
    simp [safe_heartbeat, safe_heartbeat_imp, h]

end SafeHeartbeatLengthTrust
end Agent
