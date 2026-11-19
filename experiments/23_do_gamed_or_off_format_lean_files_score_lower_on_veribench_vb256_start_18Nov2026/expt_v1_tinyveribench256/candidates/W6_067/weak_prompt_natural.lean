/-!
# Unsafe Tor circuit hop count

This is a Lean 4 translation of a Python program. The function accepts every
circuit, including circuits with too few hops.

* `unsafeCircuitHops` ports `unsafe_circuit_hops`. It returns `true` and never
  reads the hop count. Python's `int` becomes Lean's `Int`.
* `check` ports `check()`. Python raises `AssertionError` when an example fails.
  Here, `check` returns a `Bool` that the theorem `check_passes` proves is `true`.
* `safeCircuitHops` is a reference specification that is not in the Python file.
  It requires at least `minHops = 3` hops, which is Tor's default circuit length.
  The theorems below use it to state how the unsafe check fails.
-/

namespace TorCircuit

/-- Return `true` without consulting how many hops the circuit has. -/
def unsafeCircuitHops (_hopCount : Int) : Bool := true

/-- The fixed examples from the Python `check()`. Python's `is True` and
`== True` both become `== true` here. -/
def check : Bool :=
  unsafeCircuitHops 3 == true &&
  unsafeCircuitHops 1 == true &&
  unsafeCircuitHops 0 == true &&
  unsafeCircuitHops 2 == true &&
  unsafeCircuitHops 7 == true

/-- All of the fixed examples pass. -/
theorem check_passes : check = true := by decide

/-! ## The individual assertions -/

example : unsafeCircuitHops 3 = true := rfl
example : unsafeCircuitHops 1 = true := rfl
example : unsafeCircuitHops 0 = true := rfl
example : unsafeCircuitHops 2 = true := rfl
example : unsafeCircuitHops 7 = true := rfl

/-! ## Behaviour of the unsafe check -/

/-- The check accepts every hop count. -/
@[simp] theorem unsafeCircuitHops_eq_true (n : Int) : unsafeCircuitHops n = true := rfl

/-- The result never depends on the input. -/
theorem unsafeCircuitHops_const (m n : Int) :
    unsafeCircuitHops m = unsafeCircuitHops n := rfl

/-- The check accepts negative hop counts, which are meaningless. -/
theorem accepts_negative : unsafeCircuitHops (-1) = true := rfl

/-- The check accepts at least one circuit with fewer than three hops. -/
theorem accepts_short_circuit : ∃ n : Int, n < 3 ∧ unsafeCircuitHops n = true :=
  ⟨0, by omega, rfl⟩

/-- Acceptance does not imply that the circuit has at least three hops. -/
theorem not_sound : ¬ (∀ n : Int, unsafeCircuitHops n = true → 3 ≤ n) := by
  intro h
  have h0 : (3 : Int) ≤ 0 := h 0 rfl
  omega

/-! ## Comparison with a safe reference check -/

/-- The minimum hop count the reference check requires (Tor's default is 3). -/
def minHops : Int := 3

/-- Reference specification: accept only circuits with at least `minHops` hops. -/
def safeCircuitHops (hopCount : Int) : Bool := decide (minHops ≤ hopCount)

/-- The safe check rejects every circuit with fewer than `minHops` hops. -/
theorem safe_rejects_short (n : Int) (h : n < minHops) : safeCircuitHops n = false := by
  unfold safeCircuitHops
  exact decide_eq_false (by omega)

/-- The safe check accepts exactly the circuits with at least `minHops` hops. -/
theorem safe_iff (n : Int) : safeCircuitHops n = true ↔ minHops ≤ n := by
  unfold safeCircuitHops
  exact decide_eq_true_iff

/-- The unsafe check accepts every circuit that the safe check rejects. -/
theorem unsafe_accepts_rejected (n : Int) (_h : safeCircuitHops n = false) :
    unsafeCircuitHops n = true := rfl

/-- The unsafe check accepts every circuit that the safe check accepts. -/
theorem unsafe_accepts_safe (n : Int) (_h : safeCircuitHops n = true) :
    unsafeCircuitHops n = true := rfl

/-- The two checks give different results on the 0-hop circuit. -/
theorem disagree_at_zero : unsafeCircuitHops 0 ≠ safeCircuitHops 0 := by decide

/-- The unsafe check is a different function from the safe check. -/
theorem unsafe_ne_safe : unsafeCircuitHops ≠ safeCircuitHops := by
  intro h
  exact disagree_at_zero (congrFun h 0)

/-- Every circuit with fewer than `minHops` hops shows the two checks disagree. -/
theorem disagree_below_min (n : Int) (h : n < minHops) :
    unsafeCircuitHops n ≠ safeCircuitHops n := by
  rw [unsafeCircuitHops_eq_true, safe_rejects_short n h]
  decide

end TorCircuit

-- TLDR-end: [tor-hops: lean translation] `unsafeCircuitHops` always returns `true`.
-- The theorems prove the Python checks pass and that the function accepts short and
-- negative hop counts, unlike a reference check that requires at least 3 hops.
