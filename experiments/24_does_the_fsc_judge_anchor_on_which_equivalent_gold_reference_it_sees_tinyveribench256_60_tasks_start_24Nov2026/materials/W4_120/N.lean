import Mathlib
namespace Agent

/-!
# Unsafe TCP reset handling

Translation of Python's `unsafe_tcp_reset` and its six regression checks.
The function accepts precisely the half-open receive interval
`[rcvNxt, rcvNxt + rcvWnd)`, not just the exact next sequence number.

All three arguments use `Int`, matching Python's unbounded signed integers.
In particular, this model does not introduce 32-bit wraparound or assume a
positive window: zero and negative windows reject every packet. The
vulnerability is preserved, not repaired: a non-exact in-window RST is accepted.
The source's networking narrative has no additional executable packet state.
-/

namespace UnsafeTcpReset103

/-! ## Functional implementation and the Python regression suite -/

def unsafeTcpReset (pktSeq rcvNxt rcvWnd : Int) : Bool :=
  decide (rcvNxt ≤ pktSeq ∧ pktSeq < rcvNxt + rcvWnd)

/-- Boolean version of the Python assertions; no networking effects are modeled. -/
def check (candidate : Int → Int → Int → Bool) : Bool :=
  let rcvNxt : Int := 1000
  let rcvWnd : Int := 65535
  candidate rcvNxt rcvNxt rcvWnd &&
  candidate (rcvNxt + 32000) rcvNxt rcvWnd &&
  candidate (rcvNxt + rcvWnd - 1) rcvNxt rcvWnd &&
  !(candidate (rcvNxt - 1) rcvNxt rcvWnd) &&
  !(candidate (rcvNxt + rcvWnd) rcvNxt rcvWnd) &&
  !(candidate rcvNxt rcvNxt 0)

-- Exact match, mid-window attacker, last included sequence number.
example : unsafeTcpReset 1000 1000 65535 = true := by native_decide
example : unsafeTcpReset 33000 1000 65535 = true := by native_decide
example : unsafeTcpReset 66534 1000 65535 = true := by native_decide
-- Below window, exclusive upper endpoint, and zero window.
example : unsafeTcpReset 999 1000 65535 = false := by native_decide
example : unsafeTcpReset 66535 1000 65535 = false := by native_decide
example : unsafeTcpReset 1000 1000 0 = false := by native_decide
example : check unsafeTcpReset = true := by native_decide

-- Additional signed-integer and non-wrapping cases.
example : unsafeTcpReset (-6) (-10) 5 = true := by native_decide
example : unsafeTcpReset (-5) (-10) 5 = false := by native_decide
example : unsafeTcpReset (-10) (-10) (-1) = false := by native_decide
example : unsafeTcpReset 4294967300 4294967296 8 = true := by native_decide

#eval check unsafeTcpReset
#eval if check unsafeTcpReset then "All tests passed." else "Test failure."

/-! ## Preconditions and semantic properties -/

/-- Python accepts every integer triple; no extra validity restriction is imposed. -/
def Pre (_pktSeq _rcvNxt _rcvWnd : Int) : Prop := True

/-- Both necessary and sufficient conditions for accepting a packet. -/
def acceptance_prop (pktSeq rcvNxt rcvWnd : Int) : Prop :=
  unsafeTcpReset pktSeq rcvNxt rcvWnd = true ↔
    rcvNxt ≤ pktSeq ∧ pktSeq < rcvNxt + rcvWnd

theorem acceptance_thm (pktSeq rcvNxt rcvWnd : Int) :
    acceptance_prop pktSeq rcvNxt rcvWnd := by sorry

/-- A packet is rejected exactly when it lies outside the half-open interval. -/
def rejection_prop (pktSeq rcvNxt rcvWnd : Int) : Prop :=
  unsafeTcpReset pktSeq rcvNxt rcvWnd = false ↔
    pktSeq < rcvNxt ∨ rcvNxt + rcvWnd ≤ pktSeq

theorem rejection_thm (pktSeq rcvNxt rcvWnd : Int) :
    rejection_prop pktSeq rcvNxt rcvWnd := by sorry

/-- Even an exact match requires a strictly positive window. -/
def exactMatch_prop (rcvNxt rcvWnd : Int) : Prop :=
  unsafeTcpReset rcvNxt rcvNxt rcvWnd = true ↔ 0 < rcvWnd

theorem exactMatch_thm (rcvNxt rcvWnd : Int) :
    exactMatch_prop rcvNxt rcvWnd := by sorry

/-- Every offset in `[0, rcvWnd)` works, not merely offset zero. -/
def offset_prop (offset rcvNxt rcvWnd : Int) : Prop :=
  unsafeTcpReset (rcvNxt + offset) rcvNxt rcvWnd = true ↔
    0 ≤ offset ∧ offset < rcvWnd

theorem offset_thm (offset rcvNxt rcvWnd : Int) :
    offset_prop offset rcvNxt rcvWnd := by sorry

/-- The zero-window case and every negative-window case accept nothing. -/
def emptyWindow_prop (pktSeq rcvNxt rcvWnd : Int) : Prop :=
  rcvWnd ≤ 0 → unsafeTcpReset pktSeq rcvNxt rcvWnd = false

theorem emptyWindow_thm (pktSeq rcvNxt rcvWnd : Int) :
    emptyWindow_prop pktSeq rcvNxt rcvWnd := by sorry

/-- The sequence just below the window and the exclusive upper endpoint fail. -/
def boundary_prop (rcvNxt rcvWnd : Int) : Prop :=
  unsafeTcpReset (rcvNxt - 1) rcvNxt rcvWnd = false ∧
  unsafeTcpReset (rcvNxt + rcvWnd) rcvNxt rcvWnd = false

theorem boundary_thm (rcvNxt rcvWnd : Int) :
    boundary_prop rcvNxt rcvWnd := by sorry

/-- An explicit accepted, non-exact RST exists whenever the window has room.
The offset theorem also covers every other in-window attacker choice. -/
def vulnerability_prop (rcvNxt rcvWnd : Int) : Prop :=
  1 < rcvWnd →
    unsafeTcpReset (rcvNxt + 1) rcvNxt rcvWnd = true ∧ rcvNxt + 1 ≠ rcvNxt

theorem vulnerability_thm (rcvNxt rcvWnd : Int) :
    vulnerability_prop rcvNxt rcvWnd := by sorry

/-! ## Combined postcondition -/

def Post_prop (pktSeq rcvNxt rcvWnd : Int) : Prop :=
  acceptance_prop pktSeq rcvNxt rcvWnd ∧
  rejection_prop pktSeq rcvNxt rcvWnd ∧
  exactMatch_prop rcvNxt rcvWnd ∧
  offset_prop (pktSeq - rcvNxt) rcvNxt rcvWnd ∧
  emptyWindow_prop pktSeq rcvNxt rcvWnd ∧
  boundary_prop rcvNxt rcvWnd ∧
  vulnerability_prop rcvNxt rcvWnd

/-! ## Property-based tests

Exhaustive bounded PBTs, separate from the universal proofs above. The signed
range includes negative, zero, and positive widths as well as both endpoints
and interior points. Each test writes the property's executable form explicitly,
so it needs no `Decidable` instance for any of the named specification predicates.
-/

private def smallInts : List Int :=
  (List.range 17).map (fun n => (n : Int) - 8)

private def allPairs (test : Int → Int → Bool) : Bool :=
  smallInts.all (fun n => smallInts.all (fun w => test n w))

private def allTriples (test : Int → Int → Int → Bool) : Bool :=
  smallInts.all (fun s =>
    smallInts.all (fun n => smallInts.all (fun w => test s n w)))

-- PBT: acceptance_prop, all 17^3 signed triples.
example : allTriples (fun s n w =>
    decide (unsafeTcpReset s n w = true ↔ n ≤ s ∧ s < n + w)) = true := by
  native_decide

-- PBT: rejection_prop.
example : allTriples (fun s n w =>
    decide (unsafeTcpReset s n w = false ↔ s < n ∨ n + w ≤ s)) = true := by
  native_decide

-- PBT: exactMatch_prop.
example : allPairs (fun n w =>
    decide (unsafeTcpReset n n w = true ↔ 0 < w)) = true := by
  native_decide

-- PBT: offset_prop (the first input is an independently varied offset).
example : allTriples (fun offset n w =>
    decide (unsafeTcpReset (n + offset) n w = true ↔
      0 ≤ offset ∧ offset < w)) = true := by
  native_decide

-- PBT: emptyWindow_prop; all widths <= 0 are exercised without random discards.
example : allTriples (fun s n w =>
    decide (w ≤ 0 → unsafeTcpReset s n w = false)) = true := by
  native_decide

-- PBT: boundary_prop.
example : allPairs (fun n w =>
    decide (unsafeTcpReset (n - 1) n w = false ∧
      unsafeTcpReset (n + w) n w = false)) = true := by
  native_decide

-- PBT: vulnerability_prop; widths 2 through 8 exercise the non-exact witness.
example : allPairs (fun n w =>
    decide (1 < w →
      unsafeTcpReset (n + 1) n w = true ∧ n + 1 ≠ n)) = true := by
  native_decide

/-- Executable expansion of every conjunct of `Post_prop`. -/
private def postCheck (s n w : Int) : Bool :=
  decide (
    (unsafeTcpReset s n w = true ↔ n ≤ s ∧ s < n + w) ∧
    (unsafeTcpReset s n w = false ↔ s < n ∨ n + w ≤ s) ∧
    (unsafeTcpReset n n w = true ↔ 0 < w) ∧
    (unsafeTcpReset (n + (s - n)) n w = true ↔ 0 ≤ s - n ∧ s - n < w) ∧
    (w ≤ 0 → unsafeTcpReset s n w = false) ∧
    (unsafeTcpReset (n - 1) n w = false ∧
      unsafeTcpReset (n + w) n w = false) ∧
    (1 < w → unsafeTcpReset (n + 1) n w = true ∧ n + 1 ≠ n))

-- PBT: Post_prop, checking all conjuncts together on every signed triple.
example : allTriples postCheck = true := by native_decide
#eval allTriples postCheck

/-! ## Correctness over the entire Python input domain -/

theorem correctness_thm (pktSeq rcvNxt rcvWnd : Int) :
    Pre pktSeq rcvNxt rcvWnd → Post_prop pktSeq rcvNxt rcvWnd := by sorry

/-! ## Imperative implementation and regression tests -/

/-- Short-circuit comparisons with a mutable acceptance flag. -/
def unsafeTcpResetImperative (pktSeq rcvNxt rcvWnd : Int) : Bool := Id.run do
  let mut accepted := false
  if rcvNxt ≤ pktSeq then
    if pktSeq < rcvNxt + rcvWnd then
      accepted := true
  return accepted

example : unsafeTcpResetImperative 1000 1000 65535 = true := by native_decide
example : unsafeTcpResetImperative 33000 1000 65535 = true := by native_decide
example : unsafeTcpResetImperative 66534 1000 65535 = true := by native_decide
example : unsafeTcpResetImperative 999 1000 65535 = false := by native_decide
example : unsafeTcpResetImperative 66535 1000 65535 = false := by native_decide
example : unsafeTcpResetImperative 1000 1000 0 = false := by native_decide
example : check unsafeTcpResetImperative = true := by native_decide
example : unsafeTcpResetImperative (-10) (-10) (-1) = false := by native_decide

#eval check unsafeTcpResetImperative
#eval if check unsafeTcpResetImperative then "All tests passed." else "Test failure."

-- Additional bounded differential PBT for the two implementations.
example : allTriples (fun s n w =>
    unsafeTcpReset s n w == unsafeTcpResetImperative s n w) = true := by
  native_decide

/-! ## Functional/imperative equivalence -/

theorem equivalence_thm (pktSeq rcvNxt rcvWnd : Int) :
    unsafeTcpReset pktSeq rcvNxt rcvWnd =
      unsafeTcpResetImperative pktSeq rcvNxt rcvWnd := by sorry

end UnsafeTcpReset103
end Agent
