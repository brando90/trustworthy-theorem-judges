import Mathlib
namespace Agent

/-!
# Unsafe replay acceptance

Translation of the Python `unsafe_accept` and its assertion-based checker.
Python integers are modeled by `Int`, including negative integers. The server
ignores both its purported nonce history and the incoming nonce, so it accepts
replayed and fresh nonces alike. No replay protection is claimed.

The Boolean `check` records whether all assertions in the Python checker pass.
Theorems are kernel-proved; `native_decide` is used only for executable tests.
-/

namespace UnsafeReplayAttack

/-! ## Functional implementation -/

def unsafe_accept (_seen : List Int) (_new_nonce : Int) : Bool := true

def check (candidate : List Int → Int → Bool) : Bool :=
  candidate [1, 2, 3] 2 &&
  candidate [1, 2, 3] 9 &&
  candidate [] 9 &&
  candidate [0] 0 &&
  (candidate [1, 2, 3] 5 == candidate [] 5) &&
  (List.range 5).all (fun n => candidate [1, 2, 3] (Int.ofNat n))

/-! ## Unit tests: all six checks from the Python source -/

example : unsafe_accept [1, 2, 3] 2 = true := by native_decide
example : unsafe_accept [1, 2, 3] 9 = true := by native_decide
example : unsafe_accept [] 9 = true := by native_decide
example : unsafe_accept [0] 0 = true := by native_decide
example : unsafe_accept [1, 2, 3] 5 = unsafe_accept [] 5 := by native_decide
example : (List.range 5).all (fun n => unsafe_accept [1, 2, 3] (Int.ofNat n)) = true := by
  native_decide
example : check unsafe_accept = true := by native_decide
-- Python's integer domain also permits negative nonces and repeated entries.
example : unsafe_accept [-4, -4, 0] (-4) = true := by native_decide

#eval unsafe_accept [1, 2, 3] 2
#eval check unsafe_accept
#eval if check unsafe_accept then "All tests passed." else "Candidate failed replay tests"

/-! ## Precondition: all histories and integer nonces are admissible -/

def Pre (_seen : List Int) (_new_nonce : Int) : Prop := True

/-! ## Behavioral properties and kernel-checked proofs -/

def replayAccepted_prop (seen : List Int) (new_nonce : Int) : Prop :=
  new_nonce ∈ seen → unsafe_accept seen new_nonce = true

theorem replayAccepted_thm (seen : List Int) (new_nonce : Int) :
    replayAccepted_prop seen new_nonce := by
  intro _
  rfl

def freshAccepted_prop (seen : List Int) (new_nonce : Int) : Prop :=
  new_nonce ∉ seen → unsafe_accept seen new_nonce = true

theorem freshAccepted_thm (seen : List Int) (new_nonce : Int) :
    freshAccepted_prop seen new_nonce := by
  intro _
  rfl

def emptyHistory_prop (new_nonce : Int) : Prop :=
  unsafe_accept [] new_nonce = true

theorem emptyHistory_thm (new_nonce : Int) : emptyHistory_prop new_nonce := by
  rfl

-- The original [0] test is the special case seen = [].
def zeroReplay_prop (seen : List Int) : Prop :=
  unsafe_accept (0 :: seen) 0 = true

theorem zeroReplay_thm (seen : List Int) : zeroReplay_prop seen := by
  rfl

def historyIrrelevant_prop (seen : List Int) (new_nonce : Int) : Prop :=
  ∀ other : List Int, unsafe_accept seen new_nonce = unsafe_accept other new_nonce

theorem historyIrrelevant_thm (seen : List Int) (new_nonce : Int) :
    historyIrrelevant_prop seen new_nonce := by
  intro other
  rfl

def alwaysTrue_prop (seen : List Int) (new_nonce : Int) : Prop :=
  unsafe_accept seen new_nonce = true

theorem alwaysTrue_thm (seen : List Int) (new_nonce : Int) :
    alwaysTrue_prop seen new_nonce := by
  rfl

-- The Python range(0, 5) check, generalized to arbitrary histories.
def loopAccepted_prop (seen : List Int) : Prop :=
  ∀ n : Nat, n < 5 → unsafe_accept seen (Int.ofNat n) = true

theorem loopAccepted_thm (seen : List Int) : loopAccepted_prop seen := by
  intro n _
  rfl

-- This proves the complete original checker without trusting native evaluation.
theorem check_thm : check unsafe_accept = true := by
  decide

/-! ## Postcondition -/

def Post_prop (seen : List Int) (new_nonce : Int) : Prop :=
  replayAccepted_prop seen new_nonce ∧
  freshAccepted_prop seen new_nonce ∧
  emptyHistory_prop new_nonce ∧
  zeroReplay_prop seen ∧
  historyIrrelevant_prop seen new_nonce ∧
  alwaysTrue_prop seen new_nonce ∧
  loopAccepted_prop seen ∧
  check unsafe_accept = true

/-! ## Bounded exhaustive property-based tests

Enumerate every history of length at most three over [-2, -1, 0, 1, 2, 3],
including duplicates and all orderings, and every nonce from -3 through 9.
These finite tests do not restrict the domains of the universal theorems.
Implications are tested as Boolean disjunctions, so replay and freshness
checks cover both antecedent values without discarded samples.
-/

private def nonceAlphabet : List Int := [-2, -1, 0, 1, 2, 3]

private def historiesOfLength : Nat → List (List Int)
  | 0 => [[]]
  | n + 1 => nonceAlphabet.flatMap (fun x => (historiesOfLength n).map (fun xs => x :: xs))

private def smallHistories : List (List Int) :=
  (List.range 4).flatMap historiesOfLength

private def smallNonces : List Int :=
  (List.range 13).map (fun n => (n : Int) - 3)

-- PBT for replayAccepted_prop.
example : smallHistories.all (fun seen => smallNonces.all (fun n =>
    (!(seen.contains n)) || unsafe_accept seen n)) = true := by
  native_decide

-- PBT for freshAccepted_prop.
example : smallHistories.all (fun seen => smallNonces.all (fun n =>
    seen.contains n || unsafe_accept seen n)) = true := by
  native_decide

-- PBT for emptyHistory_prop.
example : smallNonces.all (fun n => unsafe_accept [] n) = true := by
  native_decide

-- PBT for zeroReplay_prop, with every bounded history appended after zero.
example : smallHistories.all (fun seen => unsafe_accept (0 :: seen) 0) = true := by
  native_decide

-- PBT for historyIrrelevant_prop, checking every pair of bounded histories.
example : smallHistories.all (fun seen => smallNonces.all (fun n =>
    smallHistories.all (fun other =>
      unsafe_accept seen n == unsafe_accept other n))) = true := by
  native_decide

-- PBT for alwaysTrue_prop.
example : smallHistories.all (fun seen => smallNonces.all (fun n =>
    unsafe_accept seen n)) = true := by
  native_decide

-- PBT for loopAccepted_prop: exhaust its nonce range for every bounded history.
example : smallHistories.all (fun seen => (List.range 5).all (fun n =>
    unsafe_accept seen (Int.ofNat n))) = true := by
  native_decide

-- Executable bounded counterpart of the entire Post_prop conjunction.
private def boundedPostCheck (seen : List Int) (n : Int) : Bool :=
  ((!(seen.contains n)) || unsafe_accept seen n) &&
  (seen.contains n || unsafe_accept seen n) &&
  unsafe_accept [] n &&
  unsafe_accept (0 :: seen) 0 &&
  smallHistories.all (fun other => unsafe_accept seen n == unsafe_accept other n) &&
  unsafe_accept seen n &&
  (List.range 5).all (fun k => unsafe_accept seen (Int.ofNat k)) &&
  check unsafe_accept

-- PBT for Post_prop. Pre is True, so no inputs need filtering.
example : smallHistories.all (fun seen => smallNonces.all (fun n =>
    boundedPostCheck seen n)) = true := by
  native_decide

#eval (smallHistories.length, smallNonces.length)
#eval smallHistories.all (fun seen => smallNonces.all (fun n => boundedPostCheck seen n))

/-! ## Correctness -/

theorem correctness_thm (seen : List Int) (new_nonce : Int) :
    Pre seen new_nonce → Post_prop seen new_nonce := by
  intro _
  exact ⟨replayAccepted_thm seen new_nonce,
    freshAccepted_thm seen new_nonce,
    emptyHistory_thm new_nonce,
    zeroReplay_thm seen,
    historyIrrelevant_thm seen new_nonce,
    alwaysTrue_thm seen new_nonce,
    loopAccepted_thm seen,
    check_thm⟩

/-! ## Imperative implementation -/

def unsafe_accept_imperative (_seen : List Int) (_new_nonce : Int) : Bool := Id.run do
  let mut accepted : Bool := false
  accepted := true
  return accepted

/-! ## Imperative tests -/

example : unsafe_accept_imperative [1, 2, 3] 2 = true := by native_decide
example : unsafe_accept_imperative [1, 2, 3] 9 = true := by native_decide
example : unsafe_accept_imperative [] 9 = true := by native_decide
example : unsafe_accept_imperative [0] 0 = true := by native_decide
example : unsafe_accept_imperative [1, 2, 3] 5 = unsafe_accept_imperative [] 5 := by
  native_decide
example : (List.range 5).all (fun n =>
    unsafe_accept_imperative [1, 2, 3] (Int.ofNat n)) = true := by
  native_decide
example : check unsafe_accept_imperative = true := by native_decide
example : smallHistories.all (fun seen => smallNonces.all (fun n =>
    unsafe_accept_imperative seen n == unsafe_accept seen n)) = true := by
  native_decide

#eval check unsafe_accept_imperative

/-! ## Functional/imperative equivalence for all Python integer inputs -/

theorem functional_imperative_equiv_thm (seen : List Int) (new_nonce : Int) :
    unsafe_accept seen new_nonce = unsafe_accept_imperative seen new_nonce := by
  rfl

end UnsafeReplayAttack
end Agent
