import Mathlib
namespace Agent

/-!
# Predictable TCP initial sequence numbers

A translation of Python's `unsafe_tcp_isn`: return the previous ISN plus 64,
ignoring the connection identifier. Both arguments use `Int`, matching Python's
unbounded signed integers. In particular, the source does not implement modular
32-bit arithmetic, despite its "wraps near max" test comment.

The specifications describe the fixed increment, independence from connection
identifiers, prediction of the following ISN, strict growth, absence of 32-bit
wrapping, and prediction after an arbitrary finite connection history. Bounded
property-based tests supplement, but do not replace, kernel-checked proofs.
-/

namespace UnsafeTcpIsn

/-! ## Functional implementation -/

/-- The connection identifier deliberately has no influence on the result. -/
def unsafe_tcp_isn (prev_isn : Int) (_connection_id : Int) : Int :=
  prev_isn + 64

/-- Repeatedly apply the Python function, using each result as the next input. -/
def connectionSequence (prev : Int) : List Int → Int
  | [] => prev
  | connection :: connections =>
      connectionSequence (unsafe_tcp_isn prev connection) connections

/-! ## Unit tests: the original Python check and additional domain checks -/

/-- Executable translation of all six assertions in Python's `check`. -/
def check (candidate : Int → Int → Int) : Bool :=
  candidate 1000 1 == 1064 &&
  candidate 1000 2 == 1064 &&
  candidate 5000 10 == 5064 &&
  candidate 0 0 == 64 &&
  candidate 100 0 == 164 &&
  candidate ((2 : Int) ^ 32 - 100) 1 == (2 : Int) ^ 32 - 36

example : unsafe_tcp_isn 1000 1 = 1064 := by native_decide
example : unsafe_tcp_isn 1000 2 = 1064 := by native_decide
example : unsafe_tcp_isn 5000 10 = 5064 := by native_decide
example : unsafe_tcp_isn 0 0 = 64 := by native_decide
example : unsafe_tcp_isn 100 0 = 164 := by native_decide
example : unsafe_tcp_isn ((2 : Int) ^ 32 - 100) 1 =
    (2 : Int) ^ 32 - 36 := by native_decide
example : check unsafe_tcp_isn = true := by native_decide

-- Negative integers are admissible; neither argument is restricted to UInt32.
example : unsafe_tcp_isn (-100) (-5) = -36 := by native_decide
example : unsafe_tcp_isn (-64) 0 = 0 := by native_decide
-- Crossing the TCP field boundary does NOT cause wrapping in this Python code.
example : unsafe_tcp_isn ((2 : Int) ^ 32 - 1) 1 =
    (2 : Int) ^ 32 + 63 := by native_decide
example : unsafe_tcp_isn ((2 : Int) ^ 80) (-(2 : Int) ^ 80) =
    (2 : Int) ^ 80 + 64 := by native_decide
example : connectionSequence 1000 [1, 2, 3] = 1192 := by native_decide

#eval check unsafe_tcp_isn
#eval unsafe_tcp_isn 1000 1
#eval unsafe_tcp_isn ((2 : Int) ^ 32 - 100) 1
#eval connectionSequence 1000 [1, 2, 3]

/-! ## Precondition -/

/-- Python addition is defined for every pair of integers, with no restrictions. -/
def Pre (_prev_isn _connection_id : Int) : Prop := True

/-! ## Properties and proofs -/

/-- Exact functional behavior, including negative and arbitrarily large inputs. -/
def increment_prop (prev connection : Int) : Prop :=
  unsafe_tcp_isn prev connection = prev + 64

theorem increment_thm (prev connection : Int) : increment_prop prev connection := by sorry

/-- Changing the connection identifier cannot change the result. -/
def connection_independent_prop (prev first second : Int) : Prop :=
  unsafe_tcp_isn prev first = unsafe_tcp_isn prev second

theorem connection_independent_thm (prev first second : Int) :
    connection_independent_prop prev first second := by sorry

/-- Knowing a previous ISN predicts two successive increments, for any IDs. -/
def predictable_prop (prev first second : Int) : Prop :=
  unsafe_tcp_isn (unsafe_tcp_isn prev first) second = prev + 128

theorem predictable_thm (prev first second : Int) :
    predictable_prop prev first second := by sorry

/-- Every invocation strictly increases the previous integer. -/
def strictly_increasing_prop (prev connection : Int) : Prop :=
  prev < unsafe_tcp_isn prev connection

theorem strictly_increasing_thm (prev connection : Int) :
    strictly_increasing_prop prev connection := by sorry

/-- At and beyond the crossing threshold, the result lies outside UInt32. -/
def non_wrapping_prop (prev connection : Int) : Prop :=
  (2 : Int) ^ 32 - 64 ≤ prev → (2 : Int) ^ 32 ≤ unsafe_tcp_isn prev connection

theorem non_wrapping_thm (prev connection : Int) :
    non_wrapping_prop prev connection := by sorry

/-- After n connections the counter has increased by exactly 64*n.
This holds for all finite histories, regardless of their identifiers. -/
def sequence_prop (prev : Int) (connections : List Int) : Prop :=
  connectionSequence prev connections = prev + 64 * (connections.length : Int)

theorem sequence_thm (prev : Int) (connections : List Int) :
    sequence_prop prev connections := by sorry

/-! ## Postcondition -/

/-- The complete behavioral specification, including all alternative identifiers
and all finite future histories, not just those exercised by the tests. -/
def Post_prop (prev connection : Int) : Prop :=
  increment_prop prev connection ∧
  (∀ other : Int, connection_independent_prop prev connection other) ∧
  (∀ next : Int, predictable_prop prev connection next) ∧
  strictly_increasing_prop prev connection ∧
  non_wrapping_prop prev connection ∧
  (∀ connections : List Int, sequence_prop prev connections)

/-! ## Property-based tests

These are bounded executable Boolean checks. In addition to exhaustive small
signed integers, they include a dense range straddling the 32-bit boundary and
large positive and negative integers. The specification and its proofs above
retain the unrestricted input domain.
-/

/-- Small signed values, original examples, large values, and 129 boundary cases. -/
def samplePrevious : List Int :=
  (List.range 41).map (fun n => (n : Int) - 20) ++
  [100, 1000, 5000, -1000, (2 : Int) ^ 80, -(2 : Int) ^ 80] ++
  (List.range 129).map (fun n => (2 : Int) ^ 32 + (n : Int) - 96)

/-- Exhaustive identifiers in [-5,5], with additional large identifiers. -/
def sampleIds : List Int :=
  (List.range 11).map (fun n => (n : Int) - 5) ++
  [10, 99, (2 : Int) ^ 40, -(2 : Int) ^ 40]

/-- All histories of length at most two over sampleIds, plus longer histories. -/
def sampleSequences : List (List Int) :=
  [[]] ++ sampleIds.map (fun c => [c]) ++
  sampleIds.flatMap (fun c => sampleIds.map (fun d => [c, d])) ++
  (List.range 17).map (fun n => List.replicate n (-7)) ++
  [[1, 2, 3], [-1, 0, 1], [(2 : Int) ^ 40, -(2 : Int) ^ 40, 0, 99]]

-- PBT for increment_prop.
example : samplePrevious.all (fun prev => sampleIds.all (fun connection =>
    decide (unsafe_tcp_isn prev connection = prev + 64))) = true := by
  native_decide

-- PBT for connection_independent_prop.
example : samplePrevious.all (fun prev => sampleIds.all (fun first =>
    sampleIds.all (fun second =>
      decide (unsafe_tcp_isn prev first = unsafe_tcp_isn prev second)))) = true := by
  native_decide

-- PBT for predictable_prop.
example : samplePrevious.all (fun prev => sampleIds.all (fun first =>
    sampleIds.all (fun second =>
      decide (unsafe_tcp_isn (unsafe_tcp_isn prev first) second = prev + 128)))) =
    true := by
  native_decide

-- PBT for strictly_increasing_prop.
example : samplePrevious.all (fun prev => sampleIds.all (fun connection =>
    decide (prev < unsafe_tcp_isn prev connection))) = true := by
  native_decide

-- PBT for non_wrapping_prop. The boundary samples exercise both sides of the
-- implication's premise, so this is not merely a vacuous small-integer check.
example : samplePrevious.all (fun prev => sampleIds.all (fun connection =>
    decide ((2 : Int) ^ 32 - 64 ≤ prev →
      (2 : Int) ^ 32 ≤ unsafe_tcp_isn prev connection))) = true := by
  native_decide

-- PBT for sequence_prop, including empty histories and lengths up to sixteen.
example : samplePrevious.all (fun prev => sampleSequences.all (fun connections =>
    decide (connectionSequence prev connections =
      prev + 64 * (connections.length : Int)))) = true := by
  native_decide

/-- Executable bounded form of every conjunct of Post_prop.
Its universally quantified clauses are checked across the corresponding samples.
Pre is True, so no sampled input needs to be excluded. -/
def boundedPostChecks : Bool :=
  samplePrevious.all (fun prev => sampleIds.all (fun connection =>
    decide (unsafe_tcp_isn prev connection = prev + 64) &&
    sampleIds.all (fun other =>
      decide (unsafe_tcp_isn prev connection = unsafe_tcp_isn prev other)) &&
    sampleIds.all (fun next =>
      decide (unsafe_tcp_isn (unsafe_tcp_isn prev connection) next = prev + 128)) &&
    decide (prev < unsafe_tcp_isn prev connection) &&
    decide ((2 : Int) ^ 32 - 64 ≤ prev →
      (2 : Int) ^ 32 ≤ unsafe_tcp_isn prev connection) &&
    sampleSequences.all (fun connections =>
      decide (connectionSequence prev connections =
        prev + 64 * (connections.length : Int)))))

-- PBT for Post_prop as a whole.
example : boundedPostChecks = true := by native_decide
#eval boundedPostChecks

/-! ## Correctness -/

theorem correctness_thm (prev connection : Int) :
    Pre prev connection → Post_prop prev connection := by sorry

/-! ## Imperative implementation -/

/-- The same integer update expressed with local mutable state. -/
def unsafe_tcp_isn_imperative (prev_isn : Int) (_connection_id : Int) : Int := Id.run do
  let mut isn := prev_isn
  isn := isn + 64
  return isn

/-! ## Imperative tests -/

example : unsafe_tcp_isn_imperative 1000 1 = 1064 := by native_decide
example : unsafe_tcp_isn_imperative 1000 2 = 1064 := by native_decide
example : unsafe_tcp_isn_imperative 5000 10 = 5064 := by native_decide
example : unsafe_tcp_isn_imperative 0 0 = 64 := by native_decide
example : unsafe_tcp_isn_imperative 100 0 = 164 := by native_decide
example : unsafe_tcp_isn_imperative ((2 : Int) ^ 32 - 100) 1 =
    (2 : Int) ^ 32 - 36 := by native_decide
example : check unsafe_tcp_isn_imperative = true := by native_decide
example : unsafe_tcp_isn_imperative (-100) (-5) = -36 := by native_decide
example : unsafe_tcp_isn_imperative ((2 : Int) ^ 32 - 1) 1 =
    (2 : Int) ^ 32 + 63 := by native_decide

-- Bounded equivalence test, separate from the unrestricted proof below.
example : samplePrevious.all (fun prev => sampleIds.all (fun connection =>
    decide (unsafe_tcp_isn prev connection =
      unsafe_tcp_isn_imperative prev connection))) = true := by
  native_decide

#eval check unsafe_tcp_isn_imperative
#eval unsafe_tcp_isn_imperative 1000 1
#eval unsafe_tcp_isn_imperative ((2 : Int) ^ 32 - 1) 1

/-! ## Equivalence -/

/-- Both implementations agree for every pair of Python integer inputs. -/
theorem functional_imperative_equivalence_thm (prev connection : Int) :
    unsafe_tcp_isn prev connection = unsafe_tcp_isn_imperative prev connection := by sorry

end UnsafeTcpIsn
end Agent
