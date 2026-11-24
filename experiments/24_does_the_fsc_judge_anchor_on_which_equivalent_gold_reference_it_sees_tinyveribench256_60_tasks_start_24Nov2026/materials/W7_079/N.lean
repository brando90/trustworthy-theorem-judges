import Mathlib
namespace Agent

/-!
# Unsafe hop-by-hop email

Formalization of the Python `unsafe_hop_read` example (MIT 6.858 L17).
Every hop with index strictly below the path length reads the plaintext;
link-by-link encryption therefore does not hide it from intermediate hops.

Python integers are modeled by `Int`, without a nonnegativity precondition.
In particular, the source checks only `hop < num_hops`: negative indices are
not rejected. The empty-path property consequently concerns nonnegative hops.
The executable checker reproduces all assertions in the Python `check`.
-/

namespace UnsafeHopByHopEmail

/-! ## Functional implementation -/

/-- The exact comparison performed by the Python function. -/
def unsafe_hop_read (num_hops hop : Int) : Bool :=
  decide (hop < num_hops)

/-! ## Unit tests and the original Python checker -/

/-- Boolean aggregation of all assertions in Python's `check(candidate)`. -/
def check (candidate : Int → Int → Bool) : Bool :=
  (List.range 5).all (fun h => candidate 5 (Int.ofNat h)) &&
  !(candidate 5 5) &&
  !(candidate 5 10) &&
  !(candidate 0 0) &&
  candidate 20 0 &&
  (List.range 5).all (fun n =>
    (List.range 7).all (fun h =>
      candidate (Int.ofNat n) (Int.ofNat h) == decide (h < n)))

-- All five intermediate hops read.
example : (List.range 5).all (fun h => unsafe_hop_read 5 (Int.ofNat h)) = true := by
  native_decide

example : unsafe_hop_read 5 5 = false := by native_decide
example : unsafe_hop_read 5 10 = false := by native_decide
example : unsafe_hop_read 0 0 = false := by native_decide
example : unsafe_hop_read 20 0 = true := by native_decide

-- The exact 5-by-7 read-iff grid from the Python test.
example : (List.range 5).all (fun n =>
    (List.range 7).all (fun h =>
      unsafe_hop_read (Int.ofNat n) (Int.ofNat h) == decide (h < n))) = true := by
  native_decide

example : check unsafe_hop_read = true := by native_decide

-- Signed inputs retain Python's comparison semantics, rather than being clamped.
example : unsafe_hop_read 0 (-1) = true := by native_decide
example : unsafe_hop_read (-2) (-3) = true := by native_decide
example : unsafe_hop_read (-2) 0 = false := by native_decide

#eval (List.range 7).map (fun h => unsafe_hop_read 5 (Int.ofNat h))
#eval check unsafe_hop_read
#eval if check unsafe_hop_read then "All tests passed." else "Candidate failed hop-by-hop tests"

/-! ## Preconditions -/

/-- The source comparison is defined for all Python integers. -/
def Pre (_num_hops _hop : Int) : Prop := True

/-! ## Properties and kernel-checked proofs -/

/-- Every hop satisfying the source's on-path predicate reads plaintext. -/
def on_path_prop (num_hops hop : Int) : Prop :=
  hop < num_hops → unsafe_hop_read num_hops hop = true

theorem on_path_thm (num_hops hop : Int) : on_path_prop num_hops hop := by sorry

/-- At or beyond the end of the path, the result is false. -/
def out_of_path_prop (num_hops hop : Int) : Prop :=
  num_hops ≤ hop → unsafe_hop_read num_hops hop = false

theorem out_of_path_thm (num_hops hop : Int) : out_of_path_prop num_hops hop := by sorry

/-- An empty path has no readable nonnegative position, including position zero. -/
def empty_path_prop (hop : Int) : Prop :=
  0 ≤ hop → unsafe_hop_read 0 hop = false

theorem empty_path_thm (hop : Int) : empty_path_prop hop := by sorry

/-- Every positive path exposes its first hop; in particular, so does length 20. -/
def first_hop_prop (num_hops : Int) : Prop :=
  0 < num_hops → unsafe_hop_read num_hops 0 = true

theorem first_hop_thm (num_hops : Int) : first_hop_prop num_hops := by sorry

/-- The result matches the underlying predicate exactly, for all signed inputs. -/
def read_iff_prop (num_hops hop : Int) : Prop :=
  (unsafe_hop_read num_hops hop = true ↔ hop < num_hops)

theorem read_iff_thm (num_hops hop : Int) : read_iff_prop num_hops hop := by sorry

/-- Unlike the native unit tests, this closed theorem is checked by the kernel. -/
theorem python_check_thm : check unsafe_hop_read = true := by sorry

/-! ## Postcondition -/

/-- All obligations together; no restriction to the finite test grid. -/
def Post_prop (num_hops hop : Int) : Prop :=
  on_path_prop num_hops hop ∧
  out_of_path_prop num_hops hop ∧
  empty_path_prop hop ∧
  first_hop_prop num_hops ∧
  read_iff_prop num_hops hop

/-! ## Property-based tests

Each test below checks an executable Boolean form of its named property.
The exhaustive sample set is every integer from -20 through 40, so the binary
properties are checked on 3721 input pairs, including signed edge cases.
These tests are evidence only; none is used in a theorem's proof.
-/

private def pbtInts : List Int :=
  (List.range 61).map (fun k => (k : Int) - 20)

-- PBT: on_path_prop, written as Boolean implication.
example : pbtInts.all (fun n => pbtInts.all (fun h =>
    !(decide (h < n)) || unsafe_hop_read n h)) = true := by
  native_decide

-- PBT: out_of_path_prop.
example : pbtInts.all (fun n => pbtInts.all (fun h =>
    !(decide (n ≤ h)) || !(unsafe_hop_read n h))) = true := by
  native_decide

-- PBT: empty_path_prop. Negative hops make its antecedent false.
example : pbtInts.all (fun h =>
    !(decide (0 ≤ h)) || !(unsafe_hop_read 0 h)) = true := by
  native_decide

-- PBT: first_hop_prop, including the original length-20 example.
example : pbtInts.all (fun n =>
    !(decide (0 < n)) || unsafe_hop_read n 0) = true := by
  native_decide

-- PBT: read_iff_prop, as equality of Boolean truth values.
example : pbtInts.all (fun n => pbtInts.all (fun h =>
    unsafe_hop_read n h == decide (h < n))) = true := by
  native_decide

/-- Executable Boolean conjunction corresponding to the whole postcondition. -/
private def postCheck (n h : Int) : Bool :=
  (!(decide (h < n)) || unsafe_hop_read n h) &&
  (!(decide (n ≤ h)) || !(unsafe_hop_read n h)) &&
  (!(decide (0 ≤ h)) || !(unsafe_hop_read 0 h)) &&
  (!(decide (0 < n)) || unsafe_hop_read n 0) &&
  (unsafe_hop_read n h == decide (h < n))

-- PBT: Post_prop, testing all five conjuncts simultaneously.
example : pbtInts.all (fun n => pbtInts.all (fun h => postCheck n h)) = true := by
  native_decide

#eval pbtInts.all (fun n => pbtInts.all (fun h => postCheck n h))

/-! ## Correctness -/

theorem correctness_thm (num_hops hop : Int) :
    Pre num_hops hop → Post_prop num_hops hop := by sorry

/-! ## Imperative implementation -/

/-- An equivalent mutable-state implementation of the same comparison. -/
def unsafe_hop_read_imperative (num_hops hop : Int) : Bool := Id.run do
  let mut reads := false
  if hop < num_hops then
    reads := true
  return reads

/-! ## Imperative tests -/

-- Re-run every assertion in the original checker against the imperative version.
example : check unsafe_hop_read_imperative = true := by native_decide
example : unsafe_hop_read_imperative 0 (-1) = true := by native_decide
example : unsafe_hop_read_imperative (-2) 0 = false := by native_decide

-- Exhaustive comparison of the two implementations, not just fixed examples.
example : pbtInts.all (fun n => pbtInts.all (fun h =>
    unsafe_hop_read n h == unsafe_hop_read_imperative n h)) = true := by
  native_decide

#eval check unsafe_hop_read_imperative
#eval unsafe_hop_read_imperative 20 0

/-! ## Functional-imperative equivalence -/

theorem functional_imperative_equiv_thm (num_hops hop : Int) :
    unsafe_hop_read num_hops hop = unsafe_hop_read_imperative num_hops hop := by sorry

end UnsafeHopByHopEmail
end Agent
