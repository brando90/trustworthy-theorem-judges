import Mathlib
namespace Agent

/-!
# HumanEval/22: filter_integers

A structural model of Python's heterogeneous values. `PyInteger` represents
objects satisfying `isinstance(x, int)`: ordinary arbitrary-precision integers,
booleans (Python's bool is an int subclass), and other int-subclass instances.
Subclass names and identity tokens are opaque; filtering never coerces objects
or invokes their arithmetic. Non-integer objects, including arbitrary `Float`
values, containers and opaque objects, are discarded without inspecting them.
The `other` constructor represents non-int objects; int-subclass objects use
`integer (.subclass ...)`. Containers are not traversed by the filter.

The result type is `List PyInteger`, a typed version of Python's `List[int]`.
Embedding it back into `PyValue` recovers precisely the original retained
objects, in order and with all duplicates. Float payloads are merely carried in
the input, so no floating-point arithmetic assumptions or finiteness restrictions
are needed. Tests are executable evidence; the named theorems use kernel proofs.
-/

namespace humaneval_22_filter_integers

inductive PyInteger where
  | int (value : Int)
  | bool (value : Bool)
  | subclass (className : String) (identity : Nat) (value : Int)
  deriving Repr, DecidableEq

inductive PyValue where
  | integer (value : PyInteger)
  | float (value : Float)
  | string (value : String)
  | list (values : List PyValue)
  | tuple (values : List PyValue)
  | dict (entries : List (PyValue × PyValue))
  | none
  | other (className : String) (identity : Nat)
  deriving Repr

def PyValue.asInteger : PyValue → Option PyInteger
  | .integer n => some n
  | _ => Option.none

def PyValue.isInteger (v : PyValue) : Bool := v.asInteger.isSome

/-- The comprehension keeps exactly the objects with the integer runtime tag. -/
def filter_integers (values : List PyValue) : List PyInteger :=
  values.filterMap PyValue.asInteger

-- The two docstring examples and all three assertions in Python's check.
example : filter_integers [.string "a", .float 3.14, .integer (.int 5)] =
    [.int 5] := by native_decide
example : filter_integers [.integer (.int 1), .integer (.int 2),
    .integer (.int 3), .string "abc", .dict [], .list []] =
    [.int 1, .int 2, .int 3] := by native_decide
example : filter_integers [] = [] := by native_decide
example : filter_integers [.integer (.int 4), .dict [], .list [], .float 23.2,
    .integer (.int 9), .string "adasd"] = [.int 4, .int 9] := by native_decide
example : filter_integers [.integer (.int 3), .string "c", .integer (.int 3),
    .integer (.int 3), .string "a", .string "b"] =
    [.int 3, .int 3, .int 3] := by native_decide
-- No coercion of floats or strings; booleans and int subclasses survive intact.
example : filter_integers [.float 1.0, .string "2", .integer (.bool true),
    .integer (.bool false), .integer (.int (-123456789012345678901234567890)),
    .integer (.subclass "MyInt" 7 8), .list [.integer (.int 99)], .none] =
    [.bool true, .bool false, .int (-123456789012345678901234567890),
      .subclass "MyInt" 7 8] := by native_decide
#eval filter_integers [.string "a", .float 3.14, .integer (.int 5)]
#eval filter_integers [.integer (.int 4), .dict [], .list [], .float 23.2,
  .integer (.int 9), .string "adasd"]

/-- All finite lists of modeled Python values are admissible. -/
def Pre (_values : List PyValue) : Prop := True

/-- Exact selection, including original object tags, order, and multiplicities. -/
def selection_prop (values : List PyValue) (result : List PyInteger) : Prop :=
  result.map PyValue.integer = values.filter PyValue.isInteger

/-- No spurious integer objects and no missing integer objects. -/
def membership_prop (values : List PyValue) (result : List PyInteger) : Prop :=
  ∀ n, n ∈ result ↔ PyValue.integer n ∈ values

/-- Stability: embedding the output gives a subsequence of the input. -/
def order_prop (values : List PyValue) (result : List PyInteger) : Prop :=
  (result.map PyValue.integer).Sublist values

/-- Number of occurrences of an exact integer object in a heterogeneous list. -/
def occurrences (n : PyInteger) (values : List PyValue) : Nat :=
  values.countP (fun v => decide (v.asInteger = some n))

def multiplicity_prop (values : List PyValue) (result : List PyInteger) : Prop :=
  ∀ n, result.count n = occurrences n values

/-- Exactly one output for each integer-tagged input, hence no length increase. -/
def length_prop (values : List PyValue) (result : List PyInteger) : Prop :=
  result.length = values.countP PyValue.isInteger ∧ result.length ≤ values.length

/-- Filtering already-filtered objects does not change them. -/
def idempotent_prop (_values : List PyValue) (result : List PyInteger) : Prop :=
  filter_integers (result.map PyValue.integer) = result

/-- Filtering respects concatenation, without reordering either segment. -/
def append_prop (xs ys : List PyValue) : Prop :=
  filter_integers (xs ++ ys) = filter_integers xs ++ filter_integers ys

theorem selection_thm (values : List PyValue) :
    selection_prop values (filter_integers values) := by sorry

theorem membership_thm (values : List PyValue) :
    membership_prop values (filter_integers values) := by sorry

theorem order_thm (values : List PyValue) :
    order_prop values (filter_integers values) := by sorry

theorem multiplicity_thm (values : List PyValue) :
    multiplicity_prop values (filter_integers values) := by sorry

theorem length_thm (values : List PyValue) :
    length_prop values (filter_integers values) := by sorry

theorem filter_embedded (ns : List PyInteger) :
    filter_integers (ns.map PyValue.integer) = ns := by sorry

theorem idempotent_thm (values : List PyValue) :
    idempotent_prop values (filter_integers values) := by sorry

theorem append_thm (xs ys : List PyValue) : append_prop xs ys := by sorry

/-- The full input/output contract. -/
def Post_prop (values : List PyValue) (result : List PyInteger) : Prop :=
  selection_prop values result ∧ membership_prop values result ∧
  order_prop values result ∧ multiplicity_prop values result ∧
  length_prop values result ∧ idempotent_prop values result

/-! ## Bounded property-based tests

All lists of length at most three over a mixed alphabet are checked. Integer
quantifiers are checked over the entire finite support of both input and output,
plus additional `integerProbes`. Outside that support, membership is false and
both occurrence counts are zero. Projecting to `Option PyInteger` makes equality and subsequence checks
executable even though the input can contain opaque primitive floats. The
projection is lossless on retained values, and `none` cannot match an output.
-/

def integerProbes : List PyInteger :=
  [.int (-2), .int 0, .int 3, .bool false, .bool true,
   .subclass "MyInt" 7 3, .int 999, .subclass "MyInt" 8 3]

def valueAlphabet : List PyValue :=
  (integerProbes.take 6).map PyValue.integer ++
  [.float 3.0, .float (-2.5), .float (-0.0), .float (0.0 / 0.0),
   .float (1.0 / 0.0), .float (-1.0 / 0.0), .string "3", .none, .dict [], .list [],
   .list [.integer (.int 3)], .tuple [.integer (.bool true)], .other "object" 0]

/-- Enumerate all lists of length at most the given bound. -/
def boundedLists : Nat → List (List PyValue)
  | 0 => [[]]
  | n + 1 => [] :: valueAlphabet.flatMap (fun v =>
      (boundedLists n).map (fun vs => v :: vs))

def selectionCheck (xs : List PyValue) (r : List PyInteger) : Bool :=
  decide (r.map some = (xs.map PyValue.asInteger).filter Option.isSome)

def objectProbes (xs : List PyValue) (r : List PyInteger) : List PyInteger :=
  integerProbes ++ xs.filterMap PyValue.asInteger ++ r

def membershipCheck (xs : List PyValue) (r : List PyInteger) : Bool :=
  (objectProbes xs r).all (fun n => decide (n ∈ r ↔ some n ∈ xs.map PyValue.asInteger))

def orderCheck (xs : List PyValue) (r : List PyInteger) : Bool :=
  decide ((r.map some).Sublist (xs.map PyValue.asInteger))

def multiplicityCheck (xs : List PyValue) (r : List PyInteger) : Bool :=
  (objectProbes xs r).all (fun n => decide (r.count n = occurrences n xs))

def lengthCheck (xs : List PyValue) (r : List PyInteger) : Bool :=
  decide (r.length = xs.countP PyValue.isInteger ∧ r.length ≤ xs.length)

def idempotentCheck (r : List PyInteger) : Bool :=
  decide (filter_integers (r.map PyValue.integer) = r)

def postCheck (xs : List PyValue) (r : List PyInteger) : Bool :=
  selectionCheck xs r && membershipCheck xs r && orderCheck xs r &&
  multiplicityCheck xs r && lengthCheck xs r && idempotentCheck r

-- PBT for selection_prop.
example : (boundedLists 3).all (fun xs =>
    selectionCheck xs (filter_integers xs)) = true := by native_decide
-- PBT for membership_prop (including absent-object probes).
example : (boundedLists 3).all (fun xs =>
    membershipCheck xs (filter_integers xs)) = true := by native_decide
-- PBT for order_prop.
example : (boundedLists 3).all (fun xs =>
    orderCheck xs (filter_integers xs)) = true := by native_decide
-- PBT for multiplicity_prop (duplicates occur in the enumeration).
example : (boundedLists 3).all (fun xs =>
    multiplicityCheck xs (filter_integers xs)) = true := by native_decide
-- PBT for length_prop.
example : (boundedLists 3).all (fun xs =>
    lengthCheck xs (filter_integers xs)) = true := by native_decide
-- PBT for idempotent_prop.
example : (boundedLists 3).all (fun xs =>
    idempotentCheck (filter_integers xs)) = true := by native_decide
-- PBT for append_prop: every pair of lists of length at most two.
example : (boundedLists 2).all (fun xs => (boundedLists 2).all (fun ys =>
    decide (filter_integers (xs ++ ys) =
      filter_integers xs ++ filter_integers ys))) = true := by native_decide
-- PBT for the complete Post_prop conjunction.
example : (boundedLists 3).all (fun xs =>
    postCheck xs (filter_integers xs)) = true := by native_decide
#eval (boundedLists 3).length
#eval (boundedLists 3).all (fun xs => postCheck xs (filter_integers xs))

theorem correctness (values : List PyValue) :
    Pre values → Post_prop values (filter_integers values) := by sorry

/-- A mutable accumulator, scanned left to right just like the comprehension. -/
def filter_integers_imperative (values : List PyValue) : List PyInteger := Id.run do
  let mut result : List PyInteger := []
  for value in values do
    match value.asInteger with
    | some n => result := result ++ [n]
    | none => pure ()
  return result

example : filter_integers_imperative [] = [] := by native_decide
example : filter_integers_imperative [.integer (.int 4), .dict [], .list [],
    .float 23.2, .integer (.int 9), .string "adasd"] =
    [.int 4, .int 9] := by native_decide
example : filter_integers_imperative [.integer (.int 3), .string "c",
    .integer (.int 3), .integer (.int 3), .string "a", .string "b"] =
    [.int 3, .int 3, .int 3] := by native_decide
example : filter_integers_imperative [.integer (.bool true), .float 1.0,
    .integer (.subclass "MyInt" 7 8), .integer (.bool false)] =
    [.bool true, .subclass "MyInt" 7 8, .bool false] := by native_decide
#eval filter_integers_imperative [.string "a", .float 3.14, .integer (.int 5)]
example : (boundedLists 3).all (fun xs =>
    decide (filter_integers xs = filter_integers_imperative xs)) = true := by
  native_decide

/-- Processing any remaining suffix appends exactly its retained integer objects. -/
theorem loop_invariant (values : List PyValue) (initial : List PyInteger) :
    (Id.run do
      let mut result := initial
      for value in values do
        match value.asInteger with
        | some n => result := result ++ [n]
        | none => pure ()
      return result) = initial ++ filter_integers values := by sorry

theorem functional_eq_imperative (values : List PyValue) :
    filter_integers values = filter_integers_imperative values := by sorry

/-- The mutable implementation satisfies the same complete contract. -/
theorem imperative_correctness (values : List PyValue) :
    Pre values → Post_prop values (filter_integers_imperative values) := by sorry


end humaneval_22_filter_integers
end Agent
