import Mathlib
namespace Agent

/-!
# Finding the last value through nullable linked-list pointers

This is a value model of Python's finite, acyclic linked lists. `Node.null`
represents `None`; `Node.mk value next` represents a node with the indicated
fields. `Int` models Python's arbitrary-precision signed integers. Cyclic
pointer graphs, on which the Python loop diverges, are not finite lists.

An `Except.error .attributeError` records the exception from dereferencing
`None`, rather than inventing a default integer. In particular, the empty
input is part of the domain and is covered by the correctness theorem.
The list conversion is only an independent specification and a test-input
generator: the implementation follows the `next` pointers directly.
-/

namespace UnsafeLinkedList

inductive Node where
  | null
  | mk (value : Int) (next : Node)
  deriving Repr, DecidableEq

inductive FindError where
  | attributeError
  deriving Repr, DecidableEq

deriving instance DecidableEq for Except

abbrev FindResult := Except FindError Int

namespace Node

def toList : Node → List Int
  | .null => []
  | .mk value next => value :: toList next

def ofList : List Int → Node
  | [] => .null
  | value :: rest => .mk value (ofList rest)

def length : Node → Nat
  | .null => 0
  | .mk _ next => next.length + 1

end Node

/-- Follow `next` until it is null, then return the current node's value.
The first case models the Python AttributeError on an initially null pointer. -/
def unsafe_find_last : Node → FindResult
  | .null => .error .attributeError
  | .mk value .null => .ok value
  | .mk _ (.mk value next) => unsafe_find_last (.mk value next)

-- Unit tests: all five cases from Python's `check`.
def n3 : Node := .mk 3 .null
def n2 : Node := .mk 2 n3
def n1 : Node := .mk 1 n2
def single : Node := .mk 42 .null
def lonely : Node := .mk 99 .null
def longList : Node := Node.ofList ((List.range 10).map Int.ofNat)

/-- Boolean form of Python's assertion-based test harness. The null test
requires the AttributeError outcome; a returned integer does not pass. -/
def check (candidate : Node → FindResult) : Bool :=
  decide (candidate n1 = .ok 3) &&
  decide (candidate single = .ok 42) &&
  decide (candidate .null = .error .attributeError) &&
  decide (candidate lonely = .ok 99) &&
  decide (candidate longList = .ok 9)

example : check unsafe_find_last = true := by native_decide
example : unsafe_find_last n1 = .ok 3 := by native_decide
example : unsafe_find_last single = .ok 42 := by native_decide
example : unsafe_find_last .null = .error .attributeError := by native_decide
example : unsafe_find_last lonely = .ok 99 := by native_decide
example : unsafe_find_last longList = .ok 9 := by native_decide
example : unsafe_find_last (Node.ofList [-8, 0, -17]) = .ok (-17) := by native_decide

#eval unsafe_find_last n1
#eval unsafe_find_last single
#eval unsafe_find_last .null
#eval unsafe_find_last lonely
#eval unsafe_find_last longList
#eval if check unsafe_find_last then "All tests passed."
  else "Candidate failed null pointer tests"

/-- All finite nullable lists are admissible, including the empty list.
Finiteness is intrinsic to `Node`; no nonemptiness restriction is imposed. -/
def Pre (_node : Node) : Prop := True

/-- Independent list specification, including the exceptional outcome. -/
def resultOfLast : Option Int → FindResult
  | none => .error .attributeError
  | some value => .ok value

/-- Exact agreement with the last element of the represented list. -/
def last_value_prop (node : Node) : Prop :=
  unsafe_find_last node = resultOfLast node.toList.getLast?

/-- AttributeError occurs exactly on the null input. -/
def null_error_prop (node : Node) : Prop :=
  unsafe_find_last node = .error .attributeError ↔ node = .null

/-- A singleton returns its own value. -/
def singleton_prop (node : Node) : Prop :=
  ∀ value, node = .mk value .null → unsafe_find_last node = .ok value

/-- On a nonterminal node, following `next` preserves the answer. -/
def tail_step_prop (node : Node) : Prop :=
  ∀ value next, node = .mk value next → next ≠ .null →
    unsafe_find_last node = unsafe_find_last next

/-- Every successful result is a value actually stored in the input. -/
def member_prop (node : Node) : Prop :=
  ∀ value, unsafe_find_last node = .ok value → value ∈ node.toList

@[simp] theorem toList_ofList (xs : List Int) :
    (Node.ofList xs).toList = xs := by
  induction xs with
  | nil => rfl
  | cons value xs ih => simp [Node.ofList, Node.toList, ih]

@[simp] theorem ofList_toList (node : Node) :
    Node.ofList node.toList = node := by
  induction node with
  | null => rfl
  | mk value next ih => simp [Node.ofList, Node.toList, ih]

theorem last_value_thm (node : Node) : last_value_prop node := by
  induction node with
  | null => rfl
  | mk value next ih =>
    cases next with
    | null => rfl
    | mk value' next =>
      simpa [last_value_prop, unsafe_find_last, Node.toList] using ih

theorem null_error_thm (node : Node) : null_error_prop node := by
  induction node with
  | null => simp [null_error_prop, unsafe_find_last]
  | mk value next ih =>
    cases next with
    | null => simp [null_error_prop, unsafe_find_last]
    | mk value' next =>
      simpa [null_error_prop, unsafe_find_last] using ih

theorem singleton_thm (node : Node) : singleton_prop node := by
  intro value h
  subst node
  rfl

theorem tail_step_thm (node : Node) : tail_step_prop node := by
  intro value next h hn
  subst node
  cases next with
  | null => exact (hn rfl).elim
  | mk value' rest => rfl

theorem member_thm (node : Node) : member_prop node := by
  induction node with
  | null => simp [member_prop, unsafe_find_last]
  | mk value next ih =>
    intro answer h
    cases next with
    | null =>
      simpa [unsafe_find_last, Node.toList] using h.symm
    | mk value' rest =>
      exact List.mem_cons_of_mem value (ih answer h)

/-- Full functional contract; the exception case is part of the postcondition. -/
def Post_prop (node : Node) : Prop :=
  last_value_prop node ∧ null_error_prop node ∧ singleton_prop node ∧
    tail_step_prop node ∧ member_prop node

/-! ## Property-based tests
The Boolean checks below eliminate the uniquely determined fields in the
singleton/step properties and inspect the result in the membership property.
Thus they test the executable forms of the propositions, not just unit cases.
`ofList_toList` shows that testing lists represents every finite `Node` shape.
-/

def last_value_check (node : Node) : Bool :=
  decide (unsafe_find_last node = resultOfLast node.toList.getLast?)

def null_error_check (node : Node) : Bool :=
  decide ((unsafe_find_last node = .error .attributeError) ↔ node = .null)

def singleton_check (node : Node) : Bool :=
  match node with
  | .mk value .null => decide (unsafe_find_last node = .ok value)
  | _ => true

def tail_step_check (node : Node) : Bool :=
  match node with
  | .mk _ (.mk value next) =>
    decide (unsafe_find_last node = unsafe_find_last (.mk value next))
  | _ => true

def member_check (node : Node) : Bool :=
  match unsafe_find_last node with
  | .error _ => true
  | .ok value => decide (value ∈ node.toList)

def post_check (node : Node) : Bool :=
  last_value_check node && null_error_check node && singleton_check node &&
    tail_step_check node && member_check node

/-- Exhaust all lists of a given length over a signed alphabet. -/
def smallLists : Nat → List (List Int)
  | 0 => [[]]
  | n + 1 => [-2, -1, 0, 1, 2].flatMap fun value =>
      (smallLists n).map (List.cons value)

/-- 3,906 inputs, including null, all singleton values, repeated and signed values. -/
def boundedInputs : List Node :=
  ((List.range 6).flatMap smallLists).map Node.ofList

-- A separate bounded PBT for each property and for the full postcondition.
example : boundedInputs.all last_value_check = true := by native_decide
example : boundedInputs.all null_error_check = true := by native_decide
example : boundedInputs.all singleton_check = true := by native_decide
example : boundedInputs.all tail_step_check = true := by native_decide
example : boundedInputs.all member_check = true := by native_decide
example : boundedInputs.all post_check = true := by native_decide
#eval boundedInputs.length
#eval boundedInputs.all post_check

-- Randomized PBTs add arbitrary Int values and larger list shapes.
#eval Plausible.Testable.check (∀ xs : List Int,
  last_value_check (Node.ofList xs) = true)
#eval Plausible.Testable.check (∀ xs : List Int,
  null_error_check (Node.ofList xs) = true)
#eval Plausible.Testable.check (∀ xs : List Int,
  singleton_check (Node.ofList xs) = true)
#eval Plausible.Testable.check (∀ xs : List Int,
  tail_step_check (Node.ofList xs) = true)
#eval Plausible.Testable.check (∀ xs : List Int,
  member_check (Node.ofList xs) = true)
#eval Plausible.Testable.check (∀ xs : List Int,
  post_check (Node.ofList xs) = true)

/-- Kernel-checked correctness for the entire domain, including null. -/
theorem correctness (node : Node) : Pre node → Post_prop node := by
  intro _
  exact ⟨last_value_thm node, null_error_thm node, singleton_thm node,
    tail_step_thm node, member_thm node⟩

/-! ## Imperative translation

The mutable `current` follows precisely the Python loop's non-null `next`
links. `break` implements the failed while guard. A finite fuel schedule of
`node.length` iterations makes termination explicit in Lean; the proof below
shows this is enough for every input, so fuel never changes the answer.
For an initially null pointer, reading the value produces AttributeError.
-/

def unsafe_find_last_imp (node : Node) : FindResult := Id.run do
  let mut current := node
  for _ in List.replicate node.length () do
    match current with
    | .mk _ (.mk value next) => current := .mk value next
    | _ => break
  match current with
  | .null => return .error .attributeError
  | .mk value _ => return .ok value

-- Imperative tests reproduce all five Python cases, including the exception.
example : check unsafe_find_last_imp = true := by native_decide
#eval check unsafe_find_last_imp
example : unsafe_find_last_imp n1 = .ok 3 := by native_decide
example : unsafe_find_last_imp single = .ok 42 := by native_decide
example : unsafe_find_last_imp .null = .error .attributeError := by native_decide
example : unsafe_find_last_imp lonely = .ok 99 := by native_decide
example : unsafe_find_last_imp longList = .ok 9 := by native_decide
example : unsafe_find_last_imp (Node.ofList [-8, 0, -17]) = .ok (-17) := by
  native_decide

#eval unsafe_find_last_imp n1
#eval unsafe_find_last_imp single
#eval unsafe_find_last_imp .null
#eval unsafe_find_last_imp lonely
#eval unsafe_find_last_imp longList

example : boundedInputs.all (fun node =>
    decide (unsafe_find_last node = unsafe_find_last_imp node)) = true := by
  native_decide
#eval Plausible.Testable.check (∀ xs : List Int,
  unsafe_find_last (Node.ofList xs) = unsafe_find_last_imp (Node.ofList xs))

/-- The very same imperative loop, with an arbitrary fuel schedule, exposed
separately to state its invariant. -/
def walk (steps : Nat) (node : Node) : Node := Id.run do
  let mut current := node
  for _ in List.replicate steps () do
    match current with
    | .mk _ (.mk value next) => current := .mk value next
    | _ => break
  return current

/-- The final Python field access; reading a null pointer is exceptional. -/
def readValue : Node → FindResult
  | .null => .error .attributeError
  | .mk value _ => .ok value

theorem walk_zero (node : Node) : walk 0 node = node := by
  simp [walk]

theorem walk_succ_null (steps : Nat) : walk (steps + 1) .null = .null := by
  simp [walk, List.replicate_succ]

theorem walk_succ_single (steps : Nat) (value : Int) :
    walk (steps + 1) (.mk value .null) = .mk value .null := by
  simp [walk, List.replicate_succ]

theorem walk_succ_next (steps : Nat) (value value' : Int) (next : Node) :
    walk (steps + 1) (.mk value (.mk value' next)) = walk steps (.mk value' next) := by
  simp [walk, List.replicate_succ]

/-- With enough iterations, the imperative pointer's value is exactly the
functional result. The fuel condition is internal, not a restriction on inputs. -/
theorem walk_answer (node : Node) (steps : Nat) (h : node.length ≤ steps) :
    readValue (walk steps node) = unsafe_find_last node := by
  induction node generalizing steps with
  | null =>
    cases steps with
    | zero => rfl
    | succ steps => simp [walk_succ_null, readValue, unsafe_find_last]
  | mk value next ih =>
    cases steps with
    | zero => simp [Node.length] at h
    | succ steps =>
      cases next with
      | null => simp [walk_succ_single, readValue, unsafe_find_last]
      | mk value' next =>
        rw [walk_succ_next]
        exact ih steps (Nat.le_of_succ_le_succ h)

/-- Definitional identification with the actual imperative program, not
an assumed correspondence to a separately specified algorithm. -/
theorem imperative_eq_read_walk (node : Node) :
    unsafe_find_last_imp node = readValue (walk node.length node) := by
  rfl

/-- Full equivalence, including the AttributeError outcome on null. -/
theorem functional_eq_imperative (node : Node) :
    unsafe_find_last node = unsafe_find_last_imp node := by
  rw [imperative_eq_read_walk]
  exact (walk_answer node node.length (Nat.le_refl _)).symm

end UnsafeLinkedList
end Agent
