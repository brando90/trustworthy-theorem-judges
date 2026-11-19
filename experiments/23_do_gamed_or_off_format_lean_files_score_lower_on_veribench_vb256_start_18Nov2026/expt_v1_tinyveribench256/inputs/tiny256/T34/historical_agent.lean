import Mathlib
namespace Agent

/-!
# Safe linked-list traversal with `None` checks

Lean 4 translation of the Python program `3_unsafeLinkedList_safe.py`.

The Python program defines a singly linked list `Node(value, next)` and the
function `safe_find_last(node)`, which
* raises `ValueError("empty list")` when `node is None`, and
* otherwise walks along the `next` pointers (`while current.next is not None`)
  until it reaches the last node and returns that node's `value`.

Modelling choices:
* `Node` is a (nested) inductive type: a node carries an `Int` value and an
  `Option Node` successor (`none` plays the role of Python's `None`).
* The argument `Optional[Node]` is modelled by `Option Node`.
* The `ValueError` is modelled by the result type `Except String Int`:
  `.error "empty list"` for `None`, and `.ok v` for the last value `v`.
* `ofList : List Int → Option Node` builds a chain of nodes from a list of
  values (`[]` ↦ `none`); it is used to state list-based specifications and to
  run randomized property-based tests.
-/

namespace «3_unsafeLinkedList_safe»

/-! ## Linked-list nodes -/

/-- A linked-list node: `Node(value, next)`. -/
inductive Node where
  | mk (value : Int) (next : Option Node)
deriving Repr

/-- `node.value` -/
def Node.value : Node → Int
  | .mk v _ => v

/-- `node.next` -/
def Node.next : Node → Option Node
  | .mk _ n => n

/-- Number of nodes reachable from `n` (including `n` itself). -/
def Node.length : Node → Nat
  | .mk _ none => 1
  | .mk _ (some n) => n.length + 1

/-- The values stored along the chain starting at `n` (in traversal order). -/
def Node.toList : Node → List Int
  | .mk v none => [v]
  | .mk v (some n) => v :: n.toList

/-- Build a chain of nodes from a list of values (`[]` ↦ `none`, i.e. `None`). -/
def ofList : List Int → Option Node
  | [] => none
  | x :: xs => some (.mk x (ofList xs))

/-- Values of an optional node (`None` ↦ `[]`). -/
def optToList : Option Node → List Int
  | none => []
  | some n => n.toList

-- Decidable equality on the result type (needed for executable tests).
deriving instance DecidableEq for Except

/-! ## Functional implementation -/

/-- The last node of the chain starting at `n`
(the node at which the Python `while` loop stops). -/
def lastNode : Node → Node
  | .mk v none => .mk v none
  | .mk _ (some n) => lastNode n

/-- Value of the last node reachable from `n`
(the `while current.next is not None` traversal of the Python code). -/
def findLastNode : Node → Int
  | .mk v none => v
  | .mk _ (some n) => findLastNode n

/-- `safe_find_last`: `ValueError("empty list")` on `None`,
otherwise the value of the last node. -/
def safeFindLast : Option Node → Except String Int
  | none => .error "empty list"
  | some n => .ok (findLastNode n)

/-! ## Unit tests (mirroring `check`) -/

/-- `n1 = Node(1, Node(2, Node(3)))` -/
def n1 : Node := .mk 1 (some (.mk 2 (some (.mk 3 none))))

/-- The long list `Node(0) -> Node(1) -> ... -> Node(9)`. -/
def longList : Option Node := ofList ((List.range 10).map (fun i => (i : Int)))

example : safeFindLast (some n1) = .ok 3 := by native_decide
example : safeFindLast (some (.mk 42 none)) = .ok 42 := by native_decide
example : safeFindLast none = .error "empty list" := by native_decide
example : safeFindLast longList = .ok 9 := by native_decide
example : optToList longList = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := by native_decide

#eval safeFindLast (some n1)              -- Except.ok 3
#eval safeFindLast (some (.mk 42 none))   -- Except.ok 42
#eval safeFindLast none                   -- Except.error "empty list"
#eval safeFindLast longList               -- Except.ok 9

/-! ## Pre-condition -/

/-- Pre-condition: `safe_find_last` accepts every `Optional[Node]`; the `None`
case is part of its contract (it raises `ValueError`). Hence every input is
admissible. -/
def Pre (_node : Option Node) : Prop := True

/-! ## Basic lemmas -/

theorem Node.length_pos (n : Node) : 1 ≤ n.length := by
  cases n with
  | mk v nx => cases nx <;> simp [Node.length]

theorem Node.toList_ne_nil (n : Node) : n.toList ≠ [] := by
  cases n with
  | mk v nx => cases nx <;> simp [Node.toList]

theorem Node.toList_length (n : Node) : n.toList.length = n.length := by
  induction n using findLastNode.induct with
  | case1 v => simp [Node.toList, Node.length]
  | case2 v m ih => simp [Node.toList, Node.length, ih]

theorem findLastNode_eq_lastNode : ∀ n : Node, findLastNode n = (lastNode n).value
  | .mk v none => rfl
  | .mk v (some m) => by
      have ih := findLastNode_eq_lastNode m
      simp [findLastNode, lastNode, ih]

theorem findLastNode_eq_getLast :
    ∀ n : Node, findLastNode n = n.toList.getLast (Node.toList_ne_nil n)
  | .mk v none => by simp [findLastNode, Node.toList]
  | .mk v (some m) => by
      have ih := findLastNode_eq_getLast m
      simp only [findLastNode, Node.toList, ih]
      rw [List.getLast_cons (Node.toList_ne_nil m)]

theorem optToList_ofList : ∀ xs : List Int, optToList (ofList xs) = xs
  | [] => rfl
  | x :: xs => by
      have ih := optToList_ofList xs
      cases hxs : xs with
      | nil => simp [ofList, optToList, Node.toList]
      | cons y ys =>
        subst hxs
        simp only [ofList, optToList, Node.toList] at ih ⊢
        simp [ih]

/-! ## Properties -/

/-- `safe_find_last(None)` raises `ValueError("empty list")`. -/
def error_on_none_prop : Prop := safeFindLast none = .error "empty list"

theorem error_on_none_thm : error_on_none_prop := rfl

/-- A single node (`next is None`) yields its own value. -/
def single_node_prop : Prop := ∀ v : Int, safeFindLast (some (.mk v none)) = .ok v

theorem single_node_thm : single_node_prop := fun _ => rfl

/-- One traversal step: the head value is irrelevant when there is a successor. -/
def step_prop : Prop :=
  ∀ (v : Int) (m : Node), safeFindLast (some (.mk v (some m))) = safeFindLast (some m)

theorem step_thm : step_prop := fun _ _ => rfl

/-- For a non-`None` node the result is the last value of the chain. -/
def last_of_toList_prop : Prop :=
  ∀ n : Node, safeFindLast (some n) = .ok (n.toList.getLast (Node.toList_ne_nil n))

theorem last_of_toList_thm : last_of_toList_prop := by
  intro n
  simp [safeFindLast, findLastNode_eq_getLast]

/-- List characterisation: on the chain built from `xs`, the result is the last
element of `xs`, or the error when `xs` is empty. -/
def ofList_prop : Prop :=
  ∀ xs : List Int,
    safeFindLast (ofList xs) = (xs.getLast?).elim (Except.error "empty list") Except.ok

theorem ofList_thm : ofList_prop := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      simp only [ofList, safeFindLast, findLastNode] at ih ⊢
      rw [List.getLast?_cons_cons]
      exact ih

/-- Appending a node at the end makes its value the result. -/
def last_append_prop : Prop :=
  ∀ (xs : List Int) (x : Int), safeFindLast (ofList (xs ++ [x])) = .ok x

theorem last_append_thm : last_append_prop := by
  intro xs x
  rw [ofList_thm (xs ++ [x])]
  simp

/-- The returned value is one of the values stored in the list. -/
def result_mem_prop : Prop :=
  ∀ n : Node, ∃ v : Int, safeFindLast (some n) = .ok v ∧ v ∈ n.toList

theorem result_mem_thm : result_mem_prop := by
  intro n
  refine ⟨findLastNode n, rfl, ?_⟩
  rw [findLastNode_eq_getLast]
  exact List.getLast_mem _

/-- The call succeeds exactly when the argument is not `None`. -/
def ok_iff_some_prop : Prop :=
  ∀ node : Option Node, (∃ v : Int, safeFindLast node = .ok v) ↔ node ≠ none

theorem ok_iff_some_thm : ok_iff_some_prop := by
  intro node
  cases node with
  | none => simp [safeFindLast]
  | some n => simp [safeFindLast]

/-! ## Post-condition -/

/-- Post-condition of `safe_find_last node = result`. -/
def Post_prop (node : Option Node) (result : Except String Int) : Prop :=
  (node = none → result = .error "empty list") ∧
  (∀ n : Node, node = some n → result = .ok (n.toList.getLast (Node.toList_ne_nil n))) ∧
  (∀ n : Node, node = some n → ∃ v : Int, result = .ok v ∧ v ∈ n.toList) ∧
  ((∃ v : Int, result = .ok v) ↔ node ≠ none)

/-! ## Property-based tests -/

-- error_on_none_prop (closed statement; checked exhaustively)
example : safeFindLast none = .error "empty list" := by native_decide

-- single_node_prop
#eval Plausible.Testable.check (∀ v : Int, safeFindLast (some (.mk v none)) = .ok v)

-- step_prop (nodes are generated through `ofList`; `w :: xs` is a non-`None` node)
#eval Plausible.Testable.check (∀ (v w : Int) (xs : List Int),
  safeFindLast (ofList (v :: w :: xs)) = safeFindLast (ofList (w :: xs)))
example : (List.range 20).all (fun k =>
    let xs := (List.range (k + 1)).map (fun i => (i : Int))
    decide (safeFindLast (ofList ((-7) :: xs)) = safeFindLast (ofList xs))) = true := by
  native_decide

-- last_of_toList_prop (`x :: xs` is a non-`None` node whose `toList` is `x :: xs`)
#eval Plausible.Testable.check (∀ (x : Int) (xs : List Int),
  safeFindLast (ofList (x :: xs)) = .ok ((x :: xs).getLast?.getD 0))
example : (List.range 20).all (fun k =>
    let xs := (List.range (k + 1)).map (fun i => (i : Int))
    decide (safeFindLast (ofList xs) = .ok (xs.getLast?.getD 0))) = true := by
  native_decide

-- ofList_prop
#eval Plausible.Testable.check (∀ xs : List Int,
  safeFindLast (ofList xs) = (xs.getLast?).elim (Except.error "empty list") Except.ok)

-- last_append_prop
#eval Plausible.Testable.check (∀ (xs : List Int) (x : Int),
  safeFindLast (ofList (xs ++ [x])) = .ok x)

-- result_mem_prop
#eval Plausible.Testable.check (∀ (x : Int) (xs : List Int),
  (safeFindLast (ofList (x :: xs))).toOption.all (fun v => decide (v ∈ x :: xs)) = true)
example : (List.range 20).all (fun k =>
    let xs := (List.range (k + 1)).map (fun i => (i : Int) * 3 - 5)
    (safeFindLast (ofList xs)).toOption.all (fun v => decide (v ∈ xs))) = true := by
  native_decide

-- ok_iff_some_prop
#eval Plausible.Testable.check (∀ xs : List Int,
  (safeFindLast (ofList xs)).toOption.isSome = !xs.isEmpty)

/-- Executable (Boolean) form of `Post_prop` on the chain built from `xs`. -/
def postCheck (xs : List Int) : Bool :=
  let r := safeFindLast (ofList xs)
  match xs.getLast? with
  | none => decide (r = .error "empty list") && !r.toOption.isSome
  | some x => decide (r = .ok x) && r.toOption.all (fun v => decide (v ∈ xs))

-- Post_prop (randomized)
#eval Plausible.Testable.check (∀ xs : List Int, postCheck xs = true)

-- Post_prop (bounded, exhaustive over chains of lengths 0..30)
example : (List.range 31).all (fun k => postCheck ((List.range k).map (fun i => (i : Int)))) = true := by
  native_decide

/-! ## Correctness -/

theorem safeFindLast_correct (node : Option Node) (_hpre : Pre node) :
    Post_prop node (safeFindLast node) := by
  refine ⟨?_, ?_, ?_, ok_iff_some_thm node⟩
  · intro h; subst h; rfl
  · intro n h; subst h; exact last_of_toList_thm n
  · intro n h; subst h; exact result_mem_thm n

/-! ## Imperative implementation -/

/-- Imperative version of `safe_find_last`: a mutable cursor `current` walks
along `next` pointers until it hits `None` (the loop is bounded by the number
of nodes, which is enough fuel to reach the last node). -/
def safeFindLastImp (node : Option Node) : Except String Int := Id.run do
  match node with
  | none => return .error "empty list"
  | some n =>
    let mut current : Node := n
    for _ in List.range n.length do
      match current.next with
      | none => break
      | some nxt => current := nxt
    return .ok current.value

/-! ## Imperative tests -/

example : safeFindLastImp (some n1) = .ok 3 := by native_decide
example : safeFindLastImp (some (.mk 42 none)) = .ok 42 := by native_decide
example : safeFindLastImp none = .error "empty list" := by native_decide
example : safeFindLastImp longList = .ok 9 := by native_decide

#eval safeFindLastImp (some n1)              -- Except.ok 3
#eval safeFindLastImp none                   -- Except.error "empty list"
#eval safeFindLastImp longList               -- Except.ok 9

#eval Plausible.Testable.check (∀ xs : List Int,
  safeFindLast (ofList xs) = safeFindLastImp (ofList xs))

/-! ## Equivalence -/

/-- The loop of `safeFindLastImp`, run with enough fuel, stops at the last node. -/
theorem imp_loop (f : Nat → Node → Id (ForInStep Node))
    (hf : ∀ (i : Nat) (c : Node), f i c =
      match c.next with
      | none => pure (ForInStep.done c)
      | some nxt => pure (ForInStep.yield nxt))
    (l : List Nat) :
    ∀ cur : Node, cur.length ≤ l.length + 1 → forIn (m := Id) l cur f = lastNode cur := by
  induction l with
  | nil =>
    intro cur h
    cases cur with
    | mk v nx =>
      cases nx with
      | none => rfl
      | some m =>
        exfalso
        have := Node.length_pos m
        simp [Node.length] at h
        omega
  | cons a l ih =>
    intro cur h
    cases cur with
    | mk v nx =>
      cases nx with
      | none =>
        rw [List.forIn_cons, hf]
        rfl
      | some m =>
        have hm : m.length ≤ l.length + 1 := by
          simp [Node.length] at h
          omega
        rw [List.forIn_cons, hf]
        show forIn (m := Id) l m f = lastNode (.mk v (some m))
        exact ih m hm

theorem safeFindLastImp_none : safeFindLastImp none = .error "empty list" := rfl

theorem safeFindLastImp_some (n : Node) :
    safeFindLastImp (some n) = .ok (lastNode n).value := by
  unfold safeFindLastImp
  dsimp only
  rw [imp_loop _ ?_ (List.range n.length) n (by simp)]
  · rfl
  · intro i c
    cases c with
    | mk v nx => cases nx <;> rfl

/-- Functional and imperative implementations agree on every input. -/
theorem safeFindLast_eq_imp (node : Option Node) :
    safeFindLast node = safeFindLastImp node := by
  cases node with
  | none => rfl
  | some n =>
    rw [safeFindLastImp_some]
    simp [safeFindLast, findLastNode_eq_lastNode]

/-- Consequently the imperative implementation satisfies the post-condition too. -/
theorem safeFindLastImp_correct (node : Option Node) (hpre : Pre node) :
    Post_prop node (safeFindLastImp node) := by
  rw [← safeFindLast_eq_imp]
  exact safeFindLast_correct node hpre

end «3_unsafeLinkedList_safe»
end Agent
