import Mathlib
namespace Agent

/-!
# HumanEval 1: separate parenthesis groups

An exact integer-depth translation of the Python scanner. Characters other than
parentheses are ignored (in particular, spaces). A final incomplete group is not
returned, just as in Python. The correctness specification applies to balanced
inputs. `Balanced` is the usual Dyck grammar; a `Group` is one outer pair around
a balanced word, so it cannot contain a top-level group boundary in its interior.
-/

namespace humaneval_1_separate_paren_groups

structure State where
  result : List (List Char) := []
  current : List Char := []
  depth : Int := 0
  deriving DecidableEq, Repr

/-- One iteration, including Python's signed depth on invalid inputs. -/
def step (s : State) (c : Char) : State :=
  if c = '(' then
    { s with current := s.current ++ [c], depth := s.depth + 1 }
  else if c = ')' then
    let d := s.depth - 1
    let cur := s.current ++ [c]
    if d = 0 then
      { result := s.result ++ [cur], current := [], depth := d }
    else
      { s with current := cur, depth := d }
  else s

def scan : List Char → State → State
  | [], s => s
  | c :: cs, s => scan cs (step s c)

def separate_paren_groups (s : String) : List String :=
  ((scan s.toList {}).result).map String.mk

example : separate_paren_groups "(()()) ((())) () ((())()())" =
    ["(()())", "((()))", "()", "((())()())"] := by native_decide
example : separate_paren_groups "() (()) ((())) (((())))" =
    ["()", "(())", "((()))", "(((())))"] := by native_decide
example : separate_paren_groups "(()(())((())))" =
    ["(()(())((())))"] := by native_decide
example : separate_paren_groups "( ) (( )) (( )( ))" =
    ["()", "(())", "(()())"] := by native_decide
example : separate_paren_groups "" = [] := by native_decide
example : separate_paren_groups "() (" = ["()"] := by native_decide
example : separate_paren_groups ")()(" = [] := by native_decide
#eval separate_paren_groups "( ) (( )) (( )( ))"

/-- The balanced-parenthesis language, including the empty word. -/
inductive Balanced : List Char → Prop
  | nil : Balanced []
  | wrap {xs} : Balanced xs → Balanced ('(' :: (xs ++ [')']))
  | append {xs ys} : Balanced xs → Balanced ys → Balanced (xs ++ ys)

/-- A nonempty, primitive balanced group, not a concatenation of groups. -/
def Group (xs : List Char) : Prop :=
  ∃ inner, Balanced inner ∧ xs = '(' :: (inner ++ [')'])

def isParen (c : Char) : Bool := c == '(' || c == ')'

def clean (s : String) : List Char := s.toList.filter isParen

/-- The parentheses in the input must be balanced; ignored characters are unrestricted. -/
def Pre (s : String) : Prop := Balanced (clean s)

/-- Signed parenthesis depth; ignored characters contribute zero. -/
def balance : List Char → Int
  | [] => 0
  | c :: cs => (if c = '(' then 1 else if c = ')' then -1 else 0) + balance cs

/-- Each group ends exactly at its first return to depth zero. In particular,
there are no internal top-level boundaries, and no premature closing braces. -/
def boundaries_prop (s : String) : Prop :=
  ∀ g ∈ separate_paren_groups s, balance g.toList = 0 ∧
    ∀ n : Nat, 0 < n → n < g.toList.length → 0 < balance (g.toList.take n)

/-- Concatenation and order of the emitted groups reproduce exactly the input
with ignored characters removed. -/
def preservation_prop (s : String) : Prop :=
  (separate_paren_groups s).flatMap String.toList = clean s

/-- Every output is a single primitive balanced group. -/
def groups_prop (s : String) : Prop :=
  ∀ g ∈ separate_paren_groups s, Group g.toList

def nonempty_prop (s : String) : Prop :=
  ∀ g ∈ separate_paren_groups s, g ≠ ""

def alphabet_prop (s : String) : Prop :=
  ∀ g ∈ separate_paren_groups s, ∀ c ∈ g.toList, c = '(' ∨ c = ')'

/-- Ignoring spaces (and all other non-parenthesis characters) is exact,
including on malformed inputs. -/
def ignored_prop (s : String) : Prop :=
  separate_paren_groups s = separate_paren_groups (String.mk (clean s))

theorem scan_append (xs ys : List Char) (s : State) :
    scan (xs ++ ys) s = scan ys (scan xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons c cs ih => exact ih (step s c)

theorem scan_filter (cs : List Char) (s : State) :
    scan (cs.filter isParen) s = scan cs s := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    by_cases ho : c = '('
    · subst c
      simpa [isParen, scan] using ih (step s '(')
    · by_cases hc : c = ')'
      · subst c
        simpa [isParen, scan] using ih (step s ')')
      · simpa [isParen, scan, step, ho, hc] using ih s

theorem balanced_alphabet {xs : List Char} (h : Balanced xs) :
    ∀ c ∈ xs, c = '(' ∨ c = ')' := by
  induction h with
  | nil => simp
  | @wrap xs h ih =>
    intro c hc
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | hc | rfl
    · exact Or.inl rfl
    · exact ih c hc
    · exact Or.inr rfl
  | append hx hy ihx ihy =>
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact ihx c hc
    · exact ihy c hc

/-- Inside an outer pair, a balanced subword never flushes the buffer. -/
theorem scan_inside {xs : List Char} (h : Balanced xs)
    (r : List (List Char)) (cur : List Char) (d : Int) (hd : 0 < d) :
    scan xs ⟨r, cur, d⟩ = ⟨r, cur ++ xs, d⟩ := by
  induction h generalizing r cur d with
  | nil => simp [scan]
  | @wrap xs h ih =>
    have hp : 0 < d + 1 := by omega
    have hn : d ≠ 0 := by omega
    change scan (xs ++ [')']) ⟨r, cur ++ ['('], d + 1⟩ = _
    rw [scan_append, ih r (cur ++ ['(']) (d + 1) hp]
    simp [scan, step, hn, List.append_assoc]
  | @append xs ys hx hy ihx ihy =>
    rw [scan_append, ihx r cur d hd, ihy r (cur ++ xs) d hd]
    simp [List.append_assoc]

/-- The scanner realizes the grammar as a list of primitive groups. -/
theorem scan_balanced {xs : List Char} (h : Balanced xs)
    (r : List (List Char)) :
    ∃ gs, scan xs ⟨r, [], 0⟩ = ⟨r ++ gs, [], 0⟩ ∧
      gs.flatten = xs ∧ ∀ g ∈ gs, Group g := by
  induction h generalizing r with
  | nil => exact ⟨[], by simp [scan], rfl, by simp⟩
  | @wrap xs h ih =>
    refine ⟨['(' :: (xs ++ [')'])], ?_, by simp, ?_⟩
    · change scan (xs ++ [')']) ⟨r, ['('], 1⟩ = _
      rw [scan_append, scan_inside h r ['('] 1 (by omega)]
      simp [scan, step]
    · intro g hg
      simp only [List.mem_singleton] at hg
      subst g
      exact ⟨xs, h, rfl⟩
  | @append xs ys hx hy ihx ihy =>
    obtain ⟨gx, hsx, hfx, hgx⟩ := ihx r
    obtain ⟨gy, hsy, hfy, hgy⟩ := ihy (r ++ gx)
    refine ⟨gx ++ gy, ?_, ?_, ?_⟩
    · rw [scan_append, hsx, hsy]
      simp [List.append_assoc]
    · simp [List.flatten_append, hfx, hfy]
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact hgx g hg
      · exact hgy g hg

/-- A concrete decomposition witness, used by the public properties. -/
theorem separate_spec (s : String) (h : Pre s) :
    ∃ gs : List (List Char), separate_paren_groups s = gs.map String.mk ∧
      gs.flatten = clean s ∧ ∀ g ∈ gs, Group g := by
  obtain ⟨gs, hs, hf, hg⟩ := scan_balanced h []
  refine ⟨gs, ?_, hf, hg⟩
  have he := scan_filter s.toList ({} : State)
  change scan (clean s) {} = scan s.toList {} at he
  simp only [List.nil_append] at hs
  unfold separate_paren_groups
  rw [← he, hs]

theorem balance_append (xs ys : List Char) :
    balance (xs ++ ys) = balance xs + balance ys := by
  induction xs with
  | nil => simp [balance]
  | cons c cs ih => simp [balance, ih, add_assoc]

theorem balanced_zero {xs : List Char} (h : Balanced xs) : balance xs = 0 := by
  induction h with
  | nil => rfl
  | wrap h ih => simp [balance, balance_append, ih]
  | append hx hy ihx ihy => simp [balance_append, ihx, ihy]

theorem balanced_prefix_nonneg {xs : List Char} (h : Balanced xs) (n : Nat) :
    0 ≤ balance (xs.take n) := by
  induction h generalizing n with
  | nil => simp [balance]
  | @wrap xs h ih =>
    cases n with
    | zero => simp [balance]
    | succ k =>
      by_cases hk : k ≤ xs.length
      · rw [List.take_succ_cons, List.take_append_of_le_length hk]
        have hi := ih k
        simp only [balance, ↓reduceIte]
        omega
      · have hlen : ('(' :: (xs ++ [')'])).length ≤ k + 1 := by
          simp only [List.length_cons, List.length_append, List.length_nil]
          omega
        rw [List.take_of_length_le hlen, balanced_zero (Balanced.wrap h)]
  | append hx hy ihx ihy =>
    rw [List.take_append, balance_append]
    exact add_nonneg (ihx n) (ihy _)

theorem preservation_thm (s : String) (h : Pre s) : preservation_prop s := by
  obtain ⟨gs, hs, hf, hg⟩ := separate_spec s h
  unfold preservation_prop
  rw [hs]
  simpa [List.flatMap_map, Function.comp_def] using hf

theorem groups_thm (s : String) (h : Pre s) : groups_prop s := by
  obtain ⟨gs, hs, hf, hg⟩ := separate_spec s h
  intro g hm
  rw [hs] at hm
  obtain ⟨cs, hcs, rfl⟩ := List.mem_map.mp hm
  simpa using hg cs hcs

theorem boundaries_thm (s : String) (h : Pre s) : boundaries_prop s := by
  intro g hg
  obtain ⟨inner, hi, hshape⟩ := groups_thm s h g hg
  rw [hshape]
  refine ⟨balanced_zero (Balanced.wrap hi), ?_⟩
  intro n hn hlen
  cases n with
  | zero => omega
  | succ k =>
    have hk : k ≤ inner.length := by
      simp only [List.length_cons, List.length_append, List.length_nil] at hlen
      omega
    rw [List.take_succ_cons, List.take_append_of_le_length hk]
    have hp := balanced_prefix_nonneg hi k
    simp only [balance, ↓reduceIte]
    omega

theorem nonempty_thm (s : String) (h : Pre s) : nonempty_prop s := by
  intro g hg he
  obtain ⟨inner, hi, hshape⟩ := groups_thm s h g hg
  subst g
  simp at hshape

theorem alphabet_thm (s : String) (h : Pre s) : alphabet_prop s := by
  intro g hg c hc
  obtain ⟨inner, hi, hshape⟩ := groups_thm s h g hg
  rw [hshape] at hc
  exact balanced_alphabet (Balanced.wrap hi) c hc

theorem ignored_thm (s : String) : ignored_prop s := by
  simp [ignored_prop, separate_paren_groups, clean, scan_filter]

/-- Exact lossless decomposition into nonempty primitive balanced groups,
with no extraneous characters, and invariance under removal of ignored text. -/
def Post_prop (s : String) : Prop :=
  preservation_prop s ∧ groups_prop s ∧ nonempty_prop s ∧
    alphabet_prop s ∧ ignored_prop s ∧ boundaries_prop s

/-! ## Property-based tests

The Boolean balance checker rejects premature closing parentheses and requires
zero final depth. `groupB` additionally requires one outer pair. These are the
executable counterparts of the Dyck-language predicates, not axioms or proofs.
The corpus exhausts **all** words of length at most seven over `(`, `)`, space,
and `x`. Thus it includes ignored text, valid inputs, and malformed inputs.
-/

def balancedB : Nat → List Char → Bool
  | d, [] => d == 0
  | d, c :: cs =>
    if c = '(' then balancedB (d + 1) cs
    else if c = ')' then
      match d with
      | 0 => false
      | n + 1 => balancedB n cs
    else false

def groupB (cs : List Char) : Bool :=
  match cs with
  | '(' :: rest =>
    match rest.reverse with
    | ')' :: revInner => balancedB 0 revInner.reverse
    | _ => false
  | _ => false

def preservationCheck (s : String) : Bool :=
  (separate_paren_groups s).flatMap String.toList == clean s

def groupsCheck (s : String) : Bool :=
  (separate_paren_groups s).all (fun g => groupB g.toList)

def nonemptyCheck (s : String) : Bool :=
  (separate_paren_groups s).all (fun g => g != "")

def alphabetCheck (s : String) : Bool :=
  (separate_paren_groups s).all (fun g => g.toList.all isParen)

def ignoredCheck (s : String) : Bool :=
  separate_paren_groups s == separate_paren_groups (String.mk (clean s))

def boundariesCheck (s : String) : Bool :=
  (separate_paren_groups s).all (fun g =>
    balance g.toList == 0 && (List.range g.toList.length).all
      (fun n => n == 0 || decide (0 < balance (g.toList.take n))))

def postCheck (s : String) : Bool :=
  preservationCheck s && groupsCheck s && nonemptyCheck s &&
    alphabetCheck s && ignoredCheck s && boundariesCheck s

def testWords : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 => [] :: ['(', ')', ' ', 'x'].flatMap
      (fun c => (testWords n).map (fun cs => c :: cs))

def testInputs : List String := (testWords 7).map String.mk

-- PBT for preservation_prop.
example : testInputs.all (fun s => !balancedB 0 (clean s) || preservationCheck s)
    = true := by native_decide
-- PBT for groups_prop: every group is primitive, not just balanced.
example : testInputs.all (fun s => !balancedB 0 (clean s) || groupsCheck s)
    = true := by native_decide
-- PBT for nonempty_prop.
example : testInputs.all (fun s => !balancedB 0 (clean s) || nonemptyCheck s)
    = true := by native_decide
-- PBT for alphabet_prop.
example : testInputs.all (fun s => !balancedB 0 (clean s) || alphabetCheck s)
    = true := by native_decide
-- PBT for ignored_prop, with no precondition, even for malformed input.
example : testInputs.all ignoredCheck = true := by native_decide
-- PBT for boundaries_prop: zero final depth and strictly positive interior depth.
example : testInputs.all (fun s => !balancedB 0 (clean s) || boundariesCheck s)
    = true := by native_decide
-- PBT for the entire postcondition.
example : testInputs.all (fun s => !balancedB 0 (clean s) || postCheck s)
    = true := by native_decide
#eval (testInputs.length,
  testInputs.countP (fun s => balancedB 0 (clean s)),
  testInputs.all (fun s => !balancedB 0 (clean s) || postCheck s))

theorem correctness (s : String) : Pre s → Post_prop s := by
  intro h
  exact ⟨preservation_thm s h, groups_thm s h, nonempty_thm s h,
    alphabet_thm s h, ignored_thm s, boundaries_thm s h⟩

/-! ## Imperative translation -/

/-- The original loop, with separate mutable result, buffer, and signed depth. -/
def imperativeScan (cs : List Char) (initial : State) : State := Id.run do
  let mut result := initial.result
  let mut current := initial.current
  let mut depth := initial.depth
  for c in cs do
    if c = '(' then
      depth := depth + 1
      current := current ++ [c]
    else if c = ')' then
      depth := depth - 1
      current := current ++ [c]
      if depth = 0 then
        result := result ++ [current]
        current := []
  return ⟨result, current, depth⟩

def separate_paren_groups_imperative (s : String) : List String :=
  ((imperativeScan s.toList {}).result).map String.mk

example : separate_paren_groups_imperative "(()()) ((())) () ((())()())" =
    ["(()())", "((()))", "()", "((())()())"] := by native_decide
example : separate_paren_groups_imperative "() (()) ((())) (((())))" =
    ["()", "(())", "((()))", "(((())))"] := by native_decide
example : separate_paren_groups_imperative "(()(())((())))" =
    ["(()(())((())))"] := by native_decide
example : separate_paren_groups_imperative "( ) (( )) (( )( ))" =
    ["()", "(())", "(()())"] := by native_decide
example : separate_paren_groups_imperative ")()(" = [] := by native_decide
#eval separate_paren_groups_imperative "( ) (( )) (( )( ))"

-- Bounded equivalence PBT also covers inputs outside Pre.
example : testInputs.all (fun s =>
    separate_paren_groups s == separate_paren_groups_imperative s) = true := by
  native_decide

theorem imperativeScan_cons (c : Char) (cs : List Char) (s : State) :
    imperativeScan (c :: cs) s = imperativeScan cs (step s c) := by
  rcases s with ⟨r, cur, d⟩
  by_cases ho : c = '('
  · subst c
    simp [imperativeScan, step, List.forIn_cons]
  · by_cases hc : c = ')'
    · subst c
      by_cases hd : d - 1 = 0
      · simp [imperativeScan, step, List.forIn_cons, hd]
      · simp [imperativeScan, step, List.forIn_cons, hd]
    · simp [imperativeScan, step, List.forIn_cons, ho, hc]

theorem scan_equivalence (cs : List Char) (s : State) :
    scan cs s = imperativeScan cs s := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    rw [imperativeScan_cons]
    exact ih (step s c)

/-- Equivalence is unconditional: malformed strings have the same behavior too. -/
theorem functional_eq_imperative (s : String) :
    separate_paren_groups s = separate_paren_groups_imperative s := by
  simp only [separate_paren_groups, separate_paren_groups_imperative,
    scan_equivalence]

end humaneval_1_separate_paren_groups
end Agent
