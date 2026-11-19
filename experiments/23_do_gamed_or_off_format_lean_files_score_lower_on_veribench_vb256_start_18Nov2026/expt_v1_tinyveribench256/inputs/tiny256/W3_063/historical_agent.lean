import Mathlib
namespace Agent

/-!
# Safe seccomp whitelist filter

A translation of the Python `safe_seccomp_filter` and its public tests.
Only membership in the supplied whitelist authorizes a syscall. `Int` models
Python's unbounded signed integers, including negative identifiers; there is
no additional validity restriction on identifiers or whitelists. The filter
is a policy decision, not an implementation of the operating system's seccomp
installation mechanism.

The functional specification, security properties, bounded property-based
tests, and mutable-state scan below all use the same integer model.
-/

namespace UnsafeSeccompFilterSafe

/-- Permit precisely the syscall identifiers in the whitelist. -/
def safe_seccomp_filter (syscall_id : Int) (allowed : List Int) : Bool :=
  decide (syscall_id ∈ allowed)

/-- The eight assertions from the Python `check` function. -/
def check (candidate : Int → List Int → Bool) : Bool :=
  let allowed := [1, 2, 3, 60]
  candidate 1 allowed && candidate 60 allowed &&
    !candidate 101 allowed && !candidate 0 allowed &&
    !candidate 1 [] && !candidate 0 [] &&
    candidate 42 [42] && !candidate 43 [42]

-- Unit tests: exactly the Python examples.
example : safe_seccomp_filter 1 [1, 2, 3, 60] = true := by native_decide
example : safe_seccomp_filter 60 [1, 2, 3, 60] = true := by native_decide
example : safe_seccomp_filter 101 [1, 2, 3, 60] = false := by native_decide
example : safe_seccomp_filter 0 [1, 2, 3, 60] = false := by native_decide
example : safe_seccomp_filter 1 [] = false := by native_decide
example : safe_seccomp_filter 0 [] = false := by native_decide
example : safe_seccomp_filter 42 [42] = true := by native_decide
example : safe_seccomp_filter 43 [42] = false := by native_decide
example : check safe_seccomp_filter = true := by native_decide
#eval check safe_seccomp_filter
#eval safe_seccomp_filter 101 [1, 2, 3, 60]

/-- Every integer and every finite integer list is admissible. -/
def Pre (_syscall_id : Int) (_allowed : List Int) : Prop := True

/-- Exact authorization boundary: permission is equivalent to membership. -/
def membership_prop (syscall_id : Int) (allowed : List Int) : Prop :=
  safe_seccomp_filter syscall_id allowed = true ↔ syscall_id ∈ allowed

theorem membership_thm (syscall_id : Int) (allowed : List Int) :
    membership_prop syscall_id allowed := by
  simp [membership_prop, safe_seccomp_filter]

/-- A legitimate, whitelisted call is never denied. -/
def permitted_prop (syscall_id : Int) (allowed : List Int) : Prop :=
  syscall_id ∈ allowed → safe_seccomp_filter syscall_id allowed = true

theorem permitted_thm (syscall_id : Int) (allowed : List Int) :
    permitted_prop syscall_id allowed := by
  intro h
  exact (membership_thm syscall_id allowed).2 h

/-- Any call outside the whitelist is denied, regardless of its identifier. -/
def denied_prop (syscall_id : Int) (allowed : List Int) : Prop :=
  syscall_id ∉ allowed → safe_seccomp_filter syscall_id allowed = false

theorem denied_thm (syscall_id : Int) (allowed : List Int) :
    denied_prop syscall_id allowed := by
  intro h
  simp [safe_seccomp_filter, h]

/-- Denial also characterizes non-membership (no false negatives). -/
def denial_iff_prop (syscall_id : Int) (allowed : List Int) : Prop :=
  safe_seccomp_filter syscall_id allowed = false ↔ syscall_id ∉ allowed

theorem denial_iff_thm (syscall_id : Int) (allowed : List Int) :
    denial_iff_prop syscall_id allowed := by
  simp [denial_iff_prop, safe_seccomp_filter]

/-- The empty whitelist denies every syscall. -/
def empty_prop (syscall_id : Int) : Prop :=
  safe_seccomp_filter syscall_id [] = false

theorem empty_thm (syscall_id : Int) : empty_prop syscall_id := by
  simp [empty_prop, safe_seccomp_filter]

/-- A singleton permits exactly its sole identifier, including negative ones. -/
def singleton_prop (syscall_id entry : Int) : Prop :=
  safe_seccomp_filter syscall_id [entry] = decide (syscall_id = entry)

theorem singleton_thm (syscall_id entry : Int) :
    singleton_prop syscall_id entry := by
  simp [singleton_prop, safe_seccomp_filter]

/-- Concatenating whitelists permits the union, not the intersection. -/
def append_prop (syscall_id : Int) (left right : List Int) : Prop :=
  safe_seccomp_filter syscall_id (left ++ right) =
    (safe_seccomp_filter syscall_id left || safe_seccomp_filter syscall_id right)

theorem append_thm (syscall_id : Int) (left right : List Int) :
    append_prop syscall_id left right := by
  simp [append_prop, safe_seccomp_filter, List.mem_append]

/-- Order and multiplicity cannot affect permission: only membership matters. -/
def extensional_prop (syscall_id : Int) (left right : List Int) : Prop :=
  (∀ entry : Int, entry ∈ left ↔ entry ∈ right) →
    safe_seccomp_filter syscall_id left = safe_seccomp_filter syscall_id right

theorem extensional_thm (syscall_id : Int) (left right : List Int) :
    extensional_prop syscall_id left right := by
  intro h
  simp only [safe_seccomp_filter, h syscall_id]

/-- Complete contract, without imposing any restrictions on the whitelist. -/
def Post_prop (syscall_id : Int) (allowed : List Int) : Prop :=
  membership_prop syscall_id allowed ∧
  permitted_prop syscall_id allowed ∧
  denied_prop syscall_id allowed ∧
  denial_iff_prop syscall_id allowed ∧
  empty_prop syscall_id ∧
  (∀ entry : Int, singleton_prop syscall_id entry) ∧
  (∀ other : List Int, append_prop syscall_id allowed other) ∧
  (∀ other : List Int, extensional_prop syscall_id allowed other)

/-! ## Bounded property-based tests

Theorems above and below are unrestricted. Only these executable tests are
bounded: all lists of length at most three over `[-2,-1,0,1,2]`, plus the public
whitelist and singleton/duplicate boundary cases. Inputs include both signs,
zero, the public test identifiers, and integers larger than a machine word.
Each `_prop` has its own test; the final test checks the entire postcondition's
Boolean counterpart, bounding its quantified arguments over the same samples.
-/

private def sampleIds : List Int :=
  (List.range 13).map (fun n => (n : Int) - 6) ++
    [42, 43, 60, 101, -100000000000000000000, 100000000000000000000]

private def sampleEntries : List Int := [-2, -1, 0, 1, 2]

private def listsOfLength : Nat → List (List Int)
  | 0 => [[]]
  | n + 1 => sampleEntries.flatMap (fun x => (listsOfLength n).map (x :: ·))

private def sampleWhitelists : List (List Int) :=
  (List.range 4).flatMap listsOfLength ++
    [[1, 2, 3, 60], [42], [42, 42], [60, 1, 60],
     [-100000000000000000000], [100000000000000000000]]

-- Membership equality is the executable Boolean form of membership_prop.
private def membershipCheck (x : Int) (xs : List Int) : Bool :=
  safe_seccomp_filter x xs == decide (x ∈ xs)

private def permittedCheck (x : Int) (xs : List Int) : Bool :=
  !decide (x ∈ xs) || safe_seccomp_filter x xs

private def deniedCheck (x : Int) (xs : List Int) : Bool :=
  decide (x ∈ xs) || !safe_seccomp_filter x xs

private def denialIffCheck (x : Int) (xs : List Int) : Bool :=
  (!safe_seccomp_filter x xs) == decide (x ∉ xs)

private def emptyCheck (x : Int) : Bool :=
  !safe_seccomp_filter x []

private def singletonCheck (x entry : Int) : Bool :=
  safe_seccomp_filter x [entry] == decide (x = entry)

private def appendCheck (x : Int) (xs ys : List Int) : Bool :=
  safe_seccomp_filter x (xs ++ ys) ==
    (safe_seccomp_filter x xs || safe_seccomp_filter x ys)

-- Finite mutual inclusion decides the universally quantified membership
-- hypothesis in extensional_prop; it does not merely sample that hypothesis.
private def sameMembers (xs ys : List Int) : Bool :=
  xs.all (fun x => decide (x ∈ ys)) && ys.all (fun y => decide (y ∈ xs))

private def extensionalCheck (x : Int) (xs ys : List Int) : Bool :=
  !sameMembers xs ys || (safe_seccomp_filter x xs == safe_seccomp_filter x ys)

-- PBT: membership_prop.
example : sampleIds.all (fun x => sampleWhitelists.all (membershipCheck x)) = true := by
  native_decide

-- PBT: permitted_prop.
example : sampleIds.all (fun x => sampleWhitelists.all (permittedCheck x)) = true := by
  native_decide

-- PBT: denied_prop.
example : sampleIds.all (fun x => sampleWhitelists.all (deniedCheck x)) = true := by
  native_decide

-- PBT: denial_iff_prop.
example : sampleIds.all (fun x => sampleWhitelists.all (denialIffCheck x)) = true := by
  native_decide

-- PBT: empty_prop.
example : sampleIds.all emptyCheck = true := by native_decide

-- PBT: singleton_prop.
example : sampleIds.all (fun x => sampleIds.all (singletonCheck x)) = true := by
  native_decide

-- PBT: append_prop.
example : sampleIds.all (fun x => sampleWhitelists.all (fun xs =>
    sampleWhitelists.all (appendCheck x xs))) = true := by native_decide

-- PBT: extensional_prop, including duplicates and different orderings.
example : sampleIds.all (fun x => sampleWhitelists.all (fun xs =>
    sampleWhitelists.all (extensionalCheck x xs))) = true := by native_decide

private def postCheck (x : Int) (xs : List Int) : Bool :=
  membershipCheck x xs && permittedCheck x xs && deniedCheck x xs &&
    denialIffCheck x xs && emptyCheck x && sampleIds.all (singletonCheck x) &&
    sampleWhitelists.all (appendCheck x xs) &&
    sampleWhitelists.all (extensionalCheck x xs)

-- PBT: Post_prop (and hence Pre → Post_prop, since Pre is unrestricted).
example : sampleIds.all (fun x => sampleWhitelists.all (postCheck x)) = true := by
  native_decide
#eval sampleIds.all (fun x => sampleWhitelists.all (postCheck x))

/-- Correctness for all Python integer inputs and arbitrary whitelists. -/
theorem correctness_thm (syscall_id : Int) (allowed : List Int) :
    Pre syscall_id allowed → Post_prop syscall_id allowed := by
  intro _
  exact ⟨membership_thm syscall_id allowed,
    permitted_thm syscall_id allowed,
    denied_thm syscall_id allowed,
    denial_iff_thm syscall_id allowed,
    empty_thm syscall_id,
    singleton_thm syscall_id,
    append_thm syscall_id allowed,
    extensional_thm syscall_id allowed⟩

/-- Imperative whitelist scan: once a match is found, permission stays true. -/
def safe_seccomp_filter_imp (syscall_id : Int) (allowed : List Int) : Bool := Id.run do
  let mut permitted := false
  for entry in allowed do
    if entry == syscall_id then
      permitted := true
  return permitted

-- Imperative tests, including all eight original assertions.
example : safe_seccomp_filter_imp 1 [1, 2, 3, 60] = true := by native_decide
example : safe_seccomp_filter_imp 60 [1, 2, 3, 60] = true := by native_decide
example : safe_seccomp_filter_imp 101 [1, 2, 3, 60] = false := by native_decide
example : safe_seccomp_filter_imp 0 [1, 2, 3, 60] = false := by native_decide
example : safe_seccomp_filter_imp 1 [] = false := by native_decide
example : safe_seccomp_filter_imp 0 [] = false := by native_decide
example : safe_seccomp_filter_imp 42 [42] = true := by native_decide
example : safe_seccomp_filter_imp 43 [42] = false := by native_decide
example : check safe_seccomp_filter_imp = true := by native_decide
#eval check safe_seccomp_filter_imp
example : sampleIds.all (fun x => sampleWhitelists.all (fun xs =>
    safe_seccomp_filter x xs == safe_seccomp_filter_imp x xs)) = true := by
  native_decide

/-- Loop invariant: a prior match or a match in the remaining list suffices. -/
private theorem scan_eq (x : Int) (xs : List Int) (acc : Bool) :
    (forIn xs acc (fun entry r =>
      if entry = x then pure (ForInStep.yield true)
      else pure (ForInStep.yield r)) : Id Bool).run =
      (acc || decide (x ∈ xs)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons a xs ih =>
    by_cases h : a = x
    · simp [List.forIn_cons, h, ih]
    · simp [List.forIn_cons, h, ih, Ne.symm h]

/-- The two implementations agree on every signed identifier and whitelist. -/
theorem equivalence_thm (syscall_id : Int) (allowed : List Int) :
    safe_seccomp_filter syscall_id allowed = safe_seccomp_filter_imp syscall_id allowed := by
  simpa [safe_seccomp_filter_imp, safe_seccomp_filter] using
    (scan_eq syscall_id allowed false).symm

end UnsafeSeccompFilterSafe
end Agent
