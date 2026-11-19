import Mathlib
namespace Agent

/-!
# Unsafe prefix-leaking comparison

Translation of the Python `unsafe_leaking_compare` timing oracle. Python's
unbounded integers are modelled by `Int`; the returned count is a `Nat`.
The traversal stops at the first unequal pair or the end of either input.
There is no byte-range or equal-length restriction. Besides the supplied
examples, the specifications characterize the *longest* common prefix and
make explicit the information exposed about the first mismatch.
-/

namespace UnsafeLeakingCompare

/-- Functional form of the early-exit loop over `zip(secret, guess)`. -/
def unsafe_leaking_compare : List Int → List Int → Nat
  | s :: ss, g :: gs =>
      if s = g then unsafe_leaking_compare ss gs + 1 else 0
  | _, _ => 0

-- The eight checks in the Python source.
example : unsafe_leaking_compare [1, 2, 3] [1, 2, 3] = 3 := by native_decide
example : unsafe_leaking_compare [1, 2, 3] [1, 2, 9] = 2 := by native_decide
example : unsafe_leaking_compare [1, 2, 3] [9, 2, 3] = 0 := by native_decide
example : unsafe_leaking_compare [10, 20, 30] [10, 20, 99] = 2 := by native_decide
example : unsafe_leaking_compare [10, 20, 30] [10, 99, 30] = 1 := by native_decide
example : unsafe_leaking_compare [10, 20, 30] [99, 20, 30] = 0 := by native_decide
example : unsafe_leaking_compare [] [] = 0 := by native_decide
example : unsafe_leaking_compare [1] [2] = 0 := by native_decide
-- Zip truncation, negative integers, and ignoring equal bytes after a mismatch.
example : unsafe_leaking_compare [-7, 256] [-7] = 1 := by native_decide
example : unsafe_leaking_compare [] [1] = 0 := by native_decide
example : unsafe_leaking_compare [1] [] = 0 := by native_decide
example : unsafe_leaking_compare [1, 2, 3] [1, 9, 3, 4] = 1 := by native_decide
#eval unsafe_leaking_compare [10, 20, 30] [10, 20, 99]
#eval unsafe_leaking_compare [-7] [-7, 256]

/-- Python imposes no additional restrictions on its two integer lists. -/
def Pre (_secret _guess : List Int) : Prop := True

/-- A zip traversal cannot count beyond either input. -/
def bounds_prop (secret guess : List Int) : Prop :=
  unsafe_leaking_compare secret guess ≤ min secret.length guess.length

theorem bounds_thm (secret guess : List Int) : bounds_prop secret guess := by
  unfold bounds_prop
  induction secret generalizing guess with
  | nil => simp [unsafe_leaking_compare]
  | cons s ss ih =>
      cases guess with
      | nil => simp [unsafe_leaking_compare]
      | cons g gs =>
          have h := ih gs
          by_cases heq : s = g
          · simp [unsafe_leaking_compare, heq] at *
            omega
          · simp [unsafe_leaking_compare, heq]

/-- All reported matching entries really are equal. -/
def matchingPrefix_prop (secret guess : List Int) : Prop :=
  secret.take (unsafe_leaking_compare secret guess) =
    guess.take (unsafe_leaking_compare secret guess)

theorem matchingPrefix_thm (secret guess : List Int) :
    matchingPrefix_prop secret guess := by
  unfold matchingPrefix_prop
  induction secret generalizing guess with
  | nil => simp [unsafe_leaking_compare]
  | cons s ss ih =>
      cases guess with
      | nil => simp [unsafe_leaking_compare]
      | cons g gs =>
          by_cases heq : s = g
          · subst g
            simp [unsafe_leaking_compare, List.take_succ_cons, ih]
          · simp [unsafe_leaking_compare, heq]

/-- No longer prefix, contained in both inputs, can be equal. -/
def maximalPrefix_prop (secret guess : List Int) : Prop :=
  ∀ k : Nat, k ≤ secret.length → k ≤ guess.length →
    secret.take k = guess.take k → k ≤ unsafe_leaking_compare secret guess

theorem maximalPrefix_thm (secret guess : List Int) :
    maximalPrefix_prop secret guess := by
  unfold maximalPrefix_prop
  induction secret generalizing guess with
  | nil => intro k hs hg hp; simpa [unsafe_leaking_compare] using hs
  | cons s ss ih =>
      cases guess with
      | nil => intro k hs hg hp; simpa [unsafe_leaking_compare] using hg
      | cons g gs =>
          intro k hs hg hp
          cases k with
          | zero => exact Nat.zero_le _
          | succ k =>
              simp only [List.take_succ_cons, List.cons.injEq] at hp
              obtain ⟨heq, hp⟩ := hp
              subst g
              have h := ih gs k (by simpa using hs) (by simpa using hg) hp
              simpa [unsafe_leaking_compare] using Nat.succ_le_succ h

/-- On equal lists every element matches. -/
def identical_prop (secret : List Int) : Prop :=
  unsafe_leaking_compare secret secret = secret.length

theorem identical_thm (secret : List Int) : identical_prop secret := by
  unfold identical_prop
  induction secret with
  | nil => rfl
  | cons s ss ih => simp [unsafe_leaking_compare, ih]

/-- The leaked count is symmetric, even for unequal input lengths. -/
def symmetry_prop (secret guess : List Int) : Prop :=
  unsafe_leaking_compare secret guess = unsafe_leaking_compare guess secret

theorem symmetry_thm (secret guess : List Int) : symmetry_prop secret guess := by
  unfold symmetry_prop
  induction secret generalizing guess with
  | nil => cases guess <;> rfl
  | cons s ss ih =>
      cases guess with
      | nil => rfl
      | cons g gs =>
          by_cases heq : s = g
          · subst g; simp [unsafe_leaking_compare, ih]
          · simp [unsafe_leaking_compare, heq, Ne.symm heq]

/-- Prepending an equal prefix increases the leak by exactly its length. -/
def commonPrefix_prop (shared secret guess : List Int) : Prop :=
  unsafe_leaking_compare (shared ++ secret) (shared ++ guess) =
    shared.length + unsafe_leaking_compare secret guess

theorem commonPrefix_thm (shared secret guess : List Int) :
    commonPrefix_prop shared secret guess := by
  unfold commonPrefix_prop
  induction shared with
  | nil => simp
  | cons x xs ih => simp [unsafe_leaking_compare, ih, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]

/-- With a known prefix, a wrong next byte reveals its exact position;
    neither suffix can affect the answer after that mismatch. -/
def mismatchLeak_prop (shared : List Int) (s g : Int)
    (secretTail guessTail : List Int) : Prop :=
  s ≠ g → unsafe_leaking_compare (shared ++ s :: secretTail)
    (shared ++ g :: guessTail) = shared.length

theorem mismatchLeak_thm (shared : List Int) (s g : Int)
    (secretTail guessTail : List Int) :
    mismatchLeak_prop shared s g secretTail guessTail := by
  intro h
  have hp := commonPrefix_thm shared (s :: secretTail) (g :: guessTail)
  simpa [commonPrefix_prop, unsafe_leaking_compare, h] using hp

/-- If both lists still have an entry at the returned index, they differ.
    Thus an equal suffix after the first mismatch is never counted. -/
def firstMismatch_prop (secret guess : List Int) : Prop :=
  let n := unsafe_leaking_compare secret guess
  n < secret.length → n < guess.length → secret[n]? ≠ guess[n]?

theorem firstMismatch_thm (secret guess : List Int) :
    firstMismatch_prop secret guess := by
  unfold firstMismatch_prop
  induction secret generalizing guess with
  | nil => simp [unsafe_leaking_compare]
  | cons s ss ih =>
      cases guess with
      | nil => simp [unsafe_leaking_compare]
      | cons g gs =>
          by_cases heq : s = g
          · subst g
            simpa [unsafe_leaking_compare] using ih gs
          · simp [unsafe_leaking_compare, heq]

/-- Independent executable specification: the initial equal pairs of zip. -/
def zipSpec_prop (secret guess : List Int) : Prop :=
  unsafe_leaking_compare secret guess =
    ((secret.zip guess).takeWhile (fun p => p.1 == p.2)).length

theorem zipSpec_thm (secret guess : List Int) : zipSpec_prop secret guess := by
  unfold zipSpec_prop
  induction secret generalizing guess with
  | nil => simp [unsafe_leaking_compare]
  | cons s ss ih =>
      cases guess with
      | nil => simp [unsafe_leaking_compare]
      | cons g gs =>
          by_cases heq : s = g <;> simp [unsafe_leaking_compare, heq, ih]

/-- A conjunction specifying the exact longest common-prefix length,
    the stopping condition, and the zip-based semantics. -/
def Post_prop (secret guess : List Int) : Prop :=
  bounds_prop secret guess ∧ matchingPrefix_prop secret guess ∧
    maximalPrefix_prop secret guess ∧ firstMismatch_prop secret guess ∧
    zipSpec_prop secret guess

/-! ## Property-based tests

These are executable checks, not proofs of the universal theorems. The
bounded alphabet deliberately includes a negative integer. `smallLists n`
enumerates *all* lists of length at most n over this alphabet. In particular,
these tests include empty lists, unequal lengths, matching inputs, and
mismatches followed by equal entries. Random checks additionally exercise
unrestricted integer values and longer lists.
-/

def smallLists : Nat → List (List Int)
  | 0 => [[]]
  | n + 1 => [] :: ([-1, 0, 1] : List Int).flatMap
      (fun x => (smallLists n).map (fun xs => x :: xs))

-- bounds_prop
example : ((smallLists 3).all fun s => (smallLists 3).all fun g =>
    decide (unsafe_leaking_compare s g ≤ min s.length g.length)) = true := by
  native_decide

-- matchingPrefix_prop
example : ((smallLists 3).all fun s => (smallLists 3).all fun g =>
    decide (s.take (unsafe_leaking_compare s g) =
      g.take (unsafe_leaking_compare s g))) = true := by
  native_decide

/-- Executable form of maximality. All admissible k occur in this range;
    larger k violate one of the two length premises of maximalPrefix_prop. -/
def maximalPrefixCheck (s g : List Int) : Bool :=
  (List.range (min s.length g.length + 1)).all fun k =>
    decide (s.take k = g.take k → k ≤ unsafe_leaking_compare s g)

-- maximalPrefix_prop
example : ((smallLists 3).all fun s => (smallLists 3).all fun g =>
    maximalPrefixCheck s g) = true := by native_decide

-- identical_prop
example : ((smallLists 4).all fun s =>
    decide (unsafe_leaking_compare s s = s.length)) = true := by native_decide

-- symmetry_prop
example : ((smallLists 3).all fun s => (smallLists 3).all fun g =>
    decide (unsafe_leaking_compare s g = unsafe_leaking_compare g s)) = true := by
  native_decide

-- commonPrefix_prop: generated shared prefixes force nontrivial matches.
example : ((smallLists 2).all fun shared => (smallLists 2).all fun s =>
    (smallLists 2).all fun g =>
    decide (unsafe_leaking_compare (shared ++ s) (shared ++ g) =
      shared.length + unsafe_leaking_compare s g)) = true := by native_decide

-- mismatchLeak_prop: every pair of next integers and every generated suffix.
example : ((smallLists 2).all fun shared => ([-1, 0, 1] : List Int).all fun s =>
    ([-1, 0, 1] : List Int).all fun g => (smallLists 2).all fun ss =>
    (smallLists 2).all fun gs =>
    decide (s ≠ g → unsafe_leaking_compare (shared ++ s :: ss)
      (shared ++ g :: gs) = shared.length)) = true := by native_decide

-- firstMismatch_prop
example : ((smallLists 3).all fun s => (smallLists 3).all fun g =>
    let n := unsafe_leaking_compare s g
    decide (n < s.length → n < g.length → s[n]? ≠ g[n]?)) = true := by
  native_decide

-- zipSpec_prop
example : ((smallLists 3).all fun s => (smallLists 3).all fun g =>
    decide (unsafe_leaking_compare s g =
      ((s.zip g).takeWhile (fun p => p.1 == p.2)).length)) = true := by
  native_decide

/-- Boolean conjunction of the five postcondition checks. -/
def postCheck (s g : List Int) : Bool :=
  let n := unsafe_leaking_compare s g
  decide (n ≤ min s.length g.length) &&
  decide (s.take n = g.take n) &&
  maximalPrefixCheck s g &&
  decide (n < s.length → n < g.length → s[n]? ≠ g[n]?) &&
  decide (n = ((s.zip g).takeWhile (fun p => p.1 == p.2)).length)

-- Post_prop
example : ((smallLists 3).all fun s => (smallLists 3).all fun g =>
    postCheck s g) = true := by native_decide
#eval ((smallLists 3).length, (smallLists 3).all fun s =>
  (smallLists 3).all fun g => postCheck s g)

#eval Plausible.Testable.check (∀ s g : List Int,
  unsafe_leaking_compare s g ≤ min s.length g.length)
#eval Plausible.Testable.check (∀ s : List Int,
  unsafe_leaking_compare s s = s.length)
#eval Plausible.Testable.check (∀ shared s g : List Int,
  unsafe_leaking_compare (shared ++ s) (shared ++ g) =
    shared.length + unsafe_leaking_compare s g)
#eval Plausible.Testable.check (∀ s g : List Int, postCheck s g = true)

/-- Total correctness for all inputs admitted by the Python signature. -/
theorem correctness_thm (secret guess : List Int) :
    Pre secret guess → Post_prop secret guess := by
  intro _
  exact ⟨bounds_thm secret guess, matchingPrefix_thm secret guess,
    maximalPrefix_thm secret guess, firstMismatch_thm secret guess,
    zipSpec_thm secret guess⟩

/-! ## Imperative implementation -/

/-- Literal mutable counter and early `break` over zipped pairs. -/
def unsafe_leaking_compare_imp (secret guess : List Int) : Nat := Id.run do
  let mut count := 0
  for (s, g) in secret.zip guess do
    if s = g then
      count := count + 1
    else
      break
  return count

-- The same source checks, now against the imperative implementation.
example : unsafe_leaking_compare_imp [1, 2, 3] [1, 2, 3] = 3 := by native_decide
example : unsafe_leaking_compare_imp [1, 2, 3] [1, 2, 9] = 2 := by native_decide
example : unsafe_leaking_compare_imp [1, 2, 3] [9, 2, 3] = 0 := by native_decide
example : unsafe_leaking_compare_imp [10, 20, 30] [10, 20, 99] = 2 := by native_decide
example : unsafe_leaking_compare_imp [10, 20, 30] [10, 99, 30] = 1 := by native_decide
example : unsafe_leaking_compare_imp [10, 20, 30] [99, 20, 30] = 0 := by native_decide
example : unsafe_leaking_compare_imp [] [] = 0 := by native_decide
example : unsafe_leaking_compare_imp [1] [2] = 0 := by native_decide
example : unsafe_leaking_compare_imp [-7, 256] [-7] = 1 := by native_decide
example : unsafe_leaking_compare_imp [] [1] = 0 := by native_decide
example : unsafe_leaking_compare_imp [1] [] = 0 := by native_decide
#eval unsafe_leaking_compare_imp [10, 20, 30] [10, 99, 30]

-- Bounded equivalence check is evidence separate from the proof below.
example : ((smallLists 3).all fun s => (smallLists 3).all fun g =>
    decide (unsafe_leaking_compare s g = unsafe_leaking_compare_imp s g)) = true := by
  native_decide

/-- The elaborated loop body: `done` really stops traversal. -/
private def loopStep (p : Int × Int) (count : Nat) : Id (ForInStep Nat) :=
  if p.1 = p.2 then .yield (count + 1) else .done count

/-- The accumulator invariant holds for every initial counter, not just zero. -/
private theorem loop_invariant (secret guess : List Int) (count : Nat) :
    (forIn (secret.zip guess) count loopStep : Id Nat) =
      count + unsafe_leaking_compare secret guess := by
  induction secret generalizing guess count with
  | nil => simp [unsafe_leaking_compare]; rfl
  | cons s ss ih =>
      cases guess with
      | nil => simp [unsafe_leaking_compare]; rfl
      | cons g gs =>
          by_cases heq : s = g
          · simpa [List.forIn_cons, loopStep, unsafe_leaking_compare, heq,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih gs (count + 1)
          · simp [List.forIn_cons, loopStep, unsafe_leaking_compare, heq]
            rfl

/-- The functional and genuinely imperative translations return the same
    leaked prefix length, for arbitrary lists and arbitrary integers. -/
theorem equivalence_thm (secret guess : List Int) :
    unsafe_leaking_compare secret guess = unsafe_leaking_compare_imp secret guess := by
  unfold unsafe_leaking_compare_imp
  change unsafe_leaking_compare secret guess =
    (forIn (secret.zip guess) 0 loopStep : Id Nat)
  simpa using (loop_invariant secret guess 0).symm

end UnsafeLeakingCompare
end Agent
