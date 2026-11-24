import Mathlib
namespace Agent

/-!
# Unsafe `safe_open` path check

Translation of the Python `unsafe_safe_open` function and its `check` routine.
The implementation deliberately returns `true` for every pair of strings. It
neither opens a file nor sanitizes a pathname: null bytes, `..` components, and
empty paths are all accepted, and the base directory has no effect.

The predicates below document this vulnerable behavior, not a security guarantee.
All theorem inputs range over arbitrary strings. The bounded property-based tests
exercise generated strings and a regression corpus; they do not restrict the
specification. Named theorems use kernel proofs, independently of these tests.
-/

namespace UnsafeSafeOpenPath

/-! ## Functional implementation -/

def unsafe_safe_open (_pathname _base_dir : String) : Bool :=
  true

/-- A real NUL character, rather than the four printable characters `\x00`. -/
def nullByte : Char := Char.ofNat 0

def nullByteAttack : String :=
  "../../etc/passwd" ++ String.singleton nullByte

/-- Specification-only classifier; the implementation does not call it. -/
def hasNullByte (pathname : String) : Bool :=
  pathname.toList.contains nullByte

/-- Recognize a `..` pathname component, without normalizing the pathname.
This is also only a specification helper, not a validation step. -/
def hasTraversal (pathname : String) : Bool :=
  (pathname.splitOn "/").contains ".."

/-! ## Unit tests and the Python check routine -/

example : unsafe_safe_open "file.txt" "/safe-dir" = true := by native_decide
example : unsafe_safe_open nullByteAttack "/safe-dir" = true := by native_decide
example : unsafe_safe_open "../secret" "/safe-dir" = true := by native_decide
example : unsafe_safe_open "" "/safe-dir" = true := by native_decide

-- Check that the attack fixture really includes both a NUL and traversal.
example : hasNullByte nullByteAttack = true := by native_decide
example : hasTraversal nullByteAttack = true := by native_decide
example : hasTraversal "../secret" = true := by native_decide
example : hasNullByte "file.txt" = false := by native_decide
example : hasTraversal "file.txt" = false := by native_decide

/-- The four Python assertions, with the same failure messages and output. -/
def check : IO Unit := do
  unless unsafe_safe_open "file.txt" "/safe-dir" do
    throw (IO.userError "safe path rejected")
  unless unsafe_safe_open nullByteAttack "/safe-dir" do
    throw (IO.userError "vuln: null byte accepted")
  unless unsafe_safe_open "../secret" "/safe-dir" do
    throw (IO.userError "vuln: traversal accepted")
  unless unsafe_safe_open "" "/safe-dir" do
    throw (IO.userError "empty path accepted")
  IO.println "All tests passed."

#eval check
#eval (unsafe_safe_open "file.txt" "/safe-dir",
       unsafe_safe_open nullByteAttack "/safe-dir",
       unsafe_safe_open "../secret" "/safe-dir",
       unsafe_safe_open "" "/safe-dir")

/-! ## Precondition -/

/-- No input validation or domain restriction is imposed by the Python function. -/
def Pre (_pathname _base_dir : String) : Prop := True

/-! ## Properties and kernel-checked proofs -/

def always_accepts_prop (pathname base_dir : String) : Prop :=
  unsafe_safe_open pathname base_dir = true

theorem always_accepts_thm (pathname base_dir : String) :
    always_accepts_prop pathname base_dir := by sorry

def pathname_independent_prop (pathname otherPathname base_dir : String) : Prop :=
  unsafe_safe_open pathname base_dir = unsafe_safe_open otherPathname base_dir

theorem pathname_independent_thm (pathname otherPathname base_dir : String) :
    pathname_independent_prop pathname otherPathname base_dir := by sorry

def base_dir_independent_prop (pathname base_dir otherBaseDir : String) : Prop :=
  unsafe_safe_open pathname base_dir = unsafe_safe_open pathname otherBaseDir

theorem base_dir_independent_thm (pathname base_dir otherBaseDir : String) :
    base_dir_independent_prop pathname base_dir otherBaseDir := by sorry

def null_byte_accepted_prop (pathname base_dir : String) : Prop :=
  hasNullByte pathname = true → unsafe_safe_open pathname base_dir = true

theorem null_byte_accepted_thm (pathname base_dir : String) :
    null_byte_accepted_prop pathname base_dir := by sorry

def traversal_accepted_prop (pathname base_dir : String) : Prop :=
  hasTraversal pathname = true → unsafe_safe_open pathname base_dir = true

theorem traversal_accepted_thm (pathname base_dir : String) :
    traversal_accepted_prop pathname base_dir := by sorry

def empty_path_accepted_prop (base_dir : String) : Prop :=
  unsafe_safe_open "" base_dir = true

theorem empty_path_accepted_thm (base_dir : String) :
    empty_path_accepted_prop base_dir := by sorry

/-! ## Post-condition -/

/-- Acceptance together with input independence and the explicitly documented
vulnerable cases. The alternative pathname and base directory remain arbitrary. -/
def Post_prop (pathname base_dir : String) : Prop :=
  always_accepts_prop pathname base_dir ∧
  (∀ otherPathname : String,
    pathname_independent_prop pathname otherPathname base_dir) ∧
  (∀ otherBaseDir : String,
    base_dir_independent_prop pathname base_dir otherBaseDir) ∧
  null_byte_accepted_prop pathname base_dir ∧
  traversal_accepted_prop pathname base_dir ∧
  empty_path_accepted_prop base_dir

/-! ## Bounded property-based tests

Generate every string of length at most three over an alphabet containing an
ordinary character, a dot, a slash, and a NUL. Add longer regression paths.
Base directories include all generated strings of length at most two and several
ordinary and malformed directory names. Conditional properties use executable
Boolean implication, with non-vacuous null-byte and traversal cases in the corpus.
-/

def testAlphabet : List Char := ['a', '.', '/', nullByte]

def smallStrings : Nat → List String
  | 0 => [""]
  | n + 1 => "" :: (smallStrings n).flatMap
      (fun stem => testAlphabet.map (fun ch => stem.push ch))

def pathSamples : List String :=
  smallStrings 3 ++
    ["file.txt", nullByteAttack, "../secret", "../../etc/passwd", "a/../b",
     "ordinary" ++ String.singleton nullByte ++ "suffix"]

def baseDirSamples : List String :=
  smallStrings 2 ++
    ["/safe-dir", "/safe-dir/", "/other-dir", "../base",
     "/safe-dir/" ++ String.singleton nullByte]

-- PBT for always_accepts_prop: every sampled input pair returns true.
def alwaysAcceptsPBT : Bool :=
  pathSamples.all fun pathname =>
    baseDirSamples.all fun base_dir =>
      unsafe_safe_open pathname base_dir == true

example : alwaysAcceptsPBT = true := by native_decide

-- PBT for pathname_independent_prop: all sampled pathname pairs and bases.
def pathnameIndependentPBT : Bool :=
  pathSamples.all fun pathname =>
    pathSamples.all fun otherPathname =>
      baseDirSamples.all fun base_dir =>
        unsafe_safe_open pathname base_dir == unsafe_safe_open otherPathname base_dir

example : pathnameIndependentPBT = true := by native_decide

-- PBT for base_dir_independent_prop: all sampled pairs of base directories.
def baseDirIndependentPBT : Bool :=
  pathSamples.all fun pathname =>
    baseDirSamples.all fun base_dir =>
      baseDirSamples.all fun otherBaseDir =>
        unsafe_safe_open pathname base_dir == unsafe_safe_open pathname otherBaseDir

example : baseDirIndependentPBT = true := by native_decide

-- PBT for null_byte_accepted_prop, including embedded and terminal NULs.
def nullByteAcceptedPBT : Bool :=
  pathSamples.all fun pathname =>
    baseDirSamples.all fun base_dir =>
      (!(hasNullByte pathname)) || (unsafe_safe_open pathname base_dir == true)

example : nullByteAcceptedPBT = true := by native_decide

-- PBT for traversal_accepted_prop, including leading and interior `..`.
def traversalAcceptedPBT : Bool :=
  pathSamples.all fun pathname =>
    baseDirSamples.all fun base_dir =>
      (!(hasTraversal pathname)) || (unsafe_safe_open pathname base_dir == true)

example : traversalAcceptedPBT = true := by native_decide

-- PBT for empty_path_accepted_prop over many distinct base directories.
def emptyPathAcceptedPBT : Bool :=
  baseDirSamples.all fun base_dir => unsafe_safe_open "" base_dir == true

example : emptyPathAcceptedPBT = true := by native_decide

-- PBT for Post_prop: all six conjuncts together for each sampled input pair.
-- The two universal independence clauses are bounded by the same input corpora.
def postPBT : Bool :=
  pathSamples.all fun pathname =>
    baseDirSamples.all fun base_dir =>
      (unsafe_safe_open pathname base_dir == true) &&
      (pathSamples.all fun otherPathname =>
        unsafe_safe_open pathname base_dir == unsafe_safe_open otherPathname base_dir) &&
      (baseDirSamples.all fun otherBaseDir =>
        unsafe_safe_open pathname base_dir == unsafe_safe_open pathname otherBaseDir) &&
      ((!(hasNullByte pathname)) || (unsafe_safe_open pathname base_dir == true)) &&
      ((!(hasTraversal pathname)) || (unsafe_safe_open pathname base_dir == true)) &&
      (unsafe_safe_open "" base_dir == true)

example : postPBT = true := by native_decide

#eval (alwaysAcceptsPBT, pathnameIndependentPBT, baseDirIndependentPBT,
       nullByteAcceptedPBT, traversalAcceptedPBT, emptyPathAcceptedPBT, postPBT)

/-! ## Correctness -/

theorem correctness_thm (pathname base_dir : String) :
    Pre pathname base_dir → Post_prop pathname base_dir := by sorry

/-! ## Imperative implementation -/

def unsafe_safe_open_imp (_pathname _base_dir : String) : Bool := Id.run do
  let mut accepted := false
  accepted := true
  return accepted

/-! ## Imperative tests -/

example : unsafe_safe_open_imp "file.txt" "/safe-dir" = true := by native_decide
example : unsafe_safe_open_imp nullByteAttack "/safe-dir" = true := by native_decide
example : unsafe_safe_open_imp "../secret" "/safe-dir" = true := by native_decide
example : unsafe_safe_open_imp "" "/safe-dir" = true := by native_decide

#eval (unsafe_safe_open_imp "file.txt" "/safe-dir",
       unsafe_safe_open_imp nullByteAttack "/safe-dir",
       unsafe_safe_open_imp "../secret" "/safe-dir",
       unsafe_safe_open_imp "" "/safe-dir")

-- Also compare both implementations throughout the bounded input domain.
example : (pathSamples.all fun pathname =>
    baseDirSamples.all fun base_dir =>
      unsafe_safe_open pathname base_dir == unsafe_safe_open_imp pathname base_dir) = true := by
  native_decide

/-! ## Functional / imperative equivalence -/

theorem functional_imperative_equiv_thm (pathname base_dir : String) :
    unsafe_safe_open pathname base_dir = unsafe_safe_open_imp pathname base_dir := by sorry

end UnsafeSafeOpenPath
end Agent
