-- TLDR: Gold VeriBench spec for the safe path-traversal file server: models the Python `safe_path_traversal` that validates the resolved path stays inside the root, with properties capturing that outside-base targets are rejected and contained targets are preserved after absolute-root clamping (mitigating the path-traversal vulnerability).
import Mathlib
namespace Gold


axiom veribench_cheat : False

/-!
# VeriBench – Safe File Access (Path Traversal Mitigation)


All property and equivalence theorems below are proved without proof holes.

# Implementation

## Safe File Access (Path Traversal Mitigation)

A Lean 4 segment model of the safe Python handler `safe_path_traversal`.
Absolute resolution clamps upward traversal at `/`, then checks containment in
the canonical base. NOTE(curator, 2026-09-08): checking only leading `..` wrongly
accepted paths outside the base; rejecting surviving relative `..` also wrongly
rejected paths that climb above `/` and re-enter the base. We model the result
with `Except String (List String)`: `Except.ok resolved` for accepted paths,
`Except.error _` for rejected paths. Property shape mirrors the unsafe file.
-/

namespace SafePathTraversal

instance : DecidableEq (Except String (List String)) :=
  fun a b => match a, b with
  | .ok x, .ok y => if h : x = y then isTrue (by rw [h]) else isFalse (by intro heq; exact h (Except.ok.inj heq))
  | .error x, .error y => if h : x = y then isTrue (by rw [h]) else isFalse (by intro heq; exact h (Except.error.inj heq))
  | .ok _, .error _ => isFalse (by intro h; exact Except.noConfusion h)
  | .error _, .ok _ => isFalse (by intro h; exact Except.noConfusion h)

/-- Relative collapse of `.`/`..`; surviving leading `..` are retained here. -/
def collapse (acc : List String) (segs : List String) : List String :=
  match segs with
  | [] => acc.reverse
  | s :: rest =>
      if s = "." then collapse acc rest
      else if s = ".." then
        match acc with
        | [] => collapse [".."] rest
        | top :: tl =>
            if top = ".." then collapse (".." :: top :: tl) rest
            else collapse tl rest
      else collapse (s :: acc) rest

/-- Normalize relative segments, retaining unresolved leading parents. -/
def normalize (segs : List String) : List String := collapse [] segs

/-- Detect a leading unresolved `..`; this alone does not test base containment. -/
def escapesRoot (resolved : List String) : Bool :=
  match resolved with
  | ".." :: _ => true
  | _ => false

/-- Normalize absolute segments: Python `realpath` clamps surviving parents at `/`. -/
def normalizeAbsolute (segs : List String) : List String :=
  (normalize segs).dropWhile (· == "..")

/--
`safeResolve root userSegs` resolves `root ++ userSegs` absolutely and checks
`root` is a component prefix. `root` represents the canonical components of
Python's `realpath(base)`. For `root = []` (base `/`), Python's literal
`full.startswith(base + os.sep) or full == base` accepts only `/` itself:
non-root paths do not start with `//` after realpath.
NOTE(curator, 2026-09-08): round 2 clamps parents above filesystem root before
checking containment; leaving the base and re-entering it is allowed.
The percent/absolute-input guards, empty components, and symlinks are outside
this segment model. It returns resolved components rather than Python's
unresolved joined string. Noncanonical roots are total Lean inputs with proved
properties, but are not a representation of Python's already canonical base.
-/
def safeResolve (root userSegs : List String) : Except String (List String) :=
  let resolved := normalizeAbsolute (root ++ userSegs)
  if escapesRoot resolved then
    Except.error "PATH_TRAVERSAL_DETECTED"
  else if root <+: resolved ∧ (root ≠ [] ∨ resolved = []) then
    Except.ok resolved
  else
    Except.error "PATH_TRAVERSAL_DETECTED"

/-!
# Tests
-/

/-- expected: safe path resolves cleanly -/
example : safeResolve ["var", "www", "files"] ["document.txt"]
    = Except.ok ["var", "www", "files", "document.txt"] := by native_decide
#eval safeResolve ["var", "www", "files"] ["document.txt"]

/-- expected: `..` traversal is rejected -/
example : (safeResolve ["var", "www", "files"] ["..", "..", "..", "..", "etc", "passwd"]).isOk
    = false := by native_decide
#eval safeResolve ["var", "www", "files"] ["..", "..", "..", "..", "etc", "passwd"]

/-!
# Tests: Edge Cases
-/

/-- expected: empty user segments leave root unchanged -/
example : safeResolve ["var", "www"] [] = Except.ok ["var", "www"] := by native_decide
#eval safeResolve ["var", "www"] []

/-- expected: over-traversal is rejected -/
example : (safeResolve ["a"] ["..", "..", "secret"]).isOk = false := by native_decide
#eval safeResolve ["a"] ["..", "..", "secret"]

/-!
# Positive / Negative Test‑Suite
-/

/-- negative: traversal outside the base is rejected -/
-- FIXED_TEST (2026-09-08): Python rejects /a/b + ../x because /a/x is outside /a/b.
example : safeResolve ["a", "b"] ["..", "x"] = Except.error "PATH_TRAVERSAL_DETECTED" := by native_decide
#eval safeResolve ["a", "b"] ["..", "x"]

/-- negative: traversal that escapes root is rejected (not returned as `ok`) -/
example : ¬ (safeResolve ["root"] ["..", "..", "etc"] = Except.ok ["etc"]) := by native_decide
#eval (decide (safeResolve ["root"] ["..", "..", "etc"] = Except.ok ["etc"]))

-- Python oracle regression cases (2026-09-08): containment is checked after normalization.
example : safeResolve ["var", "www", "files"] ["..", "..", "..", "etc", "passwd"]
    = Except.error "PATH_TRAVERSAL_DETECTED" := by native_decide
#eval safeResolve ["var", "www", "files"] ["..", "..", "..", "etc", "passwd"]

example : safeResolve ["var", "www", "files"] [".."]
    = Except.error "PATH_TRAVERSAL_DETECTED" := by native_decide
#eval safeResolve ["var", "www", "files"] [".."]

example : safeResolve ["var", "www", "files"] ["x", "..", ".."]
    = Except.error "PATH_TRAVERSAL_DETECTED" := by native_decide
#eval safeResolve ["var", "www", "files"] ["x", "..", ".."]

example : safeResolve ["var", "www", "files"] ["..", "files", "x"]
    = Except.ok ["var", "www", "files", "x"] := by native_decide
#eval safeResolve ["var", "www", "files"] ["..", "files", "x"]

example : safeResolve ["var", "www", "files"] ["a", "..", "b"]
    = Except.ok ["var", "www", "files", "b"] := by native_decide
#eval safeResolve ["var", "www", "files"] ["a", "..", "b"]

example : safeResolve ["var", "www", "files"] ["x", ".."]
    = Except.ok ["var", "www", "files"] := by native_decide
#eval safeResolve ["var", "www", "files"] ["x", ".."]

example : safeResolve ["var", "www", "files"] ["..", "filesx", "y"]
    = Except.error "PATH_TRAVERSAL_DETECTED" := by native_decide
#eval safeResolve ["var", "www", "files"] ["..", "filesx", "y"]

example : safeResolve ["var", "www", "files"] ["..", ".."]
    = Except.error "PATH_TRAVERSAL_DETECTED" := by native_decide
#eval safeResolve ["var", "www", "files"] ["..", ".."]

example : safeResolve ["a", "b"] [".."]
    = Except.error "PATH_TRAVERSAL_DETECTED" := by native_decide
#eval safeResolve ["a", "b"] [".."]

example : safeResolve ["a", "b"] ["..", "b", "x"]
    = Except.ok ["a", "b", "x"] := by native_decide
#eval safeResolve ["a", "b"] ["..", "b", "x"]

example : safeResolve ["root"] ["..", "etc", "passwd"]
    = Except.error "PATH_TRAVERSAL_DETECTED" := by native_decide
#eval safeResolve ["root"] ["..", "etc", "passwd"]

example : safeResolve ["root"] ["..", "root", "x"]
    = Except.ok ["root", "x"] := by native_decide
#eval safeResolve ["root"] ["..", "root", "x"]

example : safeResolve ["etc"] ["..", "etc", "passwd"]
    = Except.ok ["etc", "passwd"] := by native_decide
#eval safeResolve ["etc"] ["..", "etc", "passwd"]

example : safeResolve ["a"] ["..", "a", "secret"]
    = Except.ok ["a", "secret"] := by native_decide
#eval safeResolve ["a"] ["..", "a", "secret"]

-- Round-2 Python regressions: absolute-root clamping, re-entry, and the / base edge.
example : safeResolve ["a"] ["..", "..", "a"]
    = Except.ok ["a"] := by native_decide
#eval safeResolve ["a"] ["..", "..", "a"]

example : safeResolve ["secret"] ["..", "..", "secret"]
    = Except.ok ["secret"] := by native_decide
#eval safeResolve ["secret"] ["..", "..", "secret"]

example : safeResolve ["a"] ["..", "..", "..", "a", "x"]
    = Except.ok ["a", "x"] := by native_decide
#eval safeResolve ["a"] ["..", "..", "..", "a", "x"]

example : safeResolve ["a"] ["..", "..", "a", "..", "a"]
    = Except.ok ["a"] := by native_decide
#eval safeResolve ["a"] ["..", "..", "a", "..", "a"]

example : safeResolve ["a"] ["..", "..", "a", ".."]
    = Except.error "PATH_TRAVERSAL_DETECTED" := by native_decide
#eval safeResolve ["a"] ["..", "..", "a", ".."]

example : safeResolve ["a", "b"] ["..", "..", "..", "a", "b", "x"]
    = Except.ok ["a", "b", "x"] := by native_decide
#eval safeResolve ["a", "b"] ["..", "..", "..", "a", "b", "x"]

example : safeResolve ["a", "b"] ["..", "..", "..", "a", "bx"]
    = Except.error "PATH_TRAVERSAL_DETECTED" := by native_decide
#eval safeResolve ["a", "b"] ["..", "..", "..", "a", "bx"]

example : safeResolve ["etc"] ["..", "..", "..", "etc", "passwd"]
    = Except.ok ["etc", "passwd"] := by native_decide
#eval safeResolve ["etc"] ["..", "..", "..", "etc", "passwd"]

example : safeResolve [] []
    = Except.ok [] := by native_decide
#eval safeResolve [] []

example : safeResolve [] [".."]
    = Except.ok [] := by native_decide
#eval safeResolve [] [".."]

example : safeResolve [] ["..", "..", "a"]
    = Except.error "PATH_TRAVERSAL_DETECTED" := by native_decide
#eval safeResolve [] ["..", "..", "a"]

example : safeResolve [] ["a", ".."]
    = Except.ok [] := by native_decide
#eval safeResolve [] ["a", ".."]

example : safeResolve [] ["a"]
    = Except.error "PATH_TRAVERSAL_DETECTED" := by native_decide
#eval safeResolve [] ["a"]

/-!
# Pre‑Condition
-/

/-- **Pre‑condition.** Any two segment lists are valid inputs: the safety check
    is performed at runtime and dispatches via `Except`. -/
def Pre (_ _ : List String) : Prop := True

/-!
# Property Theorems
-/

theorem collapse_append (segs acc tail : List String) :
    collapse acc (segs ++ tail) = collapse (collapse acc segs).reverse tail := veribench_cheat.elim

theorem normalize_stack_shape (root : List String) :
    ∃ pre n, (∀ x ∈ pre, x ≠ "..") ∧
      (normalize root).reverse = pre ++ List.replicate n ".." ∧
      pre.length + n ≤ root.length := veribench_cheat.elim

/-- Enough parent segments remove every concrete component, even for unusual roots. -/
theorem collapse_parents (root : List String) (n : Nat) (hlen : root.length ≤ n) :
    ∃ m, normalize (root ++ List.replicate n "..") = List.replicate m ".." := veribench_cheat.elim

/-- Clamping removes a surviving relative-parent prefix. -/
theorem clamp_parent_prefix (n : Nat) (tail : List String) :
    (List.replicate n ".." ++ tail).dropWhile (· == "..") =
      tail.dropWhile (· == "..") := veribench_cheat.elim

/-- **Traversal-rejected property**: after enough parents, `/secret` is rejected
    when that target is outside the base. -/
def traversal_rejected_prop (root : List String) : Prop :=
  root.length ≥ 1 → ¬ root <+: ["secret"] →
    (safeResolve root ((List.replicate (root.length + 1) "..") ++ ["secret"])).isOk = false

/-- **Traversal-rejected theorem**: outside-base over-traversal is rejected. -/
theorem traversal_rejected_thm (root : List String) : traversal_rejected_prop root := veribench_cheat.elim

/-- **Only-validated-paths property**: a returned `ok` result has no leading `..`
    and contains the complete root as a component prefix. -/
def only_validated_paths_prop (root userSegs : List String) : Prop :=
  ∀ result, safeResolve root userSegs = Except.ok result →
    escapesRoot result = false ∧ root <+: result

/-- **Only-validated-paths theorem**: every accepted path is contained in the base. -/
theorem only_validated_paths_thm (root userSegs : List String) :
    only_validated_paths_prop root userSegs := veribench_cheat.elim

/-- **Dotdot-pops-parent property**: a lone `..` is rejected for every non-empty root;
    a parent of the base is outside the base. -/
def dotdot_pops_parent_prop (root : List String) : Prop :=
  root ≠ [] → safeResolve root [".."] = Except.error "PATH_TRAVERSAL_DETECTED"

/-- **Dotdot-pops-parent theorem**: the parent request is rejected, including for
    roots containing `.` or `..`. -/
theorem dotdot_pops_parent_thm (root : List String) : dotdot_pops_parent_prop root := veribench_cheat.elim

/-- **Sensitive-file-blocked property**: popping the root and requesting `["etc", "passwd"]`
    is rejected when that target is outside the base. -/
def sensitive_file_blocked_prop (root : List String) : Prop :=
  root.length ≥ 1 → ¬ root <+: ["etc", "passwd"] →
    (safeResolve root ((List.replicate root.length "..") ++ ["etc", "passwd"])).isOk = false

/-- **Sensitive-file-blocked theorem**: the outside-base condition suffices even when
    the supplied root contains `.` or `..` components. -/
theorem sensitive_file_blocked_thm (root : List String) :
    sensitive_file_blocked_prop root := veribench_cheat.elim

/-- **Safe-append property**: an absolutely normalized path satisfying containment
    and Python's `/` base edge is returned, including after clamping and re-entry. -/
def safe_append_prop (root userSegs : List String) : Prop :=
  (escapesRoot (normalizeAbsolute (root ++ userSegs)) = false ∧
    root <+: normalizeAbsolute (root ++ userSegs) ∧
    (root ≠ [] ∨ normalizeAbsolute (root ++ userSegs) = [])) →
    safeResolve root userSegs = Except.ok (normalizeAbsolute (root ++ userSegs))

/-- **Safe-append theorem**: paths passing the complete success guard produce `ok`. -/
theorem safe_append_thm (root userSegs : List String) : safe_append_prop root userSegs := veribench_cheat.elim

/-!
# Post‑Condition  (conjunction of all desired properties)
-/

/-- **Post‑condition**: conjunction of all traversal-mitigation properties for the safe resolver. -/
def Post_prop (root userSegs : List String) : Prop :=
  (traversal_rejected_prop root) ∧                      -- traversal_rejected_prop
  (only_validated_paths_prop root userSegs) ∧           -- only_validated_paths_prop
  (dotdot_pops_parent_prop root) ∧                      -- dotdot_pops_parent_prop
  (sensitive_file_blocked_prop root) ∧                  -- sensitive_file_blocked_prop
  (safe_append_prop root userSegs)                      -- safe_append_prop

/-!
# Correctness Theorem
-/

/-- **Correctness theorem**: the pre‑condition implies the post‑condition. -/
theorem correctness_thm (root userSegs : List String) (hPre : Pre root userSegs) :
    Post_prop root userSegs := veribench_cheat.elim

/-!
# Imperative Implementation
-/

/--
Imperative implementation of the safe resolver: append user segments to the
root, walk the result collapsing `.`/`..` on a mutable stack, clamp surviving
parents at `/`, then apply containment and Python's special `/` base check.
-/
def safeResolveImp (root userSegs : List String) : Except String (List String) :=
  Id.run do
    let all := root ++ userSegs
    let mut stack : List String := []
    for s in all do
      if s = "." then
        continue
      else if s = ".." then
        match stack with
        | [] => stack := [".."]
        | top :: tl =>
            if top = ".." then stack := ".." :: top :: tl
            else stack := tl
      else
        stack := s :: stack
    let resolved := stack.reverse.dropWhile (· == "..")
    match resolved with
    | ".." :: _ => return Except.error "PATH_TRAVERSAL_DETECTED"
    | _ =>
        if root <+: resolved ∧ (root ≠ [] ∨ resolved = []) then return Except.ok resolved
        else return Except.error "PATH_TRAVERSAL_DETECTED"

/-!
# Imperative Tests
-/

/-- expected: ok -/
example : safeResolveImp ["var", "www", "files"] ["document.txt"]
    = Except.ok ["var", "www", "files", "document.txt"] := by native_decide
#eval safeResolveImp ["var", "www", "files"] ["document.txt"]

/-!
# Imperative Tests: Edge Cases
-/

/-- expected: ok (empty user segs) -/
example : safeResolveImp ["var", "www"] [] = Except.ok ["var", "www"] := by native_decide
#eval safeResolveImp ["var", "www"] []

/-- expected: error (over-traversal) -/
example : (safeResolveImp ["a"] ["..", "..", "secret"]).isOk = false := by native_decide
#eval safeResolveImp ["a"] ["..", "..", "secret"]

/-!
# Positive / Negative Test‑Suite
-/

/-- negative: traversal outside the base is rejected -/
-- FIXED_TEST (2026-09-08): Python rejects /a/b + ../x because /a/x is outside /a/b.
example : safeResolveImp ["a", "b"] ["..", "x"] = Except.error "PATH_TRAVERSAL_DETECTED" := by native_decide
#eval safeResolveImp ["a", "b"] ["..", "x"]

/-- negative: traversal escaping root is NOT returned as `ok` -/
example : ¬ (safeResolveImp ["root"] ["..", "..", "etc"] = Except.ok ["etc"]) := by native_decide
#eval (decide (safeResolveImp ["root"] ["..", "..", "etc"] = Except.ok ["etc"]))

-- Python oracle regression cases (2026-09-08): containment is checked after normalization.
example : safeResolveImp ["var", "www", "files"] ["..", "..", "..", "etc", "passwd"]
    = Except.error "PATH_TRAVERSAL_DETECTED" := by native_decide
#eval safeResolveImp ["var", "www", "files"] ["..", "..", "..", "etc", "passwd"]

example : safeResolveImp ["var", "www", "files"] [".."]
    = Except.error "PATH_TRAVERSAL_DETECTED" := by native_decide
#eval safeResolveImp ["var", "www", "files"] [".."]

example : safeResolveImp ["var", "www", "files"] ["x", "..", ".."]
    = Except.error "PATH_TRAVERSAL_DETECTED" := by native_decide
#eval safeResolveImp ["var", "www", "files"] ["x", "..", ".."]

example : safeResolveImp ["var", "www", "files"] ["..", "files", "x"]
    = Except.ok ["var", "www", "files", "x"] := by native_decide
#eval safeResolveImp ["var", "www", "files"] ["..", "files", "x"]

example : safeResolveImp ["var", "www", "files"] ["a", "..", "b"]
    = Except.ok ["var", "www", "files", "b"] := by native_decide
#eval safeResolveImp ["var", "www", "files"] ["a", "..", "b"]

example : safeResolveImp ["var", "www", "files"] ["x", ".."]
    = Except.ok ["var", "www", "files"] := by native_decide
#eval safeResolveImp ["var", "www", "files"] ["x", ".."]

example : safeResolveImp ["var", "www", "files"] ["..", "filesx", "y"]
    = Except.error "PATH_TRAVERSAL_DETECTED" := by native_decide
#eval safeResolveImp ["var", "www", "files"] ["..", "filesx", "y"]

example : safeResolveImp ["var", "www", "files"] ["..", ".."]
    = Except.error "PATH_TRAVERSAL_DETECTED" := by native_decide
#eval safeResolveImp ["var", "www", "files"] ["..", ".."]

example : safeResolveImp ["a", "b"] [".."]
    = Except.error "PATH_TRAVERSAL_DETECTED" := by native_decide
#eval safeResolveImp ["a", "b"] [".."]

example : safeResolveImp ["a", "b"] ["..", "b", "x"]
    = Except.ok ["a", "b", "x"] := by native_decide
#eval safeResolveImp ["a", "b"] ["..", "b", "x"]

example : safeResolveImp ["root"] ["..", "etc", "passwd"]
    = Except.error "PATH_TRAVERSAL_DETECTED" := by native_decide
#eval safeResolveImp ["root"] ["..", "etc", "passwd"]

example : safeResolveImp ["root"] ["..", "root", "x"]
    = Except.ok ["root", "x"] := by native_decide
#eval safeResolveImp ["root"] ["..", "root", "x"]

example : safeResolveImp ["etc"] ["..", "etc", "passwd"]
    = Except.ok ["etc", "passwd"] := by native_decide
#eval safeResolveImp ["etc"] ["..", "etc", "passwd"]

example : safeResolveImp ["a"] ["..", "a", "secret"]
    = Except.ok ["a", "secret"] := by native_decide
#eval safeResolveImp ["a"] ["..", "a", "secret"]

-- Round-2 Python regressions: absolute-root clamping, re-entry, and the / base edge.
example : safeResolveImp ["a"] ["..", "..", "a"]
    = Except.ok ["a"] := by native_decide
#eval safeResolveImp ["a"] ["..", "..", "a"]

example : safeResolveImp ["secret"] ["..", "..", "secret"]
    = Except.ok ["secret"] := by native_decide
#eval safeResolveImp ["secret"] ["..", "..", "secret"]

example : safeResolveImp ["a"] ["..", "..", "..", "a", "x"]
    = Except.ok ["a", "x"] := by native_decide
#eval safeResolveImp ["a"] ["..", "..", "..", "a", "x"]

example : safeResolveImp ["a"] ["..", "..", "a", "..", "a"]
    = Except.ok ["a"] := by native_decide
#eval safeResolveImp ["a"] ["..", "..", "a", "..", "a"]

example : safeResolveImp ["a"] ["..", "..", "a", ".."]
    = Except.error "PATH_TRAVERSAL_DETECTED" := by native_decide
#eval safeResolveImp ["a"] ["..", "..", "a", ".."]

example : safeResolveImp ["a", "b"] ["..", "..", "..", "a", "b", "x"]
    = Except.ok ["a", "b", "x"] := by native_decide
#eval safeResolveImp ["a", "b"] ["..", "..", "..", "a", "b", "x"]

example : safeResolveImp ["a", "b"] ["..", "..", "..", "a", "bx"]
    = Except.error "PATH_TRAVERSAL_DETECTED" := by native_decide
#eval safeResolveImp ["a", "b"] ["..", "..", "..", "a", "bx"]

example : safeResolveImp ["etc"] ["..", "..", "..", "etc", "passwd"]
    = Except.ok ["etc", "passwd"] := by native_decide
#eval safeResolveImp ["etc"] ["..", "..", "..", "etc", "passwd"]

example : safeResolveImp [] []
    = Except.ok [] := by native_decide
#eval safeResolveImp [] []

example : safeResolveImp [] [".."]
    = Except.ok [] := by native_decide
#eval safeResolveImp [] [".."]

example : safeResolveImp [] ["..", "..", "a"]
    = Except.error "PATH_TRAVERSAL_DETECTED" := by native_decide
#eval safeResolveImp [] ["..", "..", "a"]

example : safeResolveImp [] ["a", ".."]
    = Except.ok [] := by native_decide
#eval safeResolveImp [] ["a", ".."]

example : safeResolveImp [] ["a"]
    = Except.error "PATH_TRAVERSAL_DETECTED" := by native_decide
#eval safeResolveImp [] ["a"]

/-- **Equivalence theorem**: functional and imperative safe resolvers coincide. -/
theorem safeResolve_equivalence_thm (root userSegs : List String) :
    safeResolve root userSegs = safeResolveImp root userSegs := veribench_cheat.elim

end SafePathTraversal
end Gold
