import Mathlib
namespace Agent

/-!
# Safe path traversal

This file gives a pure Lean model of the Python file server.  POSIX path
normalization is represented by a small stack machine: ordinary components are
pushed, `.` is ignored, and `..` pops a component.  Safety is decided by checking
that the final canonical path is equal to the canonical base or has the base plus
`/` as a prefix.  The response record is the typed analogue of the Python
dictionary returned by `safe_file_access`.
-/

namespace PathTraversalSafe

structure FileServer where
  baseDirectory : String
  deriving Repr, DecidableEq

def defaultServer : FileServer :=
  { baseDirectory := "/var/www/files" }

structure NormState where
  revComponents : List String := []
  leadingParents : Nat := 0
  escaped : Bool := false
  deriving Repr, DecidableEq

def normalizeStep (state : NormState) (component : String) : NormState :=
  if component = "" || component = "." then
    state
  else if component = ".." then
    match state.revComponents with
    | _ :: rest => { state with revComponents := rest }
    | [] =>
        { state with
          leadingParents := state.leadingParents + 1
          escaped := true }
  else
    { state with revComponents := component :: state.revComponents }

def normalizeState (path : String) : NormState :=
  (path.split (· = '/')).foldl normalizeStep {}

def normalizedComponents (path : String) : List String :=
  List.replicate (normalizeState path).leadingParents ".." ++
    (normalizeState path).revComponents.reverse

def normPath (path : String) : String :=
  let body := String.intercalate "/" (normalizedComponents path)
  if path.startsWith "/" then
    if body = "" then "/" else "/" ++ body
  else if body = "" then "." else body

def isAbsolute (path : String) : Bool :=
  (normPath path).startsWith "/"

/-- A syntactic POSIX counterpart of the uses of `os.path.realpath`. -/
def canonicalBase (server : FileServer) : String :=
  normPath server.baseDirectory

def canonicalFullPath (server : FileServer) (filePath : String) : String :=
  normPath (canonicalBase server ++ "/" ++ normPath filePath)

def isWithinBase (server : FileServer) (filePath : String) : Bool :=
  let base := canonicalBase server
  let full := canonicalFullPath server filePath
  full.startsWith (base ++ "/") || full == base

/-- The pure counterpart of `FileServer.is_path_safe`. -/
def isPathSafe (server : FileServer) (filePath : String) : Bool :=
  !filePath.contains '%' &&
    !isAbsolute filePath &&
    isWithinBase server filePath

structure AccessResult where
  error : Option String := none
  success : Option Bool := none
  filePath : Option String := none
  safe : Bool
  deriving Repr, DecidableEq

def safeFileAccess (server : FileServer) (userInput : String) : AccessResult :=
  if isPathSafe server userInput then
    { success := some true
      filePath := some (server.baseDirectory ++ "/" ++ normPath userInput)
      safe := true }
  else
    { error := some "PATH_TRAVERSAL_DETECTED"
      safe := false }

def safePathTraversal (server : FileServer) (userInput : String) : AccessResult :=
  safeFileAccess server userInput

/-! Unit tests corresponding to `check` in the Python source. -/

example : (safePathTraversal defaultServer "document.txt").safe = true := by
  native_decide

example : (safePathTraversal defaultServer "../../../etc/passwd").safe = false := by
  native_decide

example : (safePathTraversal defaultServer "..%2f..%2fetc%2fpasswd").safe = false := by
  native_decide

example : (safePathTraversal defaultServer "/etc/passwd").safe = false := by
  native_decide

example : (safePathTraversal defaultServer "document.txt").filePath =
    some "/var/www/files/document.txt" := by
  native_decide

#eval safePathTraversal defaultServer "document.txt"
#eval safePathTraversal defaultServer "../../../etc/passwd"
#eval safePathTraversal defaultServer "..%2f..%2fetc%2fpasswd"
#eval safePathTraversal defaultServer "/etc/passwd"

/-- The constructor precondition from the Python program. -/
def Pre (server : FileServer) : Prop :=
  server.baseDirectory = "/var/www/files"

def safe_flag_prop (server : FileServer) (userInput : String) : Prop :=
  (safePathTraversal server userInput).safe = isPathSafe server userInput

theorem safe_flag_thm (server : FileServer) (userInput : String) :
    safe_flag_prop server userInput := by
  unfold safe_flag_prop safePathTraversal safeFileAccess
  cases h : isPathSafe server userInput <;> simp

def accepted_path_prop (server : FileServer) (userInput : String) : Prop :=
  isPathSafe server userInput = true →
    safePathTraversal server userInput =
      { success := some true
        filePath := some (server.baseDirectory ++ "/" ++ normPath userInput)
        safe := true }

theorem accepted_path_thm (server : FileServer) (userInput : String) :
    accepted_path_prop server userInput := by
  intro h
  simp [safePathTraversal, safeFileAccess, h]

def rejected_path_prop (server : FileServer) (userInput : String) : Prop :=
  isPathSafe server userInput = false →
    safePathTraversal server userInput =
      { error := some "PATH_TRAVERSAL_DETECTED", safe := false }

theorem rejected_path_thm (server : FileServer) (userInput : String) :
    rejected_path_prop server userInput := by
  intro h
  simp [safePathTraversal, safeFileAccess, h]

/-- Every accepted path has passed each of the three security checks. -/
def accepted_is_safe_prop (server : FileServer) (userInput : String) : Prop :=
  (safePathTraversal server userInput).safe = true →
    userInput.contains '%' = false ∧
    isAbsolute userInput = false ∧
    isWithinBase server userInput = true

theorem accepted_is_safe_thm (server : FileServer) (userInput : String) :
    accepted_is_safe_prop server userInput := by
  simp only [accepted_is_safe_prop, safePathTraversal, safeFileAccess, isPathSafe]
  split <;> rename_i h
  · simp only [Bool.and_eq_true] at h
    rcases h with ⟨⟨hpercent, habsolute⟩, hwithin⟩
    simp only [Bool.not_eq_true'] at hpercent habsolute
    intro _
    exact ⟨hpercent, habsolute, hwithin⟩
  · simp

def attacks_rejected_prop (server : FileServer) : Prop :=
  (safePathTraversal server "../../../etc/passwd").error =
      some "PATH_TRAVERSAL_DETECTED" ∧
  (safePathTraversal server "..%2f..%2fetc%2fpasswd").error =
      some "PATH_TRAVERSAL_DETECTED" ∧
  (safePathTraversal server "/etc/passwd").error =
      some "PATH_TRAVERSAL_DETECTED"

theorem attacks_rejected_thm (server : FileServer) (hpre : Pre server) :
    attacks_rejected_prop server := by
  rcases server with ⟨base⟩
  simp only [Pre] at hpre
  subst base
  unfold attacks_rejected_prop
  native_decide

def Post_prop (server : FileServer) (userInput : String) : Prop :=
  safe_flag_prop server userInput ∧
  accepted_path_prop server userInput ∧
  rejected_path_prop server userInput ∧
  accepted_is_safe_prop server userInput ∧
  attacks_rejected_prop server

theorem correctness_thm (server : FileServer) (userInput : String) :
    Pre server → Post_prop server userInput := by
  intro hpre
  exact ⟨safe_flag_thm server userInput,
    accepted_path_thm server userInput,
    rejected_path_thm server userInput,
    accepted_is_safe_thm server userInput,
    attacks_rejected_thm server hpre⟩

/-- An imperative presentation of `safeFileAccess`, using mutable state. -/
def safeFileAccessImperative (server : FileServer) (userInput : String) : AccessResult :=
  Id.run do
    let mut result : AccessResult := { safe := false }
    if isPathSafe server userInput then
      result :=
        { success := some true
          filePath := some (server.baseDirectory ++ "/" ++ normPath userInput)
          safe := true }
    else
      result :=
        { error := some "PATH_TRAVERSAL_DETECTED"
          safe := false }
    return result

def safePathTraversalImperative (server : FileServer)
    (userInput : String) : AccessResult :=
  safeFileAccessImperative server userInput

example : (safePathTraversalImperative defaultServer "document.txt").safe = true := by
  native_decide

example :
    (safePathTraversalImperative defaultServer "../../../etc/passwd").error =
      some "PATH_TRAVERSAL_DETECTED" := by
  native_decide

example :
    (safePathTraversalImperative defaultServer "..%2f..%2fetc%2fpasswd").safe = false := by
  native_decide

example : (safePathTraversalImperative defaultServer "/etc/passwd").safe = false := by
  native_decide

#eval safePathTraversalImperative defaultServer "document.txt"
#eval safePathTraversalImperative defaultServer "../../../etc/passwd"

theorem functional_imperative_equivalence_thm
    (server : FileServer) (userInput : String) :
    safePathTraversal server userInput =
      safePathTraversalImperative server userInput := by
  unfold safePathTraversal safePathTraversalImperative
    safeFileAccess safeFileAccessImperative
  cases h : isPathSafe server userInput <;> simp

end PathTraversalSafe
end Agent
