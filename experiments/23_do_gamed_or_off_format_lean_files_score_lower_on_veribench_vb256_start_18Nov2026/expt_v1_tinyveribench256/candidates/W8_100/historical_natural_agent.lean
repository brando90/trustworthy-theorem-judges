import Mathlib
namespace Agent

/-!
# Path traversal file-server simulation

A pure translation of the supplied Python program on Linux: `os.path` is POSIX,
not Windows, even for inputs containing backslashes. Normalization is lexical;
no files are opened, no percent escapes are decoded, and extensions are not
validated. The typed records below represent the dictionaries (an absent field
is `none`). Sensitive-name lookup is ordered, case-sensitive substring lookup.
Traversal detection examines the *original* input, case-insensitively, and
returns the original regular-expression spellings in their original order.

This is a model of the program's behavior, not a claim that its heuristic is a
secure filesystem sandbox. In particular, absolute paths alone do not set the
unsafe handler's `vulnerable` flag.
-/

namespace PathTraversal

/-- Substring search; all patterns used by the program are nonempty. -/
def contains (text needle : String) : Bool :=
  if needle == "" then true else decide (1 < (text.splitOn needle).length)

def endsWith (text suffix : String) : Bool :=
  suffix.toList.reverse.isPrefixOf text.toList.reverse

/-- POSIX absolute paths start with a slash, not with a drive letter. -/
def isAbs (p : String) : Bool := "/".isPrefixOf p

/-- A reversed component stack implements `posixpath.normpath`'s dot rules. -/
def normStep (absolute : Bool) (stack : List String) (component : String) : List String :=
  if component == "" || component == "." then stack
  else if component == ".." then
    match stack with
    | [] => if absolute then [] else [".."]
    | top :: rest => if top == ".." then ".." :: stack else rest
  else component :: stack

/-- Exactly two initial slashes are preserved, as in Python on Linux. -/
def normPath (p : String) : String :=
  let absolute := isAbs p
  let rootPrefix := if "//".isPrefixOf p && !("///".isPrefixOf p) then "//"
                else if absolute then "/" else ""
  let parts := ((p.splitOn "/").foldl (normStep absolute) []).reverse
  let result := rootPrefix ++ String.intercalate "/" parts
  if result == "" then "." else result

/-- POSIX join does not normalize; an absolute second argument discards the base. -/
def joinPath (base p : String) : String :=
  if isAbs p then p
  else if base == "" || endsWith base "/" then base ++ p
  else base ++ "/" ++ p

structure FileServer where
  base_directory : String := "/var/www/files"
  allowed_extensions : List String := [".txt", ".pdf", ".jpg", ".png", ".gif"]
  sensitive_files : List String :=
    ["/etc/passwd", "/etc/shadow", "/etc/hosts",
     "/proc/version", "/proc/cpuinfo", "/proc/meminfo",
     "/var/log/auth.log", "/var/log/syslog",
     "C:\\Windows\\System32\\config\\SAM", "C:\\Windows\\System32\\drivers\\etc\\hosts"]
  sensitive_directories : List String :=
    ["/etc", "/proc", "/sys", "/var/log", "/root",
     "C:\\Windows\\System32", "C:\\Windows\\System32\\config"]
  deriving Repr, DecidableEq

def defaultServer : FileServer := {}

/-- These regexes have only escaped dots/backslashes and literal characters,
so regex search is exactly literal substring search after ASCII case folding.
Python's case-insensitive equivalents of the hexadecimal letters are ASCII. -/
def traversalPatterns : List (String × String) :=
  [("\\.\\./", "../"), ("\\.\\.\\\\", "..\\"),
   ("\\.\\.%2f", "..%2f"), ("\\.\\.%5c", "..%5c"),
   ("\\.\\.%252f", "..%252f"), ("\\.\\.%255c", "..%255c"),
   ("\\.\\.%c0%af", "..%c0%af"), ("\\.\\.%c1%9c", "..%c1%9c"),
   ("\\.\\.%ef%bc%8f", "..%ef%bc%8f"), ("\\.\\.%ef%bc%8c", "..%ef%bc%8c")]

def detectedPatterns (p : String) : List String :=
  (traversalPatterns.filter (fun entry => contains p.toLower entry.2)).map Prod.fst

def firstSensitiveFile (s : FileServer) (p : String) : Option String :=
  s.sensitive_files.find? (fun f => contains p f || endsWith p f)

def firstSensitiveDir (s : FileServer) (p : String) : Option String :=
  s.sensitive_directories.find? (contains p)

inductive RiskLevel where
  | HIGH | MEDIUM | LOW
  deriving Repr, DecidableEq, BEq

structure SafetyCheck where
  is_safe : Bool
  traversal_detected : Bool
  traversal_patterns : List String
  is_absolute : Bool
  sensitive_file_access : Bool
  accessed_sensitive_file : Option String
  sensitive_dir_access : Bool
  accessed_sensitive_dir : Option String
  normalized_path : String
  risk_level : RiskLevel
  deriving Repr, DecidableEq, BEq

def makeSafety (normalized : String) (patterns : List String)
    (file dir : Option String) : SafetyCheck :=
  let traversal := !patterns.isEmpty
  let absolute := isAbs normalized
  let sf := file.isSome
  let sd := dir.isSome
  { is_safe := !traversal && !absolute && !sf && !sd
    traversal_detected := traversal
    traversal_patterns := patterns
    is_absolute := absolute
    sensitive_file_access := sf
    accessed_sensitive_file := file
    sensitive_dir_access := sd
    accessed_sensitive_dir := dir
    normalized_path := normalized
    risk_level := if traversal || sf then .HIGH
                  else if absolute || sd then .MEDIUM else .LOW }

def FileServer.is_path_safe (s : FileServer) (p : String) : SafetyCheck :=
  let normalized := normPath p
  makeSafety normalized (detectedPatterns p)
    (firstSensitiveFile s normalized) (firstSensitiveDir s normalized)

/-- The two differently-shaped dictionaries returned by safe_file_access. -/
inductive SafeResult where
  | rejected (error : String) (details : SafetyCheck) (safe : Bool)
  | accepted (success : Bool) (file_path content : String) (safe : Bool)
  deriving Repr, DecidableEq, BEq

def FileServer.safe_file_access (s : FileServer) (p : String) : SafeResult :=
  let c := s.is_path_safe p
  if !c.is_safe then .rejected "PATH_TRAVERSAL_DETECTED" c false
  else
    let path := joinPath s.base_directory p
    .accepted true path ("Safe content from " ++ path) true

/-- Required common fields and optional branch-specific dictionary fields. -/
structure AccessResult where
  type : String
  requested_path : String
  safety_check : SafetyCheck
  vulnerable : Bool
  constructed_path : Option String := none
  accessed_file : Option String := none
  accessed_dir : Option String := none
  content : Option String := none
  error : Option String := none
  download_url : Option String := none
  image_url : Option String := none
  deriving Repr, DecidableEq, BEq

/-- Python's formatting of Optional[str] (None is not the empty string). -/
def optionalText : Option String → String
  | none => "None"
  | some p => p

def fileResponse (s : FileServer) (p : String) (c : SafetyCheck) : AccessResult :=
  let path := joinPath s.base_directory p
  if c.traversal_detected then
    { type := "file_traversal", requested_path := p, constructed_path := some path,
      safety_check := c, vulnerable := true, error := some "PATH_TRAVERSAL_ATTEMPTED" }
  else if c.sensitive_file_access then
    { type := "sensitive_file_access", requested_path := p,
      accessed_file := c.accessed_sensitive_file, safety_check := c, vulnerable := true,
      content := some ("Sensitive file content: " ++ optionalText c.accessed_sensitive_file) }
  else if c.sensitive_dir_access then
    { type := "sensitive_dir_access", requested_path := p,
      accessed_dir := c.accessed_sensitive_dir, safety_check := c, vulnerable := true,
      content := some ("Directory listing: " ++ optionalText c.accessed_sensitive_dir) }
  else
    { type := "file_access", requested_path := p, constructed_path := some path,
      safety_check := c, vulnerable := false, content := some ("File content from " ++ path) }

def downloadResponse (p : String) (c : SafetyCheck) : AccessResult :=
  { type := "download_traversal", requested_path := p, safety_check := c,
    vulnerable := c.traversal_detected || c.sensitive_file_access,
    download_url := some ("/download?file=" ++ p) }

def viewResponse (p : String) (c : SafetyCheck) : AccessResult :=
  { type := "view_traversal", requested_path := p, safety_check := c,
    vulnerable := c.traversal_detected || c.sensitive_file_access,
    image_url := some ("/images/" ++ p) }

def genericResponse (s : FileServer) (p : String) (c : SafetyCheck) : AccessResult :=
  { type := "generic_traversal", requested_path := p, safety_check := c,
    vulnerable := c.traversal_detected || c.sensitive_file_access || c.sensitive_dir_access,
    constructed_path := some (joinPath s.base_directory p) }

/-- Substring routing has priority file > download > view > generic. Replacement
is global and case-sensitive even though route selection is case-insensitive. -/
def unsafe_path_traversal (s : FileServer) (p : String) : AccessResult :=
  if contains p.toLower "file" then fileResponse s p (s.is_path_safe p)
  else if contains p.toLower "download" then
    let q := p.replace "download " ""
    downloadResponse q (s.is_path_safe q)
  else if contains p.toLower "view" then
    let q := p.replace "view " ""
    viewResponse q (s.is_path_safe q)
  else genericResponse s p (s.is_path_safe p)

/-! ## Unit tests: the public Python check -/

def check (candidate : FileServer → String → AccessResult) : Bool :=
  let s := defaultServer
  let r1 := candidate s "document.txt"
  let attacks := ["../../../etc/passwd", "..\\..\\..\\Windows\\System32\\config\\SAM",
    "..%2f..%2f..%2fetc%2fpasswd", "..%252f..%252f..%252fetc%252fpasswd",
    "..%c0%af..%c0%af..%c0%afetc%c0%afpasswd"]
  let r7 := candidate s "download ../../../etc/passwd"
  let r8 := candidate s "view ../../../etc/passwd"
  let r9 := candidate s "file /etc/passwd"
  let r10 := candidate s "file /etc/"
  !r1.vulnerable &&
  attacks.all (fun p => let r := candidate s p; r.vulnerable && r.safety_check.traversal_detected) &&
  r7.vulnerable && contains r7.type "download_traversal" &&
  r8.vulnerable && contains r8.type "view_traversal" &&
  r9.vulnerable && contains r9.type "sensitive_file_access" &&
  r10.vulnerable && contains r10.type "sensitive_dir_access"

example : check unsafe_path_traversal = true := by native_decide
#eval check unsafe_path_traversal
#eval unsafe_path_traversal defaultServer "file /etc/passwd"
#eval defaultServer.safe_file_access "document.txt"

example : (["", ".", "a/..", "a//b/./c/..", "../../a", "/../../a", "//etc///passwd", "///a", "..\\a"].map normPath) =
    [".", ".", ".", "a/b", "../../a", "/a", "//etc/passwd", "/a", "..\\a"] := by native_decide
example : joinPath "/var/www/files" "/tmp/a" = "/tmp/a" := by native_decide
example : joinPath "/var/www/files" "" = "/var/www/files/" := by native_decide
example : (defaultServer.is_path_safe "a/../document.txt").traversal_detected = true ∧
    (defaultServer.is_path_safe "a/../document.txt").normalized_path = "document.txt" := by native_decide
example : (defaultServer.is_path_safe "..%EF%BC%8F").traversal_detected = true := by native_decide
example : (unsafe_path_traversal defaultServer "download file.txt").type = "file_access" := by native_decide
example : (unsafe_path_traversal defaultServer "DOWNLOAD a.txt").requested_path = "DOWNLOAD a.txt" := by native_decide
example : (unsafe_path_traversal defaultServer "download download a.txt").requested_path = "a.txt" := by native_decide
example : (unsafe_path_traversal defaultServer "view /etc/").vulnerable = false ∧
    (unsafe_path_traversal defaultServer "view /etc/").safety_check.is_safe = false := by native_decide
example : (unsafe_path_traversal defaultServer "/tmp/public").vulnerable = false ∧
    (defaultServer.is_path_safe "/tmp/public").risk_level = .MEDIUM := by native_decide
example : (defaultServer.is_path_safe "C:\\Windows\\System32\\config\\SAM").accessed_sensitive_dir =
    some "C:\\Windows\\System32" := by native_decide
example : defaultServer.safe_file_access "x.exe" =
    .accepted true "/var/www/files/x.exe" "Safe content from /var/www/files/x.exe" true := by native_decide

/-! ## Preconditions and specifications
All strings and all server configurations are admissible. The unused extension
list is deliberately not a precondition or an access restriction.
-/

def Pre (_s : FileServer) (_p : String) : Prop := True

/-- Exact ordered pattern reporting and the existential detection flag. -/
def detection_prop (s : FileServer) (p : String) : Prop :=
  let c := s.is_path_safe p
  c.traversal_patterns = (traversalPatterns.filter (fun e => contains p.toLower e.2)).map Prod.fst ∧
  c.traversal_detected = traversalPatterns.any (fun e => contains p.toLower e.2)

private theorem filter_detection {α β : Type} (xs : List α) (pred : α → Bool) (f : α → β) :
    (!((xs.filter pred).map f).isEmpty) = xs.any pred := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases h : pred x
      · simpa only [List.filter_cons, h, Bool.false_eq_true, if_false, List.any_cons, Bool.false_or] using ih
      · simp [h]

theorem detection_thm (s : FileServer) (p : String) : detection_prop s p := by
  constructor
  · rfl
  · exact filter_detection traversalPatterns (fun e => contains p.toLower e.2) Prod.fst

/-- Normalized-path lookup, first match selection, and existence flags. -/
def sensitive_prop (s : FileServer) (p : String) : Prop :=
  let c := s.is_path_safe p
  c.normalized_path = normPath p ∧
  c.is_absolute = isAbs (normPath p) ∧
  c.accessed_sensitive_file = s.sensitive_files.find? (fun f => contains (normPath p) f || endsWith (normPath p) f) ∧
  c.accessed_sensitive_dir = s.sensitive_directories.find? (contains (normPath p)) ∧
  c.sensitive_file_access = s.sensitive_files.any (fun f => contains (normPath p) f || endsWith (normPath p) f) ∧
  c.sensitive_dir_access = s.sensitive_directories.any (contains (normPath p))

private theorem find_some_any {α : Type} (xs : List α) (pred : α → Bool) :
    (xs.find? pred).isSome = xs.any pred := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : pred x <;> simp [List.find?, h, ih]

theorem sensitive_thm (s : FileServer) (p : String) : sensitive_prop s p := by
  exact ⟨rfl, rfl, rfl, rfl,
    find_some_any s.sensitive_files _, find_some_any s.sensitive_directories _⟩

/-- Safety is equivalent to absence of all four reasons for rejection. -/
def safety_prop (s : FileServer) (p : String) : Prop :=
  let c := s.is_path_safe p
  c.is_safe = true ↔ c.traversal_patterns = [] ∧ c.is_absolute = false ∧
    c.accessed_sensitive_file = none ∧ c.accessed_sensitive_dir = none

theorem safety_thm (s : FileServer) (p : String) : safety_prop s p := by
  simp [safety_prop, FileServer.is_path_safe, makeSafety, Bool.and_eq_true, and_assoc]

/-- HIGH takes precedence over MEDIUM; LOW is exactly the safe case. -/
def risk_prop (s : FileServer) (p : String) : Prop :=
  let c := s.is_path_safe p
  (c.risk_level = .HIGH ↔ c.traversal_detected = true ∨ c.sensitive_file_access = true) ∧
  (c.risk_level = .MEDIUM ↔ c.traversal_detected = false ∧ c.sensitive_file_access = false ∧
    (c.is_absolute = true ∨ c.sensitive_dir_access = true)) ∧
  (c.risk_level = .LOW ↔ c.is_safe = true)

theorem risk_thm (s : FileServer) (p : String) : risk_prop s p := by
  unfold risk_prop FileServer.is_path_safe makeSafety
  cases h₁ : (detectedPatterns p).isEmpty <;>
    cases h₂ : isAbs (normPath p) <;>
    cases h₃ : (firstSensitiveFile s (normPath p)).isSome <;>
    cases h₄ : (firstSensitiveDir s (normPath p)).isSome <;> simp_all

/-- Full safe-access output contract, including rejection details and raw join. -/
def safeAccess_prop (s : FileServer) (p : String) : Prop :=
  let c := s.is_path_safe p
  (c.is_safe = false → s.safe_file_access p = .rejected "PATH_TRAVERSAL_DETECTED" c false) ∧
  (c.is_safe = true → s.safe_file_access p =
    .accepted true (joinPath s.base_directory p) ("Safe content from " ++ joinPath s.base_directory p) true)

theorem safeAccess_thm (s : FileServer) (p : String) : safeAccess_prop s p := by
  unfold safeAccess_prop FileServer.safe_file_access
  cases h : (s.is_path_safe p).is_safe <;> simp [h]

/-- An independent description of the prioritized dispatch decision. -/
inductive Route where
  | file | download | view | generic
  deriving Repr, DecidableEq, BEq

def route (p : String) : Route :=
  if contains p.toLower "file" then .file
  else if contains p.toLower "download" then .download
  else if contains p.toLower "view" then .view
  else .generic

def requestPath (p : String) : String :=
  match route p with
  | .download => p.replace "download " ""
  | .view => p.replace "view " ""
  | _ => p

def responseType (r : Route) (c : SafetyCheck) : String :=
  match r with
  | .file => if c.traversal_detected then "file_traversal"
             else if c.sensitive_file_access then "sensitive_file_access"
             else if c.sensitive_dir_access then "sensitive_dir_access" else "file_access"
  | .download => "download_traversal"
  | .view => "view_traversal"
  | .generic => "generic_traversal"

private theorem dispatch (s : FileServer) (p : String) :
    unsafe_path_traversal s p =
    match route p with
    | .file => fileResponse s p (s.is_path_safe p)
    | .download => downloadResponse (p.replace "download " "") (s.is_path_safe (p.replace "download " ""))
    | .view => viewResponse (p.replace "view " "") (s.is_path_safe (p.replace "view " ""))
    | .generic => genericResponse s p (s.is_path_safe p) := by
  unfold unsafe_path_traversal route
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

private theorem file_common (s : FileServer) (p : String) (c : SafetyCheck) :
    (fileResponse s p c).requested_path = p ∧ (fileResponse s p c).safety_check = c ∧
    (fileResponse s p c).type = responseType .file c ∧
    (fileResponse s p c).vulnerable = (c.traversal_detected || c.sensitive_file_access || c.sensitive_dir_access) := by
  cases h₁ : c.traversal_detected <;> cases h₂ : c.sensitive_file_access <;>
    cases h₃ : c.sensitive_dir_access <;> simp [fileResponse, responseType, h₁, h₂, h₃]

/-- The safety report always analyzes the requested (possibly replaced) path. -/
def routing_prop (s : FileServer) (p : String) : Prop :=
  let r := unsafe_path_traversal s p
  r.requested_path = requestPath p ∧
  r.safety_check = s.is_path_safe (requestPath p) ∧
  r.type = responseType (route p) (s.is_path_safe (requestPath p))

theorem routing_thm (s : FileServer) (p : String) : routing_prop s p := by
  unfold routing_prop
  rw [dispatch]
  cases h : route p <;> simp only [h, requestPath]
  · exact ⟨(file_common s p _).1, (file_common s p _).2.1, (file_common s p _).2.2.1⟩
  · simp [downloadResponse, responseType]
  · simp [viewResponse, responseType]
  · simp [genericResponse, responseType]

/-- Download/view ignore directory-only access; file/generic do not. Absolute
paths alone are ignored by all four unsafe routes. -/
def vulnerability_prop (s : FileServer) (p : String) : Prop :=
  let r := unsafe_path_traversal s p
  r.vulnerable = (r.safety_check.traversal_detected || r.safety_check.sensitive_file_access ||
    match route p with
    | .file | .generic => r.safety_check.sensitive_dir_access
    | .download | .view => false)

theorem vulnerability_thm (s : FileServer) (p : String) : vulnerability_prop s p := by
  unfold vulnerability_prop
  rw [dispatch]
  cases h : route p <;> dsimp only
  · rw [(file_common s p _).2.1]
    exact (file_common s p _).2.2.2
  · simp [downloadResponse]
  · simp [viewResponse]
  · rfl

/-- Every optional field, including absent fields, is specified. The content
and URLs interpolate the unnormalized path, just as in the Python code. -/
def payload_prop (s : FileServer) (p : String) : Prop :=
  let r := unsafe_path_traversal s p
  let c := r.safety_check
  r.constructed_path =
    (match route p with
    | .generic => some (joinPath s.base_directory p)
    | .file => if c.traversal_detected || !(c.sensitive_file_access || c.sensitive_dir_access)
               then some (joinPath s.base_directory p) else none
    | _ => none) ∧
  r.error = (if route p = .file ∧ c.traversal_detected = true
             then some "PATH_TRAVERSAL_ATTEMPTED" else none) ∧
  r.accessed_file = (if route p = .file ∧ c.traversal_detected = false ∧ c.sensitive_file_access = true
                     then c.accessed_sensitive_file else none) ∧
  r.accessed_dir = (if route p = .file ∧ c.traversal_detected = false ∧
                       c.sensitive_file_access = false ∧ c.sensitive_dir_access = true
                    then c.accessed_sensitive_dir else none) ∧
  r.content = (match route p with
    | .file => if c.traversal_detected then none
               else if c.sensitive_file_access then some ("Sensitive file content: " ++ optionalText c.accessed_sensitive_file)
               else if c.sensitive_dir_access then some ("Directory listing: " ++ optionalText c.accessed_sensitive_dir)
               else some ("File content from " ++ joinPath s.base_directory p)
    | _ => none) ∧
  r.download_url = (if route p = .download then some ("/download?file=" ++ r.requested_path) else none) ∧
  r.image_url = (if route p = .view then some ("/images/" ++ r.requested_path) else none)

theorem payload_thm (s : FileServer) (p : String) : payload_prop s p := by
  unfold payload_prop
  rw [dispatch]
  cases h : route p
  · cases ht : (s.is_path_safe p).traversal_detected <;>
      cases hf : (s.is_path_safe p).sensitive_file_access <;>
      cases hd : (s.is_path_safe p).sensitive_dir_access <;>
      simp [fileResponse, ht, hf, hd]
  · simp [downloadResponse]
  · simp [viewResponse]
  · simp [genericResponse]

private theorem safe_flags (s : FileServer) (p : String)
    (h : (s.is_path_safe p).is_safe = true) :
    (s.is_path_safe p).traversal_detected = false ∧
    (s.is_path_safe p).sensitive_file_access = false ∧
    (s.is_path_safe p).sensitive_dir_access = false := by
  change (!(s.is_path_safe p).traversal_detected && !(s.is_path_safe p).is_absolute &&
    !(s.is_path_safe p).sensitive_file_access && !(s.is_path_safe p).sensitive_dir_access) = true at h
  simp only [Bool.and_eq_true] at h
  simp only [Bool.not_eq_true'] at h
  exact ⟨h.1.1.1, h.1.2, h.2⟩

/-- Across all routes, traversal and sensitive files imply vulnerability, and
safe reports imply non-vulnerability. The converse is intentionally false. -/
def guarantees_prop (s : FileServer) (p : String) : Prop :=
  let r := unsafe_path_traversal s p
  (r.safety_check.traversal_detected = true → r.vulnerable = true) ∧
  (r.safety_check.sensitive_file_access = true → r.vulnerable = true) ∧
  (r.safety_check.is_safe = true → r.vulnerable = false)

theorem guarantees_thm (s : FileServer) (p : String) : guarantees_prop s p := by
  have hv := vulnerability_thm s p
  dsimp only [vulnerability_prop] at hv
  unfold guarantees_prop
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro ht
    simpa [ht] using hv
  · intro hf
    simpa [hf] using hv
  · intro hs
    have hc := (routing_thm s p).2.1
    rw [hc] at hs hv
    have flags := safe_flags s (requestPath p) hs
    cases h : route p <;> simpa [h, flags.1, flags.2.1, flags.2.2] using hv

/-- Joining preserves raw relative inputs and overrides the base for absolute
inputs. This does not claim the result is confined to the base directory. -/
def join_prop (s : FileServer) (p : String) : Prop :=
  (isAbs p = true → joinPath s.base_directory p = p) ∧
  (isAbs p = false → joinPath s.base_directory p =
    if s.base_directory == "" || endsWith s.base_directory "/" then s.base_directory ++ p
    else s.base_directory ++ "/" ++ p)

theorem join_thm (s : FileServer) (p : String) : join_prop s p := by
  constructor <;> intro h <;> simp [joinPath, h]

/-- Functional postcondition: all reports, routes, flags, and payloads, not just
the ten fixed examples. The selected path's safety report is also specified. -/
def Post_prop (s : FileServer) (p : String) : Prop :=
  detection_prop s p ∧ sensitive_prop s p ∧ safety_prop s p ∧ risk_prop s p ∧
  safeAccess_prop s p ∧ routing_prop s p ∧ vulnerability_prop s p ∧
  payload_prop s p ∧ guarantees_prop s p ∧ join_prop s p ∧
  detection_prop s (requestPath p) ∧ sensitive_prop s (requestPath p) ∧
  safety_prop s (requestPath p) ∧ risk_prop s (requestPath p)

/-! ## Property-based tests
The following instances merely make the Boolean forms executable; they do not
use the proofs. The bounded Cartesian-product generator stresses routing,
normalization, ordered lookup, case handling, and every traversal encoding.
-/

instance (s : FileServer) (p : String) : Decidable (detection_prop s p) := by
  unfold detection_prop; infer_instance
instance (s : FileServer) (p : String) : Decidable (sensitive_prop s p) := by
  unfold sensitive_prop; infer_instance
instance (s : FileServer) (p : String) : Decidable (safety_prop s p) := by
  unfold safety_prop; infer_instance
instance (s : FileServer) (p : String) : Decidable (risk_prop s p) := by
  unfold risk_prop; infer_instance
instance (s : FileServer) (p : String) : Decidable (safeAccess_prop s p) := by
  unfold safeAccess_prop; infer_instance
instance (s : FileServer) (p : String) : Decidable (routing_prop s p) := by
  unfold routing_prop; infer_instance
instance (s : FileServer) (p : String) : Decidable (vulnerability_prop s p) := by
  unfold vulnerability_prop; infer_instance
instance (s : FileServer) (p : String) : Decidable (payload_prop s p) := by
  unfold payload_prop; infer_instance
instance (s : FileServer) (p : String) : Decidable (guarantees_prop s p) := by
  unfold guarantees_prop; infer_instance
instance (s : FileServer) (p : String) : Decidable (join_prop s p) := by
  unfold join_prop; infer_instance
instance (s : FileServer) (p : String) : Decidable (Post_prop s p) := by
  unfold Post_prop; infer_instance

def testPaths : List String :=
  let atoms := ["", ".", "..", "document.txt", "x.exe", "a/../b", "/", "//", "///", "/tmp/x",
    "FILE", "download ", "view ", "..%2F", "..%C0%AF", "..%EF%BC%8F", "İ", "\x00"] ++
    defaultServer.sensitive_files ++ defaultServer.sensitive_directories ++ traversalPatterns.map Prod.snd
  ["", "file ", "download ", "view ", "FILE ", "DOWNLOAD ", "VIEW ", "x/"].flatMap fun front =>
    atoms.flatMap fun atom =>
      ["", "/", "/..", "/document.txt", "../", "\\..\\", " file", "/etc/passwd"].map fun back =>
        front ++ atom ++ back

def testServers : List FileServer :=
  [defaultServer,
   { base_directory := "", sensitive_files := [], sensitive_directories := [] },
   { base_directory := "/srv/", sensitive_files := ["/etc", "/etc/passwd", ""],
     sensitive_directories := ["/", "etc"] },
   { base_directory := "relative", allowed_extensions := [], sensitive_files := ["file", "a", "a"],
     sensitive_directories := ["view", ""] }]

def boundedCheck (f : FileServer → String → Bool) : Bool :=
  testServers.all fun s => testPaths.all (f s)

-- One bounded PBT for each executable property, and one for the full postcondition.
example : boundedCheck (fun s p => decide (detection_prop s p)) = true := by native_decide
example : boundedCheck (fun s p => decide (sensitive_prop s p)) = true := by native_decide
example : boundedCheck (fun s p => decide (safety_prop s p)) = true := by native_decide
example : boundedCheck (fun s p => decide (risk_prop s p)) = true := by native_decide
example : boundedCheck (fun s p => decide (safeAccess_prop s p)) = true := by native_decide
example : boundedCheck (fun s p => decide (routing_prop s p)) = true := by native_decide
example : boundedCheck (fun s p => decide (vulnerability_prop s p)) = true := by native_decide
example : boundedCheck (fun s p => decide (payload_prop s p)) = true := by native_decide
example : boundedCheck (fun s p => decide (guarantees_prop s p)) = true := by native_decide
example : boundedCheck (fun s p => decide (join_prop s p)) = true := by native_decide
example : boundedCheck (fun s p => decide (Post_prop s p)) = true := by native_decide
#eval (testPaths.length, testServers.length)
#eval boundedCheck (fun s p => decide (Post_prop s p))

/-- Correctness is a kernel-checked proof for every input and configuration;
none of the unit tests or PBTs is used in this proof. -/
theorem correctness (s : FileServer) (p : String) : Pre s p → Post_prop s p := by
  intro _
  exact ⟨detection_thm s p, sensitive_thm s p, safety_thm s p, risk_thm s p,
    safeAccess_thm s p, routing_thm s p, vulnerability_thm s p, payload_thm s p,
    guarantees_thm s p, join_thm s p,
    detection_thm s (requestPath p), sensitive_thm s (requestPath p),
    safety_thm s (requestPath p), risk_thm s (requestPath p)⟩

/-! ## Imperative implementation
These routines use mutable state and actual loops. In particular, pattern
collection appends in order, and sensitive lookup breaks on its first match.
The unsafe handler does not call its functional counterpart.
-/

def collectLoop {α β : Type} (pred : α → Bool) (f : α → β)
    (xs : List α) (initial : List β) : List β := Id.run do
  let mut result := initial
  for x in xs do
    result := if pred x then result ++ [f x] else result
  return result

def firstLoop {α : Type} (pred : α → Bool) (xs : List α) (initial : Option α) : Option α := Id.run do
  let mut found := initial
  for x in xs do
    if pred x then
      found := some x
      break
  return found

def normPath_imp (p : String) : String := Id.run do
  let absolute := isAbs p
  let mut parts : List String := []
  for component in p.splitOn "/" do
    parts := normStep absolute parts component
  let rootPrefix := if "//".isPrefixOf p && !("///".isPrefixOf p) then "//"
                    else if absolute then "/" else ""
  let mut result := rootPrefix ++ String.intercalate "/" parts.reverse
  if result == "" then
    result := "."
  return result

def FileServer.is_path_safe_imp (s : FileServer) (p : String) : SafetyCheck := Id.run do
  let normalized := normPath_imp p
  let patterns := collectLoop (fun e : String × String => contains p.toLower e.2) Prod.fst traversalPatterns []
  let file := firstLoop (fun f => contains normalized f || endsWith normalized f) s.sensitive_files none
  let dir := firstLoop (contains normalized) s.sensitive_directories none
  let traversal := !patterns.isEmpty
  let absolute := isAbs normalized
  let mut safe := true
  if traversal then safe := false
  if absolute then safe := false
  if file.isSome then safe := false
  if dir.isSome then safe := false
  let mut risk := RiskLevel.LOW
  if absolute || dir.isSome then risk := .MEDIUM
  if traversal || file.isSome then risk := .HIGH
  return {
    is_safe := safe, traversal_detected := traversal,
    traversal_patterns := patterns, is_absolute := absolute,
    sensitive_file_access := file.isSome, accessed_sensitive_file := file,
    sensitive_dir_access := dir.isSome, accessed_sensitive_dir := dir,
    normalized_path := normalized, risk_level := risk }

def FileServer.safe_file_access_imp (s : FileServer) (p : String) : SafeResult := Id.run do
  let c := s.is_path_safe_imp p
  let mut result := SafeResult.rejected "PATH_TRAVERSAL_DETECTED" c false
  if c.is_safe then
    let path := joinPath s.base_directory p
    result := .accepted true path ("Safe content from " ++ path) true
  return result

def unsafe_path_traversal_imp (s : FileServer) (p : String) : AccessResult := Id.run do
  let mut q := p
  let mut c := s.is_path_safe_imp q
  let mut result : AccessResult :=
    { type := "generic_traversal", requested_path := q, safety_check := c,
      vulnerable := c.traversal_detected || c.sensitive_file_access || c.sensitive_dir_access,
      constructed_path := some (joinPath s.base_directory q) }
  if contains p.toLower "file" then
    let path := joinPath s.base_directory p
    result := {
      type := "file_access", requested_path := p, safety_check := c,
      vulnerable := false, constructed_path := some path, content := some ("File content from " ++ path) }
    if c.traversal_detected then
      result := {
        type := "file_traversal", requested_path := p, safety_check := c,
        vulnerable := true, constructed_path := some path, error := some "PATH_TRAVERSAL_ATTEMPTED" }
    else if c.sensitive_file_access then
      result := {
        type := "sensitive_file_access", requested_path := p, safety_check := c,
        vulnerable := true, accessed_file := c.accessed_sensitive_file,
        content := some ("Sensitive file content: " ++ optionalText c.accessed_sensitive_file) }
    else if c.sensitive_dir_access then
      result := {
        type := "sensitive_dir_access", requested_path := p, safety_check := c,
        vulnerable := true, accessed_dir := c.accessed_sensitive_dir,
        content := some ("Directory listing: " ++ optionalText c.accessed_sensitive_dir) }
  else if contains p.toLower "download" then
    q := p.replace "download " ""
    c := s.is_path_safe_imp q
    result := {
      type := "download_traversal", requested_path := q, safety_check := c,
      vulnerable := c.traversal_detected || c.sensitive_file_access,
      download_url := some ("/download?file=" ++ q) }
  else if contains p.toLower "view" then
    q := p.replace "view " ""
    c := s.is_path_safe_imp q
    result := {
      type := "view_traversal", requested_path := q, safety_check := c,
      vulnerable := c.traversal_detected || c.sensitive_file_access,
      image_url := some ("/images/" ++ q) }
  return result

/-! ## Imperative tests -/
example : check unsafe_path_traversal_imp = true := by native_decide
#eval check unsafe_path_traversal_imp
#eval unsafe_path_traversal_imp defaultServer "view ../../../etc/passwd"
#eval defaultServer.safe_file_access_imp "../../../etc/passwd"
example : testPaths.all (fun p => normPath_imp p == normPath p) = true := by native_decide
example : boundedCheck (fun s p => s.is_path_safe_imp p == s.is_path_safe p) = true := by native_decide
example : boundedCheck (fun s p => s.safe_file_access_imp p == s.safe_file_access p) = true := by native_decide
example : boundedCheck (fun s p => unsafe_path_traversal_imp s p == unsafe_path_traversal s p) = true := by native_decide

/-! ## Kernel-checked functional/imperative equivalence -/

private theorem collectLoop_eq {α β : Type} (pred : α → Bool) (f : α → β)
    (xs : List α) (initial : List β) :
    collectLoop pred f xs initial = initial ++ (xs.filter pred).map f := by
  have fold_eq : ∀ acc : List β,
      xs.foldl (fun acc x => if pred x then acc ++ [f x] else acc) acc = acc ++ (xs.filter pred).map f := by
    induction xs with
    | nil => intro acc; simp
    | cons x xs ih =>
      intro acc
      cases h : pred x <;> simp [List.foldl_cons, h, ih, List.append_assoc]
  simpa [collectLoop, Id.run, List.forIn_pure_yield_eq_foldl] using fold_eq initial

private theorem firstLoop_eq {α : Type} (pred : α → Bool) (xs : List α) (initial : Option α) :
    firstLoop pred xs initial = (xs.find? pred).or initial := by
  induction xs with
  | nil => simp [firstLoop, Id.run] <;> rfl
  | cons x xs ih =>
    cases h : pred x
    · simpa [firstLoop, List.forIn_cons, h, Id.run, List.find?] using ih
    · simp [firstLoop, List.forIn_cons, h, Id.run, List.find?] <;> rfl

theorem normPath_imp_eq (p : String) : normPath_imp p = normPath p := by
  simp [normPath_imp, normPath, Id.run, List.forIn_pure_yield_eq_foldl] <;> rfl

theorem is_path_safe_imp_eq (s : FileServer) (p : String) :
    s.is_path_safe_imp p = s.is_path_safe p := by
  have hp : (traversalPatterns.filter (fun e => contains p.toLower e.2)).map Prod.fst =
      detectedPatterns p := rfl
  have hf : s.sensitive_files.find? (fun f => contains (normPath p) f || endsWith (normPath p) f) =
      firstSensitiveFile s (normPath p) := rfl
  have hd : s.sensitive_directories.find? (contains (normPath p)) =
      firstSensitiveDir s (normPath p) := rfl
  simp only [FileServer.is_path_safe_imp, normPath_imp_eq, collectLoop_eq, List.nil_append,
    firstLoop_eq, Option.or_none, hp, hf, hd]
  change (Id.run _) = makeSafety (normPath p) (detectedPatterns p)
    (firstSensitiveFile s (normPath p)) (firstSensitiveDir s (normPath p))
  cases h₁ : (detectedPatterns p).isEmpty <;>
    cases h₂ : isAbs (normPath p) <;>
    cases h₃ : (firstSensitiveFile s (normPath p)).isSome <;>
    cases h₄ : (firstSensitiveDir s (normPath p)).isSome <;>
    simp [makeSafety, Id.run, h₁, h₂, h₃, h₄] <;> rfl

theorem safe_file_access_equiv (s : FileServer) (p : String) :
    s.safe_file_access p = s.safe_file_access_imp p := by
  simp only [FileServer.safe_file_access_imp, is_path_safe_imp_eq]
  cases h : (s.is_path_safe p).is_safe <;> simp [FileServer.safe_file_access, Id.run, h] <;> rfl

/-- Equality includes every dictionary field and the entire nested safety report,
for every input string, not only the supplied examples. -/
theorem functional_imperative_equiv (s : FileServer) (p : String) :
    unsafe_path_traversal s p = unsafe_path_traversal_imp s p := by
  simp only [unsafe_path_traversal_imp, is_path_safe_imp_eq]
  unfold unsafe_path_traversal
  cases hf : contains p.toLower "file" <;>
    cases hd : contains p.toLower "download" <;>
    cases hv : contains p.toLower "view" <;>
    cases ht : (s.is_path_safe p).traversal_detected <;>
    cases hs : (s.is_path_safe p).sensitive_file_access <;>
    cases hr : (s.is_path_safe p).sensitive_dir_access <;>
    simp [Id.run, ht, hs, hr, fileResponse, downloadResponse, viewResponse, genericResponse] <;> rfl

end PathTraversal
end Agent
