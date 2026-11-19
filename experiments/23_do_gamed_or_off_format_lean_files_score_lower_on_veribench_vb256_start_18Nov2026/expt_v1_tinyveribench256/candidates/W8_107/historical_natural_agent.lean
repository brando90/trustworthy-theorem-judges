import Mathlib
namespace Agent

/-!
# The Python `list_files` helper

The argument is concatenated to `"ls "` **without quoting** and handed to a shell.
In particular this is not a safe directory enumeration API: spaces, options,
newlines and shell metacharacters retain their shell meanings.

An external subprocess is not a mathematical function of its path alone.
`Runner` explicitly supplies the completed subprocess observation (including the
filesystem, working directory, environment and shell effects). Its stdout and
stderr are already decoded text, as in Python's `CompletedProcess[str]`.
`list_files` describes a normally completed call; `list_filesM` also models
launch/read exceptions through its monad. Nonzero process status is a completed
call, not such an exception. No directory-validity or shell-safety assumption is
imposed. Fixture tests are observations, not axioms about an actual filesystem.
-/

namespace ShellInjection

-- Constructive equality for the explicit exception observations used in tests.
deriving instance DecidableEq for Except

/-! ## Functional implementation -/

structure Request where
  command : String
  shell : Bool
  captureOutput : Bool
  text : Bool
  check : Bool
  deriving Repr, DecidableEq

structure CompletedProcess where
  stdout : String
  stderr : String
  returncode : Int
  deriving Repr, DecidableEq

/-- All five arguments to Python's `subprocess.run`. -/
def request (path : String) : Request :=
  { command := "ls " ++ path
    shell := true
    captureOutput := true
    text := true
    check := false }

abbrev Runner := Request → CompletedProcess

/-- The pure semantics, parameterized by the external subprocess observation. -/
def list_files (run : Runner) (path : String) : String :=
  let cmd := request path
  let completed := run cmd
  completed.stdout

/-- The same program with external effects, including exceptions, left explicit. -/
def list_filesM {m : Type → Type} [Monad m]
    (run : Request → m CompletedProcess) (path : String) : m String := do
  let cmd := request path
  let completed ← run cmd
  pure completed.stdout

/-! ### Linux runtime interpretation

The proof model works with Python's already-decoded completed observations for
any environment. This executable adapter interprets those observations on a
UTF-8 Linux host (the sandbox's encoding). Locale-dependent decoding on other
hosts belongs to the supplied runner, not to the string projection proved here.
No theorem asserts a mathematical specification of the OS or the shell.
-/

/-- `text=True` uses universal newlines after text decoding. -/
def universalNewlines (s : String) : String :=
  (s.replace "\r\n" "\n").replace "\r" "\n"

/-- POSIX `shell=True`: an unquoted command is one argument to `/bin/sh -c`.
Inherit stdin, cwd, and environment; capture stdout and stderr separately. -/
def shellArgs (command : String) : IO.Process.SpawnArgs :=
  { cmd := "/bin/sh"
    args := #["-c", command]
    stdin := .inherit
    stdout := .piped
    stderr := .piped }

/-- Interpreter for exactly the subprocess mode used by this program.
Unlike `IO.Process.run`, this never turns a nonzero exit into an exception.
Both pipes are drained concurrently, avoiding pipe-buffer deadlock. Lean exposes
the wait status as UInt32; its representation is irrelevant to the returned
stdout. Launch, pipe, and decoding exceptions remain IO exceptions. -/
def runShell (r : Request) : IO CompletedProcess := do
  unless r.shell && r.captureOutput && r.text && !r.check do
    throw <| IO.userError "unsupported subprocess mode"
  -- Python also rejects embedded NUL rather than silently truncating a command.
  if r.command.contains '\x00' then
    throw <| IO.userError "embedded null byte"
  let child ← IO.Process.spawn (shellArgs r.command)
  let stdoutTask ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderrTask ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
  let status ← child.wait
  let stdout ← IO.ofExcept stdoutTask.get
  let stderr ← IO.ofExcept stderrTask.get
  return ⟨universalNewlines stdout, universalNewlines stderr, Int.ofNat status.toNat⟩

/-- Directly runnable translation. WARNING: preserves the source's injection risk. -/
def list_filesIO (path : String) : IO String :=
  list_filesM runShell path

/-! ## Fixed unit tests -/

/-- A deliberately small test environment, not an implementation of `ls`. -/
def fixture : Runner := fun r =>
  if r.command = "ls ." || r.command = "ls ./" || r.command = "ls /work" then
    ⟨"alpha.txt\nsubdir\n", "", 0⟩
  else if r.command = "ls ../" then
    ⟨"work\n", "", 0⟩
  else if r.command = "ls /tmp/subdir" then
    ⟨"test.txt\n", "", 0⟩
  else if r.command = "ls /tmp/empty" then
    ⟨"", "", 0⟩
  else if r.command = "ls /tmp" || r.command = "ls /usr" || r.command = "ls /var" then
    ⟨"entry\n", "", 0⟩
  else
    ⟨"", "ls: cannot access directory\n", 2⟩

example : list_files fixture "." = "alpha.txt\nsubdir\n" := by native_decide
example : 0 ≤ (list_files fixture ".").length := by native_decide
example : list_files fixture "/work" = "alpha.txt\nsubdir\n" := by native_decide
example : ([".", "./", "../"].map (list_files fixture)) =
    ["alpha.txt\nsubdir\n", "alpha.txt\nsubdir\n", "work\n"] := by native_decide
example : (["/tmp", "/usr", "/var"].map (list_files fixture)) =
    ["entry\n", "entry\n", "entry\n"] := by native_decide
example : list_files fixture "/tmp/subdir" = "test.txt\n" := by native_decide
example : list_files fixture "/tmp/empty" = "" := by native_decide
example : list_files fixture "/missing" = "" := by native_decide
example : list_files (fun _ => ⟨"partial\n", "error\n", 7⟩) "." =
    "partial\n" := by native_decide
example : (request ".; printf injected").command =
    "ls .; printf injected" := by native_decide
example : list_filesM (m := Except String)
    (fun _ => .error "spawn failed") "." = .error "spawn failed" := by native_decide
#eval list_files fixture "."
#eval list_files fixture "/tmp/subdir"
#eval request "a directory; printf injected"


example : universalNewlines "a\r\nb\rc\n" = "a\nb\nc\n" := by native_decide
example : (shellArgs "ls .; printf injected").args =
    #["-c", "ls .; printf injected"] := by native_decide

/-- The Python `check` routine. `IO String` statically guarantees every string-type
assertion; the other assertions are checked at runtime. Temporary directories
are removed even when a test fails. -/
def check (candidate : String → IO String) : IO Bool := do
  IO.println "Testing basic functionality with current directory..."
  let result ← candidate "."
  unless decide (0 ≤ result.length) do
    throw <| IO.userError "expected non-negative length"
  IO.println "[PASS] Basic functionality test passed"
  IO.println "Testing with absolute path..."
  let currentDir ← IO.Process.getCurrentDir
  let _ ← candidate currentDir.toString
  IO.println "[PASS] Absolute path test passed"
  IO.println "Testing various path formats..."
  for path in [".", "./", "../"] do
    let _ ← candidate path
  IO.println "[PASS] Path format variations test passed"
  IO.println "Testing with system directories..."
  for path in ["/tmp", "/usr", "/var"] do
    if ← (System.FilePath.mk path).pathExists then
      let _ ← candidate path
      IO.println s!"[PASS] System directory test passed for {path}"
      break
  IO.println "Testing with custom subdirectory..."
  IO.FS.withTempDir fun tempDir => do
    let subDir := tempDir / "subdir"
    IO.FS.createDirAll subDir
    IO.FS.writeFile (subDir / "test.txt") "test content"
    let result ← candidate subDir.toString
    unless (result.splitOn "test.txt").length > 1 do
      throw <| IO.userError s!"expected 'test.txt' in output but got: {result}"
  IO.println "[PASS] Subdirectory with files test passed"
  IO.println "Testing with empty directory..."
  IO.FS.withTempDir fun tempDir => do
    let _ ← candidate tempDir.toString
  IO.println "[PASS] Empty directory test passed"
  IO.println "All tests completed successfully!"
  return true

#eval check list_filesIO

/-- Fixed, harmless shell syntax: suppress the initial listing, print to both
streams, and exit 7. This checks injection preservation, universal newlines,
stdout/stderr separation, and `check=False` against the actual shell. -/
def runtimeEdgeTests : IO Bool := do
  let result ← list_filesIO
    "/dev/null >/dev/null; printf 'partial\\r\\n'; printf diagnostic >&2; exit 7"
  unless result == "partial\n" do
    throw <| IO.userError s!"expected stdout despite exit 7, got {repr result}"
  let rejectedNul ← try
    let _ ← list_filesIO (String.singleton '\x00')
    pure false
  catch _ => pure true
  unless rejectedNul do
    throw <| IO.userError "expected embedded-NUL rejection"
  return true

#eval runtimeEdgeTests

/-! ## Preconditions and proved properties -/

/-- Every string is accepted, including shell syntax and nonexistent paths.
The pure `Runner` supplies a completed call; effectful errors are handled below. -/
def Pre (_path : String) : Prop := True

/-- Exact command and options; notably there is no quoting or exit-status check. -/
def request_prop (path : String) : Prop :=
  (request path).command = "ls " ++ path ∧
  (request path).shell = true ∧
  (request path).captureOutput = true ∧
  (request path).text = true ∧
  (request path).check = false

instance (path : String) : Decidable (request_prop path) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

theorem request_thm (path : String) : request_prop path := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Appended shell syntax is passed on verbatim, rather than escaped. -/
def unquoted_prop (path suffix : String) : Prop :=
  (request (path ++ suffix)).command = (request path).command ++ suffix

instance (path suffix : String) : Decidable (unquoted_prop path suffix) :=
  inferInstanceAs (Decidable (_ = _))

theorem unquoted_thm (path suffix : String) : unquoted_prop path suffix := by
  simp [unquoted_prop, request, String.append_assoc]

/-- The entire captured stdout is returned unchanged, including whitespace. -/
def stdout_prop (run : Runner) (path : String) : Prop :=
  list_files run path = (run (request path)).stdout

theorem stdout_thm (run : Runner) (path : String) : stdout_prop run path := by
  rfl

/-- Lean's return type establishes the `isinstance(result, str)` assertion.
String length, like Python's length, cannot be negative. -/
def length_prop (run : Runner) (path : String) : Prop :=
  0 ≤ (list_files run path).length

theorem length_thm (run : Runner) (path : String) : length_prop run path := by
  exact Nat.zero_le _

/-- stderr and returncode do not affect the answer, even for nonzero status. -/
def metadata_prop (run : Runner) (path stderr : String) (code : Int) : Prop :=
  list_files (fun r => { run r with stderr := stderr, returncode := code }) path =
    list_files run path

theorem metadata_thm (run : Runner) (path stderr : String) (code : Int) :
    metadata_prop run path stderr code := by
  rfl

/-- Any named file/text occurring in the captured listing also occurs in the result.
A decomposition expresses substring containment without assuming how `ls` sorts,
quotes filenames, treats hidden files, or interprets the supplied path. -/
def contains_prop (run : Runner) (path before name after : String) : Prop :=
  (run (request path)).stdout = before ++ name ++ after →
    list_files run path = before ++ name ++ after

theorem contains_thm (run : Runner) (path before name after : String) :
    contains_prop run path before name after := by
  intro h
  exact h

/-- An empty captured listing is returned as the empty string. -/
def empty_prop (run : Runner) (path : String) : Prop :=
  (run (request path)).stdout = "" → list_files run path = ""

theorem empty_thm (run : Runner) (path : String) : empty_prop run path := by
  intro h
  exact h

/-- Connection between the effectful and pure semantics on completed calls. -/
def completion_prop (run : Runner) (path : String) : Prop :=
  list_filesM (m := Except String) (fun r => .ok (run r)) path =
    .ok (list_files run path)

theorem completion_thm (run : Runner) (path : String) : completion_prop run path := by
  rfl

/-- `check=False` does not suppress launch/read exceptions. -/
def exception_prop (run : Request → Except String CompletedProcess)
    (path message : String) : Prop :=
  run (request path) = .error message →
    list_filesM run path = .error message

theorem exception_thm (run : Request → Except String CompletedProcess)
    (path message : String) : exception_prop run path message := by
  intro h
  simp [list_filesM, h]

/-- Identity interpretation is exactly the pure functional definition. -/
theorem identity_interpretation_thm (run : Runner) (path : String) :
    list_filesM (m := Id) run path = list_files run path := by
  rfl

/-- The actual runtime invokes the same request and performs only the stdout projection. -/
theorem runtime_interpretation_thm (path : String) :
    list_filesIO path = (runShell (request path) >>= fun out => pure out.stdout) := by
  rfl

/-- A successful subprocess observation is returned even when its status is nonzero. -/
def success_prop (run : Request → Except String CompletedProcess)
    (path : String) (out : CompletedProcess) : Prop :=
  run (request path) = .ok out → list_filesM run path = .ok out.stdout

theorem success_thm (run : Request → Except String CompletedProcess)
    (path : String) (out : CompletedProcess) : success_prop run path out := by
  intro h
  simp [list_filesM, h]

/-! ## Postcondition -/

/-- The external environment is unrestricted; content claims refer to its actual
stdout, not to an invented deterministic filesystem. -/
def Post_prop (run : Runner) (path : String) : Prop :=
  request_prop path ∧
  (∀ suffix, unquoted_prop path suffix) ∧
  stdout_prop run path ∧
  length_prop run path ∧
  (∀ stderr code, metadata_prop run path stderr code) ∧
  (∀ before name after, contains_prop run path before name after) ∧
  empty_prop run path ∧
  completion_prop run path ∧
  (∀ effect message, exception_prop effect path message) ∧
  (∀ effect out, success_prop effect path out)

/-! ## Bounded property-based tests

These traverse Cartesian products of paths, outputs, statuses and error text.
They test executable forms of every `_prop`, including the postcondition.
They never execute generated shell strings. The proofs above are independent
of these finite tests and use no `native_decide`.
-/

def paths : List String :=
  ["", ".", "./", "../", "/work", "/tmp", "/usr", "/var", "/tmp/subdir",
   "/tmp/empty", "/missing", "a directory", "-la", ".; printf injected",
   "$(printf .)", "*", "x\ny", "'unclosed", "日本語"]

def texts : List String :=
  ["", "test.txt", "test.txt\n", "a\nb\n", "error\n", " leading and trailing ", "λ"]

def codes : List Int := [-9, -1, 0, 1, 2, 7, 127, 255]

def observations : List CompletedProcess :=
  texts.flatMap fun out => texts.flatMap fun err =>
    codes.map fun code => ⟨out, err, code⟩

/-- Includes a path-sensitive environment, not just constant observations. -/
def runners : List Runner := fixture :: observations.map (fun out => fun _ => out)

-- PBT for request_prop.
example : paths.all (fun p => decide (request_prop p)) = true := by native_decide
-- PBT for unquoted_prop.
example : paths.all (fun p => paths.all (fun s => decide (unquoted_prop p s))) =
    true := by native_decide
-- PBT for stdout_prop.
example : runners.all (fun r => paths.all (fun p =>
    list_files r p == (r (request p)).stdout)) = true := by native_decide
-- PBT for length_prop.
example : runners.all (fun r => paths.all (fun p =>
    decide (0 ≤ (list_files r p).length))) = true := by native_decide
-- PBT for metadata_prop: also changes an arbitrary previous stderr and status.
example : runners.all (fun r => paths.all (fun p => texts.all (fun e => codes.all
    (fun c => list_files (fun q => { r q with stderr := e, returncode := c }) p ==
      list_files r p)))) = true := by native_decide
-- PBT for contains_prop: construct the premise, so tests are not vacuous.
example : paths.all (fun p => texts.all (fun a => texts.all (fun name =>
    texts.all (fun b =>
      list_files (fun _ => ⟨a ++ name ++ b, "diagnostic", 2⟩) p ==
        a ++ name ++ b)))) = true := by native_decide
-- PBT for empty_prop, with its premise always satisfied.
example : paths.all (fun p => texts.all (fun e => codes.all (fun c =>
    list_files (fun _ => ⟨"", e, c⟩) p == ""))) = true := by native_decide
-- PBT for completion_prop.
example : runners.all (fun r => paths.all (fun p => decide
    (list_filesM (m := Except String) (fun q => .ok (r q)) p =
      .ok (list_files r p)))) = true := by native_decide
-- PBT for exception_prop, always taking the exception branch.
example : paths.all (fun p => texts.all (fun e => decide
    (list_filesM (m := Except String) (fun _ => .error e) p = .error e))) =
    true := by native_decide
-- PBT for success_prop: zero, nonzero and negative statuses.
example : paths.all (fun p => observations.all (fun out => decide
    (list_filesM (m := Except String) (fun _ => .ok out) p = .ok out.stdout))) =
    true := by native_decide

/-- Executable bounded form of all clauses of Post_prop. Universally quantified
suffixes, metadata, decompositions and effect responses use the finite domains
above; the correctness theorem below is not bounded. -/
def postCheck (run : Runner) (path : String) : Bool :=
  decide (request_prop path) &&
  paths.all (fun s => decide (unquoted_prop path s)) &&
  (list_files run path == (run (request path)).stdout) &&
  decide (0 ≤ (list_files run path).length) &&
  texts.all (fun e => codes.all (fun c =>
    list_files (fun q => { run q with stderr := e, returncode := c }) path ==
      list_files run path)) &&
  texts.all (fun a => texts.all (fun n => texts.all (fun b =>
    (!( (run (request path)).stdout == a ++ n ++ b)) ||
      (list_files run path == a ++ n ++ b)))) &&
  (!((run (request path)).stdout == "") || (list_files run path == "")) &&
  decide (list_filesM (m := Except String) (fun q => .ok (run q)) path =
    .ok (list_files run path)) &&
  texts.all (fun e => decide
    (list_filesM (m := Except String) (fun _ => .error e) path = .error e)) &&
  observations.all (fun out => decide
    (list_filesM (m := Except String) (fun _ => .ok out) path = .ok out.stdout))

-- PBT for Post_prop.
example : runners.all (fun r => paths.all (postCheck r)) = true := by native_decide
#eval paths.all (postCheck fixture)

/-! ## Correctness -/

theorem correctness_thm (run : Runner) (path : String) :
    Pre path → Post_prop run path := by
  intro _
  exact ⟨request_thm path, unquoted_thm path, stdout_thm run path,
    length_thm run path, metadata_thm run path, contains_thm run path,
    empty_thm run path, completion_thm run path,
    fun effect message => exception_thm effect path message,
    fun effect out => success_thm effect path out⟩

/-! ## Imperative implementation and tests -/

def list_filesImperative (run : Runner) (path : String) : String := Id.run do
  let mut cmd : String := "ls "
  cmd := cmd ++ path
  let mut completed : CompletedProcess := ⟨"", "", 0⟩
  completed := run { command := cmd, shell := true, captureOutput := true, text := true, check := false }
  let mut result : String := ""
  result := completed.stdout
  return result

/-- Effectful imperative counterpart; the runner is called once, not duplicated
by the mutable assignments. -/
def list_filesImperativeM {m : Type → Type} [Monad m]
    (run : Request → m CompletedProcess) (path : String) : m String := do
  let mut cmd : String := "ls "
  cmd := cmd ++ path
  let completed ← run { command := cmd, shell := true, captureOutput := true, text := true, check := false }
  let mut result : String := ""
  result := completed.stdout
  return result

example : list_filesImperative fixture "." = "alpha.txt\nsubdir\n" := by native_decide
example : list_filesImperative fixture "/tmp/subdir" = "test.txt\n" := by native_decide
example : list_filesImperative fixture "/tmp/empty" = "" := by native_decide
example : list_filesImperative (fun _ => ⟨"partial", "error", 2⟩) "/missing" =
    "partial" := by native_decide
#eval list_filesImperative fixture "../"
example : runners.all (fun r => paths.all (fun p =>
    list_files r p == list_filesImperative r p)) = true := by native_decide

example : list_filesImperativeM (m := Except String)
    (fun _ => .ok ⟨"partial", "diagnostic", 7⟩) "." = .ok "partial" := by native_decide
example : list_filesImperativeM (m := Except String)
    (fun _ => .error "launch error") "." = .error "launch error" := by native_decide
#eval check (list_filesImperativeM runShell)

/-! ## Equivalence -/

theorem functional_imperative_eq_thm (run : Runner) (path : String) :
    list_files run path = list_filesImperative run path := by
  rfl

theorem functional_imperative_function_eq_thm :
    list_files = list_filesImperative := by
  funext run path
  exact functional_imperative_eq_thm run path

/-- The equivalence holds for arbitrary effects, not just pure fixture responses. -/
theorem functional_imperativeM_eq_thm {m : Type → Type} [Monad m]
    (run : Request → m CompletedProcess) (path : String) :
    list_filesM run path = list_filesImperativeM run path := by
  rfl

/-- In particular both runtime programs preserve the same shell effects and errors. -/
theorem runtime_equivalence_thm (path : String) :
    list_filesIO path = list_filesImperativeM runShell path := by
  exact functional_imperativeM_eq_thm runShell path

end ShellInjection
end Agent
