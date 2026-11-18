import Mathlib
namespace Agent

/-!
# Prespecified command execution, including its shell-injection behavior

Translation of `execute_command`. The environment (filesystem, cwd, PATH, stdin,
and shell) is not a pure function of the two Python strings. Accordingly we first
build an observable command plan, and interpret it with an explicitly supplied
subprocess observation. `Completed` contains the already decoded, universal-
newline-translated strings returned by Python's `subprocess.run(text=True)`.
An `Except.error` is a subprocess/decoding exception, NOT a nonzero exit status.
The exception payload is polymorphic: it need not discard any exception data.

The theorems cover every input string and every external observation. They do
not assume that ls/wc/grep succeed, that a file exists, or that subprocesses
terminate. The plan also describes executions whose external call never returns;
the value interpreter describes executions for which an observation is available.
In particular this is NOT an argument sanitizer: metacharacters, whitespace,
and empty arguments are passed to the shell verbatim, after one separating space.

The finite fixture below is only a test environment, not an implementation of
ls, wc, grep, or a shell. A runnable POSIX/UTF-8 IO adapter is provided separately;
the kernel proofs concern the program and its explicit external-call boundary,
not the OS, its locale-dependent decoder, or the installed utilities.
-/

namespace CommandInjection

deriving instance DecidableEq for Except

/-- The dictionary in the Python source, as a functional lookup. -/
def baseCommand (name : String) : Option String :=
  if name = "list" then some "ls"
  else if name = "count" then some "wc -l"
  else if name = "search" then some "grep -r"
  else none

def unknownError : String := "Error: Unknown command"

/-- The observable arguments to subprocess.run, including its defaults. -/
structure Request where
  command : String
  shell : Bool := true
  captureOutput : Bool := true
  text : Bool := true
  check : Bool := false
  inheritStdin : Bool := true
  deriving Repr, DecidableEq

def makeRequest (base args : String) : Request :=
  { command := base ++ " " ++ args }

/-- Return locally, or issue exactly one subprocess request. -/
inductive Plan where
  | returned (value : String)
  | subprocess (request : Request)
  deriving Repr, DecidableEq

def executePlan (name : String) (args : String := "") : Plan :=
  match baseCommand name with
  | none => .returned unknownError
  | some base => .subprocess (makeRequest base args)

structure Completed where
  stdout : String
  stderr : String := ""
  /-- Python return codes can also be negative (termination by signal). -/
  returncode : Int := 0
  deriving Repr, DecidableEq

abbrev Runner (ε : Type) := Request → Except ε Completed

def interpret {ε : Type} (run : Runner ε) : Plan → Except ε String
  | .returned value => .ok value
  | .subprocess req => (run req).map Completed.stdout

/-- Functional translation. The extra parameter explicitly supplies the world. -/
def execute_command {ε : Type} (run : Runner ε)
    (cmd_name : String) (args : String := "") : Except ε String :=
  interpret run (executePlan cmd_name args)

/-- Python text-mode universal newline handling, after decoding. -/
def universalNewlines (s : String) : String :=
  (s.replace "\r\n" "\n").replace "\r" "\n"

/-- Strict UTF-8 adapter for the text-mode external boundary. -/
def decodeTextIO (bytes : ByteArray) : IO String := do
  match String.fromUTF8? bytes with
  | some text => return universalNewlines text
  | none => throw <| IO.userError "subprocess text decoding failed (invalid UTF-8)"

/--
Concrete POSIX/UTF-8 subprocess adapter for the requests produced by executePlan.
Uses /bin/sh -c, NOT tokenization/escaping and NOT IO.Process.run (which checks
exit codes). Both pipes are drained concurrently, and stdin/cwd/env are inherited.
Other Python locale encodings are represented by supplying a different runner
at the explicit external boundary, not by restricting Pre.
-/
def runShellIO (req : Request) : IO Completed := do
  -- Like Python's subprocess API, do not silently truncate an embedded NUL.
  if req.command.contains (Char.ofNat 0) then
    throw <| IO.userError "embedded null byte in subprocess command"
  let child ← IO.Process.spawn {
    cmd := "/bin/sh", args := #["-c", req.command],
    stdin := .inherit, stdout := .piped, stderr := .piped }
  let stdoutTask ← IO.asTask child.stdout.readBinToEnd Task.Priority.dedicated
  let stderrBytes ← child.stderr.readBinToEnd
  let code ← child.wait
  let stdoutBytes ← IO.ofExcept stdoutTask.get
  let stdout ← decodeTextIO stdoutBytes
  let stderr ← decodeTextIO stderrBytes
  return { stdout, stderr, returncode := Int.ofNat code.toNat }

/-- Two-string runnable entry point; real subprocess exceptions remain IO errors. -/
def execute_commandIO (cmd_name : String) (args : String := "") : IO String := do
  match executePlan cmd_name args with
  | .returned value => return value
  | .subprocess req => return (← runShellIO req).stdout

/-- Test-only observations of the files used by the Python examples. -/
def fixture : Runner String := fun req =>
  if req.command = "ls ." ∨ req.command = "ls " then
    .ok { stdout := "test.txt\n" }
  else if req.command = "wc -l /fixture/three.txt" then
    .ok { stdout := "3 /fixture/three.txt\n" }
  else if req.command = "grep -r hello /fixture" then
    .ok { stdout := "/fixture/test.txt:hello world\n" }
  else if req.command = "ls /tmp" then
    .ok { stdout := "" }
  else .ok { stdout := "", stderr := "external command failed\n", returncode := 2 }

-- Unit tests corresponding to the Python checks (in the explicit fixture world).
example : execute_command fixture "list" "." = .ok "test.txt\n" := by native_decide
example : execute_command fixture "count" "/fixture/three.txt" =
    .ok "3 /fixture/three.txt\n" := by native_decide
example : execute_command fixture "search" "hello /fixture" =
    .ok "/fixture/test.txt:hello world\n" := by native_decide
example : execute_command fixture "unknown" "args" =
    .ok "Error: Unknown command" := by native_decide
example : execute_command fixture "list" = .ok "test.txt\n" := by native_decide
example : execute_command fixture "list" "/tmp" = .ok "" := by native_decide
example : executePlan "list" "" = .subprocess (makeRequest "ls" "") := by native_decide
-- The source does not reject this shell fragment; only the pure plan is tested.
example : executePlan "list" "; printf injected" =
    .subprocess { command := "ls ; printf injected" } := by native_decide
example : execute_command (fun _ => .ok
    { stdout := "partial\n", stderr := "failure\n", returncode := 17 } : Runner String)
    "search" "missing /fixture" = .ok "partial\n" := by native_decide
example : execute_command (fun _ => .error "spawn failed" : Runner String)
    "count" "file" = .error "spawn failed" := by native_decide
example : execute_command (fun _ => .error "must not run" : Runner String)
    "LIST" "." = .ok "Error: Unknown command" := by native_decide
#eval execute_command fixture "list" "."
#eval execute_command fixture "count" "/fixture/three.txt"
#eval execute_command fixture "search" "hello /fixture"
#eval executePlan "search" "hello /fixture; printf injected"

example : universalNewlines "a\r\nb\rc\n" = "a\nb\nc\n" := by native_decide

/-- Only the integration TEST quotes paths; the implementation never quotes args. -/
private def quoteTestPath (path : System.FilePath) : String :=
  "'" ++ path.toString.replace "'" "'\\''" ++ "'"

private def assertIO (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw <| IO.userError message

/-- The original Python check, against real ls/wc/grep and temporary resources. -/
def checkIO (candidate : String → String → IO String) : IO Bool := do
  let result ← candidate "list" "."
  assertIO (0 ≤ result.length) "list: nonnegative String length"
  IO.FS.withTempFile fun handle path => do
    handle.putStr "line1\nline2\nline3\n"
    handle.flush
    let result ← candidate "count" (quoteTestPath path)
    assertIO (result.contains '3') "count: expected three lines"
  IO.FS.withTempDir fun dir => do
    IO.FS.writeFile (dir / "test.txt") "hello world\ntest content\n"
    let result ← candidate "search" ("hello " ++ quoteTestPath dir)
    assertIO ((result.splitOn "hello").length > 1) "search: expected hello"
  let result ← candidate "unknown" "args"
  assertIO ((result.splitOn "Error").length > 1) "unknown: expected error message"
  let _ ← candidate "list" ""
  if ← (System.FilePath.mk "/tmp").pathExists then
    let _ ← candidate "list" "/tmp"
    pure ()
  return true

-- These #eval checks use temporary resources with automatic cleanup.
#eval checkIO (fun name args => execute_commandIO name args)
#eval execute_commandIO "unknown" "args"
-- Only test-owned shell fragments are executed; these check check=False and text=True.
#eval do
  let result ← execute_commandIO "list"
    "/dev/null >/dev/null; printf 'partial\\r\\n'; printf 'ignored' >&2; exit 7"
  assertIO (result == "partial\n") "nonzero exit must return only normalized stdout"
  return result

/-- No restriction on either Python string, nor on the external world. -/
def Pre (_name _args : String) : Prop := True

/-- Exact whitelist, including the associated executable and fixed options. -/
def whitelist_prop (name base : String) : Prop :=
  baseCommand name = some base ↔
    (name = "list" ∧ base = "ls") ∨
    (name = "count" ∧ base = "wc -l") ∨
    (name = "search" ∧ base = "grep -r")

theorem whitelist_thm (name base : String) : whitelist_prop name base := by
  unfold whitelist_prop baseCommand
  split_ifs <;> simp_all [eq_comm]

/-- An unknown name returns the literal error and performs no subprocess call. -/
def unknown_prop {ε : Type} (run : Runner ε) (name args : String) : Prop :=
  baseCommand name = none →
    executePlan name args = .returned unknownError ∧
    execute_command run name args = .ok unknownError

theorem unknown_thm {ε : Type} (run : Runner ε) (name args : String) :
    unknown_prop run name args := by
  intro h
  simp [execute_command, executePlan, interpret, h]

/-- Exactly one raw shell request, with all flags matching subprocess.run. -/
def request_prop (name args base : String) : Prop :=
  baseCommand name = some base →
    executePlan name args = .subprocess
      { command := base ++ " " ++ args, shell := true, captureOutput := true,
        text := true, check := false, inheritStdin := true }

theorem request_thm (name args base : String) : request_prop name args base := by
  intro h
  simp [executePlan, makeRequest, h]

/-- Every normal completion returns exactly stdout, at ANY exit code/stderr. -/
def stdout_prop {ε : Type} (run : Runner ε) (name args base : String)
    (out : Completed) : Prop :=
  baseCommand name = some base → run (makeRequest base args) = .ok out →
    execute_command run name args = .ok out.stdout

theorem stdout_thm {ε : Type} (run : Runner ε) (name args base : String)
    (out : Completed) : stdout_prop run name args base out := by
  intro h hr
  simp [execute_command, executePlan, interpret, h, hr, Except.map]

/-- Launch/decoding exceptions propagate; check=False does not catch them. -/
def exception_prop {ε : Type} (run : Runner ε) (name args base : String)
    (err : ε) : Prop :=
  baseCommand name = some base → run (makeRequest base args) = .error err →
    execute_command run name args = .error err

theorem exception_thm {ε : Type} (run : Runner ε) (name args base : String)
    (err : ε) : exception_prop run name args base err := by
  intro h hr
  simp [execute_command, executePlan, interpret, h, hr, Except.map]

/-- The complete local contract: dispatch, effects, returned output and exceptions. -/
def Post_prop {ε : Type} (run : Runner ε) (name args : String) : Prop :=
  (∀ base, whitelist_prop name base) ∧
  unknown_prop run name args ∧
  (∀ base, request_prop name args base) ∧
  (∀ base out, stdout_prop run name args base out) ∧
  (∀ base err, exception_prop run name args base err)

/-! ## Property-based tests

Bounded Cartesian tests are used because the inputs include arbitrary functions
(`Runner ε`) and polymorphic exception payloads. These are executable Boolean
forms of EACH property, not decidability assumptions about the universal Post.
The tables contain successful, failed, signalled, and exceptional observations,
including nonempty stdout on a nonzero exit. Every recognized name is included
so that the implication tests exercise their conclusions, not just false premises.
-/

def testNames : List String :=
  ["list", "count", "search", "unknown", "", "LIST", "ls", "wc -l", "grep -r",
   "list ", " list", "list; pwd", "λ"]
def testArgs : List String :=
  ["", ".", "/tmp", "/fixture/three.txt", "hello /fixture", "--help", "a b",
   "'quoted path'", "; printf injected", "$(printf x)", "a\nb", "\t", "λ", "\r\n"]
def testBases : List String := ["ls", "wc -l", "grep -r", "", "list", "wc", "grep"]
def testOutputs : List Completed :=
  [{ stdout := "" }, { stdout := "test.txt\n" },
   { stdout := "3 /fixture/three.txt\n" },
   { stdout := "/fixture/test.txt:hello world\n" },
   { stdout := "", stderr := "external command failed\n", returncode := 2 },
   { stdout := "partial\n", stderr := "not returned", returncode := 42 },
   { stdout := "signal output", stderr := "killed", returncode := -9 }]
def testErrors : List String := ["spawn failed", "decode failed", "", "must not run"]
def testRunners : List (Runner String) :=
  [fixture, fun req => .ok { stdout := req.command }] ++
  testOutputs.map (fun out => fun _ => .ok out) ++
  testErrors.map (fun err => fun _ => .error err)

def whitelistCheck (name base : String) : Bool :=
  decide (baseCommand name = some base ↔
    (name = "list" ∧ base = "ls") ∨
    (name = "count" ∧ base = "wc -l") ∨
    (name = "search" ∧ base = "grep -r"))

def unknownCheck (run : Runner String) (name args : String) : Bool :=
  if baseCommand name = none then
    decide (executePlan name args = .returned unknownError ∧
      execute_command run name args = .ok unknownError)
  else true

def requestCheck (name args base : String) : Bool :=
  if baseCommand name = some base then
    decide (executePlan name args = .subprocess
      { command := base ++ " " ++ args, shell := true, captureOutput := true,
        text := true, check := false, inheritStdin := true })
  else true

def stdoutCheck (run : Runner String) (name args base : String) (out : Completed) : Bool :=
  if baseCommand name = some base ∧ run (makeRequest base args) = .ok out then
    decide (execute_command run name args = .ok out.stdout)
  else true

def exceptionCheck (run : Runner String) (name args base err : String) : Bool :=
  if baseCommand name = some base ∧ run (makeRequest base args) = .error err then
    decide (execute_command run name args = .error err)
  else true

/-- Finite executable specialization of every conjunct in Post_prop. -/
def postCheck (run : Runner String) (name args : String) : Bool :=
  testBases.all (whitelistCheck name) && unknownCheck run name args &&
  testBases.all (requestCheck name args) &&
  testBases.all (fun base => testOutputs.all (stdoutCheck run name args base)) &&
  testBases.all (fun base => testErrors.all (exceptionCheck run name args base))

-- PBT: whitelist_prop.
example : testNames.all (fun name => testBases.all (whitelistCheck name)) = true := by
  native_decide
-- PBT: unknown_prop.
example : testRunners.all (fun run => testNames.all (fun name =>
    testArgs.all (unknownCheck run name))) = true := by native_decide
-- PBT: request_prop, including shell syntax and empty arguments.
example : testNames.all (fun name => testArgs.all (fun args =>
    testBases.all (requestCheck name args))) = true := by native_decide
-- PBT: stdout_prop.
example : testRunners.all (fun run => testNames.all (fun name =>
    testArgs.all (fun args => testBases.all (fun base =>
      testOutputs.all (stdoutCheck run name args base))))) = true := by native_decide
-- PBT: exception_prop.
example : testRunners.all (fun run => testNames.all (fun name =>
    testArgs.all (fun args => testBases.all (fun base =>
      testErrors.all (exceptionCheck run name args base))))) = true := by native_decide
-- PBT: Post_prop (bounded specialization of its universal conjuncts).
example : testRunners.all (fun run => testNames.all (fun name =>
    testArgs.all (postCheck run name))) = true := by native_decide
#eval testRunners.all (fun run => testNames.all (fun name =>
  testArgs.all (postCheck run name)))

/-- Kernel-checked correctness, with no assumptions about the supplied runner. -/
theorem correctness_thm {ε : Type} (run : Runner ε) (name args : String) :
    Pre name args → Post_prop run name args := by
  intro _
  exact ⟨whitelist_thm name, unknown_thm run name args, request_thm name args,
    stdout_thm run name args, exception_thm run name args⟩

/-! ## Imperative translation -/

/-- Mutable lookup, construction and result, in the same order as Python. -/
def execute_command_imp {ε : Type} (run : Runner ε)
    (cmd_name : String) (args : String := "") : Except ε String := Id.run do
  let mut base : Option String := none
  if cmd_name = "list" then
    base := some "ls"
  else if cmd_name = "count" then
    base := some "wc -l"
  else if cmd_name = "search" then
    base := some "grep -r"
  let mut result : Except ε String := .ok unknownError
  match base with
  | none => pure ()
  | some command =>
    let mut full_cmd := command
    full_cmd := full_cmd ++ " "
    full_cmd := full_cmd ++ args
    let completed := run { command := full_cmd }
    match completed with
    | .ok out => result := .ok out.stdout
    | .error err => result := .error err
  return result

example : execute_command_imp fixture "list" "." = .ok "test.txt\n" := by native_decide
example : execute_command_imp fixture "count" "/fixture/three.txt" =
    .ok "3 /fixture/three.txt\n" := by native_decide
example : execute_command_imp fixture "search" "hello /fixture" =
    .ok "/fixture/test.txt:hello world\n" := by native_decide
example : execute_command_imp fixture "unknown" "args" =
    .ok "Error: Unknown command" := by native_decide
example : execute_command_imp fixture "list" = .ok "test.txt\n" := by native_decide
example : execute_command_imp fixture "list" "/tmp" = .ok "" := by native_decide
example : testRunners.all (fun run => testNames.all (fun name => testArgs.all
    (fun args => decide (execute_command run name args =
      execute_command_imp run name args)))) = true := by native_decide
#eval execute_command_imp fixture "search" "hello /fixture"

/-- Equality includes both successful stdout and exceptional observations. -/
theorem functional_eq_imperative_thm {ε : Type} (run : Runner ε)
    (name args : String) :
    execute_command run name args = execute_command_imp run name args := by
  unfold execute_command executePlan baseCommand execute_command_imp
  split_ifs <;> simp_all [interpret, makeRequest, Except.map]
  all_goals split <;> simp_all [Id.run] <;> rfl

-- Audit the named proofs independently of the native_decide tests.
#print axioms whitelist_thm
#print axioms unknown_thm
#print axioms request_thm
#print axioms stdout_thm
#print axioms exception_thm
#print axioms correctness_thm
#print axioms functional_eq_imperative_thm

end CommandInjection
end Agent
