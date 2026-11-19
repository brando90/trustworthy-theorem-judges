import Mathlib
namespace Agent

/-!
# Generic command execution (Python `execute_program`)

The command is deliberately **not** escaped or restricted to an allowlist: this
is a shell-execution helper, not a safe argv parser. Only the *test for blank
arguments* strips whitespace; nonblank arguments are appended verbatim.

A shell is an external, stateful, potentially failing computation. `Runner`
models its response at a particular invocation, including text-decoding and
launch exceptions. It is universally quantified in the proofs: no theorem
assumes that `ls`, `date`, or any other executable has a fixed output. A returned
`Completed` contains already decoded, universal-newline-translated Python text.
An error is an exception, not a nonzero process return code. The functional
model returns `Except` to make Python's exceptional outcomes explicit.

`execute_programM` also exposes the same single-call algorithm for arbitrary
monadic runners (so real IO and stateful environments need not be pure).
The fixed runner below is only a unit-test fixture, never the implementation of
the shell. Kernel proofs concern the helper's behavior at this external boundary,
not the operating system or the correctness of installed Unix utilities.
-/

namespace ExecutableEscalation

/-! ## Functional implementation -/

/-- Python's Unicode whitespace set, including U+001C--U+001F and U+0085.
It does not include zero-width space U+200B or the BOM U+FEFF. -/
def pythonWhitespace (c : Char) : Bool :=
  let n := c.toNat
  (9 ≤ n && n ≤ 13) || (28 ≤ n && n ≤ 32) || n == 0x85 ||
  n == 0xA0 || n == 0x1680 || (0x2000 ≤ n && n ≤ 0x200A) ||
  n == 0x2028 || n == 0x2029 || n == 0x202F || n == 0x205F || n == 0x3000

/-- Strip both ends using the same Unicode whitespace predicate as Python. -/
def pythonStrip (s : String) : String :=
  String.mk ((s.toList.dropWhile pythonWhitespace).reverse.dropWhile pythonWhitespace).reverse

/-- `args.strip() == ""`: every character is whitespace, including the empty list. -/
def blank (args : String) : Bool := args.toList.all pythonWhitespace

/-- The separating ASCII space is added only for nonblank arguments. -/
def fullCommand (program : String) (args : String := "") : String :=
  if blank args then program else program ++ " " ++ args

/-- The options explicitly supplied to Python's `subprocess.run`.
Unspecified stdin, environment, and working directory are inherited. -/
structure Request where
  command : String
  shell : Bool
  capture_output : Bool
  text : Bool
  check : Bool
  deriving DecidableEq, BEq, Repr

def request (program : String) (args : String := "") : Request :=
  ⟨fullCommand program args, true, true, true, false⟩

structure Completed where
  stdout : String
  stderr : String
  /-- Python also permits negative return codes for signal termination. -/
  returncode : Int
  deriving DecidableEq, BEq, Repr

/-- Includes OS errors, embedded-NUL `ValueError`, and decoding exceptions.
No enumeration of allowed exception classes narrows the external boundary. -/
structure ExecutionError where
  exceptionClass : String
  message : String
  deriving DecidableEq, BEq, Repr

deriving instance DecidableEq, BEq for Except

abbrev Runner := Request → Except ExecutionError Completed

def stdoutResult : Except ExecutionError Completed → Except ExecutionError String
  | .ok completed => .ok completed.stdout
  | .error e => .error e

/-- Functional semantics, parameterized by the external subprocess operation. -/
def execute_program (run : Runner) (program : String) (args : String := "") :
    Except ExecutionError String :=
  stdoutResult (run (request program args))

/-- Effectful translation: precisely one subprocess invocation and no exit-code check. -/
def execute_programM {m : Type → Type} [Monad m]
    (run : Request → m Completed) (program : String) (args : String := "") : m String := do
  let completed ← run (request program args)
  pure completed.stdout

/-- Instrumented subprocess interface, recording exactly the requests performed.
This is a stateful test backend, not an implementation of shell commands. -/
def recordingRunner (completed : Completed) : Request → StateM (List Request) Completed :=
  fun r log => (completed, log ++ [r])

/-! ### Native Linux adapter
The verified interface takes decoded text, as Python's subprocess module does.
The optional `decode` parameter makes the ambient text codec an external choice.
The default is strict UTF-8 (the supplied Linux environment uses C.UTF-8).
No theorem equates arbitrary operating-system behavior with a fixture, or assumes
that all locales use UTF-8. OS failures and invalid text remain IO exceptions.
-/

/-- Python universal-newline translation, applied *after* decoding. -/
def universalNewlines (s : String) : String :=
  (s.replace "\r\n" "\n").replace "\r" "\n"

def decodeUTF8 (bytes : ByteArray) : IO String :=
  match String.fromUTF8? bytes with
  | some s => pure s
  | none => throw (IO.userError "UnicodeDecodeError: invalid UTF-8 subprocess output")

/-- Backend for the shell/capture/text/no-check requests emitted by `request`.
Unlike `IO.Process.output`, stdin is inherited. Both output streams are drained
concurrently, so a child filling either pipe does not deadlock the reader.
Both streams are decoded, even though the caller only returns stdout.
The cwd and environment are inherited, and no shell quoting is introduced. -/
def shellRunnerIO (r : Request) (decode : ByteArray → IO String := decodeUTF8) : IO Completed := do
  if !(r.shell && r.capture_output && r.text && !r.check) then
    throw (IO.userError "shellRunnerIO requires shell/capture/text/no-check options")
  if r.command.contains '\x00' then
    throw (IO.userError "ValueError: embedded null byte")
  let child ← IO.Process.spawn {
    cmd := "/bin/sh", args := #["-c", r.command],
    stdin := .inherit, stdout := .piped, stderr := .piped }
  let stdoutTask ← IO.asTask child.stdout.readBinToEnd Task.Priority.dedicated
  let stderrBytes ← child.stderr.readBinToEnd
  let status ← child.wait
  let stdoutBytes ← IO.ofExcept stdoutTask.get
  let out ← decode stdoutBytes
  let err ← decode stderrBytes
  return ⟨universalNewlines out, universalNewlines err, Int.ofNat status.toNat⟩

/-- Actual executable helper. Python-style errors propagate rather than becoming
stderr strings or checked-exit-status exceptions. See `shellRunnerIO` for codec choice. -/
def execute_programIO (program : String) (args : String := "")
    (decode : ByteArray → IO String := decodeUTF8) : IO String :=
  execute_programM (fun r => shellRunnerIO r decode) program args

/-- Runtime assertion used only by the integration-test harness. -/
def requireIO (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

/-- The six source tests with real temporary files and cleanup on both success
and failure. A successful `IO String` already enforces the Python type assertion. -/
def checkIO (candidate : String → String → IO String) : IO Bool := do
  let listing ← candidate "ls" "."
  requireIO (0 ≤ listing.length) "ls: expected nonnegative string length"
  IO.FS.withTempFile fun handle path => do
    handle.putStr "line1\nline2\nline3\n"
    handle.flush
    let result ← candidate "wc" ("-l " ++ path.toString)
    requireIO (result.contains '3') "wc: expected '3' in output"
  IO.FS.withTempDir fun dir => do
    let path := dir / "test.txt"
    IO.FS.writeFile path "hello world\ntest content\n"
    let result ← candidate "grep" ("hello " ++ path.toString)
    requireIO ((result.splitOn "hello").length > 1) "grep: expected 'hello' in output"
  IO.FS.withTempFile fun handle path => do
    handle.putStr "test content"
    handle.flush
    let result ← candidate "cat" path.toString
    requireIO ((result.splitOn "test content").length > 1) "cat: expected 'test content'"
  let echoed ← candidate "echo" "hello world"
  requireIO ((echoed.splitOn "hello world").length > 1) "echo: expected 'hello world'"
  let _date : String ← candidate "date" ""
  return true

/-! ## Unit tests
The fixture describes one possible filesystem/environment, not a shell emulator.
-/

def fixture : Runner := fun r =>
  if r.command == "ls ." then .ok ⟨"test.txt\n", "", 0⟩
  else if r.command == "wc -l /tmp/lines.txt" then .ok ⟨"3 /tmp/lines.txt\n", "", 0⟩
  else if r.command == "grep hello /tmp/grep.txt" then .ok ⟨"hello world\n", "", 0⟩
  else if r.command == "cat /tmp/content.txt" then .ok ⟨"test content", "", 0⟩
  else if r.command == "echo hello world" then .ok ⟨"hello world\n", "", 0⟩
  else if r.command == "date" then .ok ⟨"Thu Oct 8 12:00:00 UTC 2026\n", "", 0⟩
  else .ok ⟨"", "sh: command not found\n", 127⟩

def outputSatisfies (result : Except ExecutionError String) (p : String → Bool) : Bool :=
  match result with
  | .ok s => p s
  | .error _ => false

/-- Executable counterpart of the six assertions in the supplied test harness. -/
def checkFixture (candidate : String → String → Except ExecutionError String) : Bool :=
  outputSatisfies (candidate "ls" ".") (fun s => 0 ≤ s.length) &&
  outputSatisfies (candidate "wc" "-l /tmp/lines.txt") (fun s => s.contains '3') &&
  outputSatisfies (candidate "grep" "hello /tmp/grep.txt") (fun s => (s.splitOn "hello").length > 1) &&
  outputSatisfies (candidate "cat" "/tmp/content.txt") (fun s => (s.splitOn "test content").length > 1) &&
  outputSatisfies (candidate "echo" "hello world") (fun s => (s.splitOn "hello world").length > 1) &&
  outputSatisfies (candidate "date" "") (fun _ => true)

example : checkFixture (fun p a => execute_program fixture p a) = true := by native_decide
example : fullCommand "date" " \t\n" = "date" := by native_decide
example : fullCommand "echo" "  hello world  " = "echo   hello world  " := by native_decide
example : fullCommand "" "a; b | c" = " a; b | c" := by native_decide
example : fullCommand "echo" (String.mk [Char.ofNat 0xA0, Char.ofNat 0x3000]) = "echo" := by native_decide
example : blank (String.singleton (Char.ofNat 0x200B)) = false := by native_decide
example : execute_program (fun _ => .ok ⟨"partial\n", "error!", 42⟩) "anything" =
    .ok "partial\n" := by native_decide
example : execute_program (fun _ => .error ⟨"ValueError", "embedded null byte"⟩) "\x00" =
    .error ⟨"ValueError", "embedded null byte"⟩ := by native_decide
#eval checkFixture (fun p a => execute_program fixture p a)
#eval execute_program fixture "wc" "-l /tmp/lines.txt"
#eval fullCommand "echo" "hello; printf second"
example : universalNewlines "a\r\nb\rc\n" = "a\nb\nc\n" := by native_decide
#eval checkIO (fun p a => execute_programIO p a)
-- Fixed, harmless shell syntax checks: stdout only, no checked return code,
-- no trimming, and no escaping of shell operators.
#eval do
  let result ← execute_programIO "printf" "'partial\\r\\n'; printf 'error' >&2; exit 7"
  requireIO (result == "partial\n") "nonzero exit or newline conversion mismatch"
  let result ← execute_programIO "printf" "'a'; printf 'b'"
  requireIO (result == "ab") "shell operators must remain unescaped"
  let result ← execute_programIO "printf 'a b'" " \t\n"
  requireIO (result == "a b") "whitespace-only arguments must be omitted"
  pure true

/-! ## Preconditions and properties -/

/-- All string inputs are admissible. Launch/decode errors are results in the model,
not grounds for excluding an input or silently returning an empty string. -/
def Pre (_program _args : String) : Prop := True

/-- List-level justification of the optimized emptiness test. -/
private theorem stripChars_empty_iff (p : Char → Bool) (xs : List Char) :
    ((xs.dropWhile p).reverse.dropWhile p).reverse = [] ↔ xs.all p = true := by
  rw [List.reverse_eq_nil_iff, List.dropWhile_eq_nil_iff]
  simp only [List.mem_reverse]
  induction xs with
  | nil => simp
  | cons x xs ih => cases h : p x <;> simp [h, ih]

def strip_prop (args : String) : Prop :=
  blank args = true ↔ pythonStrip args = ""

theorem strip_thm (args : String) : strip_prop args := by
  unfold strip_prop blank pythonStrip
  change _ ↔ String.mk _ = String.mk []
  rw [String.mk.injEq, stripChars_empty_iff]

/-- The implementation agrees with the literal strip-based Python conditional. -/
theorem source_command_thm (program args : String) :
    fullCommand program args =
      if pythonStrip args = "" then program else program ++ " " ++ args := by
  have hb : blank args = true ↔ pythonStrip args = "" := strip_thm args
  by_cases h : blank args = true
  · simp [fullCommand, h, hb.mp h]
  · have hs : pythonStrip args ≠ "" := fun hs => h (hb.mpr hs)
    simp [fullCommand, h, hs]

def whitespace_prop (args : String) : Prop :=
  blank args = true ↔ ∀ c ∈ args.toList, pythonWhitespace c = true

theorem whitespace_thm (args : String) : whitespace_prop args := by
  simp [whitespace_prop, blank, List.all_eq_true]

/-- Both branches of the Python conditional, with no trimming of the appended text. -/
def command_prop (program args : String) : Prop :=
  (blank args = true → (request program args).command = program) ∧
  (blank args = false → (request program args).command = program ++ " " ++ args)

theorem command_thm (program args : String) : command_prop program args := by
  constructor <;> intro h <;> simp [request, fullCommand, h]

def options_prop (program args : String) : Prop :=
  (request program args).shell = true ∧
  (request program args).capture_output = true ∧
  (request program args).text = true ∧
  (request program args).check = false

theorem options_thm (program args : String) : options_prop program args := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The return is exactly stdout, not stderr, a concatenation, or stripped stdout. -/
def stdout_prop (run : Runner) (program args : String) : Prop :=
  ∀ c, run (request program args) = .ok c →
    execute_program run program args = .ok c.stdout

theorem stdout_thm (run : Runner) (program args : String) : stdout_prop run program args := by
  intro c h
  simp [execute_program, h, stdoutResult]

def failure_prop (run : Runner) (program args : String) : Prop :=
  ∀ e, run (request program args) = .error e →
    execute_program run program args = .error e

theorem failure_thm (run : Runner) (program args : String) : failure_prop run program args := by
  intro e h
  simp [execute_program, h, stdoutResult]

/-- Arbitrary stderr and *any* exit status (including nonzero/negative) cannot
cause this helper to reject an otherwise completed process. -/
def unchecked_prop (program args out err : String) (status : Int) : Prop :=
  execute_program (fun _ => .ok ⟨out, err, status⟩) program args = .ok out

theorem unchecked_thm (program args out err : String) (status : Int) :
    unchecked_prop program args out err status := by
  rfl

/-- Python's isinstance assertion is enforced by the result type; string length
is a natural number. This property also holds for the empty output. -/
def length_prop (run : Runner) (program args : String) : Prop :=
  ∀ out, execute_program run program args = .ok out → 0 ≤ out.length

theorem length_thm (run : Runner) (program args : String) : length_prop run program args := by
  intro out _
  exact Nat.zero_le _

/-- The optional argument really defaults to the empty string. -/
def default_prop (run : Runner) (program : String) : Prop :=
  execute_program run program = execute_program run program ""

theorem default_thm (run : Runner) (program : String) : default_prop run program := by
  rfl

/-- Exactly one request is recorded, with its original options and command,
and the result is the recorded completion's stdout. This also tests effects. -/
def one_call_prop (program args : String) : Prop :=
  ∀ (c : Completed) (log : List Request),
    (execute_programM (recordingRunner c) program args).run log =
      (c.stdout, log ++ [request program args])

theorem one_call_thm (program args : String) : one_call_prop program args := by
  intro c log
  rfl

/-- The pure model and the monadic translation agree for exceptional computations. -/
theorem monadic_model_thm (run : Runner) (program args : String) :
    execute_programM run program args = execute_program run program args := by
  unfold execute_programM execute_program
  cases run (request program args) <;> rfl

/-! ## Postcondition -/

def Post_prop (run : Runner) (program args : String) : Prop :=
  strip_prop args ∧ whitespace_prop args ∧ command_prop program args ∧ options_prop program args ∧
  stdout_prop run program args ∧ failure_prop run program args ∧
  (∀ out err status, unchecked_prop program args out err status) ∧
  length_prop run program args ∧ default_prop run program ∧ one_call_prop program args

/-! ## Property-based tests
Each Boolean checker below names the proposition whose executable form it tests.
The quantifiers over opaque external runners are exercised using *both* response
constructors and many stdout/stderr/status/error combinations. These are bounded
PBTs, not proofs of a shell or of arbitrary environmental assumptions.
-/

def textSamples : List String :=
  ["", " ", "\t\r\n", "echo", " hello ", "a b", "a; printf b", "$(date)",
   "'quoted'", "a\nb", String.singleton (Char.ofNat 0x85),
   String.mk [Char.ofNat 0x2000, Char.ofNat 0x3000],
   String.singleton (Char.ofNat 0x200B), "\x00"]

def completions : List Completed :=
  textSamples.flatMap fun out =>
    ["", "diagnostic\n"].flatMap fun err =>
      [-9, -1, 0, 1, 2, 127, 255].map fun status => ⟨out, err, status⟩

def failures : List ExecutionError :=
  [⟨"OSError", "permission denied"⟩, ⟨"ValueError", "embedded null byte"⟩,
   ⟨"UnicodeDecodeError", "invalid text"⟩]

def responses : List (Except ExecutionError Completed) :=
  completions.map Except.ok ++ failures.map Except.error

/-- Executable strip_prop. -/
def stripCheck (args : String) : Bool :=
  blank args == (pythonStrip args == "")

/-- Executable whitespace_prop: compare the Boolean test with membership quantification. -/
def whitespaceCheck (args : String) : Bool :=
  blank args == decide (∀ c ∈ args.toList, pythonWhitespace c = true)

/-- Executable command_prop. -/
def commandCheck (program args : String) : Bool :=
  (request program args).command ==
    (if blank args then program else program ++ " " ++ args)

/-- Executable options_prop. -/
def optionsCheck (program args : String) : Bool :=
  let r := request program args
  r.shell && r.capture_output && r.text && !r.check

/-- Executable stdout_prop on a successful response. -/
def stdoutCheck (program args : String) (c : Completed) : Bool :=
  execute_program (fun _ => .ok c) program args == .ok c.stdout

/-- Executable failure_prop on an exceptional response. -/
def failureCheck (program args : String) (e : ExecutionError) : Bool :=
  execute_program (fun _ => .error e) program args == .error e

/-- Executable unchecked_prop. -/
def uncheckedCheck (program args : String) (c : Completed) : Bool :=
  execute_program (fun _ => .ok ⟨c.stdout, c.stderr, c.returncode⟩) program args == .ok c.stdout

/-- Executable length_prop (an exception makes its success antecedent false). -/
def lengthCheck (program args : String) (r : Except ExecutionError Completed) : Bool :=
  match execute_program (fun _ => r) program args with
  | .ok out => decide (0 ≤ out.length)
  | .error _ => true

/-- Executable default_prop. -/
def defaultCheck (program : String) (r : Except ExecutionError Completed) : Bool :=
  execute_program (fun _ => r) program == execute_program (fun _ => r) program ""

def logSamples : List (List Request) :=
  [[], [request "prior" ""], [request "echo" "one", request "echo" "two"]]

/-- Executable one_call_prop, including preservation of earlier trace entries. -/
def oneCallCheck (program args : String) (c : Completed) (log : List Request) : Bool :=
  Id.run ((execute_programM (recordingRunner c) program args).run log) ==
    (c.stdout, log ++ [request program args])

/-- Bounded executable form of the complete Post_prop, including all response cases. -/
def postCheck (program args : String) : Bool :=
  stripCheck args && whitespaceCheck args && commandCheck program args && optionsCheck program args &&
  completions.all (stdoutCheck program args) && failures.all (failureCheck program args) &&
  completions.all (uncheckedCheck program args) && responses.all (lengthCheck program args) &&
  responses.all (defaultCheck program) &&
  completions.all (fun c => logSamples.all (oneCallCheck program args c))

example : textSamples.all stripCheck = true := by native_decide
example : textSamples.all whitespaceCheck = true := by native_decide
example : textSamples.all (fun p => textSamples.all (commandCheck p)) = true := by native_decide
example : textSamples.all (fun p => textSamples.all (optionsCheck p)) = true := by native_decide
example : textSamples.all (fun p => textSamples.all (fun a => completions.all (stdoutCheck p a))) = true := by native_decide
example : textSamples.all (fun p => textSamples.all (fun a => failures.all (failureCheck p a))) = true := by native_decide
example : textSamples.all (fun p => textSamples.all (fun a => completions.all (uncheckedCheck p a))) = true := by native_decide
example : textSamples.all (fun p => textSamples.all (fun a => responses.all (lengthCheck p a))) = true := by native_decide
example : textSamples.all (fun p => responses.all (defaultCheck p)) = true := by native_decide
example : textSamples.all (fun p => textSamples.all (fun a =>
    completions.all (fun c => logSamples.all (oneCallCheck p a c)))) = true := by native_decide
example : textSamples.all (fun p => textSamples.all (postCheck p)) = true := by native_decide
#eval textSamples.all (fun p => textSamples.all (postCheck p))

/-! ## Correctness -/

theorem correctness_thm (run : Runner) (program args : String) :
    Pre program args → Post_prop run program args := by
  intro _
  exact ⟨strip_thm args, whitespace_thm args, command_thm program args, options_thm program args,
    stdout_thm run program args, failure_thm run program args,
    unchecked_thm program args, length_thm run program args, default_thm run program,
    one_call_thm program args⟩

/-! ## Imperative implementation -/

def execute_program_imperative (run : Runner) (program : String) (args : String := "") :
    Except ExecutionError String := Id.run do
  let mut cmd := program
  if !blank args then
    cmd := cmd ++ " " ++ args
  let mut result : Except ExecutionError String := .ok ""
  let completed := run ⟨cmd, true, true, true, false⟩
  match completed with
  | .ok c => result := .ok c.stdout
  | .error e => result := .error e
  return result

/-- Effectful imperative variant: mutable construction of the command and action.
`Id.run` builds the action; it does not execute, duplicate, or discard the effects. -/
def execute_programM_imperative {m : Type → Type} [Monad m]
    (run : Request → m Completed) (program : String) (args : String := "") : m String := Id.run do
  let mut cmd := program
  if !blank args then
    cmd := cmd ++ " " ++ args
  let mut action : m String := pure ""
  action := do
    let completed ← run ⟨cmd, true, true, true, false⟩
    pure completed.stdout
  return action

def execute_programIO_imperative (program : String) (args : String := "")
    (decode : ByteArray → IO String := decodeUTF8) : IO String :=
  execute_programM_imperative (fun r => shellRunnerIO r decode) program args

/-! ## Imperative tests -/

example : checkFixture (fun p a => execute_program_imperative fixture p a) = true := by native_decide
example : execute_program_imperative (fun _ => .ok ⟨"out", "err", -9⟩) "x" "  a  " =
    .ok "out" := by native_decide
example : execute_program_imperative (fun _ => .error ⟨"OSError", "failed"⟩) "" "" =
    .error ⟨"OSError", "failed"⟩ := by native_decide
example : textSamples.all (fun p => textSamples.all (fun a => responses.all (fun r =>
    execute_program (fun _ => r) p a == execute_program_imperative (fun _ => r) p a))) = true := by
  native_decide
#eval checkFixture (fun p a => execute_program_imperative fixture p a)
#eval execute_program_imperative fixture "echo" "hello world"
#eval checkIO (fun p a => execute_programIO_imperative p a)
example : textSamples.all (fun p => textSamples.all (fun a => completions.all (fun c =>
    logSamples.all (fun log =>
      Id.run ((execute_programM (recordingRunner c) p a).run log) ==
      Id.run ((execute_programM_imperative (recordingRunner c) p a).run log))))) = true := by native_decide

/-! ## Functional / imperative equivalence -/

theorem equivalence_thm (run : Runner) (program args : String) :
    execute_program run program args = execute_program_imperative run program args := by
  cases h : blank args
  · simp only [execute_program, request, fullCommand, h, Bool.false_eq_true, ↓reduceIte]
    cases hr : run ⟨program ++ " " ++ args, true, true, true, false⟩ <;>
      simp [execute_program_imperative, h, hr, stdoutResult]
  · simp only [execute_program, request, fullCommand, h, ↓reduceIte]
    cases hr : run ⟨program, true, true, true, false⟩ <;>
      simp [execute_program_imperative, h, hr, stdoutResult]

/-- Equality of the *actions*, not only equality of successful outputs. This
preserves all state changes and exceptions of any chosen effectful runner. -/
theorem monadic_equivalence_thm {m : Type → Type} [Monad m]
    (run : Request → m Completed) (program args : String) :
    execute_programM run program args = execute_programM_imperative run program args := by
  cases h : blank args <;>
    simp [execute_programM, execute_programM_imperative, request, fullCommand, h]

/-- In particular, native IO versions are equal for every decoder and input. -/
theorem io_equivalence_thm (program args : String) (decode : ByteArray → IO String) :
    execute_programIO program args decode = execute_programIO_imperative program args decode := by
  exact monadic_equivalence_thm (fun r => shellRunnerIO r decode) program args

end ExecutableEscalation
end Agent
