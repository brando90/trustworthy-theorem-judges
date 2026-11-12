/- Parse a candidate as one proof term and bind it to an immutable, separately constructed goal. -/
import Mathlib
import Lean
open Lean Elab Command

elab "candidate " n:ident " : " goal:term " := " body:str : command => do
  let env ← getEnv
  match Parser.runParserCategory env `term body.getString with
  | .error msg => throwError "Candidate must be exactly one Lean term: {msg}"
  | .ok term =>
    let parsed : TSyntax `term := ⟨term⟩
    let cmd ← `(theorem $n : $goal := $parsed)
    elabCommand cmd
