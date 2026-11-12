import Mathlib
import Lean
open Lean Elab Command
elab "specification " n:ident " : " ty:term " := " body:str : command => do
  let env ← getEnv
  match Parser.runParserCategory env `term body.getString with
  | .error msg => throwError "Specification must be exactly one Lean term: {msg}"
  | .ok term =>
    let parsed : TSyntax `term := ⟨term⟩
    let cmd ← `(def $n : $ty := $parsed)
    elabCommand cmd
