/- Statement-only formal specification coverage context (case Ne579f226b7a3aa9a).
   `AgentSpec` is the conjunction of every statement the candidate file establishes about its
   own implementation; `GoldSpec` is the conjunction of every statement the reference task
   file requires of an implementation.  Every implementation is an arbitrary function
   variable: no concrete definition and no proof from either source file is present here.
   Targets: `Natural.Coverage` and `Natural.Nonvacuous`. -/
import Mathlib

namespace Natural

/-- Every statement the agent's own file proves about its implementation. -/
def AgentSpec (f0 : List String → String → List String) (f1 : List String → String → List String) : Prop :=
  (∀ (strings : List String) (pre string : String),
      string ∈ f0 strings pre ↔ string ∈ strings ∧ String.startsWith string pre = Bool.true) ∧
    (∀ (strings : List String) (pre : String),
        f0 strings pre = List.filter (fun string => String.startsWith string pre) strings) ∧
      (∀ (strings : List String) (pre : String),
          True →
            (∀ (string : String),
                string ∈ f0 strings pre ↔
                  string ∈ strings ∧ String.startsWith string pre = Bool.true) ∧
              f0 strings pre = List.filter (fun string => String.startsWith string pre) strings) ∧
        (∀ (strings acc : List String) (pre : String),
            Id.run
                (have result := acc;
                do
                let r ←
                  ForIn.forIn strings result fun string r =>
                      have result := r;
                      if String.startsWith string pre = Bool.true then
                        have result := result ++ [string];
                        do
                        Pure.pure PUnit.unit
                        Pure.pure (ForInStep.yield result)
                      else do
                        Pure.pure PUnit.unit
                        Pure.pure (ForInStep.yield result)
                have result : List String := r
                Pure.pure result) =
              acc ++ f0 strings pre) ∧
          (∀ (strings : List String) (pre : String), f0 strings pre = f1 strings pre) ∧ True

/-- Every statement the reference task file requires of an implementation. -/
def GoldSpec (f0 : List String → String → List String) (f1 : List String → String → List String) : Prop :=
  (∀ (p : String), f0 [] p = []) ∧
    (∀ (xs : List String), f0 xs "" = xs) ∧
      (∀ (xs : List String) (p s : String), s ∈ f0 xs p → s ∈ xs) ∧
        (∀ (xs : List String) (p s : String), s ∈ f0 xs p → String.startsWith s p = Bool.true) ∧
          (∀ (xs : List String) (p : String), List.Sublist (f0 xs p) xs) ∧
            (∀ (xs : List String) (p : String),
                True →
                  f0 [] p = [] ∧
                    f0 xs "" = xs ∧
                      (∀ s ∈ f0 xs p, s ∈ xs) ∧
                        (∀ s ∈ f0 xs p, String.startsWith s p = Bool.true) ∧
                          List.Sublist (f0 xs p) xs) ∧
              (∀ (xs : List String) (p : String), f0 xs p = f1 xs p) ∧ True

/-- Formal specification coverage: the agent specification implies every reference obligation. -/
def Coverage : Prop := ∀ (f0 : List String → String → List String) (f1 : List String → String → List String), AgentSpec f0 f1 → GoldSpec f0 f1

/-- Non-vacuity: the agent specification is satisfiable. -/
def Nonvacuous : Prop := ∃ (f0 : List String → String → List String) (f1 : List String → String → List String), AgentSpec f0 f1

/-- Leakage control: the reference obligations must NOT hold for an arbitrary implementation. -/
def LeakGoldOnly : Prop := ∀ (f0 : List String → String → List String) (f1 : List String → String → List String), GoldSpec f0 f1

/-- Vacuity controls. -/
def VacuousCoverage : Prop := ∀ (f0 : List String → String → List String) (f1 : List String → String → List String), False → GoldSpec f0 f1

def VacuousWitness : Prop := ∃ (f0 : List String → String → List String) (f1 : List String → String → List String), False

end Natural
