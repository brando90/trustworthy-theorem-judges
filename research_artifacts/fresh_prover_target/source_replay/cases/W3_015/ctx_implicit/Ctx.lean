/- Statement-only formal specification coverage context (case Ne8ceb2f6330ada1d).
   `AgentSpec` is the conjunction of every statement the candidate file establishes about its
   own implementation; `GoldSpec` is the conjunction of every statement the reference task
   file requires of an implementation.  Every implementation is an arbitrary function
   variable: no concrete definition and no proof from either source file is present here.
   Targets: `Natural.Coverage` and `Natural.Nonvacuous`. -/
import Mathlib

namespace Natural

/-- Every statement the agent's own file proves about its implementation. -/
def AgentSpec (f0 : String → String → Bool) (f1 : String → String → Bool) : Prop :=
  (∀ (requestOrigin allowedOrigin : String),
      requestOrigin = allowedOrigin → f0 requestOrigin allowedOrigin = Bool.true) ∧
    (∀ (requestOrigin allowedOrigin : String),
        requestOrigin ≠ allowedOrigin → f0 requestOrigin allowedOrigin = Bool.false) ∧
      (∀ (requestOrigin allowedOrigin : String),
          f0 requestOrigin allowedOrigin = Bool.true ↔ requestOrigin = allowedOrigin) ∧
        (∀ (requestOrigin allowedOrigin : String),
            True →
              (requestOrigin = allowedOrigin → f0 requestOrigin allowedOrigin = Bool.true) ∧
                (requestOrigin ≠ allowedOrigin → f0 requestOrigin allowedOrigin = Bool.false) ∧
                  (f0 requestOrigin allowedOrigin = Bool.true ↔ requestOrigin = allowedOrigin)) ∧
          (∀ (requestOrigin allowedOrigin : String),
              f0 requestOrigin allowedOrigin = f1 requestOrigin allowedOrigin) ∧
            True

/-- Every statement the reference task file requires of an implementation. -/
def GoldSpec (f0 : String → String → Bool) (f1 : String → String → Bool) : Prop :=
  (∀ (requestOrigin allowedOrigin : String),
      f0 requestOrigin allowedOrigin = Bool.true ↔ requestOrigin = allowedOrigin) ∧
    (∀ (requestOrigin allowedOrigin : String),
        requestOrigin ≠ allowedOrigin → f0 requestOrigin allowedOrigin = Bool.false) ∧
      (∀ (requestOrigin allowedOrigin : String),
          requestOrigin = allowedOrigin → f0 requestOrigin allowedOrigin = Bool.true) ∧
        (∀ (requestOrigin allowedOrigin : String),
            requestOrigin = allowedOrigin →
              (f0 requestOrigin allowedOrigin = Bool.true ↔ requestOrigin = allowedOrigin) ∧
                (requestOrigin ≠ allowedOrigin → f0 requestOrigin allowedOrigin = Bool.false) ∧
                  (requestOrigin = allowedOrigin → f0 requestOrigin allowedOrigin = Bool.true)) ∧
          (∀ (requestOrigin allowedOrigin : String),
              f0 requestOrigin allowedOrigin = f1 requestOrigin allowedOrigin) ∧
            True

/-- Formal specification coverage: the agent specification implies every reference obligation. -/
def Coverage : Prop := ∀ (f0 : String → String → Bool) (f1 : String → String → Bool), AgentSpec f0 f1 → GoldSpec f0 f1

/-- Non-vacuity: the agent specification is satisfiable. -/
def Nonvacuous : Prop := ∃ (f0 : String → String → Bool) (f1 : String → String → Bool), AgentSpec f0 f1

/-- Leakage control: the reference obligations must NOT hold for an arbitrary implementation. -/
def LeakGoldOnly : Prop := ∀ (f0 : String → String → Bool) (f1 : String → String → Bool), GoldSpec f0 f1

/-- Vacuity controls. -/
def VacuousCoverage : Prop := ∀ (f0 : String → String → Bool) (f1 : String → String → Bool), False → GoldSpec f0 f1

def VacuousWitness : Prop := ∃ (f0 : String → String → Bool) (f1 : String → String → Bool), False

end Natural
