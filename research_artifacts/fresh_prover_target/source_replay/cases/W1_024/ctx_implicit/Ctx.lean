/- Statement-only formal specification coverage context (case Nc0e71598e6e88510).
   `AgentSpec` is the conjunction of every statement the candidate file establishes about its
   own implementation; `GoldSpec` is the conjunction of every statement the reference task
   file requires of an implementation.  Every implementation is an arbitrary function
   variable: no concrete definition and no proof from either source file is present here.
   Targets: `Natural.Coverage` and `Natural.Nonvacuous`. -/
import Mathlib

namespace Natural

/-- Every statement the agent's own file proves about its implementation. -/
def AgentSpec (f0 : String → ℕ) (f1 : String → ℕ) : Prop :=
  (∀ (s : String), f0 s = String.length s) ∧
    (∀ (s : String), s = "" → f0 s = 0) ∧
      (∀ (s : String), True → f0 s = String.length s ∧ (s = "" → f0 s = 0)) ∧
        (∀ (s : String), f0 s = f1 s) ∧ True

/-- Every statement the reference task file requires of an implementation. -/
def GoldSpec (f0 : String → ℕ) (f1 : String → ℕ) : Prop :=
  f0 "" = 0 ∧
    (∀ (c : Char), f0 { data := [c] } = 1) ∧
      (∀ (s : String), f0 s ≥ 0) ∧
        (∀ (s₁ s₂ : String), f0 (s₁ ++ s₂) = f0 s₁ + f0 s₂) ∧
          (∀ (s : String), f0 s = 0 ↔ s = "") ∧
            (∀ (s : String) (c : Char), f0 (String.push s c) = f0 s + 1) ∧
              (∀ (s : String),
                  True →
                    f0 "" = 0 ∧
                      (∀ (c : Char), f0 { data := [c] } = 1) ∧
                        f0 s ≥ 0 ∧ ∀ (s₂ : String), f0 (s ++ s₂) = f0 s + f0 s₂) ∧
                (∀ (s : String), f0 s = f1 s) ∧ True

/-- Formal specification coverage: the agent specification implies every reference obligation. -/
def Coverage : Prop := ∀ (f0 : String → ℕ) (f1 : String → ℕ), AgentSpec f0 f1 → GoldSpec f0 f1

/-- Non-vacuity: the agent specification is satisfiable. -/
def Nonvacuous : Prop := ∃ (f0 : String → ℕ) (f1 : String → ℕ), AgentSpec f0 f1

/-- Leakage control: the reference obligations must NOT hold for an arbitrary implementation. -/
def LeakGoldOnly : Prop := ∀ (f0 : String → ℕ) (f1 : String → ℕ), GoldSpec f0 f1

/-- Vacuity controls. -/
def VacuousCoverage : Prop := ∀ (f0 : String → ℕ) (f1 : String → ℕ), False → GoldSpec f0 f1

def VacuousWitness : Prop := ∃ (f0 : String → ℕ) (f1 : String → ℕ), False

end Natural
