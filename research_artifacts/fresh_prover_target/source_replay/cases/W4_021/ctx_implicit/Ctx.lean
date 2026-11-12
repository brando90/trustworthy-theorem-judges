/- Statement-only formal specification coverage context (case Nf5f57b361b04a8c7).
   `AgentSpec` is the conjunction of every statement the candidate file establishes about its
   own implementation; `GoldSpec` is the conjunction of every statement the reference task
   file requires of an implementation.  Every implementation is an arbitrary function
   variable: no concrete definition and no proof from either source file is present here.
   Targets: `Natural.Coverage` and `Natural.Nonvacuous`. -/
import Mathlib

namespace Natural

/-- Every statement the agent's own file proves about its implementation. -/
def AgentSpec (f0 : Bool → Bool → Bool) (f1 : Bool → Bool → Bool) : Prop :=
  (∀ (hasDelegation isRevoked : Bool),
      f0 hasDelegation isRevoked = Bool.true ↔ hasDelegation = Bool.true ∧ isRevoked = Bool.false) ∧
    (∀ (hasDelegation isRevoked : Bool),
        isRevoked = Bool.true → f0 hasDelegation isRevoked = Bool.false) ∧
      (∀ (hasDelegation isRevoked : Bool),
          hasDelegation = Bool.false → f0 hasDelegation isRevoked = Bool.false) ∧
        f0 Bool.true Bool.false = Bool.true ∧
          (∀ (hasDelegation isRevoked : Bool),
              f0 hasDelegation isRevoked = (hasDelegation && !isRevoked)) ∧
            (f0 Bool.true Bool.false = Bool.true ∧
                f0 Bool.true Bool.true = Bool.false ∧
                  f0 Bool.false Bool.false = Bool.false ∧ f0 Bool.false Bool.true = Bool.false) ∧
              (∀ (hasDelegation isRevoked : Bool),
                  True →
                    (f0 hasDelegation isRevoked = Bool.true ↔
                        hasDelegation = Bool.true ∧ isRevoked = Bool.false) ∧
                      (isRevoked = Bool.true → f0 hasDelegation isRevoked = Bool.false) ∧
                        (hasDelegation = Bool.false → f0 hasDelegation isRevoked = Bool.false) ∧
                          f0 hasDelegation isRevoked = (hasDelegation && !isRevoked) ∧
                            f0 Bool.true Bool.false = Bool.true ∧
                              f0 Bool.true Bool.false = Bool.true ∧
                                f0 Bool.true Bool.true = Bool.false ∧
                                  f0 Bool.false Bool.false = Bool.false ∧
                                    f0 Bool.false Bool.true = Bool.false) ∧
                (∀ (hasDelegation isRevoked : Bool),
                    f0 hasDelegation isRevoked = f1 hasDelegation isRevoked) ∧
                  f0 = f1 ∧ True

/-- Every statement the reference task file requires of an implementation. -/
def GoldSpec (f0 : Bool → Bool → Bool) (f1 : Bool → Bool → Bool) : Prop :=
  (∀ (isRevoked : Bool), isRevoked = Bool.true → f0 Bool.true isRevoked = Bool.false) ∧
    (∀ (isRevoked : Bool), f0 Bool.false isRevoked = Bool.false) ∧
      (∀ (isRevoked : Bool), isRevoked = Bool.false → f0 Bool.true isRevoked = Bool.true) ∧
        (∀ (hasDelegation isRevoked : Bool),
            hasDelegation = Bool.true ∧ isRevoked = Bool.false →
              (isRevoked = Bool.true → f0 Bool.true isRevoked = Bool.false) ∧
                f0 Bool.false isRevoked = Bool.false ∧
                  (isRevoked = Bool.false → f0 Bool.true isRevoked = Bool.true)) ∧
          (∀ (hasDelegation isRevoked : Bool),
              f0 hasDelegation isRevoked = f1 hasDelegation isRevoked) ∧
            True

/-- Formal specification coverage: the agent specification implies every reference obligation. -/
def Coverage : Prop := ∀ (f0 : Bool → Bool → Bool) (f1 : Bool → Bool → Bool), AgentSpec f0 f1 → GoldSpec f0 f1

/-- Non-vacuity: the agent specification is satisfiable. -/
def Nonvacuous : Prop := ∃ (f0 : Bool → Bool → Bool) (f1 : Bool → Bool → Bool), AgentSpec f0 f1

/-- Leakage control: the reference obligations must NOT hold for an arbitrary implementation. -/
def LeakGoldOnly : Prop := ∀ (f0 : Bool → Bool → Bool) (f1 : Bool → Bool → Bool), GoldSpec f0 f1

/-- Vacuity controls. -/
def VacuousCoverage : Prop := ∀ (f0 : Bool → Bool → Bool) (f1 : Bool → Bool → Bool), False → GoldSpec f0 f1

def VacuousWitness : Prop := ∃ (f0 : Bool → Bool → Bool) (f1 : Bool → Bool → Bool), False

end Natural
