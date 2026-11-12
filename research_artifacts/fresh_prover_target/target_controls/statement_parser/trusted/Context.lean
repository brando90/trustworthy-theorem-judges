import SpecOnly
namespace Natural
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
specification AgentSpec : (Bool → Bool → Bool) → (Bool → Bool → Bool) → Prop := "fun f0 f1 => (∀ (isRevoked : Bool), isRevoked = Bool.true → f0 Bool.true isRevoked = Bool.false) ∧\n    (∀ (isRevoked : Bool), f0 Bool.false isRevoked = Bool.false) ∧\n      (∀ (isRevoked : Bool), isRevoked = Bool.false → f0 Bool.true isRevoked = Bool.true) ∧\n        (∀ (hasDelegation isRevoked : Bool),\n            hasDelegation = Bool.true ∧ isRevoked = Bool.false →\n              (isRevoked = Bool.true → f0 Bool.true isRevoked = Bool.false) ∧\n                f0 Bool.false isRevoked = Bool.false ∧\n                  (isRevoked = Bool.false → f0 Bool.true isRevoked = Bool.true)) ∧\n          (∀ (hasDelegation isRevoked : Bool),\n              f0 hasDelegation isRevoked = f1 hasDelegation isRevoked) ∧\n            True"
def Coverage : Prop := ∀ (f0 : Bool → Bool → Bool) (f1 : Bool → Bool → Bool), AgentSpec f0 f1 → GoldSpec f0 f1
def Nonvacuous : Prop := ∃ (f0 : Bool → Bool → Bool) (f1 : Bool → Bool → Bool), AgentSpec f0 f1
def Counterexample : Prop := ∃ (f0 : Bool → Bool → Bool) (f1 : Bool → Bool → Bool), AgentSpec f0 f1 ∧ ¬ GoldSpec f0 f1
end Natural
