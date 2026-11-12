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
specification AgentSpec : (Bool → Bool → Bool) → (Bool → Bool → Bool) → Prop := "fun f0 f1 => fun f0 f1 => (f0 True False = True) ∧ (f0 True True = False) ∧ (f0 False False = False) ∧ (f0 False True = False) ∧ (f1 True False = True) ∧ (f1 True True = False) ∧ (f1 False False = False) ∧ (f1 False True = False) ∧ (f0 = f1)"
def Coverage : Prop := ∀ (f0 : Bool → Bool → Bool) (f1 : Bool → Bool → Bool), AgentSpec f0 f1 → GoldSpec f0 f1
def Nonvacuous : Prop := ∃ (f0 : Bool → Bool → Bool) (f1 : Bool → Bool → Bool), AgentSpec f0 f1
def Counterexample : Prop := ∃ (f0 : Bool → Bool → Bool) (f1 : Bool → Bool → Bool), AgentSpec f0 f1 ∧ ¬ GoldSpec f0 f1
end Natural
