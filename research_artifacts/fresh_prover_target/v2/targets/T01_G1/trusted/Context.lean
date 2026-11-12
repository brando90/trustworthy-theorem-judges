import SpecOnly
namespace Natural
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
specification AgentSpec : (String → ℕ) → (String → ℕ) → Prop := "fun f0 f1 => ∀ s : String, f0 s = f1 s"
def Coverage : Prop := ∀ (f0 : String → ℕ) (f1 : String → ℕ), AgentSpec f0 f1 → GoldSpec f0 f1
def Nonvacuous : Prop := ∃ (f0 : String → ℕ) (f1 : String → ℕ), AgentSpec f0 f1
def Counterexample : Prop := ∃ (f0 : String → ℕ) (f1 : String → ℕ), AgentSpec f0 f1 ∧ ¬ GoldSpec f0 f1
end Natural
