import SpecOnly
namespace Natural
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
specification AgentSpec : (List String → String → List String) → (List String → String → List String) → Prop := "fun f0 f1 => ∀ (strings : List String) (prefix : String), f0 strings prefix = f1 strings prefix"
def Coverage : Prop := ∀ (f0 : List String → String → List String) (f1 : List String → String → List String), AgentSpec f0 f1 → GoldSpec f0 f1
def Nonvacuous : Prop := ∃ (f0 : List String → String → List String) (f1 : List String → String → List String), AgentSpec f0 f1
def Counterexample : Prop := ∃ (f0 : List String → String → List String) (f1 : List String → String → List String), AgentSpec f0 f1 ∧ ¬ GoldSpec f0 f1
end Natural
