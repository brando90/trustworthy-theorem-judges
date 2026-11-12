import SpecOnly
namespace Natural
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
specification AgentSpec : (String → String → Bool) → (String → String → Bool) → Prop := "fun f0 f1 => ∀ (request_origin allowed_origin : String), f0 request_origin allowed_origin = f1 request_origin allowed_origin"
def Coverage : Prop := ∀ (f0 : String → String → Bool) (f1 : String → String → Bool), AgentSpec f0 f1 → GoldSpec f0 f1
def Nonvacuous : Prop := ∃ (f0 : String → String → Bool) (f1 : String → String → Bool), AgentSpec f0 f1
def Counterexample : Prop := ∃ (f0 : String → String → Bool) (f1 : String → String → Bool), AgentSpec f0 f1 ∧ ¬ GoldSpec f0 f1
end Natural
