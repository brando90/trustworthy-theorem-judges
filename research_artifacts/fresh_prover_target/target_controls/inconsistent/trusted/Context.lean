import Mathlib
namespace Natural
def GoldSpec (f : Nat → Nat) : Prop := ∀ n, f n = n
def AgentSpec (f : Nat → Nat) : Prop := False
def Coverage : Prop := ∀ f, AgentSpec f → GoldSpec f
def Nonvacuous : Prop := ∃ f, AgentSpec f
def Counterexample : Prop := ∃ f, AgentSpec f ∧ ¬ GoldSpec f
def Inconsistent : Prop := ¬ Nonvacuous
end Natural
