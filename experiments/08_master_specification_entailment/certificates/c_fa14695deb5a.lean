import CertificateAudit
import Std
def AgentMaster (f : ((List Nat) → Nat)) : Prop := f [] = 0
def GoldMaster (f : ((List Nat) → Nat)) : Prop := ∀ x : (List Nat), f x = x.length

def Coverage : Prop := ∀ f, AgentMaster f → GoldMaster f
def Nonvacuous : Prop := ∃ f, AgentMaster f
def Counterexample : Prop := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
def Inconsistent : Prop := ¬ Nonvacuous
certificate claim_Counterexample : Counterexample := "by exact \u27e8(fun _ => 0), (by simp [AgentMaster]), (by intro h; have hh := h [0]; simp at hh)\u27e9"
#audit_certificate "09e2145e5e0a9973fd1eb89d0e95de25ad6c626b47e4ee9c" claim_Counterexample : Counterexample
