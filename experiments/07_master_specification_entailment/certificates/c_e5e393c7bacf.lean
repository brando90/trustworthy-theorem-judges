import CertificateAudit
import Std
def AgentMaster (f : (Bool → Bool)) : Prop := f false = true
def GoldMaster (f : (Bool → Bool)) : Prop := ∀ x : Bool, f x = !x

def Coverage : Prop := ∀ f, AgentMaster f → GoldMaster f
def Nonvacuous : Prop := ∃ f, AgentMaster f
def Counterexample : Prop := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
def Inconsistent : Prop := ¬ Nonvacuous
certificate claim_Counterexample : Counterexample := "by exact \u27e8(fun _ => true), (by simp [AgentMaster]), (by intro h; have hh := h true; simp at hh)\u27e9"
#audit_certificate "a769467f0a0595849fd331558ed00c3c8cf9f06b8726c033" claim_Counterexample : Counterexample
