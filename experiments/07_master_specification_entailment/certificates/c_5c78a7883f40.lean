import CertificateAudit
import Std
def AgentMaster (f : ((Bool × Bool) → (Bool × Bool))) : Prop := f (false, false) = (false, false)
def GoldMaster (f : ((Bool × Bool) → (Bool × Bool))) : Prop := ∀ x : (Bool × Bool), f x = (x.2, x.1)

def Coverage : Prop := ∀ f, AgentMaster f → GoldMaster f
def Nonvacuous : Prop := ∃ f, AgentMaster f
def Counterexample : Prop := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
def Inconsistent : Prop := ¬ Nonvacuous
certificate claim_Counterexample : Counterexample := "by exact \u27e8(fun x => x), (by simp [AgentMaster]), (by intro h; have hh := h (false, true); simp at hh)\u27e9"
#audit_certificate "66286b9fa2f495b0fcdb910b61c8c8daaea17ff156408484" claim_Counterexample : Counterexample
