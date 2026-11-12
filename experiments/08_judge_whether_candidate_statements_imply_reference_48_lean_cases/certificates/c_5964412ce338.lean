import CertificateAudit
import Std
def AgentMaster (f : (Int → Int)) : Prop := ∀ x : Int, f x = x + 1
def GoldMaster (f : (Int → Int)) : Prop := ∀ x : Int, f x = -x

def Coverage : Prop := ∀ f, AgentMaster f → GoldMaster f
def Nonvacuous : Prop := ∃ f, AgentMaster f
def Counterexample : Prop := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
def Inconsistent : Prop := ¬ Nonvacuous
certificate claim_Counterexample : Counterexample := "by exact \u27e8(fun x => x + 1), (by intro x; rfl), (by intro h; have hh := h 0; simp at hh)\u27e9"
#audit_certificate "f2411aad9f4784f598213ea384482fb67cd826bf21fbfabe" claim_Counterexample : Counterexample
