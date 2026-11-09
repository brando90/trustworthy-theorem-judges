import CertificateAudit
import Std
def AgentMaster (f : (Bool → Bool)) : Prop := ∀ x : Bool, x = false → f x = !x
def GoldMaster (f : (Bool → Bool)) : Prop := ∀ x : Bool, f x = !x

def Coverage : Prop := ∀ f, AgentMaster f → GoldMaster f
def Nonvacuous : Prop := ∃ f, AgentMaster f
def Counterexample : Prop := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
def Inconsistent : Prop := ¬ Nonvacuous
certificate claim_Counterexample : Counterexample := "by exact \u27e8(fun _ => true), (by intro x hx; simp_all), (by intro h; have hh := h true; simp at hh)\u27e9"
#audit_certificate "80e84c3f27cff431f02842d303f4e2480a4a31a51336edda" claim_Counterexample : Counterexample
