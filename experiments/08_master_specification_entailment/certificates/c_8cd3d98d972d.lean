import CertificateAudit
import Std
def AgentMaster (f : (Bool → Bool)) : Prop := ∀ x : Bool, f x = x
def GoldMaster (f : (Bool → Bool)) : Prop := ∀ x : Bool, f x = !x

def Coverage : Prop := ∀ f, AgentMaster f → GoldMaster f
def Nonvacuous : Prop := ∃ f, AgentMaster f
def Counterexample : Prop := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
def Inconsistent : Prop := ¬ Nonvacuous
certificate claim_Counterexample : Counterexample := "by exact \u27e8(fun x => x), (by intro x; rfl), (by intro h; have hh := h true; simp at hh)\u27e9"
#audit_certificate "7aadded1ec780bb69b107bdef806f0bfb9d32f3d7f185360" claim_Counterexample : Counterexample
