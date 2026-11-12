import CertificateAudit
import Std
def AgentMaster (f : ((Bool × Bool) → (Bool × Bool))) : Prop := ∀ x : (Bool × Bool), ((x.2, x.1)) = f x
def GoldMaster (f : ((Bool × Bool) → (Bool × Bool))) : Prop := ∀ x : (Bool × Bool), f x = (x.2, x.1)

def Coverage : Prop := ∀ f, AgentMaster f → GoldMaster f
def Nonvacuous : Prop := ∃ f, AgentMaster f
def Counterexample : Prop := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
def Inconsistent : Prop := ¬ Nonvacuous
certificate claim_Coverage : Coverage := "by intro f h x; exact (h x).symm"
certificate claim_Nonvacuous : Nonvacuous := "by exact \u27e8fun x => (x.2, x.1), by intro x; rfl\u27e9"
#audit_certificate "56d4fb340b078351a7ed4a13cf491873532d99fa87cd2393" claim_Coverage : Coverage
#audit_certificate "56d4fb340b078351a7ed4a13cf491873532d99fa87cd2393" claim_Nonvacuous : Nonvacuous
