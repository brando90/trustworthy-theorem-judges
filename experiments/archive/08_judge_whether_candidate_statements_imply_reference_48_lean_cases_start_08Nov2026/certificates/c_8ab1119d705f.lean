import CertificateAudit
import Std
def AgentMaster (f : (Int → Int)) : Prop := ∀ x : Int, (-x) = f x
def GoldMaster (f : (Int → Int)) : Prop := ∀ x : Int, f x = -x

def Coverage : Prop := ∀ f, AgentMaster f → GoldMaster f
def Nonvacuous : Prop := ∃ f, AgentMaster f
def Counterexample : Prop := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
def Inconsistent : Prop := ¬ Nonvacuous
certificate claim_Coverage : Coverage := "by intro f h x; exact (h x).symm"
certificate claim_Nonvacuous : Nonvacuous := "by exact \u27e8fun x => -x, by intro x; rfl\u27e9"
#audit_certificate "cb2e270aefa8d6dab7441114116e56863f364027a9be84df" claim_Coverage : Coverage
#audit_certificate "cb2e270aefa8d6dab7441114116e56863f364027a9be84df" claim_Nonvacuous : Nonvacuous
