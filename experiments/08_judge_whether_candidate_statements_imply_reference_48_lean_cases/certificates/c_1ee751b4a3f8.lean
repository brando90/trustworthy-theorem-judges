import CertificateAudit
import Std
def AgentMaster (f : (Int → Int)) : Prop := ∀ x : Int, f x = -x
def GoldMaster (f : (Int → Int)) : Prop := ∀ x : Int, f x = -x

def Coverage : Prop := ∀ f, AgentMaster f → GoldMaster f
def Nonvacuous : Prop := ∃ f, AgentMaster f
def Counterexample : Prop := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
def Inconsistent : Prop := ¬ Nonvacuous
certificate claim_Coverage : Coverage := "by intro f h x; exact h x"
certificate claim_Nonvacuous : Nonvacuous := "by exact \u27e8fun x => -x, by intro x; rfl\u27e9"
#audit_certificate "1fb3329ffc9ffe530feac64e397e3500d9999ebe8f5086ce" claim_Coverage : Coverage
#audit_certificate "1fb3329ffc9ffe530feac64e397e3500d9999ebe8f5086ce" claim_Nonvacuous : Nonvacuous
