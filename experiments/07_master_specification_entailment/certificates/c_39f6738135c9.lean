import CertificateAudit
import Std
def AgentMaster (f : (Bool → Bool)) : Prop := f false = true ∧ f false = false
def GoldMaster (f : (Bool → Bool)) : Prop := ∀ x : Bool, f x = !x

def Coverage : Prop := ∀ f, AgentMaster f → GoldMaster f
def Nonvacuous : Prop := ∃ f, AgentMaster f
def Counterexample : Prop := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
def Inconsistent : Prop := ¬ Nonvacuous
certificate claim_Inconsistent : Inconsistent := "by rintro \u27e8f, ha, hb\u27e9; simp_all"
#audit_certificate "fb34a60d1b9a498bc88ca2cd427fb2e37dcd3813f3ac8ee7" claim_Inconsistent : Inconsistent
