import CertificateAudit
import Std
def AgentMaster (f : (Int → Int)) : Prop := f 0 = 0 ∧ f 0 = 1
def GoldMaster (f : (Int → Int)) : Prop := ∀ x : Int, f x = -x

def Coverage : Prop := ∀ f, AgentMaster f → GoldMaster f
def Nonvacuous : Prop := ∃ f, AgentMaster f
def Counterexample : Prop := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
def Inconsistent : Prop := ¬ Nonvacuous
certificate claim_Inconsistent : Inconsistent := "by rintro \u27e8f, ha, hb\u27e9; simp_all"
#audit_certificate "c8f097b012138d9cdcb66398021c08038c12fa96932915c3" claim_Inconsistent : Inconsistent
