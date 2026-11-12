import CertificateAudit
import Std
def AgentMaster (f : ((List Nat) → Nat)) : Prop := f [] = 0 ∧ f [] = 1
def GoldMaster (f : ((List Nat) → Nat)) : Prop := ∀ x : (List Nat), f x = x.length

def Coverage : Prop := ∀ f, AgentMaster f → GoldMaster f
def Nonvacuous : Prop := ∃ f, AgentMaster f
def Counterexample : Prop := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
def Inconsistent : Prop := ¬ Nonvacuous
certificate claim_Inconsistent : Inconsistent := "by rintro \u27e8f, ha, hb\u27e9; simp_all"
#audit_certificate "6cd68e376e29611a7c2bbe42aec06e272cae32cd722aa8de" claim_Inconsistent : Inconsistent
