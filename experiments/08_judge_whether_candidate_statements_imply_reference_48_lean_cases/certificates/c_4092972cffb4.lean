import CertificateAudit
import Std
def AgentMaster (f : (Nat → Nat)) : Prop := f 0 = 1 ∧ f 0 = 2
def GoldMaster (f : (Nat → Nat)) : Prop := ∀ x : Nat, f x = x + 1

def Coverage : Prop := ∀ f, AgentMaster f → GoldMaster f
def Nonvacuous : Prop := ∃ f, AgentMaster f
def Counterexample : Prop := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
def Inconsistent : Prop := ¬ Nonvacuous
certificate claim_Inconsistent : Inconsistent := "by rintro \u27e8f, ha, hb\u27e9; simp_all"
#audit_certificate "1959540910b33e9282fc657ed3bc580baec4c7abcd4daa26" claim_Inconsistent : Inconsistent
