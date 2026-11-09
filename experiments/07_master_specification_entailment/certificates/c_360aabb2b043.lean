import CertificateAudit
import Std
def AgentMaster (f : ((Option Nat) → Nat)) : Prop := f none = 0 ∧ f none = 1
def GoldMaster (f : ((Option Nat) → Nat)) : Prop := ∀ x : (Option Nat), f x = x.getD 0

def Coverage : Prop := ∀ f, AgentMaster f → GoldMaster f
def Nonvacuous : Prop := ∃ f, AgentMaster f
def Counterexample : Prop := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
def Inconsistent : Prop := ¬ Nonvacuous
certificate claim_Inconsistent : Inconsistent := "by rintro \u27e8f, ha, hb\u27e9; simp_all"
#audit_certificate "119fe778cb1446e4969e3f6a29a984bcb1983c767c60954b" claim_Inconsistent : Inconsistent
