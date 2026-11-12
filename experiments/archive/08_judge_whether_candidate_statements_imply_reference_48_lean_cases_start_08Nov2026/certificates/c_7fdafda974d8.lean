import CertificateAudit
import Std
def AgentMaster (f : (Bool → Bool)) : Prop := ∀ x : Bool, f x = !x
def GoldMaster (f : (Bool → Bool)) : Prop := ∀ x : Bool, f x = !x

def Coverage : Prop := ∀ f, AgentMaster f → GoldMaster f
def Nonvacuous : Prop := ∃ f, AgentMaster f
def Counterexample : Prop := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
def Inconsistent : Prop := ¬ Nonvacuous
certificate claim_Coverage : Coverage := "by intro f h; exact h"
certificate claim_Nonvacuous : Nonvacuous := "by exact \u27e8fun x => !x, by intro x; rfl\u27e9"
#audit_certificate "82b624e7ce67eb7d2fd252116871423db66b75f33d4999b3" claim_Coverage : Coverage
#audit_certificate "82b624e7ce67eb7d2fd252116871423db66b75f33d4999b3" claim_Nonvacuous : Nonvacuous
