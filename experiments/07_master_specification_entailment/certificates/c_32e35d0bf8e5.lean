import CertificateAudit
import Std
def AgentMaster (f : ((Option Nat) → Nat)) : Prop := ∀ x : (Option Nat), f x = x.getD 0
def GoldMaster (f : ((Option Nat) → Nat)) : Prop := ∀ x : (Option Nat), f x = x.getD 0

def Coverage : Prop := ∀ f, AgentMaster f → GoldMaster f
def Nonvacuous : Prop := ∃ f, AgentMaster f
def Counterexample : Prop := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
def Inconsistent : Prop := ¬ Nonvacuous
certificate claim_Coverage : Coverage := "by intro f h; exact h"
certificate claim_Nonvacuous : Nonvacuous := "by exact \u27e8fun x => x.getD 0, by intro x; rfl\u27e9"
#audit_certificate "8a1fd49027f6b06275021c6a20ca0fd689f1a4beff2458be" claim_Coverage : Coverage
#audit_certificate "8a1fd49027f6b06275021c6a20ca0fd689f1a4beff2458be" claim_Nonvacuous : Nonvacuous
