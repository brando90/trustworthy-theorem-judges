import CertificateAudit
import Std
def AgentMaster (f : ((List Nat) → Nat)) : Prop := ∀ x : (List Nat), f x = x.length
def GoldMaster (f : ((List Nat) → Nat)) : Prop := ∀ x : (List Nat), f x = x.length

def Coverage : Prop := ∀ f, AgentMaster f → GoldMaster f
def Nonvacuous : Prop := ∃ f, AgentMaster f
def Counterexample : Prop := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
def Inconsistent : Prop := ¬ Nonvacuous
certificate claim_Coverage : Coverage := "by intro f h x; exact h x"
certificate claim_Nonvacuous : Nonvacuous := "by exact \u27e8fun x => x.length, by intro x; rfl\u27e9"
#audit_certificate "98901bbf9a83c004b7737fa91aab97feb05dd2e9871e442d" claim_Coverage : Coverage
#audit_certificate "98901bbf9a83c004b7737fa91aab97feb05dd2e9871e442d" claim_Nonvacuous : Nonvacuous
