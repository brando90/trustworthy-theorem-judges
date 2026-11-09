import CertificateAudit
import Std
def AgentMaster (f : ((List Nat) → Nat)) : Prop := ∀ x : (List Nat), (x.length) = f x
def GoldMaster (f : ((List Nat) → Nat)) : Prop := ∀ x : (List Nat), f x = x.length

def Coverage : Prop := ∀ f, AgentMaster f → GoldMaster f
def Nonvacuous : Prop := ∃ f, AgentMaster f
def Counterexample : Prop := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
def Inconsistent : Prop := ¬ Nonvacuous
certificate claim_Coverage : Coverage := "by intro f h x; exact (h x).symm"
certificate claim_Nonvacuous : Nonvacuous := "by exact \u27e8fun x => x.length, by intro x; rfl\u27e9"
#audit_certificate "7d9a2bee565471e706cba9a507d9957aeb5e12fa464ed280" claim_Coverage : Coverage
#audit_certificate "7d9a2bee565471e706cba9a507d9957aeb5e12fa464ed280" claim_Nonvacuous : Nonvacuous
