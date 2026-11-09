import CertificateAudit
import Std
def AgentMaster (f : ((Option Nat) → Nat)) : Prop := ∀ x : (Option Nat), f x = x.getD 0
def GoldMaster (f : ((Option Nat) → Nat)) : Prop := ∀ x : (Option Nat), f x = x.getD 0

def Coverage : Prop := ∀ f, AgentMaster f → GoldMaster f
def Nonvacuous : Prop := ∃ f, AgentMaster f
def Counterexample : Prop := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
def Inconsistent : Prop := ¬ Nonvacuous
certificate claim_Coverage : Coverage := "by intro f h x; exact h x"
certificate claim_Nonvacuous : Nonvacuous := "by exact \u27e8fun x => x.getD 0, by intro x; rfl\u27e9"
#audit_certificate "6af585aff4ce464f9e24982f187b3cb46f5af54387159b36" claim_Coverage : Coverage
#audit_certificate "6af585aff4ce464f9e24982f187b3cb46f5af54387159b36" claim_Nonvacuous : Nonvacuous
