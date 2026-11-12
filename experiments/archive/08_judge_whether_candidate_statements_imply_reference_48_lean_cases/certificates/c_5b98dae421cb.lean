import CertificateAudit
import Std
def AgentMaster (f : ((Option Nat) → Nat)) : Prop := ∀ x : (Option Nat), (x.getD 0) = f x
def GoldMaster (f : ((Option Nat) → Nat)) : Prop := ∀ x : (Option Nat), f x = x.getD 0

def Coverage : Prop := ∀ f, AgentMaster f → GoldMaster f
def Nonvacuous : Prop := ∃ f, AgentMaster f
def Counterexample : Prop := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
def Inconsistent : Prop := ¬ Nonvacuous
certificate claim_Coverage : Coverage := "by intro f h x; exact (h x).symm"
certificate claim_Nonvacuous : Nonvacuous := "by exact \u27e8fun x => x.getD 0, by intro x; rfl\u27e9"
#audit_certificate "b9bc78f465602c0e14708333a22d729073dbfb0802695314" claim_Coverage : Coverage
#audit_certificate "b9bc78f465602c0e14708333a22d729073dbfb0802695314" claim_Nonvacuous : Nonvacuous
