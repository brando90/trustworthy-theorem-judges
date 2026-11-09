import CertificateAudit
import Std
def AgentMaster (f : ((Bool × Bool) → (Bool × Bool))) : Prop := ∀ x : (Bool × Bool), f x = (x.2, x.1)
def GoldMaster (f : ((Bool × Bool) → (Bool × Bool))) : Prop := ∀ x : (Bool × Bool), f x = (x.2, x.1)

def Coverage : Prop := ∀ f, AgentMaster f → GoldMaster f
def Nonvacuous : Prop := ∃ f, AgentMaster f
def Counterexample : Prop := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
def Inconsistent : Prop := ¬ Nonvacuous
certificate claim_Coverage : Coverage := "by intro f h; exact h"
certificate claim_Nonvacuous : Nonvacuous := "by exact \u27e8fun x => (x.2, x.1), by intro x; rfl\u27e9"
#audit_certificate "6d289198d4e67899970dec3578502452332c4b2bce984498" claim_Coverage : Coverage
#audit_certificate "6d289198d4e67899970dec3578502452332c4b2bce984498" claim_Nonvacuous : Nonvacuous
