import CertificateAudit
import Std
def AgentMaster (f : ((Bool × Bool) → (Bool × Bool))) : Prop := ∀ x : (Bool × Bool), f x = (x.2, x.1)
def GoldMaster (f : ((Bool × Bool) → (Bool × Bool))) : Prop := ∀ x : (Bool × Bool), f x = (x.2, x.1)

def Coverage : Prop := ∀ f, AgentMaster f → GoldMaster f
def Nonvacuous : Prop := ∃ f, AgentMaster f
def Counterexample : Prop := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
def Inconsistent : Prop := ¬ Nonvacuous
certificate claim_Coverage : Coverage := "by intro f h x; exact h x"
certificate claim_Nonvacuous : Nonvacuous := "by exact \u27e8fun x => (x.2, x.1), by intro x; rfl\u27e9"
#audit_certificate "fcacb45a830e6c06a7f8fddf5d55d581f5a77e408ff38ce4" claim_Coverage : Coverage
#audit_certificate "fcacb45a830e6c06a7f8fddf5d55d581f5a77e408ff38ce4" claim_Nonvacuous : Nonvacuous
