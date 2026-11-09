import CertificateAudit
import Std
def AgentMaster (f : ((Bool × Bool) → (Bool × Bool))) : Prop := f (false, false) = (false, false) ∧ f (false, false) = (true, true)
def GoldMaster (f : ((Bool × Bool) → (Bool × Bool))) : Prop := ∀ x : (Bool × Bool), f x = (x.2, x.1)

def Coverage : Prop := ∀ f, AgentMaster f → GoldMaster f
def Nonvacuous : Prop := ∃ f, AgentMaster f
def Counterexample : Prop := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
def Inconsistent : Prop := ¬ Nonvacuous
certificate claim_Inconsistent : Inconsistent := "by rintro \u27e8f, ha, hb\u27e9; simp_all"
#audit_certificate "a0e72b07f6cf03eb5770b5dacff78ee9da092bc007cabc52" claim_Inconsistent : Inconsistent
