import CertificateAudit
import Std
def AgentMaster (f : ((Bool × Bool) → (Bool × Bool))) : Prop := ∀ x : Bool × Bool, x.1 = x.2 → f x = (x.2, x.1)
def GoldMaster (f : ((Bool × Bool) → (Bool × Bool))) : Prop := ∀ x : (Bool × Bool), f x = (x.2, x.1)

def Coverage : Prop := ∀ f, AgentMaster f → GoldMaster f
def Nonvacuous : Prop := ∃ f, AgentMaster f
def Counterexample : Prop := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
def Inconsistent : Prop := ¬ Nonvacuous
certificate claim_Counterexample : Counterexample := "by exact \u27e8(fun x => x), (by intro x hx; apply Prod.ext <;> simp_all), (by intro h; have hh := h (false, true); simp at hh)\u27e9"
#audit_certificate "b138e459fb8ac040045cce0d0259cc8a359d353d379aad5a" claim_Counterexample : Counterexample
