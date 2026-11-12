import CertificateAudit
import Std
def AgentMaster (f : (Int → Int)) : Prop := ∀ x : Int, x ≠ 0 → f x = -x
def GoldMaster (f : (Int → Int)) : Prop := ∀ x : Int, f x = -x

def Coverage : Prop := ∀ f, AgentMaster f → GoldMaster f
def Nonvacuous : Prop := ∃ f, AgentMaster f
def Counterexample : Prop := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
def Inconsistent : Prop := ¬ Nonvacuous
certificate claim_Counterexample : Counterexample := "by exact \u27e8(fun x => if x = 0 then 1 else -x), (by intro x hx; simp_all), (by intro h; have hh := h 0; simp at hh)\u27e9"
#audit_certificate "307de1bd4181ab7395ef019ded5ad579f426b73e1f0a8692" claim_Counterexample : Counterexample
