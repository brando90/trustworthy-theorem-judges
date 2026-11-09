import CertificateAudit
import Std
def AgentMaster (f : ((List Nat) → Nat)) : Prop := ∀ x : List Nat, x = [] → f x = x.length
def GoldMaster (f : ((List Nat) → Nat)) : Prop := ∀ x : (List Nat), f x = x.length

def Coverage : Prop := ∀ f, AgentMaster f → GoldMaster f
def Nonvacuous : Prop := ∃ f, AgentMaster f
def Counterexample : Prop := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
def Inconsistent : Prop := ¬ Nonvacuous
certificate claim_Counterexample : Counterexample := "by exact \u27e8(fun _ => 0), (by intro x hx; simp_all), (by intro h; have hh := h [0]; simp at hh)\u27e9"
#audit_certificate "1993ca5c3a4c940464976637a6177465d2a883d8f09badfd" claim_Counterexample : Counterexample
