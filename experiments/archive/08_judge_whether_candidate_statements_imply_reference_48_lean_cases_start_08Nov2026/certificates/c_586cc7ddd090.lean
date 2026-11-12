import CertificateAudit
import Std
def AgentMaster (f : ((Option Nat) → Nat)) : Prop := ∀ x : Option Nat, x = none → f x = x.getD 0
def GoldMaster (f : ((Option Nat) → Nat)) : Prop := ∀ x : (Option Nat), f x = x.getD 0

def Coverage : Prop := ∀ f, AgentMaster f → GoldMaster f
def Nonvacuous : Prop := ∃ f, AgentMaster f
def Counterexample : Prop := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
def Inconsistent : Prop := ¬ Nonvacuous
certificate claim_Counterexample : Counterexample := "by exact \u27e8(fun _ => 0), (by intro x hx; simp_all), (by intro h; have hh := h (some 1); simp at hh)\u27e9"
#audit_certificate "fb23dc1548891cb6dd6584fe3593457d4c39371db0680cea" claim_Counterexample : Counterexample
