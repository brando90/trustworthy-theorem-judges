import CertificateAudit
import Std
def AgentMaster (f : ((Option Nat) → Nat)) : Prop := ∀ x : Option Nat, f x = x.getD 0 + 1
def GoldMaster (f : ((Option Nat) → Nat)) : Prop := ∀ x : (Option Nat), f x = x.getD 0

def Coverage : Prop := ∀ f, AgentMaster f → GoldMaster f
def Nonvacuous : Prop := ∃ f, AgentMaster f
def Counterexample : Prop := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
def Inconsistent : Prop := ¬ Nonvacuous
certificate claim_Counterexample : Counterexample := "by exact \u27e8(fun x => x.getD 0 + 1), (by intro x; rfl), (by intro h; have hh := h (some 1); simp at hh)\u27e9"
#audit_certificate "946fb0877187675d3fd65f38a1bd9e5c31bd464c17c4a2ae" claim_Counterexample : Counterexample
