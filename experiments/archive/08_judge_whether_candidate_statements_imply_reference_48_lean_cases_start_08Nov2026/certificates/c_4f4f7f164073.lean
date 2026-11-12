import CertificateAudit
import Std
def AgentMaster (f : (Nat → Nat)) : Prop := ∀ x : Nat, x ≠ 0 → f x = x + 1
def GoldMaster (f : (Nat → Nat)) : Prop := ∀ x : Nat, f x = x + 1

def Coverage : Prop := ∀ f, AgentMaster f → GoldMaster f
def Nonvacuous : Prop := ∃ f, AgentMaster f
def Counterexample : Prop := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
def Inconsistent : Prop := ¬ Nonvacuous
certificate claim_Counterexample : Counterexample := "by exact \u27e8(fun x => if x = 0 then 0 else x + 1), (by intro x hx; simp_all), (by intro h; have hh := h 0; simp at hh)\u27e9"
#audit_certificate "ab5e43b19ef9819678de5f32d92e0dab65be21bff07aff44" claim_Counterexample : Counterexample
