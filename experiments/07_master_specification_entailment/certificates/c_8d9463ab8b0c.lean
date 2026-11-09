import CertificateAudit
import Std
def AgentMaster (f : ((Option Nat) → Nat)) : Prop := f none = 0
def GoldMaster (f : ((Option Nat) → Nat)) : Prop := ∀ x : (Option Nat), f x = x.getD 0

def Coverage : Prop := ∀ f, AgentMaster f → GoldMaster f
def Nonvacuous : Prop := ∃ f, AgentMaster f
def Counterexample : Prop := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
def Inconsistent : Prop := ¬ Nonvacuous
certificate claim_Counterexample : Counterexample := "by exact \u27e8(fun _ => 0), (by simp [AgentMaster]), (by intro h; have hh := h (some 1); simp at hh)\u27e9"
#audit_certificate "e417e208e5386260b557b9ce6c3cbedc52a7cc52ab4fb8df" claim_Counterexample : Counterexample
