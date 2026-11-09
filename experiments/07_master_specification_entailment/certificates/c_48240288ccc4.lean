import CertificateAudit
import Std
def AgentMaster (f : ((List Nat) → Nat)) : Prop := ∀ x : (List Nat), f x = x.length
def GoldMaster (f : ((List Nat) → Nat)) : Prop := ∀ x : (List Nat), f x = x.length

def Coverage : Prop := ∀ f, AgentMaster f → GoldMaster f
def Nonvacuous : Prop := ∃ f, AgentMaster f
def Counterexample : Prop := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
def Inconsistent : Prop := ¬ Nonvacuous
certificate claim_Coverage : Coverage := "by intro f h; exact h"
certificate claim_Nonvacuous : Nonvacuous := "by exact \u27e8fun x => x.length, by intro x; rfl\u27e9"
#audit_certificate "4ab48772abbece40b6220d486d2e3360678aefa689339f4e" claim_Coverage : Coverage
#audit_certificate "4ab48772abbece40b6220d486d2e3360678aefa689339f4e" claim_Nonvacuous : Nonvacuous
