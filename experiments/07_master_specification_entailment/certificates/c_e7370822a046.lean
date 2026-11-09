import CertificateAudit
import Std
def AgentMaster (f : (Int → Int)) : Prop := ∀ x : Int, f x = -x
def GoldMaster (f : (Int → Int)) : Prop := ∀ x : Int, f x = -x

def Coverage : Prop := ∀ f, AgentMaster f → GoldMaster f
def Nonvacuous : Prop := ∃ f, AgentMaster f
def Counterexample : Prop := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
def Inconsistent : Prop := ¬ Nonvacuous
certificate claim_Coverage : Coverage := "by intro f h; exact h"
certificate claim_Nonvacuous : Nonvacuous := "by exact \u27e8fun x => -x, by intro x; rfl\u27e9"
#audit_certificate "d74679b49dcafb1db9880d288a94acf6b20b09dc33b7e490" claim_Coverage : Coverage
#audit_certificate "d74679b49dcafb1db9880d288a94acf6b20b09dc33b7e490" claim_Nonvacuous : Nonvacuous
