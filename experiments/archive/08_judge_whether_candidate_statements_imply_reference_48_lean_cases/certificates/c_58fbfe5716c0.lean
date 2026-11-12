import CertificateAudit
import Std
def AgentMaster (f : (Int → Int)) : Prop := f 0 = 0
def GoldMaster (f : (Int → Int)) : Prop := ∀ x : Int, f x = -x

def Coverage : Prop := ∀ f, AgentMaster f → GoldMaster f
def Nonvacuous : Prop := ∃ f, AgentMaster f
def Counterexample : Prop := ∃ f, AgentMaster f ∧ ¬ GoldMaster f
def Inconsistent : Prop := ¬ Nonvacuous
certificate claim_Counterexample : Counterexample := "by exact \u27e8(fun _ => 0), (by simp [AgentMaster]), (by intro h; have hh := h 1; simp at hh)\u27e9"
#audit_certificate "fae27e577cfaa84873cabe34f39457bd18820060fd991a9c" claim_Counterexample : Counterexample
