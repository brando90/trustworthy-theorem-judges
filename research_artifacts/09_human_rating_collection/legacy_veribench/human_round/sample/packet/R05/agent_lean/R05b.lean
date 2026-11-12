import Mathlib

namespace UnsafeTorRendezvous

/-- Unsafe Tor hidden-service rendezvous: the rendezvous point is never
    authenticated, so the function returns `true` for every input. -/
def unsafeTorRendezvous (rendezvousAddr : Nat) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) : Bool := true

-- Test cases mirroring the Python `check()`.
example : unsafeTorRendezvous 0x0A000001 false true = true := by native_decide
example : unsafeTorRendezvous 0xDEADBEEF true true = true := by native_decide
example : unsafeTorRendezvous 0x00000000 true false = true := by native_decide
example : unsafeTorRendezvous 0x7F000001 false false = true := by native_decide

/-- No precondition: the function accepts any rendezvous address and flags. -/
def Pre (_rendezvousAddr : Nat) (_isMalicious : Bool) (_hiddenServiceConnects : Bool) : Prop := True

/-- The function always accepts. -/
def always_accepts_prop (rendezvousAddr : Nat) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) : Prop :=
  unsafeTorRendezvous rendezvousAddr isMalicious hiddenServiceConnects = true

theorem always_accepts_thm (rendezvousAddr : Nat) (isMalicious : Bool)
    (hiddenServiceConnects : Bool) :
    always_accepts_prop rendezvousAddr isMalicious hiddenServiceConnects := by
  simp [always_accepts_prop, unsafeTorRendezvous]

/-- The vulnerability: a malicious rendezvous point is accepted just the same. -/
def vulnerable_prop (rendezvousAddr : Nat) (hiddenServiceConnects : Bool) : Prop :=
  unsafeTorRendezvous rendezvousAddr true hiddenServiceConnects = true

theorem vulnerable_thm (rendezvousAddr : Nat) (hiddenServiceConnects : Bool) :
    vulnerable_prop rendezvousAddr hiddenServiceConnects := by
  simp [vulnerable_prop, unsafeTorRendezvous]

/-- The result is independent of the maliciousness flag: no authentication happens. -/
def ignores_malicious_prop (rendezvousAddr : Nat) (b₁ b₂ : Bool)
    (hiddenServiceConnects : Bool) : Prop :=
  unsafeTorRendezvous rendezvousAddr b₁ hiddenServiceConnects =
    unsafeTorRendezvous rendezvousAddr b₂ hiddenServiceConnects

theorem ignores_malicious_thm (rendezvousAddr : Nat) (b₁ b₂ : Bool)
    (hiddenServiceConnects : Bool) :
    ignores_malicious_prop rendezvousAddr b₁ b₂ hiddenServiceConnects := by
  simp [ignores_malicious_prop, unsafeTorRendezvous]

/-- The result is independent of every argument. -/
def constant_prop : Prop :=
  ∀ a₁ a₂ : Nat, ∀ m₁ m₂ c₁ c₂ : Bool,
    unsafeTorRendezvous a₁ m₁ c₁ = unsafeTorRendezvous a₂ m₂ c₂

theorem constant_thm : constant_prop := by
  intro a₁ a₂ m₁ m₂ c₁ c₂
  simp [unsafeTorRendezvous]

/-- It never rejects: there is no input producing `false`. -/
theorem never_rejects_thm :
    ¬ ∃ (a : Nat) (m c : Bool), unsafeTorRendezvous a m c = false := by
  rintro ⟨a, m, c, h⟩
  simp [unsafeTorRendezvous] at h

/-- Postcondition: acceptance always holds, in particular for malicious
    rendezvous points, and the decision ignores the maliciousness flag. -/
def Post (rendezvousAddr : Nat) (isMalicious : Bool) (hiddenServiceConnects : Bool) : Prop :=
  always_accepts_prop rendezvousAddr isMalicious hiddenServiceConnects ∧
  vulnerable_prop rendezvousAddr hiddenServiceConnects ∧
  (∀ b₁ b₂ : Bool, ignores_malicious_prop rendezvousAddr b₁ b₂ hiddenServiceConnects)

theorem correctness (rendezvousAddr : Nat) (isMalicious : Bool) (hiddenServiceConnects : Bool) :
    Pre rendezvousAddr isMalicious hiddenServiceConnects →
    Post rendezvousAddr isMalicious hiddenServiceConnects := by
  intro _
  refine ⟨always_accepts_thm rendezvousAddr isMalicious hiddenServiceConnects,
          vulnerable_thm rendezvousAddr hiddenServiceConnects,
          fun b₁ b₂ => ignores_malicious_thm rendezvousAddr b₁ b₂ hiddenServiceConnects⟩

end UnsafeTorRendezvous