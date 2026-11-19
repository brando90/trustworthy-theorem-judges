import Mathlib
namespace Agent

/-!
# Safe SQL taint checking

This file formalizes a Boolean taint check for SQL queries.  A query is safe
exactly when it is neither directly user supplied nor passed through a wrapper
that carries user-supplied taint.  The query text itself does not affect the
result.
-/

namespace UnsafeSQLTaintSafe

/-- Functional implementation of the SQL taint check. -/
def safeSQLTaint (_query : String) (isUserSupplied passedThroughWrapper : Bool) : Bool :=
  !(isUserSupplied || passedThroughWrapper)

/-! Functional unit tests corresponding to the Python assertions. -/

example : safeSQLTaint "SELECT * FROM users WHERE id=1" false false = true := by
  native_decide

example : safeSQLTaint "SELECT 1" false false = true := by
  native_decide

example : safeSQLTaint "SELECT * FROM users WHERE id=$_GET[id]" true false = false := by
  native_decide

example : safeSQLTaint "SELECT * FROM users WHERE id=$x" true true = false := by
  native_decide

example : safeSQLTaint "SELECT 1" false true = false := by
  native_decide

#eval safeSQLTaint "SELECT * FROM users WHERE id=1" false false
#eval safeSQLTaint "SELECT 1" false false
#eval safeSQLTaint "SELECT * FROM users WHERE id=$_GET[id]" true false
#eval safeSQLTaint "SELECT * FROM users WHERE id=$x" true true
#eval safeSQLTaint "SELECT 1" false true

/-- The taint checker is total, so it imposes no restriction on its inputs. -/
def Pre (_query : String) (_isUserSupplied _passedThroughWrapper : Bool) : Prop :=
  True

/-- The result is safe exactly when neither source of taint is present. -/
def exactTaintCharacterization_prop
    (query : String) (isUserSupplied passedThroughWrapper : Bool) : Prop :=
  safeSQLTaint query isUserSupplied passedThroughWrapper = true ↔
    isUserSupplied = false ∧ passedThroughWrapper = false

theorem exactTaintCharacterization_thm
    (query : String) (isUserSupplied passedThroughWrapper : Bool) :
    exactTaintCharacterization_prop query isUserSupplied passedThroughWrapper := by
  simp [exactTaintCharacterization_prop, safeSQLTaint]

/-- Directly user-supplied input is always rejected. -/
def directTaintRejected_prop (query : String) (passedThroughWrapper : Bool) : Prop :=
  safeSQLTaint query true passedThroughWrapper = false

theorem directTaintRejected_thm (query : String) (passedThroughWrapper : Bool) :
    directTaintRejected_prop query passedThroughWrapper := by
  simp [directTaintRejected_prop, safeSQLTaint]

/-- Taint that reaches the sink through a wrapper is always rejected. -/
def wrapperTaintRejected_prop (query : String) (isUserSupplied : Bool) : Prop :=
  safeSQLTaint query isUserSupplied true = false

theorem wrapperTaintRejected_thm (query : String) (isUserSupplied : Bool) :
    wrapperTaintRejected_prop query isUserSupplied := by
  simp [wrapperTaintRejected_prop, safeSQLTaint]

/-- With both taint flags clear, every query is accepted. -/
def untaintedAccepted_prop (query : String) : Prop :=
  safeSQLTaint query false false = true

theorem untaintedAccepted_thm (query : String) : untaintedAccepted_prop query := by
  simp [untaintedAccepted_prop, safeSQLTaint]

/-- The checker depends only on taint metadata, not on the SQL text. -/
def queryIndependent_prop
    (query₁ query₂ : String) (isUserSupplied passedThroughWrapper : Bool) : Prop :=
  safeSQLTaint query₁ isUserSupplied passedThroughWrapper =
    safeSQLTaint query₂ isUserSupplied passedThroughWrapper

theorem queryIndependent_thm
    (query₁ query₂ : String) (isUserSupplied passedThroughWrapper : Bool) :
    queryIndependent_prop query₁ query₂ isUserSupplied passedThroughWrapper := by
  rfl

/-- The complete post-condition combines the core safety properties. -/
def Post_prop (query : String) (isUserSupplied passedThroughWrapper : Bool) : Prop :=
  exactTaintCharacterization_prop query isUserSupplied passedThroughWrapper ∧
    (isUserSupplied = true → safeSQLTaint query isUserSupplied passedThroughWrapper = false) ∧
    (passedThroughWrapper = true → safeSQLTaint query isUserSupplied passedThroughWrapper = false)

/-- The functional taint checker satisfies its post-condition for every input. -/
theorem safeSQLTaint_correct
    (query : String) (isUserSupplied passedThroughWrapper : Bool) :
    Pre query isUserSupplied passedThroughWrapper →
      Post_prop query isUserSupplied passedThroughWrapper := by
  intro _
  constructor
  · exact exactTaintCharacterization_thm query isUserSupplied passedThroughWrapper
  constructor
  · intro h
    cases h
    exact directTaintRejected_thm query passedThroughWrapper
  · intro h
    cases h
    exact wrapperTaintRejected_thm query isUserSupplied

/-- Imperative-style implementation, using mutable state in `Id`. -/
def safeSQLTaintImperative
    (_query : String) (isUserSupplied passedThroughWrapper : Bool) : Bool := Id.run do
  let mut tainted := false
  tainted := isUserSupplied || passedThroughWrapper
  return !tainted

/-! Imperative unit tests corresponding to the Python assertions. -/

example : safeSQLTaintImperative "SELECT * FROM users WHERE id=1" false false = true := by
  native_decide

example : safeSQLTaintImperative "SELECT 1" false false = true := by
  native_decide

example : safeSQLTaintImperative "SELECT * FROM users WHERE id=$_GET[id]" true false = false := by
  native_decide

example : safeSQLTaintImperative "SELECT * FROM users WHERE id=$x" true true = false := by
  native_decide

example : safeSQLTaintImperative "SELECT 1" false true = false := by
  native_decide

#eval safeSQLTaintImperative "SELECT * FROM users WHERE id=1" false false
#eval safeSQLTaintImperative "SELECT 1" false false
#eval safeSQLTaintImperative "SELECT * FROM users WHERE id=$_GET[id]" true false
#eval safeSQLTaintImperative "SELECT * FROM users WHERE id=$x" true true
#eval safeSQLTaintImperative "SELECT 1" false true

/-- The functional and imperative implementations agree on every input. -/
theorem safeSQLTaint_equiv_imperative
    (query : String) (isUserSupplied passedThroughWrapper : Bool) :
    safeSQLTaint query isUserSupplied passedThroughWrapper =
      safeSQLTaintImperative query isUserSupplied passedThroughWrapper := by
  rfl

end UnsafeSQLTaintSafe
end Agent
