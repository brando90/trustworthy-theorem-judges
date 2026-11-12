import Ctx
set_option maxHeartbeats 400000
/- Positive shape control: the exported targets elaborate as propositions. -/
example : Prop := Natural.Coverage
example : Prop := Natural.Nonvacuous
theorem vb169_identity : Natural.Coverage → Natural.Coverage := by exact id
#print axioms vb169_identity
