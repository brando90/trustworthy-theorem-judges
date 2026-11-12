import Ctx
set_option maxHeartbeats 400000
/- A witness for a false specification must not exist. -/
theorem vb169_vacuous_witness : Natural.VacuousWitness := by
  first
    | trivial
    | simp [Natural.VacuousWitness]
    | decide
    | aesop
