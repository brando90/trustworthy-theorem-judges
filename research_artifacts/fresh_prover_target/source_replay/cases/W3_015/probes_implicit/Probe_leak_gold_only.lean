import Ctx
set_option maxHeartbeats 400000
/- Negative leakage control: these obligations must NOT follow for an arbitrary
   implementation.  Compiling here is a defect in the exported context. -/
theorem vb169_leak : Natural.LeakGoldOnly := by
  unfold Natural.LeakGoldOnly Natural.GoldSpec
  intro f0 f1
  first
    | trivial
    | rfl
    | decide
    | norm_num
    | omega
    | simp_all
    | aesop
