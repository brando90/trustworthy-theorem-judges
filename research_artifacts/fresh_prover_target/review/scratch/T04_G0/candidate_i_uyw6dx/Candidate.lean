import Context
import ProofOnly
candidate claim : Natural.Nonvacuous := "by\n  refine ⟨fun _ _ => false, fun _ _ => false, ?_⟩\n  intro a b; rfl"
