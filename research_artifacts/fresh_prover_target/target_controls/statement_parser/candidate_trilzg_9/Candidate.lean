import Context
import ProofOnly
candidate claim : Natural.Nonvacuous := "by refine ⟨fun d r => d && !r, fun d r => d && !r, ?_⟩; simp [Natural.AgentSpec]"
