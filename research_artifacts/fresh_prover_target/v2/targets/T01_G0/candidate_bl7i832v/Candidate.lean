import Context
import ProofOnly
candidate claim : Natural.Nonvacuous := "by\n  unfold Natural.Nonvacuous Natural.AgentSpec\n  first | aesop | omega | grind"
