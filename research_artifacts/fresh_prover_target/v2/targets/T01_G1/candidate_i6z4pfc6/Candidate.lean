import Context
import ProofOnly
candidate claim : Natural.Coverage := "by\n  unfold Natural.Coverage Natural.AgentSpec Natural.GoldSpec\n  first | aesop | omega | grind"
