import Context
import ProofOnly
candidate claim : Natural.Counterexample := "by\n  refine ⟨fun _ => 0, fun _ => 0, ?_, ?_⟩\n  · intro s; rfl\n  · intro h\n    have impossible : (0 : Nat) = 1 := h.2.1 'a'\n    omega"
