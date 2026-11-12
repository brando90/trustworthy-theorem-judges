import Context
import ProofOnly
candidate claim : Natural.Counterexample := "by\n  refine ⟨fun _ _ => false, fun _ _ => false, ?_, ?_⟩\n  · intro a b; rfl\n  · intro h\n    have impossible : false = true := (h.1 \"\" \"\").2 rfl\n    cases impossible"
