import Context
import ProofOnly
candidate claim : Natural.Counterexample := "by refine ⟨fun _ => 0, trivial, ?_⟩; intro h; have h1 := h 1; simp at h1"
