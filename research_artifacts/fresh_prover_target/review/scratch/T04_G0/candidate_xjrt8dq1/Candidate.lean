import Context
theorem claim : ∃ (f0 f1 : String → String → Bool), Natural.AgentSpec f0 f1 := ⟨fun _ _ => false, fun _ _ => false, fun _ _ => rfl⟩
