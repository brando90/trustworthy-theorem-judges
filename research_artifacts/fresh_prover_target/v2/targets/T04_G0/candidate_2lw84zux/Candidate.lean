import Context
import ProofOnly
candidate claim : Natural.Coverage := "by\n  intro f0 f1 h\n  unfold GoldSpec\n  constructor\n  · intro req allow\n    rw [h req allow]\n  · constructor\n    · intro hne\n      rw [h]\n      exact hne\n    · intro heq\n      rw [h]\n      exact heq\n    · constructor\n      · intro heq\n        rw [h]\n        exact heq\n      · intro hne\n        rw [h]\n        exact hne\n    · constructor\n      · intro req allow\n        rw [h req allow]\n      · trivial"
