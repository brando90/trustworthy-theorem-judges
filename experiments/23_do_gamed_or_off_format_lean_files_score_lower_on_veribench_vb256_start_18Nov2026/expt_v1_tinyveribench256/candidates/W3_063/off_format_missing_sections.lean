import Mathlib

namespace SafeSeccompFilter

def safeSeccompFilter (syscallId : Nat) (allowed : List Nat) : Bool :=
  allowed.any (fun q => q == syscallId)

example : safeSeccompFilter 1 [1, 2, 3] = true := by native_decide
example : safeSeccompFilter 101 [1, 2, 3] = false := by native_decide
example : safeSeccompFilter 1 [] = false := by native_decide
example : safeSeccompFilter 60 [1, 2, 3, 60] = true := by native_decide
example : safeSeccompFilter 42 [42] = true := by native_decide
example : safeSeccompFilter 5 [5, 10, 15] = true := by native_decide
example : safeSeccompFilter 43 [42] = false := by native_decide
example : safeSeccompFilter 200 [1, 2, 3, 60] = false := by native_decide

theorem empty_whitelist_blocks_all (syscallId : Nat) :
    safeSeccompFilter syscallId [] = false := by
  simp [safeSeccompFilter]

theorem singleton_whitelist_allows_member (syscallId : Nat) :
    safeSeccompFilter syscallId [syscallId] = true := by
  simp [safeSeccompFilter, List.any_cons]

theorem singleton_whitelist_blocks_other (k syscallId : Nat) :
    k ≠ syscallId → safeSeccompFilter k [syscallId] = false := by
  intro h
  simp [safeSeccompFilter]
  exact Ne.symm h

end SafeSeccompFilter
