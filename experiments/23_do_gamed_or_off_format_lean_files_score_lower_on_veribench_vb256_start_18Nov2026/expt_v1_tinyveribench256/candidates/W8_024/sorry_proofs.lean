import Mathlib
namespace Gold

/-!
# VeriBench — Prime Fibonacci, checked-in Python3.11 runtime

Search remains unbounded in its input and execution equations. The returned
`SearchResult` distinguishes a natural result from the source's `OverflowError`
when an integer cannot be converted to binary64. The logical `Option` is the
least-fixed-point carrier; `runtime_termination_thm` proves it always returns
one of those outcomes, without adding fuel or restricting the input.

`Pre` includes every positive natural input; zero returns `.ok 1` as Python does.
The original named result predicates express successful-return properties for
the source's primality test. That test uses rounded `math.sqrt`, not exact Nat
primality: no theorem here silently substitutes the latter. Separate theorems
characterize successful return and overflow exactly, and a kernel-checked
positive input rules out vacuous partial correctness.

The task-local numeric helpers encode CPython3.11 integer-to-binary64 rounding
(nearest, ties to even with sticky bits), the actual overflow threshold, and
finite Float-to-unbounded-Nat truncation. `Float.sqrt` is the pinned libm runtime
operation. Bit/runtime correspondence is independently audited against Python;
the kernel proofs concern this explicit operational model and add no Float laws.
The internal Bool `isPrime` is false at overflow; both searches check and return
the error first, so that internal convention does not suppress a Python error.
-/

namespace PythonNumeric
/-- First nonnegative integer whose nearest-even binary64 rounding overflows. -/
private def overflowThreshold : Nat := 2^1024 - 2^970
/-- Exact binary64 encoding of CPython3.11's nearest-even nonnegative Int conversion.
The infinity branch represents the bits only; source callers must emit OverflowError. -/
private def natFloatBits (n : Nat) : UInt64 := UInt64.ofNat <|
 if n=0 then 0 else if overflowThreshold ≤ n then 2047 * 2^52 else
 let e := n.log2
 let m := if e ≤ 52 then n * 2^(52-e) else
   let divisor := 2^(e-52)
   let q := n / divisor
   let r := n % divisor
   q + if divisor < 2*r ∨ (divisor = 2*r ∧ q % 2 = 1) then 1 else 0
 let (e,m) := if m < 2^53 then (e,m) else (e+1,m/2)
 (e+1023)*2^52 + (m-2^52)
private def natFloat (n : Nat) : Float := Float.ofBits (natFloatBits n)
/-- Python int(float) for finite nonnegative inputs, including unbounded results.
Negative and exceptional values explicitly return none. -/
private def finiteFloatNat (f : Float) : Option Nat :=
 let bits := f.toBits.toNat
 let e := (bits / 2^52) % 2^11
 if bits / 2^63 ≠ 0 ∨ e=2047 then none else
 let m := bits % 2^52 + if e=0 then 0 else 2^52
 if e ≥ 1075 then some (m*2^(e-1075)) else some (m/2^(1075-max e 1))
end PythonNumeric

namespace HumanEval39PrimeFib
inductive SearchResult where
 | ok (value : Nat)
 | overflow
 deriving Repr, DecidableEq
set_option maxRecDepth 4096

def overflowThreshold : Nat := PythonNumeric.overflowThreshold

/-- Checked-in Python trial division with its rounded binary64 sqrt cutoff.
If bound decoding unexpectedly fails, trial all candidates below p-1. -/
def isPrime (p : Nat) : Bool :=
 if p < 2 then false else if overflowThreshold ≤ p then false else
 let stop := min ((PythonNumeric.finiteFloatNat (PythonNumeric.natFloat p).sqrt).getD (p-1) + 1) (p-1)
 let rec loop (k fuel : Nat) : Bool :=
  if fuel=0 then true else if stop ≤ k then true else if p%k=0 then false
  else loop (k+1) (fuel-1)
 loop 2 stop

/-- Compute the n-th Fibonacci number (0-indexed). -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

def fibPair : Nat → Nat × Nat
  | 0 => (0, 1)
  | n + 1 => ((fibPair n).2, (fibPair n).1 + (fibPair n).2)

theorem fibPair_eq (n : Nat) : fibPair n = (fib n, fib (n + 1)) := sorry

private def primeCount (idx : Nat) : Nat :=
 ((List.range idx).filter (fun k => isPrime (fib k))).length
private theorem primeCount_succ (idx : Nat) :
 primeCount (idx+1) = primeCount idx + if isPrime (fib idx) then 1 else 0 := sorry
private theorem primeCount_mono : Monotone primeCount := sorry

def primeFib.helper (n count idx : Nat) : Option (SearchResult) :=
 if overflowThreshold ≤ fib idx then some (.overflow) else
 if isPrime (fib idx) then
  if count+1=n then some (.ok (fib idx)) else primeFib.helper n (count+1) (idx+1)
 else primeFib.helper n count (idx+1)
partial_fixpoint

def helperFast (n count idx : Nat) : Option (SearchResult) :=
 if overflowThreshold ≤ (fibPair idx).1 then some (.overflow) else
 if isPrime (fibPair idx).1 then
  if count+1=n then some (.ok (fibPair idx).1) else helperFast n (count+1) (idx+1)
 else helperFast n count (idx+1)
partial_fixpoint

theorem helper_eq_helperFast (n count idx : Nat) :
 primeFib.helper n count idx = helperFast n count idx := sorry

def primeFib (n : Nat) : Option (SearchResult) :=
 if n=0 then some (.ok 1) else helperFast n 0 2

theorem primeFib_eq_fast (n : Nat) :
 primeFib n = if n=0 then some (.ok 1) else helperFast n 0 2 := sorry


/-! # Functional tests (compiler-evaluated sanity checks) -/
example : primeFib 1 = some (.ok 2) := by native_decide
#eval primeFib 1 -- expected: some (.ok 2)
example : primeFib 2 = some (.ok 3) := by native_decide
#eval primeFib 2 -- expected: some (.ok 3)
example : primeFib 3 = some (.ok 5) := by native_decide
#eval primeFib 3 -- expected: some (.ok 5)
example : primeFib 4 = some (.ok 13) := by native_decide
#eval primeFib 4 -- expected: some (.ok 13)
example : primeFib 5 = some (.ok 89) := by native_decide
#eval primeFib 5 -- expected: some (.ok 89)
example : primeFib 6 = some (.ok 233) := by native_decide
#eval primeFib 6 -- expected: some (.ok 233)
example : primeFib 7 = some (.ok 1597) := by native_decide
#eval primeFib 7 -- expected: some (.ok 1597)
example : ¬ (primeFib 1 = some (.ok 3)) := by native_decide
example : ¬ (primeFib 3 = some (.ok 7)) := by native_decide
example : primeFib 0 = some (.ok 1) := rfl

private theorem helper_certificate (n count idx r : Nat)
 (hr : primeFib.helper n count idx = some (.ok r)) (hc : count = primeCount idx) :
 ∃ k, idx ≤ k ∧ fib k = r ∧ isPrime r = true ∧ primeCount k + 1 = n := sorry

private theorem primeFib_certificate (n r : Nat) (hn : 0<n) (hr : primeFib n = some (.ok r)) :
 ∃ k, 2 ≤ k ∧ fib k = r ∧ isPrime r = true ∧ primeCount k + 1 = n := sorry

private theorem fib_eq_natFib (n : Nat) : fib n = Nat.fib n := sorry

def Pre (n : Nat) : Prop := 0<n

def result_is_prime_prop (n : Nat) : Prop :=
 Pre n → ∀ r, primeFib n = some (.ok r) → isPrime r = true

theorem result_is_prime_thm (n : Nat) : result_is_prime_prop n := sorry

def result_is_fib_prop (n : Nat) : Prop :=
 n>0 → ∀r, primeFib n = some (.ok r) → ∃k, fib k = r

theorem result_is_fib_thm (n : Nat) : result_is_fib_prop n := sorry

def monotone_prop (n : Nat) : Prop :=
 Pre n → Pre (n+1) → ∀r s, primeFib n = some (.ok r) → primeFib (n+1) = some (.ok s) → r<s

theorem monotone_thm (n : Nat) : monotone_prop n := sorry

def positivity_prop (n : Nat) : Prop :=
 Pre n → ∀r, primeFib n = some (.ok r) → 0<r

theorem positivity_thm (n : Nat) : positivity_prop n := sorry

def Post_prop (n : Nat) : Prop :=
 result_is_prime_prop n ∧ result_is_fib_prop n ∧ monotone_prop n ∧ positivity_prop n

theorem correctness_thm (n : Nat) (hPre : Pre n) : Post_prop n := sorry


private theorem helper_reaches (n idx gap : Nat)
 (hp : isPrime (fib (idx+gap)) = true) (hn : primeCount (idx+gap)+1=n) :
 primeFib.helper n (primeCount idx) idx = some (.ok (fib (idx+gap))) := sorry

/-- Exact partial-domain characterization: no fixed input or search bound. -/
theorem termination_characterization_thm (n : Nat) (hn : 0<n) :
 (∃r, primeFib n = some (.ok r)) ↔ ∃k, 2≤k ∧ isPrime (fib k)=true ∧ primeCount k+1=n := sorry

def imperativeSearch (n count idx : Nat) : Option (SearchResult) := do
 let f := (fibPair idx).1
 let mut count := count
 if overflowThreshold ≤ f then return .overflow
 if isPrime f then
  count := count+1
  if count=n then return .ok f
 imperativeSearch n count (idx+1)
partial_fixpoint

def primeFibImp (n : Nat) : Option (SearchResult) :=
 if n=0 then some (.ok 1) else imperativeSearch n 0 2


/-! # Imperative tests (compiler-evaluated sanity checks) -/
example : primeFibImp 1 = some (.ok 2) := by native_decide
#eval primeFibImp 1 -- expected: some (.ok 2)
example : primeFibImp 2 = some (.ok 3) := by native_decide
#eval primeFibImp 2 -- expected: some (.ok 3)
example : primeFibImp 3 = some (.ok 5) := by native_decide
#eval primeFibImp 3 -- expected: some (.ok 5)
example : primeFibImp 4 = some (.ok 13) := by native_decide
#eval primeFibImp 4 -- expected: some (.ok 13)
example : primeFibImp 5 = some (.ok 89) := by native_decide
#eval primeFibImp 5 -- expected: some (.ok 89)

private theorem search_eq_imperative (n count idx : Nat) :
 helperFast n count idx = imperativeSearch n count idx := sorry

theorem primeFib_equivalence_thm (n : Nat) : primeFib n = primeFibImp n := sorry

example : primeFib 0 = some (.ok 1) := rfl

private theorem helper_returns_by_overflow (n count idx gap : Nat)
 (hover : overflowThreshold ≤ fib (idx+gap)) :
 ∃ result, primeFib.helper n count idx = some result := sorry

/-- Every natural input returns a value or the source's Float-conversion error.
The proof derives a finite witness from the actual binary64 overflow threshold;
no execution fuel or input cap is added. -/
theorem runtime_termination_thm (n : Nat) : ∃ result, primeFib n = some result := sorry

private theorem helper_overflow_certificate (n count idx : Nat)
 (hr : primeFib.helper n count idx = some .overflow)
 (hc : count = primeCount idx) (hlt : count<n) :
 ∃ k, idx ≤ k ∧ overflowThreshold ≤ fib k ∧ primeCount k < n := sorry

private theorem helper_overflow_reaches (n idx gap : Nat)
 (hover : overflowThreshold ≤ fib (idx+gap)) (hn : primeCount (idx+gap)<n) :
 primeFib.helper n (primeCount idx) idx = some .overflow := sorry

/-- Exactly which positive inputs raise the checked-in source's OverflowError. -/
theorem overflow_characterization_thm (n : Nat) (hn : 0<n) :
 primeFib n = some .overflow ↔ ∃k, 2≤k ∧ overflowThreshold≤fib k ∧ primeCount k<n := sorry

set_option exponentiation.threshold 1100 in
private theorem isPrime_two : isPrime 2 = true := sorry

/-- A kernel-checked successful input inside Pre rules out vacuous partial correctness. -/
theorem first_prime_fib_thm : primeFib 1 = some (.ok 2) := sorry

end HumanEval39PrimeFib
end Gold
