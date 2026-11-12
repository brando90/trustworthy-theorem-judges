import Mathlib

/-!
# HumanEval/39 — `prime_fib`

Translation of the Python program

```python
def prime_fib(n: int):
    def is_prime(p): ...            # trial division, correct primality test
    f = [0, 1]
    while True:
        f.append(f[-1] + f[-2])
        if is_prime(f[-1]):
            n -= 1
        if n == 0:
            return f[-1]
```

The Python loop appends `f[2], f[3], f[4], …` (the Fibonacci numbers with
`fib 0 = 0`, `fib 1 = 1`) and returns the `n`-th one of those that is prime.
Its `is_prime` is ordinary trial division, so we model it by `Nat.Prime`.

The loop of the Python program need not terminate (whether infinitely many
Fibonacci numbers are prime is an open problem), so the Lean model is driven by
a step budget `fuelBound n`; `0` is returned when the budget is exhausted.  All
specifications are therefore stated under the hypothesis that a value was
actually found.

The file contains a functional implementation, an imperative (`Id.run do`,
mutable state) implementation, unit tests, the specification theorems and the
equivalence proof.
-/

namespace humaneval_39_prime_fib

/-! ## Implementation (functional) -/

/-- Number of Fibonacci indices inspected before giving up.
`fib 43 = 433494437` is the 10th Fibonacci prime, so this budget covers (at
least) all inputs used in the test suite. -/
def fuelBound (n : Nat) : Nat := 64 * n + 64

/-- `go k n fuel` scans the Fibonacci numbers `fib k, fib (k+1), …` (for at most
`fuel` steps) and returns the `n`-th prime among them, or `0` if the budget runs
out. -/
def go (k n fuel : Nat) : Nat :=
  match fuel with
  | 0 => 0
  | f + 1 =>
      if Nat.Prime (Nat.fib k) then
        (if n ≤ 1 then Nat.fib k else go (k + 1) (n - 1) f)
      else
        go (k + 1) n f

/-- `primeFib n` is the `n`-th Fibonacci number that is prime, searching from
index `2` exactly as the Python program does (`f[2]` is the first appended
element).  `0` means "not found within the budget". -/
def primeFib (n : Nat) : Nat := go 2 n (fuelBound n)

/-! ## Unit tests (functional) -/

example : primeFib 1 = 2 := by native_decide
example : primeFib 2 = 3 := by native_decide
example : primeFib 3 = 5 := by native_decide
example : primeFib 4 = 13 := by native_decide
example : primeFib 5 = 89 := by native_decide
example : primeFib 6 = 233 := by native_decide
example : primeFib 7 = 1597 := by native_decide
example : primeFib 8 = 28657 := by native_decide
example : primeFib 9 = 514229 := by native_decide
example : primeFib 10 = 433494437 := by native_decide

#eval primeFib 1
#eval primeFib 5
#eval primeFib 10

/-! ## Pre-condition -/

/-- The Python function only behaves as documented for `n ≥ 1`. -/
def Pre (n : Nat) : Prop := 1 ≤ n

/-! ## Properties -/

/-- `v` is *the* `n`-th prime Fibonacci number: it is `fib j` for a prime
Fibonacci index `j ≥ 2`, and exactly `n - 1` earlier indices `i` with
`2 ≤ i < j` already carry a prime Fibonacci number. -/
def IsNthPrimeFib (n v : Nat) : Prop :=
  ∃ j, 2 ≤ j ∧ Nat.Prime (Nat.fib j) ∧ v = Nat.fib j ∧
    ((Finset.Ico 2 j).filter fun i => Nat.Prime (Nat.fib i)).card = n - 1

/-- The result, when found, is prime. -/
def primality_prop (n : Nat) : Prop := primeFib n ≠ 0 → Nat.Prime (primeFib n)

/-- The result, when found, is a Fibonacci number. -/
def fibonacci_prop (n : Nat) : Prop := primeFib n ≠ 0 → ∃ j, 2 ≤ j ∧ primeFib n = Nat.fib j

/-- The result, when found, is the `n`-th prime Fibonacci number. -/
def nth_prop (n : Nat) : Prop := primeFib n ≠ 0 → IsNthPrimeFib n (primeFib n)

/-- There is at most one `n`-th prime Fibonacci number. -/
def unique_prop (n : Nat) : Prop := ∀ v w, IsNthPrimeFib n v → IsNthPrimeFib n w → v = w

/-! ### Key lemma about the search -/

/-- Full specification of the search loop: whenever `go k n fuel` succeeds, the
value it returns is `fib j` for the index `j ≥ k` that carries the `n`-th prime
Fibonacci number at or after index `k`. -/
theorem go_spec :
    ∀ (fuel k n : Nat), 1 ≤ n → go k n fuel ≠ 0 →
      ∃ j, k ≤ j ∧ Nat.Prime (Nat.fib j) ∧ go k n fuel = Nat.fib j ∧
        ((Finset.Ico k j).filter fun i => Nat.Prime (Nat.fib i)).card = n - 1 := by
  intro fuel
  induction fuel with
  | zero => intro k n _ h; simp [go] at h
  | succ f ih =>
      intro k n hn h
      by_cases hp : Nat.Prime (Nat.fib k)
      · by_cases h1 : n ≤ 1
        · refine ⟨k, le_refl k, hp, ?_, ?_⟩
          · simp [go, hp, h1]
          · have : n = 1 := le_antisymm h1 hn
            simp [this]
        · have hgo : go k n (f + 1) = go (k + 1) (n - 1) f := by simp [go, hp, h1]
          have hn' : 1 ≤ n - 1 := by omega
          have hne : go (k + 1) (n - 1) f ≠ 0 := by rw [hgo] at h; exact h
          obtain ⟨j, hkj, hpj, hval, hcard⟩ := ih (k + 1) (n - 1) hn' hne
          refine ⟨j, by omega, hpj, by rw [hgo]; exact hval, ?_⟩
          have hins : Finset.Ico k j = insert k (Finset.Ico (k + 1) j) := by
            ext x
            simp only [Finset.mem_Ico, Finset.mem_insert]
            omega
          have hnotmem : k ∉ (Finset.Ico (k + 1) j).filter fun i => Nat.Prime (Nat.fib i) := by
            simp [Finset.mem_filter, Finset.mem_Ico]
          rw [hins, Finset.filter_insert, if_pos hp, Finset.card_insert_of_notMem hnotmem,
            hcard]
          omega
      · have hgo : go k n (f + 1) = go (k + 1) n f := by simp [go, hp]
        have hne : go (k + 1) n f ≠ 0 := by rw [hgo] at h; exact h
        obtain ⟨j, hkj, hpj, hval, hcard⟩ := ih (k + 1) n hn hne
        refine ⟨j, by omega, hpj, by rw [hgo]; exact hval, ?_⟩
        have hins : Finset.Ico k j = insert k (Finset.Ico (k + 1) j) := by
          ext x
          simp only [Finset.mem_Ico, Finset.mem_insert]
          omega
        rw [hins, Finset.filter_insert, if_neg hp, hcard]

/-! ### Theorems -/

theorem primality_thm (n : Nat) (hn : Pre n) : primality_prop n := by
  intro h
  obtain ⟨j, _, hpj, hval, _⟩ := go_spec (fuelBound n) 2 n hn h
  rw [show primeFib n = go 2 n (fuelBound n) from rfl, hval]
  exact hpj

theorem fibonacci_thm (n : Nat) (hn : Pre n) : fibonacci_prop n := by
  intro h
  obtain ⟨j, hkj, _, hval, _⟩ := go_spec (fuelBound n) 2 n hn h
  exact ⟨j, hkj, hval⟩

theorem nth_thm (n : Nat) (hn : Pre n) : nth_prop n := by
  intro h
  obtain ⟨j, hkj, hpj, hval, hcard⟩ := go_spec (fuelBound n) 2 n hn h
  exact ⟨j, hkj, hpj, hval, hcard⟩

theorem unique_thm (n : Nat) : unique_prop n := by
  rintro v w ⟨j, hj2, hjp, hjv, hjc⟩ ⟨i, hi2, hip, hiw, hic⟩
  -- the counting condition pins down the index
  have key : ∀ a b : Nat, 2 ≤ b → Nat.Prime (Nat.fib b) →
      ((Finset.Ico 2 a).filter fun t => Nat.Prime (Nat.fib t)).card
        = ((Finset.Ico 2 b).filter fun t => Nat.Prime (Nat.fib t)).card → a ≤ b := by
    intro a b hb hpb hcards
    by_contra hlt
    push_neg at hlt
    have hsub : insert b ((Finset.Ico 2 b).filter fun t => Nat.Prime (Nat.fib t))
        ⊆ (Finset.Ico 2 a).filter fun t => Nat.Prime (Nat.fib t) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_Ico] at hx ⊢
      rcases hx with rfl | ⟨⟨h1, h2⟩, h3⟩
      · exact ⟨⟨hb, hlt⟩, hpb⟩
      · exact ⟨⟨h1, by omega⟩, h3⟩
    have hnm : b ∉ (Finset.Ico 2 b).filter fun t => Nat.Prime (Nat.fib t) := by
      simp only [Finset.mem_filter, Finset.mem_Ico, not_and]
      intro hmem
      omega
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hnm] at hcard
    omega
  have h1 := key j i hi2 hip (by rw [hjc, hic])
  have h2 := key i j hj2 hjp (by rw [hjc, hic])
  have hij : i = j := le_antisymm h2 h1
  rw [hjv, hiw, hij]

/-! ## Post-condition -/

/-- Full post-condition: the returned value (when the search succeeded) is the
`n`-th prime Fibonacci number, it is prime, it is a Fibonacci number, and such a
value is unique. -/
def Post_prop (n : Nat) : Prop :=
  primality_prop n ∧ fibonacci_prop n ∧ nth_prop n ∧ unique_prop n

/-- Correctness: the pre-condition implies the post-condition. -/
theorem correctness_thm (n : Nat) (hn : Pre n) : Post_prop n :=
  ⟨primality_thm n hn, fibonacci_thm n hn, nth_thm n hn, unique_thm n⟩

/-! ## Implementation (imperative) -/

/-- One iteration of the Python `while True` body, on the state
`(a, b, cnt, res) = (f[-2], f[-1], n, result)`.  Once `cnt = 0` the answer has
been produced and the state is frozen. -/
def istep (s : Nat × Nat × Nat × Nat) : Nat × Nat × Nat × Nat := Id.run do
  let (a, b, cnt, res) := s
  if cnt = 0 then
    return (a, b, cnt, res)
  -- f.append(f[-1] + f[-2])
  let mut a' := b
  let mut b' := a + b
  let mut cnt' := cnt
  let mut res' := res
  if Nat.Prime b' then
    cnt' := cnt' - 1          -- n -= 1
    if cnt' = 0 then
      res' := b'              -- return f[-1]
  return (a', b', cnt', res')

/-- The imperative loop, run over a list of ticks. -/
def impLoop (ticks : List Unit) (s : Nat × Nat × Nat × Nat) :
    Nat × Nat × Nat × Nat := Id.run do
  let mut st := s
  for _ in ticks do
    st := istep st
  return st

/-- Imperative version of `primeFib`, with mutable state `(f[-2], f[-1], n, res)`. -/
def primeFibImp (n : Nat) : Nat := Id.run do
  let mut st : Nat × Nat × Nat × Nat := (0, 1, n, 0)
  for _ in List.replicate (fuelBound n) () do
    st := istep st
  return st.2.2.2

/-! ## Unit tests (imperative) -/

example : primeFibImp 1 = 2 := by native_decide
example : primeFibImp 2 = 3 := by native_decide
example : primeFibImp 3 = 5 := by native_decide
example : primeFibImp 4 = 13 := by native_decide
example : primeFibImp 5 = 89 := by native_decide
example : primeFibImp 6 = 233 := by native_decide
example : primeFibImp 7 = 1597 := by native_decide
example : primeFibImp 8 = 28657 := by native_decide
example : primeFibImp 9 = 514229 := by native_decide
example : primeFibImp 10 = 433494437 := by native_decide

#eval primeFibImp 5
#eval primeFibImp 10

/-! ## Equivalence: functional = imperative -/

/-- Closed form of one imperative step. -/
theorem istep_eq (a b cnt res : Nat) :
    istep (a, b, cnt, res) =
      if cnt = 0 then (a, b, cnt, res)
      else if Nat.Prime (a + b) then (b, a + b, cnt - 1, if cnt - 1 = 0 then a + b else res)
      else (b, a + b, cnt, res) := by
  unfold istep
  simp only [Id.run]
  split
  · rfl
  · split
    · split <;> rfl
    · rfl

theorem impLoop_nil (s : Nat × Nat × Nat × Nat) : impLoop [] s = s := rfl

theorem impLoop_cons (u : Unit) (l : List Unit) (s : Nat × Nat × Nat × Nat) :
    impLoop (u :: l) s = impLoop l (istep s) := by
  simp [impLoop, Id.run]

theorem primeFibImp_eq_impLoop (n : Nat) :
    primeFibImp n = (impLoop (List.replicate (fuelBound n) ()) (0, 1, n, 0)).2.2.2 := rfl

/-- Once the counter has reached `0` the state no longer changes. -/
theorem impLoop_done (l : List Unit) (a b res : Nat) :
    impLoop l (a, b, 0, res) = (a, b, 0, res) := by
  induction l with
  | nil => rfl
  | cons u l ih => rw [impLoop_cons, istep_eq]; simpa using ih

/-- Main loop invariant: starting from `(fib m, fib (m+1), n, 0)` the imperative
loop computes exactly what the functional search from index `m + 2` computes. -/
theorem impLoop_eq_go :
    ∀ (fuel m n : Nat), 1 ≤ n →
      (impLoop (List.replicate fuel ()) (Nat.fib m, Nat.fib (m + 1), n, 0)).2.2.2
        = go (m + 2) n fuel := by
  intro fuel
  induction fuel with
  | zero => intro m n _; simp [impLoop, go]
  | succ f ih =>
      intro m n hn
      have e1 : m + 1 + 1 = m + 2 := by omega
      have e2 : m + 1 + 2 = m + 2 + 1 := by omega
      have hfib : Nat.fib m + Nat.fib (m + 1) = Nat.fib (m + 2) := (Nat.fib_add_two).symm
      rw [List.replicate_succ, impLoop_cons, istep_eq, if_neg (show ¬ n = 0 by omega), hfib]
      by_cases hp : Nat.Prime (Nat.fib (m + 2))
      · rw [if_pos hp]
        by_cases h1 : n - 1 = 0
        · have hn1 : n ≤ 1 := by omega
          rw [if_pos h1, h1, impLoop_done]
          simp [go, hp, hn1]
        · rw [if_neg h1]
          have hih := ih (m + 1) (n - 1) (by omega)
          rw [e1, e2] at hih
          rw [hih]
          simp [go, hp, show ¬ n ≤ 1 by omega]
      · rw [if_neg hp]
        have hih := ih (m + 1) n hn
        rw [e1, e2] at hih
        rw [hih]
        simp [go, hp]

/-- The functional and imperative implementations agree on all valid inputs. -/
theorem equivalence_thm (n : Nat) (hn : Pre n) : primeFib n = primeFibImp n := by
  rw [primeFibImp_eq_impLoop]
  have h := impLoop_eq_go (fuelBound n) 0 n hn
  norm_num [Nat.fib_one, Nat.fib_zero] at h
  rw [h]
  rfl

end humaneval_39_prime_fib
