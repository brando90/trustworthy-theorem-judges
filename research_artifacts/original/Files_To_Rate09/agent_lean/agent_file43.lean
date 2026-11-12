import Mathlib

/-!
# VeriBench — HumanEval/39 `prime_fib`

Translate the Python function `prime_fib(n)`, which returns the `n`-th
(1-indexed) Fibonacci number that is also prime.

The Python program starts from the Fibonacci pair `[0, 1]` and repeatedly appends
the next sum. After each append it tests primality by trial division up to
`min(floor(sqrt(p)) + 1, p - 1)`. The first ten values are
`2, 3, 5, 13, 89, 233, 1597, 28657, 514229, 433494437`,
at Fibonacci indices `3, 4, 5, 7, 11, 13, 17, 23, 29, 43`.

`Nat.fib 0 = 0` and `Nat.fib 1 = 1` are not prime, so scanning from index `0`
returns the same prime subsequence as the Python loop, which first tests
`Nat.fib 2`. For every integer below `2^53` (hence for every value this search
encounters), Python's `int(math.sqrt(p))` agrees with `Nat.sqrt`.

The Python loop is partial: it terminates for a given `n` only if at least `n`
prime Fibonacci numbers exist. Infinitely many Fibonacci primes is an open
question, so the total Lean implementation searches indices `< searchBound`
(`60`, which strictly contains the HumanEval range: the 10th prime Fibonacci
number is `Nat.fib 43`). Partial correctness is proved for every `n`, and the
full HumanEval specification is proved unconditionally for every `1 ≤ n ≤ 10`.
-/

namespace humaneval_39_prime_fib

def isPrimeAux (p k upper : Nat) : Bool :=
  if k ≥ upper then true
  else if p % k = 0 then false
  else isPrimeAux p (k + 1) upper
termination_by upper - k

def isPrime (p : Nat) : Bool :=
  if p < 2 then false else isPrimeAux p 2 (min (Nat.sqrt p + 1) (p - 1))

theorem isPrimeAux_iff (p k upper : Nat) :
    isPrimeAux p k upper = true ↔ ∀ m, k ≤ m → m < upper → ¬ m ∣ p := by
  induction hdiff : upper - k generalizing k with
  | zero =>
    unfold isPrimeAux
    have hge : upper ≤ k := by omega
    simp [hge]
    intro m _ hm2
    omega
  | succ d ih =>
    have hklt : k < upper := by omega
    conv_lhs => unfold isPrimeAux
    simp [show ¬ (upper ≤ k) by omega]
    by_cases hdiv : p % k = 0
    · simp [hdiv]
      exact ⟨k, le_rfl, hklt, Nat.dvd_of_mod_eq_zero hdiv⟩
    · simp [hdiv]
      rw [ih (k + 1) (by omega)]
      constructor
      · intro h m hm1 hm2
        by_cases heq : m = k
        · subst heq
          rw [Nat.dvd_iff_mod_eq_zero]
          exact hdiv
        · exact h m (by omega) hm2
      · intro h m hm1 hm2
        exact h m (by omega) hm2

lemma pred_sq_gt (p : Nat) (hp : 4 ≤ p) : p < (p - 1) * (p - 1) := by
  have h2 : 2 ≤ p - 1 := by omega
  have h1 : 1 < p - 1 := by omega
  calc
    p = (p - 1) + 1 := by omega
    _ < (p - 1) + (p - 1) := Nat.add_lt_add_left h1 (p - 1)
    _ = 2 * (p - 1) := by rw [Nat.two_mul]
    _ ≤ (p - 1) * (p - 1) := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left (p - 1) h2

theorem isPrime_iff (p : Nat) : isPrime p = true ↔ Nat.Prime p := by
  unfold isPrime
  by_cases hp : p < 2
  · simp [hp]
    interval_cases p <;> decide
  · simp [hp]
    rw [isPrimeAux_iff, Nat.prime_def_le_sqrt]
    constructor
    · intro h
      refine ⟨Nat.not_lt.mp hp, ?_⟩
      intro m hm2 hmle
      apply h m hm2
      have hm_sqrt : m < Nat.sqrt p + 1 := Nat.lt_succ_of_le hmle
      have hm_pm1 : m < p - 1 := by
        by_cases h4 : p < 4
        · interval_cases p
          · have hsqrt : Nat.sqrt 2 = 1 := by decide
            have : m ≤ 1 := by simpa [hsqrt] using hmle
            omega
          · have hsqrt : Nat.sqrt 3 = 1 := by decide
            have : m ≤ 1 := by simpa [hsqrt] using hmle
            omega
        · have hp4 : 4 ≤ p := by omega
          have hmul : Nat.sqrt p * Nat.sqrt p ≤ p := Nat.sqrt_le p
          have hlt : Nat.sqrt p < p := Nat.sqrt_lt_self (by omega)
          have hle2 : Nat.sqrt p ≤ p - 2 := by
            by_contra hgt
            have heq : Nat.sqrt p = p - 1 := by omega
            have : (p - 1) * (p - 1) ≤ p := by simpa [heq] using hmul
            exact not_le_of_gt (pred_sq_gt p hp4) this
          omega
      exact lt_min hm_sqrt hm_pm1
    · intro ⟨_, hall⟩ m hm2 hlt
      apply hall m hm2
      have : m < Nat.sqrt p + 1 := lt_of_lt_of_le hlt (min_le_left _ _)
      omega

def searchBound : Nat := 60

def primeFibFrom (count idx : Nat) : Nat :=
  if count = 0 ∨ searchBound ≤ idx then 0
  else if isPrime (Nat.fib idx) = true then
    if count = 1 then Nat.fib idx
    else primeFibFrom (count - 1) (idx + 1)
  else primeFibFrom count (idx + 1)
termination_by searchBound - idx
decreasing_by all_goals simp_wf; omega

def primeFib (n : Nat) : Nat := primeFibFrom n 0

def fibPrimeCount (n : Nat) : Nat := Nat.count (fun i => Nat.Prime (Nat.fib i)) n

theorem primeFibFrom_not_prime (count idx : Nat) (hcount : count ≠ 0) (hidx : idx < searchBound)
    (hp : ¬ Nat.Prime (Nat.fib idx)) :
    primeFibFrom count idx = primeFibFrom count (idx + 1) := by
  conv_lhs => unfold primeFibFrom
  simp [hcount, show ¬ searchBound ≤ idx by omega, isPrime_iff, hp]

theorem primeFibFrom_prime_one (idx : Nat) (hidx : idx < searchBound) (hp : Nat.Prime (Nat.fib idx)) :
    primeFibFrom 1 idx = Nat.fib idx := by
  conv_lhs => unfold primeFibFrom
  simp [show ¬ searchBound ≤ idx by omega, isPrime_iff, hp]

theorem primeFibFrom_prime_succ (count idx : Nat) (hcount : 1 < count) (hidx : idx < searchBound)
    (hp : Nat.Prime (Nat.fib idx)) :
    primeFibFrom count idx = primeFibFrom (count - 1) (idx + 1) := by
  conv_lhs => unfold primeFibFrom
  have hc0 : count ≠ 0 := by omega
  have hc1 : count ≠ 1 := by omega
  simp [hc0, show ¬ searchBound ≤ idx by omega, isPrime_iff, hp, hc1]

theorem primeFibFrom_spec (count idx k : Nat) (hcount : 0 < count) (hklt : k < searchBound)
    (hle : idx ≤ k) (hp : Nat.Prime (Nat.fib k))
    (hcnt : fibPrimeCount k = fibPrimeCount idx + (count - 1)) :
    primeFibFrom count idx = Nat.fib k := by
  induction hgap : k - idx generalizing count idx k with
  | zero =>
    have hk : k = idx := by omega
    subst hk
    have hc1 : count = 1 := by
      have : fibPrimeCount k = fibPrimeCount k + (count - 1) := hcnt
      omega
    subst hc1
    exact primeFibFrom_prime_one k hklt hp
  | succ gap ih =>
    have hidx_lt_k : idx < k := by omega
    have hidx : idx < searchBound := lt_of_le_of_lt hle hklt
    by_cases hpidx : Nat.Prime (Nat.fib idx)
    · have hcgt : 1 < count := by
        by_contra hle1
        have hc1 : count = 1 := by omega
        subst hc1
        have hce : fibPrimeCount k = fibPrimeCount idx := by simpa using hcnt
        have heq := Nat.count_injective (p := fun i => Nat.Prime (Nat.fib i)) hpidx hp hce.symm
        omega
      rw [primeFibFrom_prime_succ count idx hcgt hidx hpidx]
      have hcs : fibPrimeCount (idx + 1) = fibPrimeCount idx + 1 := by
        unfold fibPrimeCount
        rw [Nat.count_succ, if_pos hpidx]
      apply ih (count - 1) (idx + 1) k (by omega) (by omega) (by omega) hp
      · rw [hcs]; omega
      · omega
    · rw [primeFibFrom_not_prime count idx (by omega) hidx hpidx]
      have hcs : fibPrimeCount (idx + 1) = fibPrimeCount idx := by
        unfold fibPrimeCount
        rw [Nat.count_succ, if_neg hpidx]
        omega
      apply ih count (idx + 1) k (by omega) (by omega) (by omega) hp
      · rw [hcs]; exact hcnt
      · omega

def primeFibFromList (count : Nat) (idxs : List Nat) : Nat :=
  match idxs with
  | [] => 0
  | idx :: rest =>
    if count = 0 then 0
    else if isPrime (Nat.fib idx) = true then
      if count = 1 then Nat.fib idx
      else primeFibFromList (count - 1) rest
    else primeFibFromList count rest

theorem primeFibFrom_eq_list (count idx : Nat) (hidx : idx ≤ searchBound) :
    primeFibFrom count idx = primeFibFromList count (List.range' idx (searchBound - idx)) := by
  induction hdiff : searchBound - idx generalizing count idx with
  | zero =>
    have hidx' : idx = searchBound := by omega
    subst hidx'
    simp [primeFibFrom, primeFibFromList, List.range']
  | succ d ih =>
    have hlt : idx < searchBound := by omega
    have hcons : List.range' idx (d + 1) = idx :: List.range' (idx + 1) d := by
      rw [List.range'_eq_cons_iff]
      refine ⟨rfl, by omega, ?_⟩
      simp
    conv_lhs => unfold primeFibFrom
    rw [hcons]
    by_cases hc0 : count = 0
    · simp [primeFibFromList, hc0]
    · simp [primeFibFromList, hc0, show ¬ searchBound ≤ idx by omega]
      by_cases hp : isPrime (Nat.fib idx) = true
      · simp [hp]
        by_cases hc1 : count = 1
        · simp [hc1]
        · simp [hc1]
          exact ih (count - 1) (idx + 1) (by omega) (by omega)
      · simp [hp]
        exact ih count (idx + 1) (by omega) (by omega)

def loopStep (idx : Nat) (r : MProd Nat Nat) : Id (ForInStep (MProd Nat Nat)) :=
  if r.1 = 0 then pure (ForInStep.done r)
  else if isPrime (Nat.fib idx) = true then
    if r.1 = 1 then pure (ForInStep.yield ⟨r.1 - 1, Nat.fib idx⟩)
    else pure (ForInStep.yield ⟨r.1 - 1, r.2⟩)
  else pure (ForInStep.yield r)

def loop (count result : Nat) (idxs : List Nat) : MProd Nat Nat :=
  match idxs with
  | [] => ⟨count, result⟩
  | idx :: rest =>
    if count = 0 then ⟨count, result⟩
    else if isPrime (Nat.fib idx) = true then
      if count = 1 then loop (count - 1) (Nat.fib idx) rest
      else loop (count - 1) result rest
    else loop count result rest

theorem loop_zero (result : Nat) (idxs : List Nat) : (loop 0 result idxs).2 = result := by
  cases idxs <;> simp [loop]

theorem forIn_eq_loop (count result : Nat) (idxs : List Nat) :
    forIn idxs (⟨count, result⟩ : MProd Nat Nat) loopStep = pure (loop count result idxs) := by
  induction idxs generalizing count result with
  | nil => simp [loop]
  | cons idx rest ih =>
    simp [List.forIn_cons, loop, loopStep]
    split_ifs <;> simp [ih]

theorem loop_snd_eq_list (count : Nat) (idxs : List Nat) :
    (loop count 0 idxs).2 = primeFibFromList count idxs := by
  induction idxs generalizing count with
  | nil => simp [loop, primeFibFromList]
  | cons idx rest ih =>
    unfold loop primeFibFromList
    split_ifs with h0 hp h1
    · rfl
    · have : count - 1 = 0 := by omega
      simp [this, loop_zero]
    · rw [ih]
    · rw [ih]


/-! ## Unit tests -/

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
#eval primeFib 2
#eval primeFib 3
#eval primeFib 4
#eval primeFib 5
#eval primeFib 6
#eval primeFib 7
#eval primeFib 8
#eval primeFib 9
#eval primeFib 10

/-! ## Pre-condition -/

/-- The Python docstring asks for the `n`-th prime Fibonacci number, `n ≥ 1`. -/
def Pre (n : Nat) : Prop := 0 < n

/-- The `n`-th prime Fibonacci number occurs at an index below `searchBound`.
`0 < n` is included so that Nat subtraction in `n - 1` cannot collapse `n = 0`
to a spurious witness. -/
def hasNthFibPrime (n : Nat) : Prop :=
  0 < n ∧ ∃ k, k < searchBound ∧ Nat.Prime (Nat.fib k) ∧ fibPrimeCount k = n - 1

theorem fibPrimeCount_step_not {n c : Nat}
    (hc : fibPrimeCount n = c) (hp : ¬ Nat.Prime (Nat.fib n)) :
    fibPrimeCount (n + 1) = c := by
  unfold fibPrimeCount at *
  rw [Nat.count_succ, if_neg hp, hc]
  omega

theorem fibPrimeCount_step_yes {n c : Nat}
    (hc : fibPrimeCount n = c) (hp : Nat.Prime (Nat.fib n)) :
    fibPrimeCount (n + 1) = c + 1 := by
  unfold fibPrimeCount at *
  rw [Nat.count_succ, if_pos hp, hc]

theorem fibPrimeCount_0 : fibPrimeCount 0 = 0 := Nat.count_zero _

theorem fibPrimeCount_1 : fibPrimeCount 1 = 0 :=
  fibPrimeCount_step_not fibPrimeCount_0 (by norm_num)

theorem fibPrimeCount_2 : fibPrimeCount 2 = 0 :=
  fibPrimeCount_step_not fibPrimeCount_1 (by norm_num)

theorem fibPrimeCount_3 : fibPrimeCount 3 = 0 :=
  fibPrimeCount_step_not fibPrimeCount_2 (by norm_num)

theorem fibPrimeCount_4 : fibPrimeCount 4 = 1 :=
  fibPrimeCount_step_yes fibPrimeCount_3 (by norm_num)

theorem fibPrimeCount_5 : fibPrimeCount 5 = 2 :=
  fibPrimeCount_step_yes fibPrimeCount_4 (by norm_num)

theorem fibPrimeCount_6 : fibPrimeCount 6 = 3 :=
  fibPrimeCount_step_yes fibPrimeCount_5 (by norm_num)

theorem fibPrimeCount_7 : fibPrimeCount 7 = 3 :=
  fibPrimeCount_step_not fibPrimeCount_6 (by norm_num)

theorem fibPrimeCount_8 : fibPrimeCount 8 = 4 :=
  fibPrimeCount_step_yes fibPrimeCount_7 (by norm_num)

theorem fibPrimeCount_9 : fibPrimeCount 9 = 4 :=
  fibPrimeCount_step_not fibPrimeCount_8 (by norm_num)

theorem fibPrimeCount_10 : fibPrimeCount 10 = 4 :=
  fibPrimeCount_step_not fibPrimeCount_9 (by norm_num)

theorem fibPrimeCount_11 : fibPrimeCount 11 = 4 :=
  fibPrimeCount_step_not fibPrimeCount_10 (by norm_num)

theorem fibPrimeCount_12 : fibPrimeCount 12 = 5 :=
  fibPrimeCount_step_yes fibPrimeCount_11 (by norm_num)

theorem fibPrimeCount_13 : fibPrimeCount 13 = 5 :=
  fibPrimeCount_step_not fibPrimeCount_12 (by norm_num)

theorem fibPrimeCount_14 : fibPrimeCount 14 = 6 :=
  fibPrimeCount_step_yes fibPrimeCount_13 (by norm_num)

theorem fibPrimeCount_15 : fibPrimeCount 15 = 6 :=
  fibPrimeCount_step_not fibPrimeCount_14 (by norm_num)

theorem fibPrimeCount_16 : fibPrimeCount 16 = 6 :=
  fibPrimeCount_step_not fibPrimeCount_15 (by norm_num)

theorem fibPrimeCount_17 : fibPrimeCount 17 = 6 :=
  fibPrimeCount_step_not fibPrimeCount_16 (by norm_num)

theorem fibPrimeCount_18 : fibPrimeCount 18 = 7 :=
  fibPrimeCount_step_yes fibPrimeCount_17 (by norm_num)

theorem fibPrimeCount_19 : fibPrimeCount 19 = 7 :=
  fibPrimeCount_step_not fibPrimeCount_18 (by norm_num)

theorem fibPrimeCount_20 : fibPrimeCount 20 = 7 :=
  fibPrimeCount_step_not fibPrimeCount_19 (by norm_num)

theorem fibPrimeCount_21 : fibPrimeCount 21 = 7 :=
  fibPrimeCount_step_not fibPrimeCount_20 (by norm_num)

theorem fibPrimeCount_22 : fibPrimeCount 22 = 7 :=
  fibPrimeCount_step_not fibPrimeCount_21 (by norm_num)

theorem fibPrimeCount_23 : fibPrimeCount 23 = 7 :=
  fibPrimeCount_step_not fibPrimeCount_22 (by norm_num)

theorem fibPrimeCount_24 : fibPrimeCount 24 = 8 :=
  fibPrimeCount_step_yes fibPrimeCount_23 (by norm_num)

theorem fibPrimeCount_25 : fibPrimeCount 25 = 8 :=
  fibPrimeCount_step_not fibPrimeCount_24 (by norm_num)

theorem fibPrimeCount_26 : fibPrimeCount 26 = 8 :=
  fibPrimeCount_step_not fibPrimeCount_25 (by norm_num)

theorem fibPrimeCount_27 : fibPrimeCount 27 = 8 :=
  fibPrimeCount_step_not fibPrimeCount_26 (by norm_num)

theorem fibPrimeCount_28 : fibPrimeCount 28 = 8 :=
  fibPrimeCount_step_not fibPrimeCount_27 (by norm_num)

theorem fibPrimeCount_29 : fibPrimeCount 29 = 8 :=
  fibPrimeCount_step_not fibPrimeCount_28 (by norm_num)

theorem fibPrimeCount_30 : fibPrimeCount 30 = 9 :=
  fibPrimeCount_step_yes fibPrimeCount_29 (by norm_num)

theorem fibPrimeCount_31 : fibPrimeCount 31 = 9 :=
  fibPrimeCount_step_not fibPrimeCount_30 (by norm_num)

theorem fibPrimeCount_32 : fibPrimeCount 32 = 9 :=
  fibPrimeCount_step_not fibPrimeCount_31 (by norm_num)

theorem fibPrimeCount_33 : fibPrimeCount 33 = 9 :=
  fibPrimeCount_step_not fibPrimeCount_32 (by norm_num)

theorem fibPrimeCount_34 : fibPrimeCount 34 = 9 :=
  fibPrimeCount_step_not fibPrimeCount_33 (by norm_num)

theorem fibPrimeCount_35 : fibPrimeCount 35 = 9 :=
  fibPrimeCount_step_not fibPrimeCount_34 (by norm_num)

theorem fibPrimeCount_36 : fibPrimeCount 36 = 9 :=
  fibPrimeCount_step_not fibPrimeCount_35 (by norm_num)

theorem fibPrimeCount_37 : fibPrimeCount 37 = 9 :=
  fibPrimeCount_step_not fibPrimeCount_36 (by norm_num)

theorem fibPrimeCount_38 : fibPrimeCount 38 = 9 :=
  fibPrimeCount_step_not fibPrimeCount_37 (by norm_num)

theorem fibPrimeCount_39 : fibPrimeCount 39 = 9 :=
  fibPrimeCount_step_not fibPrimeCount_38 (by norm_num)

theorem fibPrimeCount_40 : fibPrimeCount 40 = 9 :=
  fibPrimeCount_step_not fibPrimeCount_39 (by norm_num)

theorem fibPrimeCount_41 : fibPrimeCount 41 = 9 :=
  fibPrimeCount_step_not fibPrimeCount_40 (by norm_num)

theorem fibPrimeCount_42 : fibPrimeCount 42 = 9 :=
  fibPrimeCount_step_not fibPrimeCount_41 (by norm_num)

theorem fibPrimeCount_43 : fibPrimeCount 43 = 9 :=
  fibPrimeCount_step_not fibPrimeCount_42 (by norm_num)

theorem fibPrimeCount_44 : fibPrimeCount 44 = 10 :=
  fibPrimeCount_step_yes fibPrimeCount_43 (by norm_num)


/-! ## Properties -/

theorem primeFib_eq_of_index (n k : Nat) (hn : 0 < n) (hk : k < searchBound)
    (hp : Nat.Prime (Nat.fib k)) (hc : fibPrimeCount k = n - 1) :
    primeFib n = Nat.fib k := by
  unfold primeFib
  apply primeFibFrom_spec n 0 k hn hk (Nat.zero_le _) hp
  have h0 : fibPrimeCount 0 = 0 := Nat.count_zero _
  rw [h0, Nat.zero_add]
  exact hc

theorem fibPrimeIndex_unique (j k c : Nat) (hpj : Nat.Prime (Nat.fib j))
    (hpk : Nat.Prime (Nat.fib k)) (hcj : fibPrimeCount j = c) (hck : fibPrimeCount k = c) :
    j = k := by
  apply Nat.count_injective (p := fun i => Nat.Prime (Nat.fib i)) hpj hpk
  simpa [fibPrimeCount] using hcj.trans hck.symm

theorem fibPrime_index_ge_three (k : Nat) (hp : Nat.Prime (Nat.fib k)) : 3 ≤ k := by
  by_contra hlt
  have : k < 3 := by omega
  interval_cases k <;> norm_num at hp

theorem count_succ_of_fibPrime (k : Nat) (hp : Nat.Prime (Nat.fib k)) :
    fibPrimeCount (k + 1) = fibPrimeCount k + 1 := by
  unfold fibPrimeCount
  rw [Nat.count_succ, if_pos hp]

theorem primeFib_witness (n : Nat) (hn : 0 < n) (h : hasNthFibPrime n) :
    ∃ k, primeFib n = Nat.fib k ∧ Nat.Prime (Nat.fib k) ∧
      fibPrimeCount k = n - 1 ∧ fibPrimeCount (k + 1) = n ∧
      ∀ j, Nat.Prime (Nat.fib j) → fibPrimeCount j = n - 1 → j = k := by
  rcases h with ⟨_, k, hk, hp, hc⟩
  refine ⟨k, primeFib_eq_of_index n k hn hk hp hc, hp, hc, ?_, ?_⟩
  · rw [count_succ_of_fibPrime k hp, hc]; omega
  · intro j hpj hcj
    exact fibPrimeIndex_unique j k (n - 1) hpj hp hcj hc

/-- If the search can reach the `n`-th prime Fibonacci number, the result is prime. -/
def is_prime_prop (n : Nat) : Prop :=
  hasNthFibPrime n → Nat.Prime (primeFib n)

theorem is_prime_thm (n : Nat) : is_prime_prop n := by
  intro h
  obtain ⟨k, heq, hp, _, _, _⟩ := primeFib_witness n h.1 h
  simpa [heq] using hp

/-- The result is a Fibonacci number. -/
def is_fibonacci_prop (n : Nat) : Prop :=
  hasNthFibPrime n → ∃ k, primeFib n = Nat.fib k

theorem is_fibonacci_thm (n : Nat) : is_fibonacci_prop n := by
  intro h
  obtain ⟨k, heq, _, _, _, _⟩ := primeFib_witness n h.1 h
  exact ⟨k, heq⟩

/-- The result is exactly the `n`-th prime Fibonacci number:
there are `n - 1` prime Fibonacci numbers of smaller index, it itself is one,
and the index is unique. -/
def is_nth_prop (n : Nat) : Prop :=
  hasNthFibPrime n →
    ∃ k, primeFib n = Nat.fib k ∧ Nat.Prime (Nat.fib k) ∧
      fibPrimeCount k = n - 1 ∧ fibPrimeCount (k + 1) = n ∧
      ∀ j, Nat.Prime (Nat.fib j) → fibPrimeCount j = n - 1 → j = k

theorem is_nth_thm (n : Nat) : is_nth_prop n := by
  intro h
  exact primeFib_witness n h.1 h

/-- Every prime Fibonacci number is at least `2`. -/
def positive_prop (n : Nat) : Prop :=
  hasNthFibPrime n → 1 < primeFib n

theorem positive_thm (n : Nat) : positive_prop n := by
  intro h
  obtain ⟨k, heq, hp, _, _, _⟩ := primeFib_witness n h.1 h
  have hk : 3 ≤ k := fibPrime_index_ge_three k hp
  have hfib3 : Nat.fib 3 = 2 := by decide
  have hle : Nat.fib 3 ≤ Nat.fib k := Nat.fib_mono hk
  have h2 : 2 ≤ Nat.fib k := by simpa [hfib3] using hle
  have hpos : 1 < primeFib n := by
    rw [heq]
    omega
  exact hpos

theorem exists_fibPrime_of_count {k target : Nat} (ht : target < fibPrimeCount k) :
    ∃ j, j < k ∧ Nat.Prime (Nat.fib j) ∧ fibPrimeCount j = target := by
  induction k with
  | zero =>
    simp [fibPrimeCount, Nat.count_zero] at ht
  | succ k ih =>
    by_cases hp : Nat.Prime (Nat.fib k)
    · have hcs : fibPrimeCount (k + 1) = fibPrimeCount k + 1 := count_succ_of_fibPrime k hp
      rw [hcs] at ht
      by_cases hlt : target < fibPrimeCount k
      · obtain ⟨j, hj, hpj, hc⟩ := ih hlt
        exact ⟨j, Nat.lt_succ_of_lt hj, hpj, hc⟩
      · have heq : target = fibPrimeCount k := by omega
        exact ⟨k, Nat.lt_succ_self _, hp, heq.symm⟩
    · have hcs : fibPrimeCount (k + 1) = fibPrimeCount k := by
        unfold fibPrimeCount
        rw [Nat.count_succ, if_neg hp]
        omega
      rw [hcs] at ht
      obtain ⟨j, hj, hpj, hc⟩ := ih ht
      exact ⟨j, Nat.lt_succ_of_lt hj, hpj, hc⟩

/-- `primeFib` is strictly increasing on inputs whose prime Fibonacci numbers exist. -/
def monotonic_prop (n : Nat) : Prop :=
  Pre n → ∀ m, n < m → hasNthFibPrime m → primeFib n < primeFib m

theorem monotonic_thm (n : Nat) : monotonic_prop n := by
  intro hn m hnm hm
  rcases hm with ⟨hm0, km, hkm_lt, hkm_p, hkm_c⟩
  have hm' : hasNthFibPrime m := ⟨hm0, km, hkm_lt, hkm_p, hkm_c⟩
  have hltc : n - 1 < fibPrimeCount km := by
    have hle : n ≤ m - 1 := Nat.le_pred_of_lt hnm
    have hlt : n - 1 < n := Nat.sub_lt hn (by decide)
    have : n - 1 < m - 1 := lt_of_lt_of_le hlt hle
    simpa [hkm_c] using this
  obtain ⟨j, hj_lt, hpj, hcj⟩ := exists_fibPrime_of_count hltc
  have hexn : hasNthFibPrime n := ⟨hn, j, lt_trans hj_lt hkm_lt, hpj, hcj⟩
  obtain ⟨kn, hkn_eq, hkn_p, hkn_c, _, _⟩ := primeFib_witness n hn hexn
  obtain ⟨km', hkm_eq, _, hkm_c', _, _⟩ := primeFib_witness m hm0 hm'
  have hkn_lt_km : kn < km' := by
    have hc : fibPrimeCount kn < fibPrimeCount km' := by
      rw [hkn_c, hkm_c']
      omega
    by_contra hge
    have hle : km' ≤ kn := by omega
    have hmono : fibPrimeCount km' ≤ fibPrimeCount kn :=
      Nat.count_monotone (p := fun i => Nat.Prime (Nat.fib i)) hle
    omega
  have hkn2 : 2 ≤ kn := by
    have := fibPrime_index_ge_three kn hkn_p
    omega
  have hfib : Nat.fib kn < Nat.fib km' := (Nat.fib_lt_fib hkn2).mpr hkn_lt_km
  simpa [hkn_eq, hkm_eq] using hfib

/-- Concrete HumanEval values, proved from the counting specification rather than kernel trial division. -/
theorem primeFib_values_thm :
    primeFib 1 = 2 ∧ primeFib 2 = 3 ∧ primeFib 3 = 5 ∧ primeFib 4 = 13 ∧
    primeFib 5 = 89 ∧ primeFib 6 = 233 ∧ primeFib 7 = 1597 ∧ primeFib 8 = 28657 ∧
    primeFib 9 = 514229 ∧ primeFib 10 = 433494437 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [primeFib_eq_of_index 1 3 (by decide) (by decide) (by norm_num) fibPrimeCount_3]; norm_num
  · rw [primeFib_eq_of_index 2 4 (by decide) (by decide) (by norm_num) fibPrimeCount_4]; norm_num
  · rw [primeFib_eq_of_index 3 5 (by decide) (by decide) (by norm_num) fibPrimeCount_5]; norm_num
  · rw [primeFib_eq_of_index 4 7 (by decide) (by decide) (by norm_num) fibPrimeCount_7]; norm_num
  · rw [primeFib_eq_of_index 5 11 (by decide) (by decide) (by norm_num) fibPrimeCount_11]; norm_num
  · rw [primeFib_eq_of_index 6 13 (by decide) (by decide) (by norm_num) fibPrimeCount_13]; norm_num
  · rw [primeFib_eq_of_index 7 17 (by decide) (by decide) (by norm_num) fibPrimeCount_17]; norm_num
  · rw [primeFib_eq_of_index 8 23 (by decide) (by decide) (by norm_num) fibPrimeCount_23]; norm_num
  · rw [primeFib_eq_of_index 9 29 (by decide) (by decide) (by norm_num) fibPrimeCount_29]; norm_num
  · rw [primeFib_eq_of_index 10 43 (by decide) (by decide) (by norm_num) fibPrimeCount_43]; norm_num

theorem hasNthFibPrime_of_le_ten (n : Nat) (h1 : 0 < n) (h2 : n ≤ 10) : hasNthFibPrime n := by
  interval_cases n
  · exact ⟨h1, ⟨3, by decide, by norm_num, fibPrimeCount_3⟩⟩
  · exact ⟨h1, ⟨4, by decide, by norm_num, fibPrimeCount_4⟩⟩
  · exact ⟨h1, ⟨5, by decide, by norm_num, fibPrimeCount_5⟩⟩
  · exact ⟨h1, ⟨7, by decide, by norm_num, fibPrimeCount_7⟩⟩
  · exact ⟨h1, ⟨11, by decide, by norm_num, fibPrimeCount_11⟩⟩
  · exact ⟨h1, ⟨13, by decide, by norm_num, fibPrimeCount_13⟩⟩
  · exact ⟨h1, ⟨17, by decide, by norm_num, fibPrimeCount_17⟩⟩
  · exact ⟨h1, ⟨23, by decide, by norm_num, fibPrimeCount_23⟩⟩
  · exact ⟨h1, ⟨29, by decide, by norm_num, fibPrimeCount_29⟩⟩
  · exact ⟨h1, ⟨43, by decide, by norm_num, fibPrimeCount_43⟩⟩

/-- Unconditional specification on the entire HumanEval test domain. -/
theorem primeFib_spec_le_ten_thm (n : Nat) (h1 : 0 < n) (h2 : n ≤ 10) :
    Nat.Prime (primeFib n) ∧
      ∃ k, primeFib n = Nat.fib k ∧ fibPrimeCount k = n - 1 ∧ fibPrimeCount (k + 1) = n := by
  have h := hasNthFibPrime_of_le_ten n h1 h2
  obtain ⟨k, heq, hp, hc, hc1, _⟩ := primeFib_witness n h1 h
  refine ⟨?_, ⟨k, heq, hc, hc1⟩⟩
  simpa [heq] using hp

/-! ## Post-condition -/

def Post_prop (n : Nat) : Prop :=
  is_prime_prop n ∧ is_fibonacci_prop n ∧ is_nth_prop n ∧ positive_prop n ∧ monotonic_prop n

/-! ## Property-based tests

Executable checks of every `_prop` and of `Post_prop` on the admissible range
`1 ≤ n ≤ 10`, where `hasNthFibPrime` is proved above. Randomized checks use
`Fin` so every sample is admissible (a bare `Nat` sampler mostly misses `n ≤ 10`).
-/

def isFibValue (v : Nat) : Bool :=
  (List.range searchBound).any (fun k => Nat.fib k == v)

def isNthValue (n : Nat) : Bool :=
  let v := primeFib n
  (List.range searchBound).any (fun k =>
    Nat.fib k == v && decide (Nat.Prime (Nat.fib k)) &&
      decide (fibPrimeCount k = n - 1) && decide (fibPrimeCount (k + 1) = n))

def postBool (n : Nat) : Bool :=
  isPrime (primeFib n) && isFibValue (primeFib n) && isNthValue n && decide (1 < primeFib n)

-- PBT: is_prime_prop
example : (List.range 10).all (fun i => isPrime (primeFib (i + 1))) = true := by native_decide

-- PBT: is_fibonacci_prop
example : (List.range 10).all (fun i => isFibValue (primeFib (i + 1))) = true := by native_decide

-- PBT: is_nth_prop
example : (List.range 10).all (fun i => isNthValue (i + 1)) = true := by native_decide

-- PBT: positive_prop
example : (List.range 10).all (fun i => decide (1 < primeFib (i + 1))) = true := by native_decide

-- PBT: monotonic_prop
example : (List.range 10).all (fun i =>
    (List.range (9 - i)).all (fun d => decide (primeFib (i + 1) < primeFib (i + 2 + d)))) = true := by
  native_decide

-- PBT: Post_prop
example : (List.range 10).all (fun i => postBool (i + 1)) = true := by native_decide

#eval Plausible.Testable.check (∀ k : Fin 8, isPrime (primeFib (k.val + 1)) = true)
#eval Plausible.Testable.check (∀ k : Fin 8, isFibValue (primeFib (k.val + 1)) = true)
#eval Plausible.Testable.check (∀ k : Fin 6, isNthValue (k.val + 1) = true)
#eval Plausible.Testable.check (∀ k : Fin 8, 1 < primeFib (k.val + 1))
#eval Plausible.Testable.check (∀ a b : Fin 5, primeFib (a.val + 1) < primeFib (b.val + a.val + 2))
#eval Plausible.Testable.check (∀ k : Fin 6, postBool (k.val + 1) = true)

/-! ## Correctness -/

theorem correctness_thm (n : Nat) (_h : Pre n) : Post_prop n :=
  ⟨is_prime_thm n, is_fibonacci_thm n, is_nth_thm n, positive_thm n, monotonic_thm n⟩

/-! ## Imperative implementation -/

/-- Imperative `prime_fib`, using `Id.run` and mutable state.
The loop walks Fibonacci indices, decrementing `count` at each prime Fibonacci
number and recording the value that exhausts the counter. This is the Python
`while` loop, made total by the same index bound as `primeFib`. -/
def primeFibImp (n : Nat) : Nat :=
  Id.run do
    let mut count := n
    let mut result : Nat := 0
    for idx in List.range searchBound do
      if count = 0 then
        break
      if isPrime (Nat.fib idx) then
        if count = 1 then
          result := Nat.fib idx
        count := count - 1
    return result

/-! ## Imperative tests -/

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

#eval primeFibImp 1
#eval primeFibImp 5
#eval primeFibImp 10

/-! ## Equivalence -/

theorem primeFibImp_eq_loop (n : Nat) :
    primeFibImp n = (loop n 0 (List.range searchBound)).2 := by
  simp [primeFibImp, Id.run]
  change (MProd.snd <$>
      (forIn (List.range searchBound) (⟨n, 0⟩ : MProd Nat Nat) loopStep : Id (MProd Nat Nat))) =
    (loop n 0 (List.range searchBound)).2
  rw [forIn_eq_loop]
  simp [Functor.map, Pure.pure]

theorem range_eq_range' : List.range searchBound = List.range' 0 searchBound := by
  simp [List.range_eq_range']

theorem equivalence_thm (n : Nat) : primeFib n = primeFibImp n := by
  unfold primeFib
  rw [primeFibFrom_eq_list n 0 (by omega)]
  have : searchBound - 0 = searchBound := by omega
  simp [this, range_eq_range', primeFibImp_eq_loop, loop_snd_eq_list]

end humaneval_39_prime_fib
