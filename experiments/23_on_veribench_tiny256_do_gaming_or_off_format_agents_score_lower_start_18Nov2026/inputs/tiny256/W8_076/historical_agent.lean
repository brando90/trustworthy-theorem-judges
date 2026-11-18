import Mathlib
namespace Agent

/-!
# TLS compression and the CRIME length oracle

A character-level translation of the supplied Python model. Strings are viewed
as lists of Unicode characters, not UTF-8 bytes. `longestPrefix` searches lengths
in descending order, using the ordinary contiguous-substring relation. The raw
request includes both the attacker guess and the secret; their lengths are NOT
silently padded or equalized. Thus the two successful guesses in `check` both
produce length 30, while the wrong three-character guess produces length 33.
This is a model of a compression side channel, not a DEFLATE implementation.
-/

namespace UnsafeTLSCompression158

/-- Search `n, n-1, ..., 1`, returning zero if none matches. -/
def longestPrefix (s p : List Char) : Nat → Nat
  | 0 => 0
  | n + 1 => if p.take (n + 1) <:+: s then n + 1 else longestPrefix s p n

/-- Length of the longest prefix of `candidate_prefix` occurring anywhere in `s`. -/
def count_matching_prefix (s candidate_prefix : String) : Nat :=
  longestPrefix s.toList candidate_prefix.toList candidate_prefix.toList.length

def request_body (cookie attacker_guess : String) : String :=
  "PyZoobar=" ++ attacker_guess ++ "&secret_cookie=" ++ cookie

def raw_size (cookie attacker_guess : String) : Nat :=
  (request_body cookie attacker_guess).toList.length

def base_match (attacker_guess : String) : Nat :=
  count_matching_prefix ("PyZoobar=" ++ attacker_guess)
    ("&secret_cookie=" ++ attacker_guess)

def eligible (cookie attacker_guess : String) : Prop :=
  attacker_guess.toList <+: cookie.toList ∧ 3 ≤ attacker_guess.toList.length

instance (cookie attacker_guess : String) : Decidable (eligible cookie attacker_guess) :=
  inferInstanceAs (Decidable (_ ∧ _))

def savings (cookie attacker_guess : String) : Nat :=
  if eligible cookie attacker_guess then
    max (base_match attacker_guess) attacker_guess.toList.length
  else base_match attacker_guess

/-- Compress before encryption, exposing the resulting character count. -/
def unsafe_tls_compress_send (cookie attacker_guess : String) : Nat :=
  raw_size cookie attacker_guess - savings cookie attacker_guess

/-- The four assertions in the Python `check` function. -/
def check (candidate : String → String → Nat) : Bool :=
  let cookie := "abc123"
  let full := candidate cookie cookie
  let part := candidate cookie "abc"
  let wrong := candidate cookie "xyz"
  decide (full < wrong ∧ part < wrong ∧ full ≤ part ∧
    candidate cookie "a" ≤ candidate cookie "z")

-- Unit tests, including an interior substring, an empty prefix, and Unicode.
example : count_matching_prefix "xxabczz" "abcd" = 3 := by native_decide
example : count_matching_prefix "abc" "" = 0 := by native_decide
example : count_matching_prefix "" "abc" = 0 := by native_decide
example : count_matching_prefix "λ🙂λ" "🙂λ!" = 2 := by native_decide
example : unsafe_tls_compress_send "abc123" "abc123" = 30 := by native_decide
example : unsafe_tls_compress_send "abc123" "abc" = 30 := by native_decide
example : unsafe_tls_compress_send "abc123" "xyz" = 33 := by native_decide
example : unsafe_tls_compress_send "abc123" "a" = 31 := by native_decide
example : unsafe_tls_compress_send "abc123" "z" = 31 := by native_decide
example : check unsafe_tls_compress_send = true := by native_decide
#eval check unsafe_tls_compress_send
#eval ["abc123", "abc", "xyz", "a", "z"].map (unsafe_tls_compress_send "abc123")

/-- Python accepts arbitrary strings; no alphabet, size, or prefix restriction. -/
def Pre (_cookie _attacker_guess : String) : Prop := True

/-- The search returns an attained maximum among admissible prefix lengths. -/
def matching_prefix_prop (s p : String) : Prop :=
  let m := count_matching_prefix s p
  m ≤ p.toList.length ∧ p.toList.take m <:+: s.toList ∧
    ∀ k, k ≤ p.toList.length → p.toList.take k <:+: s.toList → k ≤ m

theorem longestPrefix_spec (s p : List Char) (n : Nat) :
    longestPrefix s p n ≤ n ∧ p.take (longestPrefix s p n) <:+: s ∧
      ∀ k, k ≤ n → p.take k <:+: s → k ≤ longestPrefix s p n := by
  induction n with
  | zero => simp [longestPrefix]
  | succ n ih =>
    by_cases h : p.take (n + 1) <:+: s
    · simp only [longestPrefix, if_pos h]
      exact ⟨le_rfl, h, fun _ hk _ => hk⟩
    · simp only [longestPrefix, if_neg h]
      refine ⟨by omega, ih.2.1, ?_⟩
      intro k hk hm
      have hne : k ≠ n + 1 := by intro he; subst k; exact h hm
      exact ih.2.2 k (by omega) hm

theorem matching_prefix_thm (s p : String) : matching_prefix_prop s p := by
  exact longestPrefix_spec s.toList p.toList p.toList.length

/-- Exact sizes and the four side-channel observations required by Python. -/
def check_prop : Prop :=
  unsafe_tls_compress_send "abc123" "abc123" = 30 ∧
  unsafe_tls_compress_send "abc123" "abc" = 30 ∧
  unsafe_tls_compress_send "abc123" "xyz" = 33 ∧
  unsafe_tls_compress_send "abc123" "abc123" < unsafe_tls_compress_send "abc123" "xyz" ∧
  unsafe_tls_compress_send "abc123" "abc" < unsafe_tls_compress_send "abc123" "xyz" ∧
  unsafe_tls_compress_send "abc123" "abc123" ≤ unsafe_tls_compress_send "abc123" "abc" ∧
  unsafe_tls_compress_send "abc123" "a" ≤ unsafe_tls_compress_send "abc123" "z"

theorem check_thm : check_prop := by
  unfold check_prop
  decide


/-- The request really contains both strings, plus 24 delimiter characters. -/
def raw_size_prop (cookie guess : String) : Prop :=
  raw_size cookie guess = 24 + guess.toList.length + cookie.toList.length

theorem raw_size_thm (cookie guess : String) : raw_size_prop cookie guess := by
  simp [raw_size_prop, raw_size, request_body, String.toList, List.length_append]
  omega

theorem count_matching_prefix_le_source (s p : String) :
    count_matching_prefix s p ≤ s.toList.length := by
  have h := matching_prefix_thm s p
  have hm := h.2.1.length_le
  simpa only [List.length_take, Nat.min_eq_left h.1] using hm

theorem base_match_bound (guess : String) :
    base_match guess ≤ 9 + guess.toList.length := by
  have h := count_matching_prefix_le_source ("PyZoobar=" ++ guess)
    ("&secret_cookie=" ++ guess)
  simp [String.toList] at h
  change base_match guess ≤ _ at h
  change base_match guess ≤ 9 + guess.length
  omega

/-- Both branches of the savings rule, and bounds preventing Nat truncation. -/
def savings_prop (cookie guess : String) : Prop :=
  (eligible cookie guess →
    savings cookie guess = max (base_match guess) guess.toList.length) ∧
  (¬ eligible cookie guess → savings cookie guess = base_match guess) ∧
  base_match guess ≤ savings cookie guess ∧
  (eligible cookie guess → guess.toList.length ≤ savings cookie guess) ∧
  savings cookie guess ≤ 9 + guess.toList.length

theorem savings_thm (cookie guess : String) : savings_prop cookie guess := by
  have hb := base_match_bound guess
  unfold savings_prop savings
  by_cases h : eligible cookie guess
  · simp [h]
    exact hb
  · simp [h]
    exact hb

/-- The returned size is bounded, and subtraction loses no information. -/
def compression_prop (cookie guess : String) : Prop :=
  savings cookie guess ≤ raw_size cookie guess ∧
  unsafe_tls_compress_send cookie guess + savings cookie guess = raw_size cookie guess ∧
  unsafe_tls_compress_send cookie guess ≤ raw_size cookie guess

theorem compression_thm (cookie guess : String) : compression_prop cookie guess := by
  have hr := raw_size_thm cookie guess
  have hs := (savings_thm cookie guess).2.2.2.2
  change raw_size cookie guess = 24 + guess.toList.length + cookie.toList.length at hr
  unfold compression_prop unsafe_tls_compress_send
  omega

/-- A qualifying prefix saves at least its length; otherwise use only the
substring match. In particular length-one/two prefixes get no special bonus. -/
def prefix_savings_prop (cookie guess : String) : Prop :=
  (eligible cookie guess → unsafe_tls_compress_send cookie guess ≤
    raw_size cookie guess - guess.toList.length) ∧
  (¬ eligible cookie guess → unsafe_tls_compress_send cookie guess =
    raw_size cookie guess - base_match guess)

theorem prefix_savings_thm (cookie guess : String) : prefix_savings_prop cookie guess := by
  constructor
  · intro h
    have hs := (savings_thm cookie guess).2.2.2.1 h
    unfold unsafe_tls_compress_send
    omega
  · intro h
    simp [unsafe_tls_compress_send, savings, h]

/-- Without an ampersand in the guess, the candidate beginning with '&' has
no nonempty substring match in the first occurrence. -/
theorem base_match_eq_zero (guess : String) (h : '&' ∉ guess.toList) :
    base_match guess = 0 := by
  have hm := (matching_prefix_thm ("PyZoobar=" ++ guess)
    ("&secret_cookie=" ++ guess)).2.1
  change ("&secret_cookie=" ++ guess).toList.take (base_match guess) <:+:
    ("PyZoobar=" ++ guess).toList at hm
  cases he : base_match guess with
  | zero => rfl
  | succ n =>
    rw [he] at hm
    have ha : '&' ∈ ("&secret_cookie=" ++ guess).toList.take (n + 1) := by
      simp [String.toList, List.take_succ_cons]
    have hb := hm.subset ha
    have hn : '&' ∉ ("PyZoobar=" ++ guess).toList := by
      simpa [String.toList] using h
    exact False.elim (hn hb)

/-- On guesses without '&', this is the exact observable oracle: eligible
prefixes remove the entire guess contribution; all others retain it. -/
def oracle_prop (cookie guess : String) : Prop :=
  '&' ∉ guess.toList →
    unsafe_tls_compress_send cookie guess =
      if eligible cookie guess then 24 + cookie.toList.length
      else 24 + guess.toList.length + cookie.toList.length

theorem oracle_thm (cookie guess : String) : oracle_prop cookie guess := by
  intro h
  have hb := base_match_eq_zero guess h
  have hr := raw_size_thm cookie guess
  change raw_size cookie guess = 24 + guess.toList.length + cookie.toList.length at hr
  unfold unsafe_tls_compress_send savings
  rw [hr, hb]
  by_cases he : eligible cookie guess
  · simp [he]
    omega
  · simp [he]

/-- Exact equal-length distinguishing experiment. This is a general leak law,
not a claim that a longer successful guess always beats every shorter guess. -/
def side_channel_prop (cookie good bad : String) : Prop :=
  '&' ∉ good.toList → '&' ∉ bad.toList →
  eligible cookie good → ¬ (bad.toList <+: cookie.toList) →
  good.toList.length = bad.toList.length →
  unsafe_tls_compress_send cookie good + good.toList.length =
    unsafe_tls_compress_send cookie bad ∧
  unsafe_tls_compress_send cookie good < unsafe_tls_compress_send cookie bad

theorem side_channel_thm (cookie good bad : String) : side_channel_prop cookie good bad := by
  intro hg hb he hn hl
  have hgood := oracle_thm cookie good hg
  have hbad := oracle_thm cookie bad hb
  have hne : ¬ eligible cookie bad := fun h => hn h.1
  rw [if_pos he] at hgood
  rw [if_neg hne] at hbad
  have hlen := he.2
  constructor <;> omega


/-- The complete per-request contract, including the longest-match model,
exact arithmetic, and every equal-length distinguishing experiment. -/
def Post_prop (cookie guess : String) : Prop :=
  matching_prefix_prop cookie guess ∧
  matching_prefix_prop ("PyZoobar=" ++ guess) ("&secret_cookie=" ++ guess) ∧
  raw_size_prop cookie guess ∧ savings_prop cookie guess ∧
  compression_prop cookie guess ∧ prefix_savings_prop cookie guess ∧
  oracle_prop cookie guess ∧ (∀ bad, side_channel_prop cookie guess bad) ∧
  check_prop

/-! ## Property-based tests
The maximum condition is checked at *every* admissible prefix length. Other
finite propositions are checked directly with executable decision procedures.
The universal comparator in Post is tested over the same bounded string corpus.
These tests supply evidence only: none is used by any theorem below.
-/

def matching_prefix_test (s p : String) : Bool :=
  let m := count_matching_prefix s p
  decide (m ≤ p.toList.length ∧ p.toList.take m <:+: s.toList) &&
    (List.range (p.toList.length + 1)).all (fun k =>
      decide (p.toList.take k <:+: s.toList → k ≤ m))

def raw_size_test (c g : String) : Bool :=
  @decide (raw_size_prop c g) (by unfold raw_size_prop; infer_instance)

def savings_test (c g : String) : Bool :=
  @decide (savings_prop c g) (by unfold savings_prop; infer_instance)

def compression_test (c g : String) : Bool :=
  @decide (compression_prop c g) (by unfold compression_prop; infer_instance)

def prefix_savings_test (c g : String) : Bool :=
  @decide (prefix_savings_prop c g) (by unfold prefix_savings_prop; infer_instance)

def oracle_test (c g : String) : Bool :=
  @decide (oracle_prop c g) (by unfold oracle_prop; infer_instance)

/-- Short-circuit the implication; its conclusion is evaluated exactly when
all five premises of side_channel_prop hold. This avoids expensive oracle calls
on inadmissible triples without discarding any test input. -/
def side_channel_test (c g b : String) : Bool :=
  if '&' ∉ g.toList ∧ '&' ∉ b.toList ∧ eligible c g ∧
      ¬ (b.toList <+: c.toList) ∧ g.toList.length = b.toList.length then
    decide (unsafe_tls_compress_send c g + g.toList.length =
      unsafe_tls_compress_send c b ∧
      unsafe_tls_compress_send c g < unsafe_tls_compress_send c b)
  else true

def check_test : Bool :=
  @decide check_prop (by unfold check_prop; infer_instance)

/-- Enumerate every word of length at most n over this four-character alphabet. -/
def smallWords : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 => [] :: ['a', 'b', '&', 'λ'].flatMap
      (fun ch => (smallWords n).map (ch :: ·))

def testStrings : List String :=
  (smallWords 3).map String.mk ++
    ["abc123", "abc", "xyz", "a", "z", "ab", "abcd", "xxabczz",
     "&secret_cookie=", "PyZoobar=", "&&secret_cookie=a", "🙂λ!"]

-- PBT for matching_prefix_prop: all string pairs and all legal prefix lengths.
example : testStrings.all (fun s => testStrings.all (matching_prefix_test s)) = true := by
  native_decide
-- PBT for raw_size_prop.
example : testStrings.all (fun c => testStrings.all (raw_size_test c)) = true := by
  native_decide
-- PBT for savings_prop, including guesses which contain '&'.
example : testStrings.all (fun c => testStrings.all (savings_test c)) = true := by
  native_decide
-- PBT for compression_prop.
example : testStrings.all (fun c => testStrings.all (compression_test c)) = true := by
  native_decide
-- PBT for prefix_savings_prop, including lengths zero, one, two, and three.
example : testStrings.all (fun c => testStrings.all (prefix_savings_test c)) = true := by
  native_decide
-- PBT for oracle_prop.
example : testStrings.all (fun c => testStrings.all (oracle_test c)) = true := by
  native_decide
-- PBT for side_channel_prop: all triples, with admissibility checked by implication.
example : testStrings.all (fun c => testStrings.all (fun g =>
    testStrings.all (side_channel_test c g))) = true := by native_decide
-- check_prop is closed: its executable check exhausts its (singleton) input domain.
example : check_test = true := by native_decide

def post_test (c g : String) : Bool :=
  matching_prefix_test c g &&
  matching_prefix_test ("PyZoobar=" ++ g) ("&secret_cookie=" ++ g) &&
  raw_size_test c g && savings_test c g && compression_test c g &&
  prefix_savings_test c g && oracle_test c g &&
  testStrings.all (side_channel_test c g) && check_test

-- PBT for the entire postcondition, on every bounded input pair.
example : testStrings.all (fun c => testStrings.all (post_test c)) = true := by
  native_decide

/-- A generator of qualifying prefixes, avoiding vacuous rejection of samples. -/
def repeated (n : Nat) (ch : Char) : String := String.mk (List.replicate n ch)

#eval Plausible.Testable.check (∀ n : Nat,
  let k := n % 25 + 3
  side_channel_test (repeated k 'a' ++ "123") (repeated k 'a') (repeated k 'z') = true)
#eval testStrings.length
#eval testStrings.all (fun c => testStrings.all (post_test c))

/-- All obligations hold on the entire Python input domain. -/
theorem correctness_thm (cookie guess : String) : Pre cookie guess → Post_prop cookie guess := by
  intro _
  exact ⟨matching_prefix_thm cookie guess,
    matching_prefix_thm ("PyZoobar=" ++ guess) ("&secret_cookie=" ++ guess),
    raw_size_thm cookie guess, savings_thm cookie guess,
    compression_thm cookie guess, prefix_savings_thm cookie guess,
    oracle_thm cookie guess, fun bad => side_channel_thm cookie guess bad, check_thm⟩


/-! ## Imperative translation
The search scans lengths 1 through n, overwriting a mutable result on each
match. Keeping the last match is equivalent to returning the first match in the
descending Python search. It does not call the functional prefix search.
-/

def scanStep (s p : List Char) (best i : Nat) : Nat :=
  if p.take (i + 1) <:+: s then i + 1 else best

def scanImp (s p : List Char) (indices : List Nat) (initial : Nat) : Nat := Id.run do
  let mut best := initial
  for i in indices do
    best := if p.take (i + 1) <:+: s then i + 1 else best
  return best

def count_matching_prefix_imp (s candidate_prefix : String) : Nat :=
  scanImp s.toList candidate_prefix.toList (List.range candidate_prefix.toList.length) 0

def unsafe_tls_compress_send_imp (cookie attacker_guess : String) : Nat := Id.run do
  let request := "PyZoobar=" ++ attacker_guess ++ "&secret_cookie=" ++ cookie
  let raw := request.toList.length
  let mut matchLen := count_matching_prefix_imp ("PyZoobar=" ++ attacker_guess)
    ("&secret_cookie=" ++ attacker_guess)
  if attacker_guess.toList <+: cookie.toList then
    if 3 ≤ attacker_guess.toList.length then
      matchLen := max matchLen attacker_guess.toList.length
  return raw - matchLen

-- Imperative unit tests and bounded equivalence tests.
example : count_matching_prefix_imp "xxabczz" "abcd" = 3 := by native_decide
example : count_matching_prefix_imp "λ🙂λ" "🙂λ!" = 2 := by native_decide
example : unsafe_tls_compress_send_imp "abc123" "abc123" = 30 := by native_decide
example : unsafe_tls_compress_send_imp "abc123" "abc" = 30 := by native_decide
example : unsafe_tls_compress_send_imp "abc123" "xyz" = 33 := by native_decide
example : unsafe_tls_compress_send_imp "" "" = 24 := by native_decide
example : unsafe_tls_compress_send_imp "" "&" = 24 := by native_decide
example : check unsafe_tls_compress_send_imp = true := by native_decide
example : testStrings.all (fun s => testStrings.all (fun p =>
    decide (count_matching_prefix s p = count_matching_prefix_imp s p))) = true := by
  native_decide
example : testStrings.all (fun c => testStrings.all (fun g =>
    decide (unsafe_tls_compress_send c g = unsafe_tls_compress_send_imp c g))) = true := by
  native_decide
#eval check unsafe_tls_compress_send_imp
#eval ["abc123", "abc", "xyz", "a", "z"].map (unsafe_tls_compress_send_imp "abc123")

theorem scanImp_fold (s p : List Char) (indices : List Nat) (initial : Nat) :
    scanImp s p indices initial = indices.foldl (scanStep s p) initial := by
  simp [scanImp]
  rfl

theorem fold_range (s p : List Char) (n : Nat) :
    (List.range n).foldl (scanStep s p) 0 = longestPrefix s p n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.range_succ, List.foldl_append, ih, scanStep, longestPrefix]

theorem count_matching_prefix_equiv (s p : String) :
    count_matching_prefix s p = count_matching_prefix_imp s p := by
  simp only [count_matching_prefix, count_matching_prefix_imp, scanImp_fold, fold_range]

/-- Functional and imperative compression agree on all strings, not only
on the test cookie or on delimiter-free inputs. -/
theorem functional_imperative_equiv (cookie guess : String) :
    unsafe_tls_compress_send cookie guess = unsafe_tls_compress_send_imp cookie guess := by
  by_cases hp : guess.data <+: cookie.data
  · by_cases hl : 3 ≤ guess.length
    · simp [unsafe_tls_compress_send_imp, unsafe_tls_compress_send, raw_size,
        request_body, savings, eligible, base_match, hp, hl, ← count_matching_prefix_equiv]
    · simp [unsafe_tls_compress_send_imp, unsafe_tls_compress_send, raw_size,
        request_body, savings, eligible, base_match, hp, hl, ← count_matching_prefix_equiv]
  · simp [unsafe_tls_compress_send_imp, unsafe_tls_compress_send, raw_size,
      request_body, savings, eligible, base_match, hp, ← count_matching_prefix_equiv]

end UnsafeTLSCompression158
end Agent
