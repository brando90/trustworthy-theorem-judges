import Mathlib
namespace Agent

/-!
# `63_unsafeSynFlood_safe`: SYN cookies (stateless TCP three-way handshake)

Lean 4 translation of the Python program `63_unsafeSynFlood_safe.py`
(MIT 6.858, Lecture 13: SYN-flood defence via RFC 4987 / Bernstein SYN cookies).

The Python program defines

* `safe_syn_flood(src_ip, src_port, dst_ip, dst_port, secret, timestamp)`: a 32-bit SYN
  cookie (initial sequence number)
  `(src_ip*p1 + src_port*p2 + dst_ip*p3 + dst_port*p4 + secret*p5 + timestamp*p6) mod 2^32`
  with the fixed odd primes `p1 = 2654435761`, `p2 = 2246822519`, `p3 = 3266489917`,
  `p4 = 668265263`, `p5 = 374761393`, `p6 = 1597334677`;
* `verify_syn_cookie(..., received_ack)`: recompute the cookie for the current epoch
  `timestamp` and the previous epoch `timestamp - 1` and accept iff
  `(cookie + 1) mod 2^32 == received_ack` for one of them.

Python `int`s are unbounded and may be negative (e.g. `timestamp - 1` for `timestamp = 0`),
so every argument is modelled by `Int`.  Python's `%` with a positive modulus returns a value
in `[0, 2^32)`, exactly like Lean's `Int.emod` (the `%` operator on `Int`), so the
translation is exact.

Besides the functional model we state and prove the properties exercised by the Python `check`
function (32-bit range, determinism, sensitivity of the cookie to `src_ip` / `secret` /
`timestamp`, stateless batch generation, acceptance of the valid ACK, tolerance of the previous
epoch, rejection of a wrong ACK and of a replayed cookie from an older epoch), an exact
characterisation of `verify_syn_cookie`, imperative `Id.run do` implementations, and the
functional/imperative equivalence theorems.
-/

namespace «63_unsafeSynFlood_safe»

/-! ## Functional implementation -/

/-- Python `safe_syn_flood`: the SYN cookie (32-bit initial sequence number) that encodes the
connection 4-tuple, the server secret and the coarse timestamp. -/
def safe_syn_flood (src_ip src_port dst_ip dst_port secret timestamp : Int) : Int :=
  (src_ip * 2654435761
    + src_port * 2246822519
    + dst_ip * 3266489917
    + dst_port * 668265263
    + secret * 374761393
    + timestamp * 1597334677) % (2 ^ 32)

/-- Python `verify_syn_cookie`: the ACK number is valid iff it equals `cookie + 1 (mod 2^32)`
for the cookie of the current epoch `timestamp` or of the previous epoch `timestamp - 1`
(`for ts in (timestamp, timestamp - 1): ... return True` / `return False`). -/
def verify_syn_cookie (src_ip src_port dst_ip dst_port secret timestamp received_ack : Int) :
    Bool :=
  [timestamp, timestamp - 1].any fun ts =>
    (safe_syn_flood src_ip src_port dst_ip dst_port secret ts + 1) % (2 ^ 32) == received_ack

/-- The stateless batch of cookies built by the Python `check`:
`[candidate(0x0A000002 + i, 1000 + i, 0x0A000001, 80, secret, timestamp) for i in range(n)]`. -/
def generate_cookies (n : Nat) (secret timestamp : Int) : List Int :=
  (List.range n).map fun (i : Nat) =>
    safe_syn_flood (0x0A000002 + (i : Int)) (1000 + (i : Int)) 0x0A000001 80 secret timestamp

/-! ## Unit tests (the assertions of the Python `check`) -/

-- Determinism: same inputs produce the same cookie.
example : safe_syn_flood 0xC0A80101 12345 0x0A000001 80 0xDEADBEEF 1000
    = safe_syn_flood 0xC0A80101 12345 0x0A000001 80 0xDEADBEEF 1000 := by native_decide

-- Concrete value of `c1` (cross-checked against the Python implementation).
example : safe_syn_flood 0xC0A80101 12345 0x0A000001 80 0xDEADBEEF 1000 = 2237255268 := by
  native_decide

-- In range: the cookie fits in 32 bits.
example : 0 ≤ safe_syn_flood 0xC0A80101 12345 0x0A000001 80 0xDEADBEEF 1000 ∧
    safe_syn_flood 0xC0A80101 12345 0x0A000001 80 0xDEADBEEF 1000 < 2 ^ 32 := by native_decide

-- Different `src_ip` yields a different cookie.
example : safe_syn_flood 0xC0A80102 12345 0x0A000001 80 0xDEADBEEF 1000
    ≠ safe_syn_flood 0xC0A80101 12345 0x0A000001 80 0xDEADBEEF 1000 := by native_decide
example : safe_syn_flood 0xC0A80102 12345 0x0A000001 80 0xDEADBEEF 1000 = 596723733 := by
  native_decide

-- Different secret yields a different cookie (an attacker cannot predict it).
example : safe_syn_flood 0xC0A80101 12345 0x0A000001 80 0xCAFEBABE 1000
    ≠ safe_syn_flood 0xC0A80101 12345 0x0A000001 80 0xDEADBEEF 1000 := by native_decide
example : safe_syn_flood 0xC0A80101 12345 0x0A000001 80 0xCAFEBABE 1000 = 3761385859 := by
  native_decide

-- Different timestamp yields a different cookie.
example : safe_syn_flood 0xC0A80101 12345 0x0A000001 80 0xDEADBEEF 1001
    ≠ safe_syn_flood 0xC0A80101 12345 0x0A000001 80 0xDEADBEEF 1000 := by native_decide
example : safe_syn_flood 0xC0A80101 12345 0x0A000001 80 0xDEADBEEF 1001 = 3834589945 := by
  native_decide

-- Stateless: 1000 cookies are generated without any server-side state.
example : (generate_cookies 1000 0xDEADBEEF 1000).length = 1000 := by native_decide

-- Valid ACK verification.
example : verify_syn_cookie 0xC0A80101 12345 0x0A000001 80 0xDEADBEEF 1000
    ((safe_syn_flood 0xC0A80101 12345 0x0A000001 80 0xDEADBEEF 1000 + 1) % 2 ^ 32) = true := by
  native_decide
example : verify_syn_cookie 0xC0A80101 12345 0x0A000001 80 0xDEADBEEF 1000 2237255269 = true := by
  native_decide

-- Invalid ACK rejected.
example : verify_syn_cookie 0xC0A80101 12345 0x0A000001 80 0xDEADBEEF 1000
    ((safe_syn_flood 0xC0A80101 12345 0x0A000001 80 0xDEADBEEF 1000 + 2) % 2 ^ 32) = false := by
  native_decide
example : verify_syn_cookie 0xC0A80101 12345 0x0A000001 80 0xDEADBEEF 1000 2237255270 = false := by
  native_decide

-- Clock-skew tolerance: a cookie from the previous timestamp is still accepted.
example : verify_syn_cookie 0xC0A80103 22222 0x0A000001 80 0xDEADBEEF 1000
    ((safe_syn_flood 0xC0A80103 22222 0x0A000001 80 0xDEADBEEF (1000 - 1) + 1) % 2 ^ 32)
    = true := by native_decide

-- Replay protection: a cookie from 5 epochs ago is rejected.
example : verify_syn_cookie 0xC0A80104 33333 0x0A000001 80 0xDEADBEEF 1000
    ((safe_syn_flood 0xC0A80104 33333 0x0A000001 80 0xDEADBEEF (1000 - 5) + 1) % 2 ^ 32)
    = false := by native_decide

-- Negative Python integers are handled like Python's `%` (result stays in `[0, 2^32)`).
example : safe_syn_flood 0 0 0 0 0 (-1) = 2697632619 := by native_decide
example : safe_syn_flood 0 0 0 0 0 0 = 0 := by native_decide

#eval safe_syn_flood 0xC0A80101 12345 0x0A000001 80 0xDEADBEEF 1000   -- 2237255268
#eval verify_syn_cookie 0xC0A80101 12345 0x0A000001 80 0xDEADBEEF 1000 2237255269   -- true
#eval verify_syn_cookie 0xC0A80101 12345 0x0A000001 80 0xDEADBEEF 1000 2237255270   -- false
#eval (generate_cookies 1000 0xDEADBEEF 1000).length   -- 1000

/-! ## Pre-condition -/

set_option linter.unusedVariables false in
/-- Pre-condition of `safe_syn_flood` / `verify_syn_cookie`.  The Python functions accept
arbitrary (unbounded, possibly negative) integers for every argument and never raise, so the
admissible input domain is all of `Int^6` and there is no restriction. -/
def Pre (src_ip src_port dst_ip dst_port secret timestamp : Int) : Prop :=
  True

/-! ## Arithmetic helper lemmas -/

theorem two_pow_32 : (2 : Int) ^ 32 = 4294967296 := by norm_num

/-- `p1` is odd, hence a unit modulo `2^32`. -/
theorem coprime_p1 : IsCoprime (2 ^ 32 : Int) 2654435761 := by
  rw [Int.isCoprime_iff_gcd_eq_one]; norm_num

/-- `p5` is odd, hence a unit modulo `2^32`. -/
theorem coprime_p5 : IsCoprime (2 ^ 32 : Int) 374761393 := by
  rw [Int.isCoprime_iff_gcd_eq_one]; norm_num

/-- `p6` is odd, hence a unit modulo `2^32`. -/
theorem coprime_p6 : IsCoprime (2 ^ 32 : Int) 1597334677 := by
  rw [Int.isCoprime_iff_gcd_eq_one]; norm_num

/-- A unit factor modulo `2^32` can be cancelled:
if `x*p + R ≡ y*p + R (mod 2^32)` and `p` is coprime to `2^32` then `x ≡ y (mod 2^32)`. -/
theorem emod_eq_of_coprime_mul {p x y R : Int} (hp : IsCoprime (2 ^ 32 : Int) p)
    (h : (x * p + R) % 2 ^ 32 = (y * p + R) % 2 ^ 32) : x % 2 ^ 32 = y % 2 ^ 32 := by
  have h1 : x * p + R ≡ y * p + R [ZMOD 2 ^ 32] := h
  have h2 : (2 ^ 32 : Int) ∣ (y * p + R) - (x * p + R) := h1.dvd
  have h3 : (2 ^ 32 : Int) ∣ (y - x) * p := by
    have e : (y * p + R) - (x * p + R) = (y - x) * p := by ring
    rwa [e] at h2
  have h4 : (2 ^ 32 : Int) ∣ y - x := hp.dvd_of_dvd_mul_right h3
  exact Int.modEq_iff_dvd.mpr h4

/-! ## Properties of `safe_syn_flood` -/

/-- The cookie is a 32-bit value: `0 ≤ cookie < 2^32`. -/
def cookie_range_prop (src_ip src_port dst_ip dst_port secret timestamp : Int) : Prop :=
  0 ≤ safe_syn_flood src_ip src_port dst_ip dst_port secret timestamp ∧
    safe_syn_flood src_ip src_port dst_ip dst_port secret timestamp < 2 ^ 32

theorem cookie_range_thm (src_ip src_port dst_ip dst_port secret timestamp : Int) :
    cookie_range_prop src_ip src_port dst_ip dst_port secret timestamp := by
  unfold cookie_range_prop safe_syn_flood
  exact ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩

/-- Determinism: recomputing the cookie for the same inputs gives the same value
(the server can recompute it on ACK receipt without storing any state). -/
def cookie_deterministic_prop (src_ip src_port dst_ip dst_port secret timestamp : Int) : Prop :=
  safe_syn_flood src_ip src_port dst_ip dst_port secret timestamp =
    safe_syn_flood src_ip src_port dst_ip dst_port secret timestamp

theorem cookie_deterministic_thm (src_ip src_port dst_ip dst_port secret timestamp : Int) :
    cookie_deterministic_prop src_ip src_port dst_ip dst_port secret timestamp := rfl

/-- The cookie is exactly the documented formula
`(src_ip*p1 + src_port*p2 + dst_ip*p3 + dst_port*p4 + secret*p5 + ts*p6) mod 2^32`. -/
def cookie_formula_prop (src_ip src_port dst_ip dst_port secret timestamp : Int) : Prop :=
  safe_syn_flood src_ip src_port dst_ip dst_port secret timestamp =
    (src_ip * 2654435761 + src_port * 2246822519 + dst_ip * 3266489917 + dst_port * 668265263
      + secret * 374761393 + timestamp * 1597334677) % 2 ^ 32

theorem cookie_formula_thm (src_ip src_port dst_ip dst_port secret timestamp : Int) :
    cookie_formula_prop src_ip src_port dst_ip dst_port secret timestamp := rfl

/-- The cookie only depends on the inputs modulo `2^32`: it is a function of the 32-bit
truncation of every field. -/
def cookie_mod_invariant_prop (src_ip src_port dst_ip dst_port secret timestamp : Int) : Prop :=
  safe_syn_flood src_ip src_port dst_ip dst_port secret timestamp =
    safe_syn_flood (src_ip % 2 ^ 32) (src_port % 2 ^ 32) (dst_ip % 2 ^ 32) (dst_port % 2 ^ 32)
      (secret % 2 ^ 32) (timestamp % 2 ^ 32)

theorem cookie_mod_invariant_thm (src_ip src_port dst_ip dst_port secret timestamp : Int) :
    cookie_mod_invariant_prop src_ip src_port dst_ip dst_port secret timestamp := by
  unfold cookie_mod_invariant_prop safe_syn_flood
  have h : ∀ x : Int, x ≡ x % 2 ^ 32 [ZMOD 2 ^ 32] := fun x => (Int.mod_modEq x _).symm
  exact ((((((h src_ip).mul_right _).add ((h src_port).mul_right _)).add
    ((h dst_ip).mul_right _)).add ((h dst_port).mul_right _)).add
    ((h secret).mul_right _)).add ((h timestamp).mul_right _)

/-- Different source IPs (different as 32-bit values) yield different cookies. -/
def cookie_src_ip_sensitive_prop (src_ip src_port dst_ip dst_port secret timestamp : Int) :
    Prop :=
  ∀ src_ip' : Int, src_ip % 2 ^ 32 ≠ src_ip' % 2 ^ 32 →
    safe_syn_flood src_ip src_port dst_ip dst_port secret timestamp ≠
      safe_syn_flood src_ip' src_port dst_ip dst_port secret timestamp

theorem cookie_src_ip_sensitive_thm (src_ip src_port dst_ip dst_port secret timestamp : Int) :
    cookie_src_ip_sensitive_prop src_ip src_port dst_ip dst_port secret timestamp := by
  intro src_ip' hne heq
  apply hne
  unfold safe_syn_flood at heq
  refine emod_eq_of_coprime_mul coprime_p1
    (R := src_port * 2246822519 + dst_ip * 3266489917 + dst_port * 668265263
      + secret * 374761393 + timestamp * 1597334677) ?_
  convert heq using 2 <;> ring

/-- Different secrets (different as 32-bit values) yield different cookies, so an attacker
who does not know the secret cannot produce the server's cookie. -/
def cookie_secret_sensitive_prop (src_ip src_port dst_ip dst_port secret timestamp : Int) :
    Prop :=
  ∀ secret' : Int, secret % 2 ^ 32 ≠ secret' % 2 ^ 32 →
    safe_syn_flood src_ip src_port dst_ip dst_port secret timestamp ≠
      safe_syn_flood src_ip src_port dst_ip dst_port secret' timestamp

theorem cookie_secret_sensitive_thm (src_ip src_port dst_ip dst_port secret timestamp : Int) :
    cookie_secret_sensitive_prop src_ip src_port dst_ip dst_port secret timestamp := by
  intro secret' hne heq
  apply hne
  unfold safe_syn_flood at heq
  refine emod_eq_of_coprime_mul coprime_p5
    (R := src_ip * 2654435761 + src_port * 2246822519 + dst_ip * 3266489917
      + dst_port * 668265263 + timestamp * 1597334677) ?_
  convert heq using 2 <;> ring

/-- Different timestamps (different as 32-bit values) yield different cookies. -/
def cookie_timestamp_sensitive_prop (src_ip src_port dst_ip dst_port secret timestamp : Int) :
    Prop :=
  ∀ timestamp' : Int, timestamp % 2 ^ 32 ≠ timestamp' % 2 ^ 32 →
    safe_syn_flood src_ip src_port dst_ip dst_port secret timestamp ≠
      safe_syn_flood src_ip src_port dst_ip dst_port secret timestamp'

theorem cookie_timestamp_sensitive_thm
    (src_ip src_port dst_ip dst_port secret timestamp : Int) :
    cookie_timestamp_sensitive_prop src_ip src_port dst_ip dst_port secret timestamp := by
  intro timestamp' hne heq
  apply hne
  unfold safe_syn_flood at heq
  refine emod_eq_of_coprime_mul coprime_p6
    (R := src_ip * 2654435761 + src_port * 2246822519 + dst_ip * 3266489917
      + dst_port * 668265263 + secret * 374761393) ?_
  convert heq using 2 <;> ring

/-- Corollary for genuine 32-bit fields: two *different* source addresses in `[0, 2^32)`
(e.g. `0xC0A80101` and `0xC0A80102`) always yield different cookies. -/
theorem cookie_src_ip_injective_thm
    (src_ip src_ip' src_port dst_ip dst_port secret timestamp : Int)
    (h1 : 0 ≤ src_ip) (h2 : src_ip < 2 ^ 32) (h1' : 0 ≤ src_ip') (h2' : src_ip' < 2 ^ 32)
    (hne : src_ip ≠ src_ip') :
    safe_syn_flood src_ip src_port dst_ip dst_port secret timestamp ≠
      safe_syn_flood src_ip' src_port dst_ip dst_port secret timestamp :=
  cookie_src_ip_sensitive_thm src_ip src_port dst_ip dst_port secret timestamp src_ip'
    (by rw [Int.emod_eq_of_lt h1 h2, Int.emod_eq_of_lt h1' h2']; exact hne)

/-- Corollary for 32-bit secrets: two different secrets in `[0, 2^32)` (e.g. `0xDEADBEEF` and
`0xCAFEBABE`) always yield different cookies. -/
theorem cookie_secret_injective_thm
    (src_ip src_port dst_ip dst_port secret secret' timestamp : Int)
    (h1 : 0 ≤ secret) (h2 : secret < 2 ^ 32) (h1' : 0 ≤ secret') (h2' : secret' < 2 ^ 32)
    (hne : secret ≠ secret') :
    safe_syn_flood src_ip src_port dst_ip dst_port secret timestamp ≠
      safe_syn_flood src_ip src_port dst_ip dst_port secret' timestamp :=
  cookie_secret_sensitive_thm src_ip src_port dst_ip dst_port secret timestamp secret'
    (by rw [Int.emod_eq_of_lt h1 h2, Int.emod_eq_of_lt h1' h2']; exact hne)

/-- Corollary for 32-bit timestamps: two different timestamps in `[0, 2^32)` always yield
different cookies. -/
theorem cookie_timestamp_injective_thm
    (src_ip src_port dst_ip dst_port secret timestamp timestamp' : Int)
    (h1 : 0 ≤ timestamp) (h2 : timestamp < 2 ^ 32) (h1' : 0 ≤ timestamp')
    (h2' : timestamp' < 2 ^ 32) (hne : timestamp ≠ timestamp') :
    safe_syn_flood src_ip src_port dst_ip dst_port secret timestamp ≠
      safe_syn_flood src_ip src_port dst_ip dst_port secret timestamp' :=
  cookie_timestamp_sensitive_thm src_ip src_port dst_ip dst_port secret timestamp timestamp'
    (by rw [Int.emod_eq_of_lt h1 h2, Int.emod_eq_of_lt h1' h2']; exact hne)

/-- The cookie of the next epoch differs from the current one (`c_later != c1`). -/
def cookie_next_epoch_prop (src_ip src_port dst_ip dst_port secret timestamp : Int) : Prop :=
  safe_syn_flood src_ip src_port dst_ip dst_port secret (timestamp + 1) ≠
    safe_syn_flood src_ip src_port dst_ip dst_port secret timestamp

theorem cookie_next_epoch_thm (src_ip src_port dst_ip dst_port secret timestamp : Int) :
    cookie_next_epoch_prop src_ip src_port dst_ip dst_port secret timestamp :=
  cookie_timestamp_sensitive_thm src_ip src_port dst_ip dst_port secret (timestamp + 1)
    timestamp (by omega)

/-- Two cookies for the same 4-tuple and secret coincide iff their timestamps agree modulo
`2^32`. -/
theorem cookie_timestamp_eq_iff (src_ip src_port dst_ip dst_port secret t₁ t₂ : Int) :
    safe_syn_flood src_ip src_port dst_ip dst_port secret t₁ =
      safe_syn_flood src_ip src_port dst_ip dst_port secret t₂ ↔ t₁ % 2 ^ 32 = t₂ % 2 ^ 32 := by
  constructor
  · intro h
    by_contra hne
    exact cookie_timestamp_sensitive_thm src_ip src_port dst_ip dst_port secret t₁ t₂ hne h
  · intro h
    unfold safe_syn_flood
    have h1 : t₁ ≡ t₂ [ZMOD 2 ^ 32] := h
    exact (h1.mul_right 1597334677).add_left _

/-- Going back one epoch subtracts `p6` from the cookie (modulo `2^32`). -/
theorem cookie_prev_epoch_eq (src_ip src_port dst_ip dst_port secret timestamp : Int) :
    safe_syn_flood src_ip src_port dst_ip dst_port secret (timestamp - 1) =
      (safe_syn_flood src_ip src_port dst_ip dst_port secret timestamp - 1597334677) % 2 ^ 32 := by
  unfold safe_syn_flood
  rw [two_pow_32]
  omega

/-- For two 32-bit values, `(x + 1) % 2^32 = (y + 1) % 2^32` iff `x = y`. -/
theorem ack_eq_iff {x y : Int} (hx : 0 ≤ x ∧ x < 2 ^ 32) (hy : 0 ≤ y ∧ y < 2 ^ 32) :
    (x + 1) % 2 ^ 32 = (y + 1) % 2 ^ 32 ↔ x = y := by
  rw [two_pow_32] at *
  constructor <;> intro h <;> omega

/-- Every cookie of the stateless batch is a 32-bit value and the batch has the requested
length (`len(cookies) == 1000`). -/
def generate_cookies_prop (n : Nat) (secret timestamp : Int) : Prop :=
  (generate_cookies n secret timestamp).length = n ∧
    ∀ c ∈ generate_cookies n secret timestamp, 0 ≤ c ∧ c < 2 ^ 32

theorem generate_cookies_thm (n : Nat) (secret timestamp : Int) :
    generate_cookies_prop n secret timestamp := by
  refine ⟨by simp [generate_cookies], ?_⟩
  intro c hc
  simp only [generate_cookies, List.mem_map, List.mem_range] at hc
  obtain ⟨i, _, rfl⟩ := hc
  exact cookie_range_thm _ _ _ _ _ _

/-! ## Properties of `verify_syn_cookie` -/

/-- Exact characterisation of the verifier: an ACK is accepted iff it equals `cookie + 1
(mod 2^32)` for the current epoch or for the previous epoch. -/
def verify_iff_prop (src_ip src_port dst_ip dst_port secret timestamp : Int) : Prop :=
  ∀ received_ack : Int,
    verify_syn_cookie src_ip src_port dst_ip dst_port secret timestamp received_ack = true ↔
      ((safe_syn_flood src_ip src_port dst_ip dst_port secret timestamp + 1) % 2 ^ 32
          = received_ack ∨
        (safe_syn_flood src_ip src_port dst_ip dst_port secret (timestamp - 1) + 1) % 2 ^ 32
          = received_ack)

theorem verify_iff_thm (src_ip src_port dst_ip dst_port secret timestamp : Int) :
    verify_iff_prop src_ip src_port dst_ip dst_port secret timestamp := by
  intro received_ack
  simp [verify_syn_cookie]

/-- The genuine ACK `(cookie + 1) % 2^32` of the current epoch is accepted. -/
def verify_valid_ack_prop (src_ip src_port dst_ip dst_port secret timestamp : Int) : Prop :=
  verify_syn_cookie src_ip src_port dst_ip dst_port secret timestamp
    ((safe_syn_flood src_ip src_port dst_ip dst_port secret timestamp + 1) % 2 ^ 32) = true

theorem verify_valid_ack_thm (src_ip src_port dst_ip dst_port secret timestamp : Int) :
    verify_valid_ack_prop src_ip src_port dst_ip dst_port secret timestamp := by
  unfold verify_valid_ack_prop
  simp [verify_syn_cookie]

/-- Clock-skew tolerance: the ACK built from the cookie of the previous epoch is accepted. -/
def verify_prev_epoch_prop (src_ip src_port dst_ip dst_port secret timestamp : Int) : Prop :=
  verify_syn_cookie src_ip src_port dst_ip dst_port secret timestamp
    ((safe_syn_flood src_ip src_port dst_ip dst_port secret (timestamp - 1) + 1) % 2 ^ 32) = true

theorem verify_prev_epoch_thm (src_ip src_port dst_ip dst_port secret timestamp : Int) :
    verify_prev_epoch_prop src_ip src_port dst_ip dst_port secret timestamp := by
  unfold verify_prev_epoch_prop
  simp [verify_syn_cookie]

/-- A wrong ACK (`cookie + 2`) is rejected. -/
def verify_invalid_ack_prop (src_ip src_port dst_ip dst_port secret timestamp : Int) : Prop :=
  verify_syn_cookie src_ip src_port dst_ip dst_port secret timestamp
    ((safe_syn_flood src_ip src_port dst_ip dst_port secret timestamp + 2) % 2 ^ 32) = false

theorem verify_invalid_ack_thm (src_ip src_port dst_ip dst_port secret timestamp : Int) :
    verify_invalid_ack_prop src_ip src_port dst_ip dst_port secret timestamp := by
  unfold verify_invalid_ack_prop
  rw [Bool.eq_false_iff]
  intro hv
  rcases (verify_iff_thm src_ip src_port dst_ip dst_port secret timestamp _).mp hv with h | h
  · rw [two_pow_32] at h
    omega
  · rw [cookie_prev_epoch_eq] at h
    have hr := cookie_range_thm src_ip src_port dst_ip dst_port secret timestamp
    unfold cookie_range_prop at hr
    rw [two_pow_32] at h hr
    omega

/-- Replay protection: an ACK built from the cookie of an older epoch
(`timestamp - k` with `2 ≤ k < 2^32`, e.g. `k = 5`) is rejected. -/
def verify_replay_prop (src_ip src_port dst_ip dst_port secret timestamp : Int) : Prop :=
  ∀ k : Int, 2 ≤ k → k < 2 ^ 32 →
    verify_syn_cookie src_ip src_port dst_ip dst_port secret timestamp
      ((safe_syn_flood src_ip src_port dst_ip dst_port secret (timestamp - k) + 1) % 2 ^ 32)
      = false

theorem verify_replay_thm (src_ip src_port dst_ip dst_port secret timestamp : Int) :
    verify_replay_prop src_ip src_port dst_ip dst_port secret timestamp := by
  intro k hk1 hk2
  rw [Bool.eq_false_iff]
  intro hv
  rw [two_pow_32] at hk2
  rcases (verify_iff_thm src_ip src_port dst_ip dst_port secret timestamp _).mp hv with h | h
  · rw [ack_eq_iff (cookie_range_thm _ _ _ _ _ _) (cookie_range_thm _ _ _ _ _ _),
      cookie_timestamp_eq_iff, two_pow_32] at h
    omega
  · rw [ack_eq_iff (cookie_range_thm _ _ _ _ _ _) (cookie_range_thm _ _ _ _ _ _),
      cookie_timestamp_eq_iff, two_pow_32] at h
    omega

/-! ## Post-condition -/

/-- Post-condition: conjunction of all properties of the cookie generator and verifier for
the given connection parameters. -/
def Post_prop (src_ip src_port dst_ip dst_port secret timestamp : Int) : Prop :=
  cookie_range_prop src_ip src_port dst_ip dst_port secret timestamp ∧
  cookie_deterministic_prop src_ip src_port dst_ip dst_port secret timestamp ∧
  cookie_formula_prop src_ip src_port dst_ip dst_port secret timestamp ∧
  cookie_mod_invariant_prop src_ip src_port dst_ip dst_port secret timestamp ∧
  cookie_src_ip_sensitive_prop src_ip src_port dst_ip dst_port secret timestamp ∧
  cookie_secret_sensitive_prop src_ip src_port dst_ip dst_port secret timestamp ∧
  cookie_timestamp_sensitive_prop src_ip src_port dst_ip dst_port secret timestamp ∧
  cookie_next_epoch_prop src_ip src_port dst_ip dst_port secret timestamp ∧
  verify_iff_prop src_ip src_port dst_ip dst_port secret timestamp ∧
  verify_valid_ack_prop src_ip src_port dst_ip dst_port secret timestamp ∧
  verify_prev_epoch_prop src_ip src_port dst_ip dst_port secret timestamp ∧
  verify_invalid_ack_prop src_ip src_port dst_ip dst_port secret timestamp ∧
  verify_replay_prop src_ip src_port dst_ip dst_port secret timestamp ∧
  (∀ n : Nat, generate_cookies_prop n secret timestamp)

/-! ## Property-based tests -/

-- cookie_range_prop
#eval Plausible.Testable.check (∀ a b c d e f : Int,
  0 ≤ safe_syn_flood a b c d e f ∧ safe_syn_flood a b c d e f < 2 ^ 32)

-- cookie_deterministic_prop
#eval Plausible.Testable.check (∀ a b c d e f : Int,
  safe_syn_flood a b c d e f = safe_syn_flood a b c d e f)

-- cookie_formula_prop
#eval Plausible.Testable.check (∀ a b c d e f : Int,
  safe_syn_flood a b c d e f =
    (a * 2654435761 + b * 2246822519 + c * 3266489917 + d * 668265263
      + e * 374761393 + f * 1597334677) % 2 ^ 32)

-- cookie_mod_invariant_prop
#eval Plausible.Testable.check (∀ a b c d e f : Int,
  safe_syn_flood a b c d e f =
    safe_syn_flood (a % 2 ^ 32) (b % 2 ^ 32) (c % 2 ^ 32) (d % 2 ^ 32) (e % 2 ^ 32) (f % 2 ^ 32))

-- cookie_src_ip_sensitive_prop (randomised, plus a bounded exhaustive check)
#eval Plausible.Testable.check (∀ a a' b c d e f : Int,
  a % 2 ^ 32 ≠ a' % 2 ^ 32 → safe_syn_flood a b c d e f ≠ safe_syn_flood a' b c d e f)
example : (List.range 40).all (fun i => (List.range 40).all fun j =>
    (i : Int) % 2 ^ 32 == (j : Int) % 2 ^ 32 ||
      safe_syn_flood i 12345 0x0A000001 80 0xDEADBEEF 1000
        != safe_syn_flood j 12345 0x0A000001 80 0xDEADBEEF 1000) = true := by native_decide

-- cookie_secret_sensitive_prop (randomised, plus a bounded exhaustive check)
#eval Plausible.Testable.check (∀ a b c d e e' f : Int,
  e % 2 ^ 32 ≠ e' % 2 ^ 32 → safe_syn_flood a b c d e f ≠ safe_syn_flood a b c d e' f)
example : (List.range 40).all (fun i => (List.range 40).all fun j =>
    (i : Int) % 2 ^ 32 == (j : Int) % 2 ^ 32 ||
      safe_syn_flood 0xC0A80101 12345 0x0A000001 80 (0xDEADBEEF + i) 1000
        != safe_syn_flood 0xC0A80101 12345 0x0A000001 80 (0xDEADBEEF + j) 1000) = true := by
  native_decide

-- cookie_timestamp_sensitive_prop (randomised, plus a bounded exhaustive check)
#eval Plausible.Testable.check (∀ a b c d e f f' : Int,
  f % 2 ^ 32 ≠ f' % 2 ^ 32 → safe_syn_flood a b c d e f ≠ safe_syn_flood a b c d e f')
example : (List.range 40).all (fun i => (List.range 40).all fun j =>
    (i : Int) % 2 ^ 32 == (j : Int) % 2 ^ 32 ||
      safe_syn_flood 0xC0A80101 12345 0x0A000001 80 0xDEADBEEF (1000 + i)
        != safe_syn_flood 0xC0A80101 12345 0x0A000001 80 0xDEADBEEF (1000 + j)) = true := by
  native_decide

-- cookie_next_epoch_prop
#eval Plausible.Testable.check (∀ a b c d e f : Int,
  safe_syn_flood a b c d e (f + 1) ≠ safe_syn_flood a b c d e f)

-- verify_iff_prop
#eval Plausible.Testable.check (∀ a b c d e f ack : Int,
  verify_syn_cookie a b c d e f ack = true ↔
    ((safe_syn_flood a b c d e f + 1) % 2 ^ 32 = ack ∨
      (safe_syn_flood a b c d e (f - 1) + 1) % 2 ^ 32 = ack))

-- verify_valid_ack_prop
#eval Plausible.Testable.check (∀ a b c d e f : Int,
  verify_syn_cookie a b c d e f ((safe_syn_flood a b c d e f + 1) % 2 ^ 32) = true)

-- verify_prev_epoch_prop
#eval Plausible.Testable.check (∀ a b c d e f : Int,
  verify_syn_cookie a b c d e f ((safe_syn_flood a b c d e (f - 1) + 1) % 2 ^ 32) = true)

-- verify_invalid_ack_prop
#eval Plausible.Testable.check (∀ a b c d e f : Int,
  verify_syn_cookie a b c d e f ((safe_syn_flood a b c d e f + 2) % 2 ^ 32) = false)

-- verify_replay_prop (randomised with the decidable precondition, plus a bounded check
-- over `k = 2, …, 101` for a fixed connection)
#eval Plausible.Testable.check (∀ a b c d e f k : Int, 2 ≤ k → k < 2 ^ 32 →
  verify_syn_cookie a b c d e f ((safe_syn_flood a b c d e (f - k) + 1) % 2 ^ 32) = false)
example : (List.range 100).all (fun k =>
    verify_syn_cookie 0xC0A80104 33333 0x0A000001 80 0xDEADBEEF 1000
      ((safe_syn_flood 0xC0A80104 33333 0x0A000001 80 0xDEADBEEF (1000 - ((k : Int) + 2)) + 1)
        % 2 ^ 32) == false) = true := by native_decide

-- generate_cookies_prop
#eval Plausible.Testable.check (∀ (n : Nat) (e f : Int),
  (generate_cookies n e f).length = n ∧
    (generate_cookies n e f).all (fun c => 0 ≤ c ∧ c < 2 ^ 32) = true)

-- Post_prop: executable Boolean form (the inner quantifiers of the sensitivity, verifier and
-- replay conjuncts become the extra arguments `a' e' f' ack k`; the batch conjunct is
-- instantiated at `n = 10`).
set_option synthInstance.maxSize 8192 in
/-- Executable Boolean form of `Post_prop`, used by the property-based tests below. -/
def post_check (a b c d e f a' e' f' ack k : Int) : Bool :=
  decide (
    (0 ≤ safe_syn_flood a b c d e f ∧ safe_syn_flood a b c d e f < 2 ^ 32) ∧
    safe_syn_flood a b c d e f = safe_syn_flood a b c d e f ∧
    safe_syn_flood a b c d e f =
      (a * 2654435761 + b * 2246822519 + c * 3266489917 + d * 668265263
        + e * 374761393 + f * 1597334677) % 2 ^ 32 ∧
    safe_syn_flood a b c d e f =
      safe_syn_flood (a % 2 ^ 32) (b % 2 ^ 32) (c % 2 ^ 32) (d % 2 ^ 32) (e % 2 ^ 32)
        (f % 2 ^ 32) ∧
    (a % 2 ^ 32 ≠ a' % 2 ^ 32 → safe_syn_flood a b c d e f ≠ safe_syn_flood a' b c d e f) ∧
    (e % 2 ^ 32 ≠ e' % 2 ^ 32 → safe_syn_flood a b c d e f ≠ safe_syn_flood a b c d e' f) ∧
    (f % 2 ^ 32 ≠ f' % 2 ^ 32 → safe_syn_flood a b c d e f ≠ safe_syn_flood a b c d e f') ∧
    safe_syn_flood a b c d e (f + 1) ≠ safe_syn_flood a b c d e f ∧
    (verify_syn_cookie a b c d e f ack = true ↔
      ((safe_syn_flood a b c d e f + 1) % 2 ^ 32 = ack ∨
        (safe_syn_flood a b c d e (f - 1) + 1) % 2 ^ 32 = ack)) ∧
    verify_syn_cookie a b c d e f ((safe_syn_flood a b c d e f + 1) % 2 ^ 32) = true ∧
    verify_syn_cookie a b c d e f ((safe_syn_flood a b c d e (f - 1) + 1) % 2 ^ 32) = true ∧
    verify_syn_cookie a b c d e f ((safe_syn_flood a b c d e f + 2) % 2 ^ 32) = false ∧
    (2 ≤ k → k < 2 ^ 32 →
      verify_syn_cookie a b c d e f ((safe_syn_flood a b c d e (f - k) + 1) % 2 ^ 32)
        = false) ∧
    (generate_cookies 10 e f).length = 10 ∧
    (generate_cookies 10 e f).all (fun c => 0 ≤ c ∧ c < 2 ^ 32) = true)

-- Post_prop: randomised PBT
#eval Plausible.Testable.check (∀ a b c d e f a' e' f' ack k : Int,
  post_check a b c d e f a' e' f' ack k = true)

-- Post_prop: bounded PBT on a grid around the connection of the Python `check`
example : (List.range 6).all (fun i => (List.range 6).all fun j =>
    post_check (0xC0A80101 + i) 12345 0x0A000001 80 (0xDEADBEEF + j) (1000 + i)
      (0xC0A80101 + j) (0xDEADBEEF + i) (1000 + j) (2237255268 + i + j) (2 + i + j))
    = true := by native_decide

/-! ## Correctness theorem -/

/-- Correctness: for every admissible input (every integer 6-tuple), the post-condition holds. -/
theorem correctness_thm (src_ip src_port dst_ip dst_port secret timestamp : Int)
    (_hpre : Pre src_ip src_port dst_ip dst_port secret timestamp) :
    Post_prop src_ip src_port dst_ip dst_port secret timestamp :=
  ⟨cookie_range_thm src_ip src_port dst_ip dst_port secret timestamp,
   cookie_deterministic_thm src_ip src_port dst_ip dst_port secret timestamp,
   cookie_formula_thm src_ip src_port dst_ip dst_port secret timestamp,
   cookie_mod_invariant_thm src_ip src_port dst_ip dst_port secret timestamp,
   cookie_src_ip_sensitive_thm src_ip src_port dst_ip dst_port secret timestamp,
   cookie_secret_sensitive_thm src_ip src_port dst_ip dst_port secret timestamp,
   cookie_timestamp_sensitive_thm src_ip src_port dst_ip dst_port secret timestamp,
   cookie_next_epoch_thm src_ip src_port dst_ip dst_port secret timestamp,
   verify_iff_thm src_ip src_port dst_ip dst_port secret timestamp,
   verify_valid_ack_thm src_ip src_port dst_ip dst_port secret timestamp,
   verify_prev_epoch_thm src_ip src_port dst_ip dst_port secret timestamp,
   verify_invalid_ack_thm src_ip src_port dst_ip dst_port secret timestamp,
   verify_replay_thm src_ip src_port dst_ip dst_port secret timestamp,
   fun n => generate_cookies_thm n secret timestamp⟩

/-! ## Imperative implementation -/

/-- Imperative `safe_syn_flood`: accumulate the weighted fields in a mutable accumulator, then
reduce modulo `2^32`. -/
def safe_syn_flood_imp (src_ip src_port dst_ip dst_port secret timestamp : Int) : Int :=
  Id.run do
    let mut acc : Int := 0
    acc := acc + src_ip * 2654435761
    acc := acc + src_port * 2246822519
    acc := acc + dst_ip * 3266489917
    acc := acc + dst_port * 668265263
    acc := acc + secret * 374761393
    acc := acc + timestamp * 1597334677
    return acc % (2 ^ 32)

/-- Imperative `verify_syn_cookie`: loop over the two epochs exactly like the Python
`for ts in (timestamp, timestamp - 1)` with an early `return True`. -/
def verify_syn_cookie_imp
    (src_ip src_port dst_ip dst_port secret timestamp received_ack : Int) : Bool :=
  Id.run do
    for ts in [timestamp, timestamp - 1] do
      let expected := safe_syn_flood_imp src_ip src_port dst_ip dst_port secret ts
      if (expected + 1) % (2 ^ 32) == received_ack then
        return true
    return false

/-- Imperative stateless batch generation (the `cookies = [...]` list comprehension of the
Python `check`, built by pushing into a mutable array). -/
def generate_cookies_imp (n : Nat) (secret timestamp : Int) : List Int := Id.run do
  let mut cookies : Array Int := #[]
  for i in List.range n do
    cookies := cookies.push
      (safe_syn_flood_imp (0x0A000002 + (i : Int)) (1000 + (i : Int)) 0x0A000001 80 secret
        timestamp)
  return cookies.toList

/-! ## Imperative tests -/

example : safe_syn_flood_imp 0xC0A80101 12345 0x0A000001 80 0xDEADBEEF 1000 = 2237255268 := by
  native_decide
example : safe_syn_flood_imp 0xC0A80102 12345 0x0A000001 80 0xDEADBEEF 1000 = 596723733 := by
  native_decide
example : safe_syn_flood_imp 0xC0A80101 12345 0x0A000001 80 0xCAFEBABE 1000 = 3761385859 := by
  native_decide
example : safe_syn_flood_imp 0xC0A80101 12345 0x0A000001 80 0xDEADBEEF 1001 = 3834589945 := by
  native_decide
example : safe_syn_flood_imp 0 0 0 0 0 (-1) = 2697632619 := by native_decide
example : verify_syn_cookie_imp 0xC0A80101 12345 0x0A000001 80 0xDEADBEEF 1000 2237255269
    = true := by native_decide
example : verify_syn_cookie_imp 0xC0A80101 12345 0x0A000001 80 0xDEADBEEF 1000 2237255270
    = false := by native_decide
example : verify_syn_cookie_imp 0xC0A80103 22222 0x0A000001 80 0xDEADBEEF 1000
    ((safe_syn_flood_imp 0xC0A80103 22222 0x0A000001 80 0xDEADBEEF (1000 - 1) + 1) % 2 ^ 32)
    = true := by native_decide
example : verify_syn_cookie_imp 0xC0A80104 33333 0x0A000001 80 0xDEADBEEF 1000
    ((safe_syn_flood_imp 0xC0A80104 33333 0x0A000001 80 0xDEADBEEF (1000 - 5) + 1) % 2 ^ 32)
    = false := by native_decide
example : (generate_cookies_imp 1000 0xDEADBEEF 1000).length = 1000 := by native_decide
example : generate_cookies_imp 1000 0xDEADBEEF 1000 = generate_cookies 1000 0xDEADBEEF 1000 := by
  native_decide

#eval safe_syn_flood_imp 0xC0A80101 12345 0x0A000001 80 0xDEADBEEF 1000   -- 2237255268
#eval verify_syn_cookie_imp 0xC0A80101 12345 0x0A000001 80 0xDEADBEEF 1000 2237255269   -- true
#eval verify_syn_cookie_imp 0xC0A80101 12345 0x0A000001 80 0xDEADBEEF 1000 2237255270   -- false
#eval (generate_cookies_imp 1000 0xDEADBEEF 1000).length   -- 1000

-- PBTs for the functional/imperative equivalence
#eval Plausible.Testable.check (∀ a b c d e f : Int,
  safe_syn_flood_imp a b c d e f = safe_syn_flood a b c d e f)
#eval Plausible.Testable.check (∀ a b c d e f ack : Int,
  verify_syn_cookie_imp a b c d e f ack = verify_syn_cookie a b c d e f ack)
#eval Plausible.Testable.check (∀ (n : Nat) (e f : Int),
  generate_cookies_imp n e f = generate_cookies n e f)

/-! ## Equivalence theorems: functional = imperative -/

theorem safe_syn_flood_imp_eq (src_ip src_port dst_ip dst_port secret timestamp : Int) :
    safe_syn_flood_imp src_ip src_port dst_ip dst_port secret timestamp =
      safe_syn_flood src_ip src_port dst_ip dst_port secret timestamp := by
  simp [safe_syn_flood_imp, safe_syn_flood]

theorem verify_syn_cookie_imp_eq
    (src_ip src_port dst_ip dst_port secret timestamp received_ack : Int) :
    verify_syn_cookie_imp src_ip src_port dst_ip dst_port secret timestamp received_ack =
      verify_syn_cookie src_ip src_port dst_ip dst_port secret timestamp received_ack := by
  simp [verify_syn_cookie_imp, verify_syn_cookie, safe_syn_flood_imp_eq]
  split_ifs <;> simp_all

/-- Running the push-loop over any list from any accumulator appends the mapped cookies. -/
theorem generate_cookies_loop (secret timestamp : Int) :
    ∀ (l : List Nat) (acc : Array Int),
      (Id.run (forIn l acc (fun (i : Nat) (r : Array Int) =>
        pure (ForInStep.yield (r.push (safe_syn_flood_imp (0x0A000002 + (i : Int))
          (1000 + (i : Int)) 0x0A000001 80 secret timestamp)))))).toList
      = acc.toList ++ l.map (fun (i : Nat) =>
          safe_syn_flood (0x0A000002 + (i : Int)) (1000 + (i : Int)) 0x0A000001 80 secret
            timestamp) := by
  intro l acc
  simp [safe_syn_flood_imp_eq]

theorem generate_cookies_imp_eq (n : Nat) (secret timestamp : Int) :
    generate_cookies_imp n secret timestamp = generate_cookies n secret timestamp := by
  unfold generate_cookies_imp generate_cookies
  simp only [pure_bind, Id.run_bind, Id.run_pure]
  exact (generate_cookies_loop secret timestamp (List.range n) #[]).trans (by simp)

/-- Equivalence of the whole verification pipeline: the imperative verifier applied to the
imperative cookie accepts exactly when the functional verifier applied to the functional
cookie does. -/
theorem pipeline_imp_eq (src_ip src_port dst_ip dst_port secret timestamp ts : Int) :
    verify_syn_cookie_imp src_ip src_port dst_ip dst_port secret timestamp
        ((safe_syn_flood_imp src_ip src_port dst_ip dst_port secret ts + 1) % 2 ^ 32) =
      verify_syn_cookie src_ip src_port dst_ip dst_port secret timestamp
        ((safe_syn_flood src_ip src_port dst_ip dst_port secret ts + 1) % 2 ^ 32) := by
  rw [verify_syn_cookie_imp_eq, safe_syn_flood_imp_eq]

end «63_unsafeSynFlood_safe»
end Agent
