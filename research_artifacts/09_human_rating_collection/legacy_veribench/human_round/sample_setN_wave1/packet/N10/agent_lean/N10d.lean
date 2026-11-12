import Mathlib

/-!
# Base32 encoding and decoding

A Lean 4 formalisation of the Python Base32 codec (`b32encode` / `b32decode`)
sourced from Python's standard `base64` library, as given in the VeriBench task
`23_base32`.

Modelling choices:

* A *bytes-like object* is modelled as `List Nat` whose elements are `< 256`.
* `b32encode : List Nat -> List Nat` returns the ASCII codes of the Base32 text
  (Python returns a `bytes` object; ASCII codes are the faithful representation).
* `b32decode : Bool -> List Nat -> Option (List Nat)`; the `Bool` is Python's
  `casefold` flag and `none` models `binascii.Error('Non-base32 digit found')`.
  Python's `map01` argument is left at its default `None` (unused by the tests).
* All arithmetic is on `Nat`, so the whole development is kernel-checkable.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000

namespace B32Codec

/-! ## Convenience conversions between text and byte lists -/

/-- ASCII codes of a string. -/
def strToBytes (s : String) : List Nat := s.toList.map Char.toNat

/-- String built from ASCII codes. -/
def bytesToStr (bs : List Nat) : String := String.mk (bs.map Char.ofNat)

/-! ## The Base32 alphabet -/

/-- `_b32alphabet = b'ABCDEFGHIJKLMNOPQRSTUVWXYZ234567'` indexed by a 5-bit value. -/
def b32Char (i : Nat) : Nat := if i < 26 then 65 + i else 50 + (i - 26)

/-- Inverse of `b32Char`: `rev_alphabet` from the Python source. -/
def b32IndexOf (c : Nat) : Option Nat :=
  if 65 ≤ c ∧ c ≤ 90 then some (c - 65)
  else if 50 ≤ c ∧ c ≤ 55 then some (c - 50 + 26)
  else none

/-- `bytes.upper()` restricted to ASCII letters. -/
def toUpperAscii (c : Nat) : Nat := if 97 ≤ c ∧ c ≤ 122 then c - 32 else c

/-- `bytes.lower()` restricted to ASCII letters. -/
def toLowerByte (c : Nat) : Nat := if 65 ≤ c ∧ c ≤ 90 then c + 32 else c

/-- The `casefold` transformation applied to one byte. -/
def casefoldByte (casefold : Bool) (c : Nat) : Nat :=
  if casefold then toUpperAscii c else c

/-! ## Chunking and bit accumulation -/

/-- `for i in range(0, len(s), 5): chunk = s[i:i+5]` -/
def chunksOf5 : List Nat → List (List Nat)
  | [] => []
  | [a] => [[a]]
  | [a, b] => [[a, b]]
  | [a, b, c] => [[a, b, c]]
  | [a, b, c, d] => [[a, b, c, d]]
  | a :: b :: c :: d :: e :: rest => [a, b, c, d, e] :: chunksOf5 rest

/-- `chunk = chunk + b'\0' * (5 - len(chunk))` -/
def padTo5 (bs : List Nat) : List Nat := bs ++ List.replicate (5 - bs.length) 0

/-- `int.from_bytes(chunk, 'big')` -/
def toValBE (bs : List Nat) : Nat := bs.foldl (fun a b => a * 256 + b) 0

/-- The `k` most significant base-32 digits of `n`, most significant first. -/
def digits32 (n : Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => (n / 32 ^ k % 32) :: digits32 n k

/-- The eight 5-bit indices `(val >> 35) & 0x1F`, ..., `val & 0x1F`. -/
def encIndices (val : Nat) : List Nat :=
  [ val / 2 ^ 35 % 32, val / 2 ^ 30 % 32, val / 2 ^ 25 % 32, val / 2 ^ 20 % 32,
    val / 2 ^ 15 % 32, val / 2 ^ 10 % 32, val / 2 ^ 5 % 32, val % 32 ]

/-- Number of `=` characters appended for a chunk of the given length.
This is Python's `rem = len(s) % 5` padding fix-up. -/
def padCount : Nat → Nat
  | 1 => 6
  | 2 => 4
  | 3 => 3
  | 4 => 1
  | _ => 0

/-- The 40-bit value of a (possibly short) chunk. -/
def chunkVal (bs : List Nat) : Nat := toValBE (padTo5 bs)

/-- The significant Base32 indices of a chunk (before `=` padding). -/
def sigIndices (bs : List Nat) : List Nat :=
  (encIndices (chunkVal bs)).take (8 - padCount bs.length)

/-- The significant Base32 characters of a chunk. -/
def sigChunk (bs : List Nat) : List Nat := (sigIndices bs).map b32Char

/-- One encoded 8-character block, `=` padding included. -/
def encChunk (bs : List Nat) : List Nat :=
  sigChunk bs ++ List.replicate (padCount bs.length) 61

/-- `b32encode` -/
def b32encode (s : List Nat) : List Nat := ((chunksOf5 s).map encChunk).flatten

/-! ## Decoding helpers -/

/-- `s.rstrip(b'=')`, implemented by stripping leading `=` from the reverse. -/
def lstripEq : List Nat → List Nat
  | [] => []
  | c :: cs => if c = 61 then lstripEq cs else c :: cs

/-- `s.rstrip(b'=')` -/
def rstripEq (cs : List Nat) : List Nat := (lstripEq cs.reverse).reverse

/-- Mapping every character through `rev_alphabet`, failing on a non-base32 digit. -/
def toIndices : List Nat → Option (List Nat)
  | [] => some []
  | c :: cs =>
      match b32IndexOf c with
      | none => none
      | some i => (toIndices cs).map (i :: ·)

/-- The `val`/`bits` accumulator loop of `b32decode`. -/
def bitsToBytes : Nat → Nat → List Nat → List Nat
  | _, _, [] => []
  | val, bits, i :: rest =>
      let val' := val * 32 + i
      let bits' := bits + 5
      if bits' ≥ 8 then
        (val' / 2 ^ (bits' - 8)) % 256 :: bitsToBytes val' (bits' - 8) rest
      else bitsToBytes val' bits' rest

/-- `foldl (fun a b => a * 32 + b) 0`, the base-32 value of an index list. -/
def foldl32 (cs : List Nat) : Nat := cs.foldl (fun a b => a * 32 + b) 0

/-- Big-endian byte expansion of the top `B` bits of `W`. -/
def bytesOf (W : Nat) : Nat → List Nat
  | B + 8 => (W / 2 ^ B) % 256 :: bytesOf W B
  | _ => []

/-- `b32decode` -/
def b32decode (casefold : Bool) (s : List Nat) : Option (List Nat) :=
  (toIndices (rstripEq (s.map (casefoldByte casefold)))).map (bitsToBytes 0 0)

/-! ## The two benchmark entry points of the Python source -/

def benchmark_b32encode (s : List Nat) : List Nat := b32encode s

def benchmark_b32decode (casefold : Bool) (s : List Nat) : Option (List Nat) :=
  b32decode casefold s

/-! ## Unit tests (the `check` function of the Python source) -/

example : b32encode [] = [] := by native_decide
example : b32encode (strToBytes "f") = strToBytes "MY======" := by native_decide
example : b32encode (strToBytes "fo") = strToBytes "MZXQ====" := by native_decide
example : b32encode (strToBytes "foo") = strToBytes "MZXW6===" := by native_decide
example : b32encode (strToBytes "foob") = strToBytes "MZXW6YQ=" := by native_decide
example : b32encode (strToBytes "fooba") = strToBytes "MZXW6YTB" := by native_decide
example : b32encode (strToBytes "foobar") = strToBytes "MZXW6YTBOI======" := by native_decide

example : b32decode false (b32encode (strToBytes "VeriBench"))
    = some (strToBytes "VeriBench") := by native_decide
example : b32decode true (strToBytes "mzxw6ytb") = some (strToBytes "fooba") := by native_decide
example : b32decode false (strToBytes "MZXW6YTBOI======") = some (strToBytes "foobar") := by native_decide
example : b32decode false (strToBytes "MZXW6!==") = none := by native_decide
example : b32decode false (strToBytes "") = some [] := by native_decide
example : (b32encode (strToBytes "foobar")).length = 16 := by native_decide

#eval bytesToStr (b32encode (strToBytes "foobar"))
#eval (b32decode true (strToBytes "mzxw6ytb")).map bytesToStr

/-! ## Pre-conditions -/

/-- `pre_encode`: the input is a bytes-like object, i.e. every element is a byte. -/
def Pre (s : List Nat) : Prop := ∀ b ∈ s, b < 256

/-- `pre_decode`: the input is a bytes-like object (or an ASCII string, whose
characters are exactly the codes `< 128`). -/
def PreDecode (s : List Nat) : Prop := ∀ c ∈ s, c < 128

/-! ## Alphabet lemmas -/

theorem b32Char_lt26 (i : Nat) (h : i < 26) : b32Char i = 65 + i := by
  simp [b32Char, h]

theorem b32Char_ge26 (i : Nat) (h : 26 ≤ i) : b32Char i = 50 + (i - 26) := by
  simp [b32Char, show ¬(i < 26) from by omega]

theorem b32Char_range (i : Nat) (h : i < 32) :
    (65 ≤ b32Char i ∧ b32Char i ≤ 90) ∨ (50 ≤ b32Char i ∧ b32Char i ≤ 55) := by
  by_cases hi : i < 26
  · have h1 : b32Char i = 65 + i := b32Char_lt26 i hi
    exact Or.inl (by omega)
  · have h2 : 26 ≤ i := by omega
    have h1 : b32Char i = 50 + (i - 26) := b32Char_ge26 i h2
    exact Or.inr (by omega)

theorem b32Char_ne_61 (i : Nat) (h : i < 32) : b32Char i ≠ 61 := by
  rcases b32Char_range i h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

theorem b32IndexOf_b32Char (i : Nat) (h : i < 32) : b32IndexOf (b32Char i) = some i := by
  by_cases hi : i < 26
  · have h1 : b32Char i = 65 + i := b32Char_lt26 i hi
    have h2 : 65 ≤ 65 + i ∧ 65 + i ≤ 90 := by omega
    rw [h1, b32IndexOf, if_pos h2]
    congr 1; omega
  · have h2 : 26 ≤ i := by omega
    have h1 : b32Char i = 50 + (i - 26) := b32Char_ge26 i h2
    have h3 : ¬(65 ≤ 50 + (i - 26) ∧ 50 + (i - 26) ≤ 90) := by omega
    have h4 : 50 ≤ 50 + (i - 26) ∧ 50 + (i - 26) ≤ 55 := by omega
    rw [h1, b32IndexOf, if_neg h3, if_pos h4]
    congr 1; omega

theorem b32IndexOf_eq_none (c : Nat) :
    b32IndexOf c = none ↔ ¬(65 ≤ c ∧ c ≤ 90) ∧ ¬(50 ≤ c ∧ c ≤ 55) := by
  by_cases h : 65 ≤ c ∧ c ≤ 90
  · simp [b32IndexOf, h]
  · by_cases h' : 50 ≤ c ∧ c ≤ 55
    · simp [b32IndexOf, h, h']
    · simp [b32IndexOf, h, h']

theorem toUpperAscii_61 : toUpperAscii 61 = 61 := by
  simp [toUpperAscii]

theorem toLowerByte_61 : toLowerByte 61 = 61 := by
  simp [toLowerByte]

theorem casefoldByte_false (c : Nat) : casefoldByte false c = c := by
  simp [casefoldByte]

theorem casefoldByte_true (c : Nat) : casefoldByte true c = toUpperAscii c := by
  simp [casefoldByte]

theorem toUpperAscii_toLowerByte_b32Char (i : Nat) (h : i < 32) :
    toUpperAscii (toLowerByte (b32Char i)) = b32Char i := by
  rcases b32Char_range i h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hl : 65 ≤ b32Char i ∧ b32Char i ≤ 90 := ⟨h1, h2⟩
    have hu : 97 ≤ b32Char i + 32 ∧ b32Char i + 32 ≤ 122 := by omega
    rw [toLowerByte, if_pos hl, toUpperAscii, if_pos hu]
    omega
  · have hl : ¬(65 ≤ b32Char i ∧ b32Char i ≤ 90) := by omega
    have hu : ¬(97 ≤ b32Char i ∧ b32Char i ≤ 122) := by omega
    rw [toLowerByte, if_neg hl, toUpperAscii, if_neg hu]

theorem toLowerByte_ne_61 (c : Nat) (h : c ≠ 61) : toLowerByte c ≠ 61 := by
  by_cases hc : 65 ≤ c ∧ c ≤ 90
  · rw [toLowerByte, if_pos hc]; omega
  · rw [toLowerByte, if_neg hc]; exact h

theorem toUpperAscii_ne_61 (c : Nat) (h : c ≠ 61) : toUpperAscii c ≠ 61 := by
  by_cases hc : 97 ≤ c ∧ c ≤ 122
  · rw [toUpperAscii, if_pos hc]; omega
  · rw [toUpperAscii, if_neg hc]; exact h

/-! ## Generic accumulator lemmas -/

theorem foldl_mul_pow (m a : Nat) : ∀ (l : List Nat),
    l.foldl (fun x y => x * m + y) a = a * m ^ l.length + l.foldl (fun x y => x * m + y) 0 := by
  intro l
  induction l generalizing a with
  | nil => simp
  | cons b rest ih =>
      simp only [List.foldl_cons, List.length_cons, pow_succ, zero_mul, zero_add]
      rw [ih (a * m + b), ih b]
      ring

theorem toValBE_cons (b : Nat) (bs : List Nat) :
    toValBE (b :: bs) = b * 256 ^ bs.length + toValBE bs := by
  simp only [toValBE, List.foldl_cons, zero_mul, zero_add]
  exact foldl_mul_pow 256 b bs

theorem toValBE_nil : toValBE [] = 0 := rfl

theorem toValBE_append (xs ys : List Nat) :
    toValBE (xs ++ ys) = toValBE xs * 256 ^ ys.length + toValBE ys := by
  simp only [toValBE, List.foldl_append]
  exact foldl_mul_pow 256 (xs.foldl (fun a b => a * 256 + b) 0) ys

theorem toValBE_replicate_zero (k : Nat) : toValBE (List.replicate k 0) = 0 := by
  induction k with
  | zero => simp [toValBE]
  | succ k ih => simp [List.replicate_succ, toValBE_cons, ih]

theorem toValBE_lt : ∀ (bs : List Nat), (∀ b ∈ bs, b < 256) → toValBE bs < 256 ^ bs.length := by
  intro bs
  induction bs with
  | nil => simp [toValBE]
  | cons b rest ih =>
      intro h
      have hb : b < 256 := h b (List.mem_cons.mpr (Or.inl rfl))
      have hr : toValBE rest < 256 ^ rest.length :=
        ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))
      have hp : 0 < 256 ^ rest.length := pow_pos (by norm_num : (0 : Nat) < 256) rest.length
      rw [toValBE_cons, List.length_cons, pow_succ']
      have : b + 1 ≤ 256 := by omega
      calc b * 256 ^ rest.length + toValBE rest
          < b * 256 ^ rest.length + 256 ^ rest.length := Nat.add_lt_add_left hr _
        _ = (b + 1) * 256 ^ rest.length := by ring
        _ ≤ 256 * 256 ^ rest.length := Nat.mul_le_mul_right _ this

theorem foldl32_cons (i : Nat) (is : List Nat) :
    foldl32 (i :: is) = i * 32 ^ is.length + foldl32 is := by
  simp only [foldl32, List.foldl_cons, zero_mul, zero_add]
  exact foldl_mul_pow 32 i is

theorem foldl32_nil : foldl32 [] = 0 := rfl

theorem foldl32_append (xs ys : List Nat) :
    foldl32 (xs ++ ys) = foldl32 xs * 32 ^ ys.length + foldl32 ys := by
  simp only [foldl32, List.foldl_append]
  exact foldl_mul_pow 32 (xs.foldl (fun a b => a * 32 + b) 0) ys

theorem foldl32_lt : ∀ (cs : List Nat), (∀ c ∈ cs, c < 32) → foldl32 cs < 32 ^ cs.length := by
  intro cs
  induction cs with
  | nil => simp [foldl32]
  | cons c rest ih =>
      intro h
      have hc : c < 32 := h c (List.mem_cons.mpr (Or.inl rfl))
      have hr : foldl32 rest < 32 ^ rest.length :=
        ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))
      rw [foldl32_cons, List.length_cons, pow_succ']
      have : c + 1 ≤ 32 := by omega
      calc c * 32 ^ rest.length + foldl32 rest
          < c * 32 ^ rest.length + 32 ^ rest.length := Nat.add_lt_add_left hr _
        _ = (c + 1) * 32 ^ rest.length := by ring
        _ ≤ 32 * 32 ^ rest.length := Nat.mul_le_mul_right _ this


/-! ## Small list helpers -/

theorem take_map (f : Nat → Nat) : ∀ (n : Nat) (l : List Nat),
    (l.map f).take n = (l.take n).map f := by
  intro n l
  induction l generalizing n with
  | nil => simp
  | cons a rest ih =>
      cases n with
      | zero => simp
      | succ n => simp only [List.map_cons, List.take_succ_cons, ih]

theorem flatten_map_singleton (f : Nat → Nat) : ∀ (l : List Nat),
    ((l.map (fun x => [f x])).flatten) = l.map f := by
  intro l
  induction l with
  | nil => simp
  | cons a rest ih => simp only [List.map_cons, List.flatten_cons, ih]; rfl

theorem pow32_eq (m : Nat) : (32 : Nat) ^ m = 2 ^ (5 * m) := by
  rw [show (32 : Nat) = 2 ^ 5 by norm_num, ← pow_mul]

theorem pow256_eq (m : Nat) : (256 : Nat) ^ m = 2 ^ (8 * m) := by
  rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_mul]

/-! ## Base-32 digit lemmas -/

@[simp] theorem digits32_zero (n : Nat) : digits32 n 0 = [] := rfl

@[simp] theorem digits32_succ (n k : Nat) :
    digits32 n (k + 1) = (n / 32 ^ k % 32) :: digits32 n k := rfl

theorem digits32_length (n k : Nat) : (digits32 n k).length = k := by
  induction k with
  | zero => simp
  | succ k ih => simp only [digits32_succ, List.length_cons, ih]

theorem digits32_lt (n : Nat) : ∀ (k d : Nat), d ∈ digits32 n k → d < 32 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      intro d hd
      simp only [digits32_succ, List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact Nat.mod_lt _ (by norm_num)
      · exact ih d hd

theorem mod_mul_thirtytwo (m t u : Nat) (hu : u < m) :
    (m * t + u) % (m * 32) = m * (t % 32) + u := by
  have h1 : m * (t % 32) + u < m * 32 := by
    have h2 : t % 32 < 32 := Nat.mod_lt t (by norm_num)
    nlinarith
  have h5 : m * t + u = (m * (t % 32) + u) + m * 32 * (t / 32) := by
    have h4 := Nat.div_add_mod t 32
    conv_lhs => rw [← h4]
    ring
  rw [h5, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1]

theorem foldl32_digits32 (n : Nat) : ∀ (k : Nat), foldl32 (digits32 n k) = n % 32 ^ k := by
  intro k
  induction k with
  | zero => simp [foldl32, Nat.mod_one]
  | succ k ih =>
      have hlt : n % 32 ^ k < 32 ^ k :=
        Nat.mod_lt n (pow_pos (by norm_num : (0 : Nat) < 32) k)
      have hsum : 32 ^ k * (n / 32 ^ k) + n % 32 ^ k = n := Nat.div_add_mod n (32 ^ k)
      have hkey := mod_mul_thirtytwo (32 ^ k) (n / 32 ^ k) (n % 32 ^ k) hlt
      rw [hsum] at hkey
      rw [Nat.mul_comm (32 ^ k) (n / 32 ^ k % 32)] at hkey
      rw [digits32_succ, foldl32_cons, digits32_length, ih]
      rw [show (32 : Nat) ^ (k + 1) = 32 ^ k * 32 by rw [pow_succ]]
      exact hkey.symm

theorem digits32_take (n : Nat) : ∀ (j k : Nat), j ≤ k →
    (digits32 n k).take j = digits32 (n / 32 ^ (k - j)) j := by
  intro j
  induction j with
  | zero => intro k hk; simp
  | succ j ih =>
      intro k hk
      obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      subst hk'
      have hj : j ≤ k' := by omega
      have hsub : k' + 1 - (j + 1) = k' - j := by omega
      have hdiv : n / 32 ^ (k' - j) / 32 ^ j = n / 32 ^ k' := by
        rw [Nat.div_div_eq_div_mul, ← pow_add, show k' - j + j = k' by omega]
      simp only [digits32_succ, List.take_succ_cons]
      rw [ih k' hj, hsub, hdiv]

theorem encIndices_eq (val : Nat) : encIndices val = digits32 val 8 := by
  simp [encIndices, digits32]

theorem encIndices_length (val : Nat) : (encIndices val).length = 8 := by
  rw [encIndices_eq, digits32_length]

theorem encIndices_lt (val : Nat) : ∀ d ∈ encIndices val, d < 32 :=
  fun d hd => digits32_lt val 8 d (by rw [encIndices_eq] at hd; exact hd)

theorem foldl32_encIndices (val : Nat) : foldl32 (encIndices val) = val % 2 ^ 40 := by
  rw [encIndices_eq, foldl32_digits32]
  congr 1

theorem encIndices_take (val j : Nat) (hj : j ≤ 8) :
    (encIndices val).take j = digits32 (val / 32 ^ (8 - j)) j := by
  rw [encIndices_eq, digits32_take val j 8 hj]

/-! ## Division helpers -/

theorem div_pow_add (a b k j : Nat) (hb : b < 2 ^ k) :
    (a * 2 ^ k + b) / 2 ^ (k + j) = a / 2 ^ j := by
  have h2 : a % 2 ^ j < 2 ^ j := Nat.mod_lt a (pow_pos (by norm_num : (0 : Nat) < 2) j)
  have h4 : 2 ^ (k + j) = 2 ^ j * 2 ^ k := by rw [pow_add, Nat.mul_comm]
  have h3 : a % 2 ^ j * 2 ^ k + b < 2 ^ (k + j) := by
    have h5 : a % 2 ^ j + 1 ≤ 2 ^ j := by omega
    have h6 : a % 2 ^ j * 2 ^ k + b < a % 2 ^ j * 2 ^ k + 2 ^ k := Nat.add_lt_add_left hb _
    have h7 : a % 2 ^ j * 2 ^ k + 2 ^ k = (a % 2 ^ j + 1) * 2 ^ k := by ring
    have h8 : (a % 2 ^ j + 1) * 2 ^ k ≤ 2 ^ j * 2 ^ k := Nat.mul_le_mul_right _ h5
    rw [h7] at h6
    have h9 : a % 2 ^ j * 2 ^ k + b < 2 ^ j * 2 ^ k := Nat.lt_of_lt_of_le h6 h8
    rw [← h4] at h9
    exact h9
  have hkey : a * 2 ^ k + b = (a % 2 ^ j * 2 ^ k + b) + 2 ^ (k + j) * (a / 2 ^ j) := by
    calc a * 2 ^ k + b
        = (2 ^ j * (a / 2 ^ j) + a % 2 ^ j) * 2 ^ k + b := by
          rw [Nat.div_add_mod a (2 ^ j)]
      _ = (a % 2 ^ j * 2 ^ k + b) + 2 ^ (k + j) * (a / 2 ^ j) := by rw [pow_add]; ring
  rw [hkey, Nat.add_mul_div_left _ _ (pow_pos (by norm_num : (0 : Nat) < 2) (k + j)),
    Nat.div_eq_of_lt h3, zero_add]

theorem div_mul_pow_mod (Wx Vy B B'' : Nat) (h : B'' + 8 ≤ B) :
    (Wx * 2 ^ B + Vy) / 2 ^ B'' % 256 = Vy / 2 ^ B'' % 256 := by
  have hle : B'' ≤ B := by omega
  have hpow : 2 ^ B = 2 ^ B'' * 2 ^ (B - B'') := by
    rw [← pow_add, Nat.add_sub_cancel' hle]
  have hpow2 : 2 ^ (B - B'') = 256 * 2 ^ (B - B'' - 8) := by
    have hsub : 8 + (B - B'' - 8) = B - B'' := by omega
    rw [show (2 : Nat) ^ (B - B'') = 2 ^ (8 + (B - B'' - 8)) by rw [hsub], pow_add]
    norm_num
  have hkey : Wx * (2 ^ B'' * (256 * 2 ^ (B - B'' - 8))) + Vy
      = Vy + 2 ^ B'' * (Wx * (256 * 2 ^ (B - B'' - 8))) := by ring
  have hkey2 : Vy / 2 ^ B'' + Wx * (256 * 2 ^ (B - B'' - 8))
      = Vy / 2 ^ B'' + 256 * (Wx * 2 ^ (B - B'' - 8)) := by ring
  rw [hpow, hpow2, hkey,
    Nat.add_mul_div_left _ _ (pow_pos (by norm_num : (0 : Nat) < 2) B''), hkey2,
    Nat.add_mul_mod_self_left]

theorem div_mul_pow (a c k B : Nat) (hc : c < 2 ^ B) :
    (a * 2 ^ B + c) / (2 ^ k * 2 ^ B) = a / 2 ^ k := by
  have h3 : a % 2 ^ k * 2 ^ B + c < 2 ^ k * 2 ^ B := by
    have h2 : a % 2 ^ k < 2 ^ k := Nat.mod_lt a (pow_pos (by norm_num : (0 : Nat) < 2) k)
    have h5 : a % 2 ^ k + 1 ≤ 2 ^ k := by omega
    have h6 : a % 2 ^ k * 2 ^ B + c < a % 2 ^ k * 2 ^ B + 2 ^ B := Nat.add_lt_add_left hc _
    have h7 : a % 2 ^ k * 2 ^ B + 2 ^ B = (a % 2 ^ k + 1) * 2 ^ B := by ring
    have h8 : (a % 2 ^ k + 1) * 2 ^ B ≤ 2 ^ k * 2 ^ B := Nat.mul_le_mul_right _ h5
    rw [h7] at h6
    exact Nat.lt_of_lt_of_le h6 h8
  have hkey : a * 2 ^ B + c = (a % 2 ^ k * 2 ^ B + c) + (2 ^ k * 2 ^ B) * (a / 2 ^ k) := by
    calc a * 2 ^ B + c
        = (2 ^ k * (a / 2 ^ k) + a % 2 ^ k) * 2 ^ B + c := by
          rw [Nat.div_add_mod a (2 ^ k)]
      _ = (a % 2 ^ k * 2 ^ B + c) + (2 ^ k * 2 ^ B) * (a / 2 ^ k) := by ring
  rw [hkey,
    Nat.add_mul_div_left _ _ (Nat.mul_pos (pow_pos (by norm_num : (0 : Nat) < 2) k)
      (pow_pos (by norm_num : (0 : Nat) < 2) B)),
    Nat.div_eq_of_lt h3, zero_add]

/-! ## `bytesOf`: big-endian byte expansion of the top `B` bits -/

theorem bytesOf_add8 (W k : Nat) :
    bytesOf W (k + 8) = (W / 2 ^ k) % 256 :: bytesOf W k := rfl

theorem bytesOf_zero (W : Nat) : bytesOf W 0 = [] := rfl

theorem bytesOf_lt (W B : Nat) (h : B < 8) : bytesOf W B = [] := by
  have h2 : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 ∨ B = 5 ∨ B = 6 ∨ B = 7 := by omega
  rcases h2 with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> exact rfl

theorem bytesOf_ge (W B : Nat) (h : 8 ≤ B) :
    bytesOf W B = (W / 2 ^ (B - 8)) % 256 :: bytesOf W (B - 8) := by
  have h2 : B = (B - 8) + 8 := by omega
  conv_lhs => rw [h2]
  rw [bytesOf_add8]

theorem bytesOf_shift (Vy : Nat) : ∀ (B B' Wx : Nat), B' ≤ B →
    bytesOf (Wx * 2 ^ B + Vy) B' = bytesOf Vy B' := by
  intro B
  induction B with
  | zero =>
      intro B' Wx hle
      have h0 : B' = 0 := by omega
      subst h0
      rw [bytesOf_zero, bytesOf_zero]
  | succ B1 ih =>
      intro B' Wx hle
      by_cases h8 : B' < 8
      · rw [bytesOf_lt _ _ h8, bytesOf_lt _ _ h8]
      · have hB' : B' - 8 ≤ B1 := by omega
        have hw : Wx * 2 ^ (B1 + 1) + Vy = (Wx * 2) * 2 ^ B1 + Vy := by
          rw [pow_succ]; ring
        have h1 := ih (B' - 8) (Wx * 2) hB'
        rw [← hw] at h1
        rw [bytesOf_ge (Wx * 2 ^ (B1 + 1) + Vy) B' (by omega)]
        rw [bytesOf_ge Vy B' (by omega)]
        rw [h1, div_mul_pow_mod Wx Vy (B1 + 1) (B' - 8) (by omega)]

theorem bytesOf_add (Wx Vy A B : Nat) (hA : 8 ∣ A) (hVy : Vy < 2 ^ B) :
    bytesOf (Wx * 2 ^ B + Vy) (A + B) = bytesOf Wx A ++ bytesOf Vy B := by
  obtain ⟨k, rfl⟩ : ∃ k, A = 8 * k := hA
  induction k generalizing Wx Vy B with
  | zero =>
      simp only [Nat.mul_zero, zero_add, bytesOf_zero, List.nil_append]
      exact bytesOf_shift Vy B B Wx (le_refl B)
  | succ k ih =>
      have hhead : ((Wx * 2 ^ B + Vy) / 2 ^ (8 * k + B)) % 256
          = (Wx / 2 ^ (8 * k)) % 256 := by
        have hp : 2 ^ (8 * k + B) = 2 ^ (8 * k) * 2 ^ B := by rw [pow_add]
        rw [hp, div_mul_pow Wx Vy (8 * k) B hVy]
      have htail := ih Wx Vy B hVy
      have hA : 8 * (k + 1) + B = (8 * k + B) + 8 := by ring
      have hA2 : 8 * (k + 1) = 8 * k + 8 := by ring
      rw [hA, bytesOf_add8, hA2, bytesOf_add8, hhead, htail, List.cons_append]


/-! ## The bit-accumulator loop of `b32decode` -/

theorem bitsToBytes_nil (val bits : Nat) : bitsToBytes val bits [] = [] := rfl

theorem bitsToBytes_eq_bytesOf : ∀ (cs : List Nat), ∀ (val bits : Nat), bits < 8 →
    (∀ c ∈ cs, c < 32) →
    bitsToBytes val bits cs
      = bytesOf (val * 32 ^ cs.length + foldl32 cs) (bits + 5 * cs.length) := by
  intro cs
  induction cs with
  | nil =>
      intro val bits hb hc
      simp only [List.length_nil, pow_zero, Nat.mul_one, foldl32_nil, Nat.add_zero,
        Nat.mul_zero, bitsToBytes, bytesOf_lt val bits hb]
  | cons i rest ih =>
      intro val bits hb hc
      have hi : i < 32 := hc i (List.mem_cons.mpr (Or.inl rfl))
      have hr : ∀ c ∈ rest, c < 32 := fun c hcx => hc c (List.mem_cons.mpr (Or.inr hcx))
      have hrest : foldl32 rest < 2 ^ (5 * rest.length) := by
        rw [← pow32_eq rest.length]; exact foldl32_lt rest hr
      have hW : val * 32 ^ (rest.length + 1) + (i * 32 ^ rest.length + foldl32 rest)
          = (val * 32 + i) * 32 ^ rest.length + foldl32 rest := by
        rw [pow_succ]; ring
      simp only [bitsToBytes, List.length_cons, foldl32_cons, hW]
      by_cases h8 : bits + 5 ≥ 8
      · simp only [if_pos h8]
        rw [ih (val * 32 + i) (bits + 5 - 8) (by omega) hr]
        have hB : bits + 5 * (rest.length + 1)
            = (bits + 5 - 8 + 5 * rest.length) + 8 := by omega
        rw [hB, bytesOf_add8]
        have hdiv : ((val * 32 + i) * 32 ^ rest.length + foldl32 rest)
              / 2 ^ (bits + 5 - 8 + 5 * rest.length)
            = (val * 32 + i) / 2 ^ (bits + 5 - 8) := by
          rw [pow32_eq rest.length,
            show bits + 5 - 8 + 5 * rest.length = 5 * rest.length + (bits + 5 - 8) by omega]
          exact div_pow_add (val * 32 + i) (foldl32 rest) (5 * rest.length)
            (bits + 5 - 8) hrest
        rw [hdiv]
      · simp only [if_neg h8]
        have hB : bits + 5 * (rest.length + 1) = bits + 5 + 5 * rest.length := by ring
        rw [ih (val * 32 + i) (bits + 5) (by omega) hr, hB]

theorem bitsToBytes_append (v : Nat) (xs ys : List Nat) (h8 : 8 ∣ xs.length)
    (hxs : ∀ c ∈ xs, c < 32) (hys : ∀ c ∈ ys, c < 32) :
    bitsToBytes v 0 (xs ++ ys) = bitsToBytes v 0 xs ++ bitsToBytes 0 0 ys := by
  have hxy : ∀ c ∈ xs ++ ys, c < 32 := by
    intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact hxs c h
    · exact hys c h
  have e1 := bitsToBytes_eq_bytesOf xs v 0 (by omega) hxs
  have e2 := bitsToBytes_eq_bytesOf ys 0 0 (by omega) hys
  have e3 := bitsToBytes_eq_bytesOf (xs ++ ys) v 0 (by omega) hxy
  rw [e1, e2, e3]
  simp only [zero_add, Nat.zero_mul, List.length_append, foldl32_append]
  have hW : v * 32 ^ (xs.length + ys.length)
      + (foldl32 xs * 32 ^ ys.length + foldl32 ys)
      = (v * 32 ^ xs.length + foldl32 xs) * 32 ^ ys.length + foldl32 ys := by
    rw [pow_add]; ring
  have hB : 5 * (xs.length + ys.length) = 5 * xs.length + 5 * ys.length := by ring
  have h32 : (32 : Nat) ^ ys.length = 2 ^ (5 * ys.length) := pow32_eq ys.length
  have hVy : foldl32 ys < 2 ^ (5 * ys.length) := by
    rw [← h32]; exact foldl32_lt ys hys
  have hA : 8 ∣ 5 * xs.length := by
    obtain ⟨k, hk⟩ := h8
    exact ⟨5 * k, by rw [hk]; ring⟩
  rw [hW, hB, h32]
  exact bytesOf_add _ _ _ _ hA hVy

/-! ## Chunking lemmas -/

theorem chunksOf5_nil : chunksOf5 [] = ([] : List (List Nat)) := rfl
theorem chunksOf5_one (a : Nat) : chunksOf5 [a] = [[a]] := rfl
theorem chunksOf5_two (a b : Nat) : chunksOf5 [a, b] = [[a, b]] := rfl
theorem chunksOf5_three (a b c : Nat) : chunksOf5 [a, b, c] = [[a, b, c]] := rfl
theorem chunksOf5_four (a b c d : Nat) : chunksOf5 [a, b, c, d] = [[a, b, c, d]] := rfl
theorem chunksOf5_five (a b c d e : Nat) (rest : List Nat) :
    chunksOf5 (a :: b :: c :: d :: e :: rest) = [a, b, c, d, e] :: chunksOf5 rest := rfl

/-- Six-way induction principle matching the equations of `chunksOf5`. -/
theorem chunksInduction {motive : List Nat → Prop}
    (c0 : motive [])
    (c1 : ∀ a, motive [a])
    (c2 : ∀ a b, motive [a, b])
    (c3 : ∀ a b c, motive [a, b, c])
    (c4 : ∀ a b c d, motive [a, b, c, d])
    (c5 : ∀ a b c d e rest, motive rest → motive (a :: b :: c :: d :: e :: rest)) :
    ∀ l, motive l := by
  have key : ∀ (n : Nat) (l : List Nat), l.length ≤ n → motive l := by
    intro n
    induction n with
    | zero =>
        intro l hl
        cases l with
        | nil => exact c0
        | cons a rest =>
            simp only [List.length_cons] at hl
            omega
    | succ n ih =>
        intro l hl
        cases l with
        | nil => exact c0
        | cons a l1 =>
            cases l1 with
            | nil => exact c1 a
            | cons b l2 =>
                cases l2 with
                | nil => exact c2 a b
                | cons c l3 =>
                    cases l3 with
                    | nil => exact c3 a b c
                    | cons d l4 =>
                        cases l4 with
                        | nil => exact c4 a b c d
                        | cons e rest =>
                            exact c5 a b c d e rest
                              (ih rest (by simp only [List.length_cons] at hl; omega))
  intro l
  exact key l.length l (Nat.le_refl _)

theorem chunksOf5_length_le : ∀ (s : List Nat), ∀ c ∈ chunksOf5 s, c.length ≤ 5 := by
  intro s
  induction s using chunksInduction with
  | c0 => simp [chunksOf5_nil]
  | c1 a => simp [chunksOf5_one]
  | c2 a b => simp [chunksOf5_two]
  | c3 a b c => simp [chunksOf5_three]
  | c4 a b c d => simp [chunksOf5_four]
  | c5 a b c d e rest ih =>
      simp only [chunksOf5_five, List.mem_cons]
      intro x hx
      rcases hx with rfl | hx
      · rfl
      · exact ih x hx

theorem chunksOf5_flatten : ∀ (s : List Nat), (chunksOf5 s).flatten = s := by
  intro s
  induction s using chunksInduction with
  | c0 => simp [chunksOf5_nil]
  | c1 a => simp [chunksOf5_one]
  | c2 a b => simp [chunksOf5_two]
  | c3 a b c => simp [chunksOf5_three]
  | c4 a b c d => simp [chunksOf5_four]
  | c5 a b c d e rest ih => simp [chunksOf5_five, ih]

theorem chunksOf5_length : ∀ (s : List Nat), (chunksOf5 s).length = (s.length + 4) / 5 := by
  intro s
  induction s using chunksInduction with
  | c0 => simp [chunksOf5_nil]
  | c1 a => simp [chunksOf5_one]
  | c2 a b => simp [chunksOf5_two]
  | c3 a b c => simp [chunksOf5_three]
  | c4 a b c d => simp [chunksOf5_four]
  | c5 a b c d e rest ih =>
      simp only [chunksOf5_five, List.length_cons]
      omega

theorem chunksOf5_structure : ∀ (s : List Nat),
    (chunksOf5 s = [] ∧ s = []) ∨
    (∃ cs last, chunksOf5 s = cs ++ [last] ∧ (∀ c ∈ cs, c.length = 5)
      ∧ 1 ≤ last.length ∧ last.length ≤ 5) := by
  intro s
  induction s using chunksInduction with
  | c0 => exact Or.inl ⟨rfl, rfl⟩
  | c1 a =>
      exact Or.inr ⟨[], [a], by simp [chunksOf5_one], by simp, by simp, by simp⟩
  | c2 a b =>
      exact Or.inr ⟨[], [a, b], by simp [chunksOf5_two], by simp, by simp, by simp⟩
  | c3 a b c =>
      exact Or.inr ⟨[], [a, b, c], by simp [chunksOf5_three], by simp, by simp, by simp⟩
  | c4 a b c d =>
      exact Or.inr ⟨[], [a, b, c, d], by simp [chunksOf5_four], by simp, by simp, by simp⟩
  | c5 a b c d e rest ih =>
      rcases ih with ⟨h1, h2⟩ | ⟨cs, last, hcs, hfull, hlen1, hlen2⟩
      · subst h2
        have hh : chunksOf5 (a :: b :: c :: d :: e :: []) = [] ++ [[a, b, c, d, e]] := by
          simp [chunksOf5_five, chunksOf5_nil]
        exact Or.inr ⟨[], [a, b, c, d, e], hh, by simp, by simp, by simp⟩
      · have hh : chunksOf5 (a :: b :: c :: d :: e :: rest)
            = ([[a, b, c, d, e]] ++ cs) ++ [last] := by
          simp [chunksOf5_five, hcs]
        have h2 : ∀ x ∈ [[a, b, c, d, e]] ++ cs, x.length = 5 := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · have hx' : x = [a, b, c, d, e] := by simpa using hx
            simp [hx']
          · exact hfull x hx
        exact Or.inr ⟨[[a, b, c, d, e]] ++ cs, last, hh, h2, hlen1, hlen2⟩

/-! ## `lstripEq` / `rstripEq` -/

@[simp] theorem lstripEq_nil : lstripEq [] = [] := rfl

@[simp] theorem lstripEq_cons (c : Nat) (cs : List Nat) :
    lstripEq (c :: cs) = if c = 61 then lstripEq cs else c :: cs := rfl

theorem lstripEq_no61 : ∀ (xs : List Nat), (∀ x ∈ xs, x ≠ 61) → lstripEq xs = xs := by
  intro xs
  induction xs with
  | nil => simp
  | cons x rest ih =>
      intro h
      have hx : x ≠ 61 := h x (List.mem_cons.mpr (Or.inl rfl))
      have hr : ∀ y ∈ rest, y ≠ 61 := fun y hy => h y (List.mem_cons.mpr (Or.inr hy))
      simp [hx, ih hr]

theorem lstripEq_append (a b : List Nat) (hb : ∀ x ∈ b, x ≠ 61) :
    lstripEq (a ++ b) = lstripEq a ++ b := by
  induction a generalizing b with
  | nil => simp [lstripEq_no61 b hb]
  | cons x rest ih =>
      by_cases hx : x = 61
      · subst hx
        simp [ih b hb]
      · simp [hx, ih b hb]

theorem lstripEq_replicate (p : Nat) (xs : List Nat) :
    lstripEq (List.replicate p 61 ++ xs) = lstripEq xs := by
  induction p with
  | zero => simp
  | succ p ih => simp [List.replicate_succ, ih]

theorem rstripEq_append_replicate (xs : List Nat) (hx : ∀ x ∈ xs, x ≠ 61) (p : Nat) :
    rstripEq (xs ++ List.replicate p 61) = xs := by
  have h1 : (xs ++ List.replicate p 61).reverse
      = List.replicate p 61 ++ xs.reverse := by
    rw [List.reverse_append, List.reverse_replicate]
  have h2 : lstripEq xs.reverse = xs.reverse :=
    lstripEq_no61 xs.reverse (fun x hx' h => hx x (List.mem_reverse.mp hx') h)
  simp only [rstripEq, h1, lstripEq_replicate, h2, List.reverse_reverse]

theorem rstripEq_append (xs ys : List Nat) (hx : ∀ x ∈ xs, x ≠ 61) :
    rstripEq (xs ++ ys) = xs ++ rstripEq ys := by
  have h1 : (xs ++ ys).reverse = ys.reverse ++ xs.reverse := List.reverse_append
  have h2 : lstripEq (ys.reverse ++ xs.reverse) = lstripEq ys.reverse ++ xs.reverse :=
    lstripEq_append ys.reverse xs.reverse (fun x hx' h => hx x (List.mem_reverse.mp hx') h)
  simp only [rstripEq, h1, h2, List.reverse_append, List.reverse_reverse]

theorem rstripEq_no61 (xs : List Nat) (hx : ∀ x ∈ xs, x ≠ 61) : rstripEq xs = xs := by
  have := rstripEq_append_replicate xs hx 0
  simpa using this


/-! ## `toIndices` -/

theorem mem_take_imp : ∀ (l : List Nat) (n d : Nat), d ∈ l.take n → d ∈ l := by
  intro l
  induction l with
  | nil => intro n d hd; simp at hd
  | cons a rest ih =>
      intro n d hd
      cases n with
      | zero => simp at hd
      | succ n =>
          simp only [List.take_succ_cons, List.mem_cons] at hd
          rcases hd with h | hd
          · rw [← h]; simp
          · exact List.mem_cons_of_mem a (ih n d hd)

theorem toIndices_map_b32Char : ∀ (cs : List Nat), (∀ c ∈ cs, c < 32) →
    toIndices (cs.map b32Char) = some cs := by
  intro cs
  induction cs with
  | nil => simp [toIndices]
  | cons c rest ih =>
      intro h
      have hc : c < 32 := h c (List.mem_cons.mpr (Or.inl rfl))
      have hr : ∀ x ∈ rest, x < 32 := fun x hx => h x (List.mem_cons.mpr (Or.inr hx))
      have h1 : b32IndexOf (b32Char c) = some c := b32IndexOf_b32Char c hc
      have h2 : toIndices (rest.map b32Char) = some rest := ih hr
      simp only [List.map_cons, toIndices, h1, h2]
      rfl

theorem toIndices_cons_some (x i : Nat) (hidx : b32IndexOf x = some i) (rest : List Nat) :
    toIndices (x :: rest) = (toIndices rest).map (i :: ·) := by
  simp [toIndices, hidx]

theorem toIndices_append : ∀ (xs is : List Nat), toIndices xs = some is →
    ∀ (ys js : List Nat), toIndices ys = some js → toIndices (xs ++ ys) = some (is ++ js) := by
  intro xs
  induction xs with
  | nil =>
      intro is hi ys js hj
      have h0 : toIndices [] = some [] := rfl
      have his : is = [] := by
        rw [h0] at hi
        exact (Option.some.inj hi).symm
      subst his
      simp [hj]
  | cons x rest ih =>
      intro is hi ys js hj
      cases hidx : b32IndexOf x with
      | none =>
          have hnn : toIndices (x :: rest) = none := by simp [toIndices, hidx]
          rw [hnn] at hi
          exact Option.noConfusion hi
      | some i =>
          have hcons : toIndices (x :: rest) = (toIndices rest).map (i :: ·) :=
            toIndices_cons_some x i hidx rest
          rw [hcons] at hi
          rw [Option.map_eq_some_iff] at hi
          obtain ⟨rest', hrest, his⟩ := hi
          have hgoal : toIndices (x :: rest ++ ys) = (toIndices (rest ++ ys)).map (i :: ·) :=
            toIndices_cons_some x i hidx (rest ++ ys)
          rw [hgoal, ih rest' hrest ys js hj]
          simp only [Option.map, ← his]
          rfl

theorem toIndices_none : ∀ (cs : List Nat),
    toIndices cs = none ↔ ∃ c ∈ cs, b32IndexOf c = none := by
  intro cs
  induction cs with
  | nil => simp [toIndices]
  | cons c rest ih =>
      cases hidx : b32IndexOf c with
      | none =>
          constructor
          · intro _; exact ⟨c, by simp, hidx⟩
          · intro _; simp [toIndices, hidx]
      | some i =>
          have hcons : toIndices (c :: rest) = (toIndices rest).map (i :: ·) :=
            toIndices_cons_some c i hidx rest
          constructor
          · intro h
            rw [hcons, Option.map_eq_none_iff] at h
            rw [ih] at h
            obtain ⟨d, hd, hd2⟩ := h
            exact ⟨d, List.mem_cons_of_mem c hd, hd2⟩
          · intro h
            obtain ⟨d, hd, hd2⟩ := h
            rw [List.mem_cons] at hd
            rcases hd with hce | hd
            · have hnn : b32IndexOf c = none := by rw [← hce]; exact hd2
              rw [hidx] at hnn; exact Option.noConfusion hnn
            · rw [hcons, Option.map_eq_none_iff, ih]
              exact ⟨d, hd, hd2⟩


/-! ## Chunk-level encoding lemmas -/

theorem padCount_five : padCount 5 = 0 := by simp [padCount]

theorem padCount_le (n : Nat) (h : n ≤ 5) : padCount n ≤ 8 := by
  have h2 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
  rcases h2 with (rfl|rfl|rfl|rfl|rfl|rfl) <;> simp [padCount]

theorem padCount_facts (r : Nat) (h1 : 1 ≤ r) (h2 : r ≤ 5) :
    5 * padCount r ≤ 8 * (5 - r) ∧ 8 * (5 - r) - 5 * padCount r < 8 ∧
    5 * (8 - padCount r) = 8 * r + (8 * (5 - r) - 5 * padCount r) ∧ padCount r ≤ 8 := by
  have h3 : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 := by omega
  rcases h3 with (rfl|rfl|rfl|rfl|rfl) <;> simp [padCount]

theorem padTo5_length (bs : List Nat) (h : bs.length ≤ 5) : (padTo5 bs).length = 5 := by
  simp [padTo5, h]

theorem chunkVal_eq (bs : List Nat) (h : bs.length ≤ 5) :
    chunkVal bs = toValBE bs * 2 ^ (8 * (5 - bs.length)) := by
  have h1 : (List.replicate (5 - bs.length) 0).length = 5 - bs.length := by simp
  simp only [chunkVal, padTo5, toValBE_append, h1, toValBE_replicate_zero, add_zero, pow256_eq]

theorem chunkVal_lt (bs : List Nat) (h : bs.length ≤ 5) (hb : ∀ b ∈ bs, b < 256) :
    chunkVal bs < 2 ^ 40 := by
  rw [chunkVal_eq bs h]
  have h1 : toValBE bs < 256 ^ bs.length := toValBE_lt bs hb
  rw [pow256_eq] at h1
  have h2 : 8 * bs.length + 8 * (5 - bs.length) = 40 := by omega
  have h3 : toValBE bs * 2 ^ (8 * (5 - bs.length))
      < 2 ^ (8 * bs.length) * 2 ^ (8 * (5 - bs.length)) :=
    Nat.mul_lt_mul_of_pos_right h1 (pow_pos (by norm_num : (0 : Nat) < 2) _)
  rw [← pow_add, h2] at h3
  exact h3

theorem mul_pow_div_pow (a m k : Nat) (h : k ≤ m) : (a * 2 ^ m) / 2 ^ k = a * 2 ^ (m - k) := by
  have h1 : a * 2 ^ m = (a * 2 ^ (m - k)) * 2 ^ k := by
    have h2 : 2 ^ m = 2 ^ (m - k) * 2 ^ k := by
      rw [← pow_add, show (m - k) + k = m by omega]
    rw [h2]
    ring
  exact Nat.div_eq_of_eq_mul_left (pow_pos (by norm_num : (0 : Nat) < 2) k) h1

theorem bytesOf_mul_pow (W d : Nat) (hd : d < 8) : ∀ (r : Nat),
    bytesOf (W * 2 ^ d) (8 * r + d) = bytesOf W (8 * r) := by
  intro r
  induction r with
  | zero =>
      simp only [Nat.mul_zero, zero_add]
      rw [bytesOf_lt _ _ hd, bytesOf_zero]
  | succ r ih =>
      have h1 : 8 * (r + 1) + d = (8 * r + d) + 8 := by ring
      have h2 : 8 * (r + 1) = 8 * r + 8 := by ring
      have hdiv : (W * 2 ^ d) / 2 ^ (8 * r + d) = W / 2 ^ (8 * r) := by
        have hz : W * 2 ^ d = W * 2 ^ d + 0 := by ring
        have hp : 2 ^ (8 * r + d) = 2 ^ (8 * r) * 2 ^ d := by rw [pow_add]
        rw [hz, hp, div_mul_pow W 0 (8 * r) d
          (pow_pos (by norm_num : (0 : Nat) < 2) d)]
      rw [h1, bytesOf_add8, h2, bytesOf_add8, hdiv, ih]

theorem bytesOf_toValBE : ∀ (bs : List Nat), (∀ b ∈ bs, b < 256) →
    bytesOf (toValBE bs) (8 * bs.length) = bs := by
  intro bs
  induction bs with
  | nil => intro h; simp [bytesOf_zero, toValBE]
  | cons b rest ih =>
      intro h
      have hb : b < 256 := h b (List.mem_cons.mpr (Or.inl rfl))
      have hr : ∀ x ∈ rest, x < 256 := fun x hx => h x (List.mem_cons.mpr (Or.inr hx))
      have hT : toValBE rest < 2 ^ (8 * rest.length) := by
        have hz := toValBE_lt rest hr
        rw [pow256_eq] at hz
        exact hz
      have hlen : 8 * (rest.length + 1) = 8 * rest.length + 8 := by ring
      have hcons : toValBE (b :: rest) = b * 2 ^ (8 * rest.length) + toValBE rest := by
        rw [toValBE_cons, pow256_eq]
      have hdiv : (b * 2 ^ (8 * rest.length) + toValBE rest) / 2 ^ (8 * rest.length) = b := by
        have hkey : b * 2 ^ (8 * rest.length) + toValBE rest
            = toValBE rest + 2 ^ (8 * rest.length) * b := by ring
        rw [hkey, Nat.add_mul_div_left _ _ (pow_pos (by norm_num : (0 : Nat) < 2) _),
          Nat.div_eq_of_lt hT, zero_add]
      rw [List.length_cons, hlen, bytesOf_add8, hcons, hdiv, Nat.mod_eq_of_lt hb,
        bytesOf_shift (toValBE rest) (8 * rest.length) (8 * rest.length) b (le_refl _),
        ih hr]

theorem sigIndices_eq (bs : List Nat) :
    sigIndices bs = (encIndices (chunkVal bs)).take (8 - padCount bs.length) := rfl

theorem sigIndices_lt (bs : List Nat) : ∀ d ∈ sigIndices bs, d < 32 := by
  intro d hd
  rw [sigIndices_eq] at hd
  exact encIndices_lt _ d (mem_take_imp _ _ _ hd)

theorem sigIndices_length (bs : List Nat) (h : bs.length ≤ 5) :
    (sigIndices bs).length = 8 - padCount bs.length := by
  have hp : padCount bs.length ≤ 8 := padCount_le bs.length h
  simp [sigIndices_eq, List.length_take, encIndices_length, hp]

theorem sigIndices_length_full (bs : List Nat) (h : bs.length = 5) :
    (sigIndices bs).length = 8 := by
  have hp : padCount bs.length = 0 := by rw [h]; exact padCount_five
  rw [sigIndices_length bs (by omega), hp]

theorem sigChunk_eq (bs : List Nat) : sigChunk bs = (sigIndices bs).map b32Char := rfl

theorem sigChunk_ne_61 (bs : List Nat) : ∀ c ∈ sigChunk bs, c ≠ 61 := by
  intro c hc
  rw [sigChunk_eq, List.mem_map] at hc
  obtain ⟨d, hd, rfl⟩ := hc
  exact b32Char_ne_61 d (sigIndices_lt bs d hd)

theorem toIndices_sigChunk (bs : List Nat) :
    toIndices (sigChunk bs) = some (sigIndices bs) :=
  toIndices_map_b32Char (sigIndices bs) (sigIndices_lt bs)

theorem encChunk_eq (bs : List Nat) :
    encChunk bs = sigChunk bs ++ List.replicate (padCount bs.length) 61 := rfl

theorem encChunk_full (bs : List Nat) (h : bs.length = 5) : encChunk bs = sigChunk bs := by
  have hp : padCount bs.length = 0 := by rw [h]; exact padCount_five
  simp [encChunk_eq, hp]

theorem encChunk_length (bs : List Nat) (h : bs.length ≤ 5) : (encChunk bs).length = 8 := by
  have hp : padCount bs.length ≤ 8 := padCount_le bs.length h
  simp [encChunk_eq, sigChunk_eq, sigIndices_length bs h, hp]

theorem mem_encChunk (bs : List Nat) : ∀ c ∈ encChunk bs,
    c = 61 ∨ ∃ i, i < 32 ∧ c = b32Char i := by
  intro c hc
  rw [encChunk_eq, List.mem_append] at hc
  rcases hc with hc | hc
  · rw [sigChunk_eq, List.mem_map] at hc
    obtain ⟨d, hd, rfl⟩ := hc
    exact Or.inr ⟨d, sigIndices_lt bs d hd, rfl⟩
  · rw [List.mem_replicate] at hc
    obtain ⟨-, h⟩ := hc
    exact Or.inl h

theorem mem_b32encode (s : List Nat) : ∀ c ∈ b32encode s,
    c = 61 ∨ ∃ i, i < 32 ∧ c = b32Char i := by
  intro c hc
  rw [b32encode, List.mem_flatten] at hc
  obtain ⟨l, hl, hc2⟩ := hc
  rw [List.mem_map] at hl
  obtain ⟨bs, hbs, rfl⟩ := hl
  exact mem_encChunk bs c hc2

theorem bitsToBytes_sigIndices (bs : List Nat) (h1 : 1 ≤ bs.length) (h2 : bs.length ≤ 5)
    (hb : ∀ b ∈ bs, b < 256) :
    bitsToBytes 0 0 (sigIndices bs) = bs := by
  obtain ⟨hp1, hp2, hp3, hp4⟩ := padCount_facts bs.length h1 h2
  have hV : chunkVal bs < 2 ^ 40 := chunkVal_lt bs h2 hb
  have hVeq : chunkVal bs = toValBE bs * 2 ^ (8 * (5 - bs.length)) := chunkVal_eq bs h2
  have hm : 8 - padCount bs.length ≤ 8 := by omega
  have hsub : 8 - (8 - padCount bs.length) = padCount bs.length := by omega
  have hstep1 : sigIndices bs
      = digits32 (chunkVal bs / 32 ^ padCount bs.length) (8 - padCount bs.length) := by
    rw [sigIndices_eq, encIndices_take _ _ hm, hsub]
  have hdiv : chunkVal bs / 32 ^ padCount bs.length
      = toValBE bs * 2 ^ (8 * (5 - bs.length) - 5 * padCount bs.length) := by
    rw [hVeq, pow32_eq (padCount bs.length), mul_pow_div_pow _ _ _ hp1]
  rw [hstep1, hdiv]
  have h40 : (2 : Nat) ^ 40 = 32 ^ 8 := by norm_num
  have hV2 : chunkVal bs < 32 ^ 8 := by rw [← h40]; exact hV
  have hlt : chunkVal bs / 32 ^ padCount bs.length < 32 ^ (8 - padCount bs.length) := by
    rw [Nat.div_lt_iff_lt_mul (pow_pos (by norm_num : (0 : Nat) < 32) _)]
    have hpw : 32 ^ (8 - padCount bs.length) * 32 ^ padCount bs.length = 32 ^ 8 := by
      rw [← pow_add, show 8 - padCount bs.length + padCount bs.length = 8 by omega]
    rw [hpw]
    exact hV2
  have hlt2 : toValBE bs * 2 ^ (8 * (5 - bs.length) - 5 * padCount bs.length)
      < 32 ^ (8 - padCount bs.length) := by
    rw [← hdiv]
    exact hlt
  have hfold : foldl32 (digits32
      (toValBE bs * 2 ^ (8 * (5 - bs.length) - 5 * padCount bs.length))
      (8 - padCount bs.length))
      = toValBE bs * 2 ^ (8 * (5 - bs.length) - 5 * padCount bs.length) := by
    rw [foldl32_digits32, Nat.mod_eq_of_lt hlt2]
  have hall : ∀ c ∈ digits32
      (toValBE bs * 2 ^ (8 * (5 - bs.length) - 5 * padCount bs.length))
      (8 - padCount bs.length), c < 32 := fun c hc => digits32_lt _ _ c hc
  rw [bitsToBytes_eq_bytesOf _ 0 0 (by omega) hall]
  simp only [digits32_length, Nat.zero_mul, zero_add, hfold]
  rw [hp3, bytesOf_mul_pow _ _ hp2]
  exact bytesOf_toValBE bs hb

theorem flatten_length_sigIndices : ∀ (cs : List (List Nat)), (∀ c ∈ cs, c.length = 5) →
    ((cs.map sigIndices).flatten).length = 8 * cs.length := by
  intro cs
  induction cs with
  | nil => simp
  | cons c rest ih =>
      intro h
      have hc : c.length = 5 := h c (List.mem_cons.mpr (Or.inl rfl))
      have hr : ∀ x ∈ rest, x.length = 5 := fun x hx => h x (List.mem_cons.mpr (Or.inr hx))
      simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons,
        sigIndices_length_full c hc, ih hr]
      omega

theorem flatten_mem_sigIndices : ∀ (cs : List (List Nat)),
    ∀ d ∈ (cs.map sigIndices).flatten, d < 32 := by
  intro cs
  induction cs with
  | nil => simp
  | cons c rest ih =>
      intro d hd
      simp only [List.map_cons, List.flatten_cons, List.mem_append] at hd
      rcases hd with hd | hd
      · exact sigIndices_lt c d hd
      · exact ih d hd

theorem bitsToBytes_sigIndices_all : ∀ (cs : List (List Nat)),
    (∀ c ∈ cs, c.length = 5) → (∀ c ∈ cs, ∀ b ∈ c, b < 256) →
    bitsToBytes 0 0 ((cs.map sigIndices).flatten) = cs.flatten := by
  intro cs
  induction cs with
  | nil => intro _ _; simp [bitsToBytes_nil]
  | cons c rest ih =>
      intro hfull hbytes
      have hc5 : c.length = 5 := hfull c (List.mem_cons.mpr (Or.inl rfl))
      have hrfull : ∀ x ∈ rest, x.length = 5 :=
        fun x hx => hfull x (List.mem_cons.mpr (Or.inr hx))
      have hrbytes : ∀ x ∈ rest, ∀ b ∈ x, b < 256 :=
        fun x hx b hb => hbytes x (List.mem_cons.mpr (Or.inr hx)) b hb
      have hcbytes : ∀ b ∈ c, b < 256 := hbytes c (List.mem_cons.mpr (Or.inl rfl))
      have hlen : (sigIndices c).length = 8 := sigIndices_length_full c hc5
      have h8 : 8 ∣ (sigIndices c).length := by rw [hlen]
      have hflat : ((c :: rest).map sigIndices).flatten
          = sigIndices c ++ (rest.map sigIndices).flatten := by simp
      rw [hflat, bitsToBytes_append 0 (sigIndices c) _ h8 (sigIndices_lt c)
          (flatten_mem_sigIndices rest),
        bitsToBytes_sigIndices c (by omega) (by omega) hcbytes,
        ih hrfull hrbytes, List.flatten_cons]

theorem toIndices_flatten_sigChunk : ∀ (cs : List (List Nat)),
    toIndices ((cs.map sigChunk).flatten) = some ((cs.map sigIndices).flatten) := by
  intro cs
  induction cs with
  | nil => simp [toIndices]
  | cons c rest ih =>
      simp only [List.map_cons, List.flatten_cons]
      exact toIndices_append _ _ (toIndices_sigChunk c) _ _ ih


/-! ## Generic list helpers used below -/

theorem map_congr_gen {α β : Type} (f g : α → β) : ∀ (l : List α),
    (∀ c ∈ l, f c = g c) → l.map f = l.map g := by
  intro l
  induction l with
  | nil => simp
  | cons a rest ih =>
      intro h
      simp only [List.map_cons, h a (List.mem_cons.mpr (Or.inl rfl)),
        ih (fun c hc => h c (List.mem_cons.mpr (Or.inr hc)))]

theorem map_map_id (l : List Nat) (f g : Nat → Nat) (h : ∀ c ∈ l, g (f c) = c) :
    (l.map f).map g = l := by
  induction l with
  | nil => simp
  | cons a rest ih =>
      have hr : ∀ c ∈ rest, g (f c) = c := fun c hc => h c (List.mem_cons.mpr (Or.inr hc))
      simp only [List.map_cons, ih hr, h a (List.mem_cons.mpr (Or.inl rfl))]

theorem map_casefold_false (l : List Nat) : l.map (casefoldByte false) = l := by
  have h : casefoldByte false = id := by
    funext c
    exact casefoldByte_false c
  rw [h, List.map_id]

theorem count_eq_zero_of_ne : ∀ (l : List Nat) (a : Nat), (∀ x ∈ l, x ≠ a) → l.count a = 0 := by
  intro l
  induction l with
  | nil => intro a _; simp
  | cons x rest ih =>
      intro a h
      have hx : x ≠ a := h x (List.mem_cons.mpr (Or.inl rfl))
      have hr : ∀ y ∈ rest, y ≠ a := fun y hy => h y (List.mem_cons.mpr (Or.inr hy))
      have h2 : rest.count a = 0 := ih a hr
      have h3 : (if x == a then 1 else 0 : Nat) = 0 := by
        by_cases hbe : x == a
        · have hae : x = a := by simpa using hbe
          exact absurd hae hx
        · exact if_neg hbe
      rw [List.count_cons, h3, h2]

theorem count_replicate_61 (n : Nat) : (List.replicate n 61).count 61 = n := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, List.count_cons, ih]

theorem map_const_five : ∀ (cs : List (List Nat)),
    cs.map (fun _ => 5) = List.replicate cs.length 5 := by
  intro cs
  induction cs with
  | nil => simp
  | cons c rest ih =>
      simp only [List.map_cons, List.length_cons, List.replicate_succ, ih]

theorem flatten_append_singleton : ∀ (A : List (List Nat)) (B : List Nat),
    (A ++ [B]).flatten = A.flatten ++ B := by
  intro A
  induction A with
  | nil => intro B; simp
  | cons x rest ih =>
      intro B
      calc ((x :: rest) ++ [B]).flatten
          = (x :: (rest ++ [B])).flatten := rfl
        _ = x ++ (rest ++ [B]).flatten := List.flatten_cons
        _ = x ++ (rest.flatten ++ B) := by rw [ih B]
        _ = (x ++ rest.flatten) ++ B := (List.append_assoc _ _ _).symm
        _ = (x :: rest).flatten ++ B := by rw [List.flatten_cons]

theorem sum_replicate_five : ∀ (n : Nat), (List.replicate n 5).sum = 5 * n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [List.replicate_succ, List.sum_cons, List.sum_nil, ih]
      omega

/-! ## Structure of the encoder output -/

theorem rstripEq_b32encode : ∀ (s : List Nat),
    (rstripEq (b32encode s) = [] ∧ s = []) ∨
    (∃ cs last, chunksOf5 s = cs ++ [last]
      ∧ rstripEq (b32encode s) = ((cs ++ [last]).map sigChunk).flatten
      ∧ (∀ c ∈ cs, c.length = 5) ∧ 1 ≤ last.length ∧ last.length ≤ 5) := by
  intro s
  rcases chunksOf5_structure s with ⟨h1, h2⟩ | ⟨cs, last, hcs, hfull, hlen1, hlen2⟩
  · subst h2
    have hb : b32encode [] = [] := by simp [b32encode, chunksOf5_nil]
    exact Or.inl ⟨by simp [hb, rstripEq], rfl⟩
  · have hmap : cs.map encChunk = cs.map sigChunk :=
      map_congr_gen encChunk sigChunk cs (fun c hc => encChunk_full c (hfull c hc))
    have henc : b32encode s
        = ((cs.map sigChunk).flatten ++ sigChunk last)
          ++ List.replicate (padCount last.length) 61 := by
      simp only [b32encode, hcs, List.map_append, List.map_singleton, hmap,
        encChunk_eq last, flatten_append_singleton, List.append_assoc]
    have hno : ∀ x ∈ (cs.map sigChunk).flatten ++ sigChunk last, x ≠ 61 := by
      intro x hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · rw [List.mem_flatten] at hx
        obtain ⟨l, hl, hx2⟩ := hx
        rw [List.mem_map] at hl
        obtain ⟨y, hy, rfl⟩ := hl
        exact sigChunk_ne_61 y x hx2
      · exact sigChunk_ne_61 last x hx
    have hgoal : rstripEq (b32encode s) = ((cs ++ [last]).map sigChunk).flatten := by
      rw [henc, rstripEq_append_replicate _ hno _]
      simp
    exact Or.inr ⟨cs, last, hcs, hgoal, hfull, hlen1, hlen2⟩

/-! ## Round trip: decoding undoes encoding -/

theorem b32decode_b32encode : ∀ (s : List Nat), (∀ b ∈ s, b < 256) →
    b32decode false (b32encode s) = some s := by
  intro s hs
  rcases rstripEq_b32encode s with ⟨h1, h2⟩ | ⟨cs, last, hcs, hr, hfull, hlen1, hlen2⟩
  · subst h2
    have hb : b32encode [] = [] := by simp [b32encode, chunksOf5_nil]
    have hz : b32decode false [] = some [] := by decide
    rw [hb]
    exact hz
  · have hbytes : ∀ c ∈ cs ++ [last], ∀ b ∈ c, b < 256 := by
      intro c hc b hb
      have hm : b ∈ (chunksOf5 s).flatten := by
        rw [hcs]
        exact List.mem_flatten.mpr ⟨c, hc, hb⟩
      rw [chunksOf5_flatten] at hm
      exact hs b hm
    have hcsbytes : ∀ c ∈ cs, ∀ b ∈ c, b < 256 :=
      fun c hc b hb => hbytes c (List.mem_append.mpr (Or.inl hc)) b hb
    have hlastbytes : ∀ b ∈ last, b < 256 :=
      fun b hb => hbytes last (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))) b hb
    have hidx : toIndices (((cs ++ [last]).map sigChunk).flatten)
        = some ((cs.map sigIndices).flatten ++ sigIndices last) := by
      have hh : ((cs ++ [last]).map sigChunk).flatten
          = (cs.map sigChunk).flatten ++ sigChunk last := by simp
      rw [hh]
      exact toIndices_append _ _ (toIndices_flatten_sigChunk cs) _ _ (toIndices_sigChunk last)
    have hAlen : ((cs.map sigIndices).flatten).length = 8 * cs.length :=
      flatten_length_sigIndices cs hfull
    have hmain : bitsToBytes 0 0 ((cs.map sigIndices).flatten ++ sigIndices last)
        = cs.flatten ++ last := by
      have h8' : 8 ∣ ((cs.map sigIndices).flatten).length := by
        rw [hAlen]; exact ⟨cs.length, rfl⟩
      rw [bitsToBytes_append 0 _ _ h8' (flatten_mem_sigIndices cs) (sigIndices_lt last),
        bitsToBytes_sigIndices_all cs hfull hcsbytes,
        bitsToBytes_sigIndices last hlen1 hlen2 hlastbytes]
    have hfin : cs.flatten ++ last = s := by
      have hz : cs.flatten ++ last = (cs ++ [last]).flatten := by simp
      rw [hz, ← hcs, chunksOf5_flatten]
    have hstep : b32decode false (b32encode s)
        = (toIndices (rstripEq (b32encode s))).map (bitsToBytes 0 0) := by
      simp only [b32decode, map_casefold_false]
    have hgoal : bitsToBytes 0 0 ((cs.map sigIndices).flatten ++ sigIndices last) = s := by
      rw [hmain, hfin]
    rw [hstep, hr, hidx]
    simp only [Option.map, hgoal]

theorem casefold_lower_encode (s : List Nat) :
    ((b32encode s).map toLowerByte).map (casefoldByte true) = b32encode s :=
  map_map_id (b32encode s) toLowerByte (casefoldByte true) (by
    intro c hc
    rcases mem_b32encode s c hc with h61 | ⟨i, hi, hci⟩
    · subst h61
      simp [casefoldByte, toUpperAscii, toLowerByte_61, toUpperAscii_61]
    · subst hci
      rw [casefoldByte_true, toUpperAscii_toLowerByte_b32Char i hi])

theorem b32decode_casefold_lower : ∀ (s : List Nat), (∀ b ∈ s, b < 256) →
    b32decode true ((b32encode s).map toLowerByte) = some s := by
  intro s hs
  have hcf : ((b32encode s).map toLowerByte).map (casefoldByte true) = b32encode s :=
    casefold_lower_encode s
  have hstep : b32decode true ((b32encode s).map toLowerByte)
      = (toIndices (rstripEq (b32encode s))).map (bitsToBytes 0 0) := by
    simp only [b32decode, hcf]
  have hstep2 : b32decode false (b32encode s)
      = (toIndices (rstripEq (b32encode s))).map (bitsToBytes 0 0) := by
    simp only [b32decode, map_casefold_false]
  rw [hstep, ← hstep2]
  exact b32decode_b32encode s hs

theorem decode_error_iff (cs : List Nat) :
    b32decode false cs = none ↔ ∃ c ∈ rstripEq cs, b32IndexOf c = none := by
  have h1 : b32decode false cs
      = (toIndices (rstripEq cs)).map (bitsToBytes 0 0) := by
    simp only [b32decode, map_casefold_false]
  rw [h1, Option.map_eq_none_iff, toIndices_none]

theorem decode_error (cs : List Nat) (h : ∃ c ∈ rstripEq cs, b32IndexOf c = none) :
    b32decode false cs = none := (decode_error_iff cs).mpr h

theorem decode_casefold_error_iff (cs : List Nat) :
    b32decode true cs = none ↔ ∃ c ∈ rstripEq (cs.map toUpperAscii), b32IndexOf c = none := by
  have h1 : cs.map (casefoldByte true) = cs.map toUpperAscii :=
    map_congr_gen (casefoldByte true) toUpperAscii cs (fun c _ => casefoldByte_true c)
  have h2 : b32decode true cs
      = (toIndices (rstripEq (cs.map toUpperAscii))).map (bitsToBytes 0 0) := by
    simp only [b32decode, h1]
  rw [h2, Option.map_eq_none_iff, toIndices_none]

/-! ## Encoder output properties -/

theorem flatten_length_encChunk : ∀ (cs : List (List Nat)), (∀ c ∈ cs, c.length ≤ 5) →
    ((cs.map encChunk).flatten).length = 8 * cs.length := by
  intro cs
  induction cs with
  | nil => simp
  | cons c rest ih =>
      intro h
      have hc : c.length ≤ 5 := h c (List.mem_cons.mpr (Or.inl rfl))
      have hr : ∀ x ∈ rest, x.length ≤ 5 := fun x hx => h x (List.mem_cons.mpr (Or.inr hx))
      simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons,
        encChunk_length c hc, ih hr]
      omega

theorem encode_length (s : List Nat) : (b32encode s).length = 8 * ((s.length + 4) / 5) := by
  have h := flatten_length_encChunk (chunksOf5 s) (chunksOf5_length_le s)
  rw [chunksOf5_length s] at h
  simp only [b32encode]
  exact h

theorem encode_charset (s : List Nat) : ∀ c ∈ b32encode s,
    c = 61 ∨ (65 ≤ c ∧ c ≤ 90) ∨ (50 ≤ c ∧ c ≤ 55) := by
  intro c hc
  rcases mem_b32encode s c hc with h | ⟨i, hi, hci⟩
  · exact Or.inl h
  · subst hci
    rcases b32Char_range i hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · exact Or.inr (Or.inr ⟨h1, h2⟩)

theorem count_sigChunk (bs : List Nat) : (sigChunk bs).count 61 = 0 :=
  count_eq_zero_of_ne (sigChunk bs) 61 (fun c hc => sigChunk_ne_61 bs c hc)

theorem count_encChunk (bs : List Nat) : (encChunk bs).count 61 = padCount bs.length := by
  rw [encChunk_eq, List.count_append, count_sigChunk, zero_add, count_replicate_61]

theorem padCount_mod5 (n : Nat) (h : n ≤ 5) : padCount (n % 5) = padCount n := by
  have h2 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
  rcases h2 with (rfl|rfl|rfl|rfl|rfl|rfl) <;> simp [padCount]

theorem encode_pad (s : List Nat) : (b32encode s).count 61 = padCount (s.length % 5) := by
  have hsum : ∀ (cs : List (List Nat)), (∀ c ∈ cs, c.length = 5) →
      (cs.map (fun c => padCount c.length)).sum = 0 := by
    intro cs
    induction cs with
    | nil => intro _; simp
    | cons c rest ih =>
        intro h
        have hc : c.length = 5 := h c (List.mem_cons.mpr (Or.inl rfl))
        have hr : ∀ x ∈ rest, x.length = 5 := fun x hx => h x (List.mem_cons.mpr (Or.inr hx))
        simp [List.map_cons, List.sum_cons, ih hr, hc, padCount_five]
  rcases chunksOf5_structure s with ⟨h1, h2⟩ | ⟨cs, last, hcs, hfull, hlen1, hlen2⟩
  · subst h2
    simp [b32encode, chunksOf5_nil, padCount]
  · have hflat : (cs ++ [last]).flatten = s := by rw [← hcs, chunksOf5_flatten]
    have hlen : s.length = (cs.map List.length).sum + last.length := by
      have hz : ((cs ++ [last]).flatten).length = s.length := by rw [hflat]
      rw [List.length_flatten, List.map_append, List.map_singleton, List.sum_append,
        List.sum_singleton] at hz
      omega
    have hsum2 : (cs.map List.length).sum = 5 * cs.length := by
      have hz : cs.map List.length = List.replicate cs.length 5 := by
        rw [map_congr_gen List.length (fun _ => 5) cs (fun c hc => hfull c hc),
          map_const_five]
      rw [hz, sum_replicate_five]
    have hcount : (b32encode s).count 61 = padCount last.length := by
      have hmap : cs.map encChunk = cs.map sigChunk :=
        map_congr_gen encChunk sigChunk cs (fun c hc => encChunk_full c (hfull c hc))
      have h0 : ((cs.map sigChunk).flatten).count 61 = 0 :=
        count_eq_zero_of_ne _ 61 (by
          intro c hc
          rw [List.mem_flatten] at hc
          obtain ⟨l, hl, hc2⟩ := hc
          rw [List.mem_map] at hl
          obtain ⟨y, hy, rfl⟩ := hl
          exact sigChunk_ne_61 y c hc2)
      have hz : b32encode s = (cs.map sigChunk).flatten ++ encChunk last := by
        simp only [b32encode, hcs, List.map_append, List.map_singleton, hmap,
          flatten_append_singleton]
      rw [hz, List.count_append, h0, zero_add, encChunk_eq, List.count_append,
        count_sigChunk, zero_add, count_replicate_61]
    have hmod : (5 * cs.length + last.length) % 5 = last.length % 5 := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left]
    rw [hlen, hsum2, hmod, hcount, padCount_mod5 last.length hlen2]

theorem length_filter_ne (l : List Nat) (a : Nat) :
    (l.filter (· ≠ a)).length + l.count a = l.length := by
  induction l with
  | nil => simp
  | cons x rest ih =>
      by_cases hx : x = a
      · have hf : (x :: rest).filter (· ≠ a) = rest.filter (· ≠ a) := by simp [hx]
        have hc : (x :: rest).count a = rest.count a + 1 := by simp [hx, List.count_cons]
        rw [hf, hc, List.length_cons]
        omega
      · have hf : (x :: rest).filter (· ≠ a) = x :: rest.filter (· ≠ a) := by simp [hx]
        have hc : (x :: rest).count a = rest.count a := by simp [hx, List.count_cons]
        rw [hf, hc, List.length_cons, List.length_cons]
        omega

theorem encode_sig_arith (n : Nat) :
    8 * ((n + 4) / 5) - padCount (n % 5) = (n * 8 + 4) / 5 := by
  have hd : n = 5 * (n / 5) + n % 5 := (Nat.div_add_mod n 5).symm
  rcases show n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 by omega
    with h | h | h | h | h <;> rw [h] <;> simp [padCount] <;> omega

theorem encode_sig (s : List Nat) :
    (b32encode s).length - (b32encode s).count 61 = (s.length * 8 + 4) / 5 := by
  rw [encode_length, encode_pad, encode_sig_arith]

theorem encode_sig_filter (s : List Nat) :
    ((b32encode s).filter (· ≠ 61)).length = (s.length * 8 + 4) / 5 := by
  have h := length_filter_ne (b32encode s) 61
  have h2 := encode_sig s
  omega

theorem encode_injective : ∀ (a b : List Nat), (∀ x ∈ a, x < 256) → (∀ x ∈ b, x < 256) →
    b32encode a = b32encode b → a = b := by
  intro a b ha hb hab
  have h1 := b32decode_b32encode a ha
  have h2 := b32decode_b32encode b hb
  have h3 : some a = some b := by rw [← h1, ← h2, hab]
  exact Option.some.inj h3


/-! ## Auxiliary facts needed by the properties -/

theorem bytesOf_lt256 : ∀ (B W : Nat), ∀ b ∈ bytesOf W B, b < 256 := by
  have key : ∀ (B : Nat), (∀ m, m < B → ∀ (W : Nat), ∀ b ∈ bytesOf W m, b < 256) →
      ∀ (W : Nat), ∀ b ∈ bytesOf W B, b < 256 := by
    intro B ih W b hb
    by_cases h8 : B < 8
    · rw [bytesOf_lt _ _ h8] at hb
      simp at hb
    · rw [bytesOf_ge _ _ (by omega), List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact Nat.mod_lt _ (by norm_num)
      · exact ih (B - 8) (by omega) W b hb
  intro B
  exact Nat.strongRecOn B key

theorem b32IndexOf_lt (c i : Nat) (h : b32IndexOf c = some i) : i < 32 := by
  by_cases h1 : 65 ≤ c ∧ c ≤ 90
  · have hz : b32IndexOf c = some (c - 65) := by simp [b32IndexOf, h1]
    rw [hz] at h
    have hi := Option.some.inj h
    rw [← hi]
    omega
  · by_cases h2 : 50 ≤ c ∧ c ≤ 55
    · have hz : b32IndexOf c = some (c - 50 + 26) := by simp [b32IndexOf, h1, h2]
      rw [hz] at h
      have hi := Option.some.inj h
      rw [← hi]
      omega
    · have hz : b32IndexOf c = none := by simp [b32IndexOf, h1, h2]
      rw [hz] at h
      exact Option.noConfusion h

theorem toIndices_lt32 : ∀ (cs is : List Nat), toIndices cs = some is → ∀ i ∈ is, i < 32 := by
  intro cs
  induction cs with
  | nil =>
      intro is hi i hin
      have h0 : toIndices [] = some [] := rfl
      rw [h0] at hi
      have : is = [] := (Option.some.inj hi).symm
      subst this
      simp at hin
  | cons c rest ih =>
      intro is hi i hin
      cases hidx : b32IndexOf c with
      | none =>
          have hnn : toIndices (c :: rest) = none := by simp [toIndices, hidx]
          rw [hnn] at hi
          exact Option.noConfusion hi
      | some j =>
          have hcons : toIndices (c :: rest) = (toIndices rest).map (j :: ·) :=
            toIndices_cons_some c j hidx rest
          rw [hcons] at hi
          rw [Option.map_eq_some_iff] at hi
          obtain ⟨rest', hrest, his⟩ := hi
          have hj : j < 32 := b32IndexOf_lt c j hidx
          have hr : ∀ x ∈ rest', x < 32 := ih rest' hrest
          rw [← his] at hin
          simp only [List.mem_cons] at hin
          rcases hin with rfl | hin
          · exact hj
          · exact hr i hin

theorem bitsToBytes_lt256 (cs : List Nat) (val bits : Nat) (hb : bits < 8)
    (hcs : ∀ c ∈ cs, c < 32) :
    ∀ b ∈ bitsToBytes val bits cs, b < 256 := by
  have heq := bitsToBytes_eq_bytesOf cs val bits hb hcs
  intro b hmem
  rw [heq] at hmem
  exact bytesOf_lt256 _ _ b hmem

theorem padCount_formula (n : Nat) :
    padCount (n % 5) = if n % 5 = 0 then 0 else 8 - (n % 5 * 8 + 4) / 5 := by
  rcases show n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 by omega
    with h | h | h | h | h <;> rw [h] <;> simp [padCount]

/-! ## Properties and their theorems -/

/-- The encoded text has 8 characters per 5-byte block. -/
def EncodeLength_prop (s : List Nat) : Prop :=
  (b32encode s).length = 8 * ((s.length + 4) / 5)

theorem EncodeLength_thm (s : List Nat) : EncodeLength_prop s := encode_length s

/-- Every output character is in the Base32 alphabet or is the `=` pad. -/
def EncodeCharset_prop (s : List Nat) : Prop :=
  ∀ c ∈ b32encode s, c = 61 ∨ (65 ≤ c ∧ c ≤ 90) ∨ (50 ≤ c ∧ c ≤ 55)

theorem EncodeCharset_thm (s : List Nat) : EncodeCharset_prop s := encode_charset s

/-- The number of `=` pad characters is the one RFC 4648 prescribes. -/
def EncodePad_prop (s : List Nat) : Prop :=
  (b32encode s).count 61 = if s.length % 5 = 0 then 0 else 8 - (s.length % 5 * 8 + 4) / 5

theorem EncodePad_thm (s : List Nat) : EncodePad_prop s := by
  rw [EncodePad_prop, encode_pad, padCount_formula]

/-- The number of significant (non-pad) characters is `ceil (8 * len / 5)`. -/
def EncodeSig_prop (s : List Nat) : Prop :=
  (b32encode s).length - (b32encode s).count 61 = (s.length * 8 + 4) / 5

theorem EncodeSig_thm (s : List Nat) : EncodeSig_prop s := encode_sig s

/-- `dec (enc msg) == msg` -/
def RoundTrip_prop (s : List Nat) : Prop :=
  b32decode false (b32encode s) = some s

theorem RoundTrip_thm (s : List Nat) (h : Pre s) : RoundTrip_prop s :=
  b32decode_b32encode s h

/-- `dec (b'mzxw6ytb', True) == b'fooba'`: casefolded input decodes too. -/
def CasefoldRoundTrip_prop (s : List Nat) : Prop :=
  b32decode true ((b32encode s).map toLowerByte) = some s

theorem CasefoldRoundTrip_thm (s : List Nat) (h : Pre s) : CasefoldRoundTrip_prop s :=
  b32decode_casefold_lower s h

/-- `binascii.Error('Non-base32 digit found')` is raised on a bad digit. -/
def DecodeError_prop (cs : List Nat) : Prop :=
  (∃ c ∈ rstripEq cs, b32IndexOf c = none) → b32decode false cs = none

theorem DecodeError_thm (cs : List Nat) : DecodeError_prop cs := fun h => decode_error cs h

/-- Conversely: no bad digit means decoding succeeds. -/
def DecodeSome_prop (cs : List Nat) : Prop :=
  (∀ c ∈ rstripEq cs, b32IndexOf c ≠ none) → ∃ bs, b32decode false cs = some bs

theorem DecodeSome_thm (cs : List Nat) : DecodeSome_prop cs := by
  intro h
  have h1 : b32decode false cs = (toIndices (rstripEq cs)).map (bitsToBytes 0 0) := by
    simp only [b32decode, map_casefold_false]
  have hne : ¬(∃ c ∈ rstripEq cs, b32IndexOf c = none) := by
    intro hex
    obtain ⟨c, hc, hc2⟩ := hex
    exact h c hc hc2
  have hsome : ∃ is, toIndices (rstripEq cs) = some is := by
    by_contra hcontra
    push_neg at hcontra
    have hnone : toIndices (rstripEq cs) = none := by
      cases hopt : toIndices (rstripEq cs) with
      | none => rfl
      | some is => exact absurd hopt (hcontra is)
    rw [toIndices_none] at hnone
    exact hne hnone
  obtain ⟨is, his⟩ := hsome
  exact ⟨bitsToBytes 0 0 is, by rw [h1, his]; rfl⟩

/-- `pre_decode` is respected: an ASCII input either raises the
`Non-base32 digit found` error or decodes to a genuine byte string. -/
def DecodeTotal_prop (cs : List Nat) : Prop :=
  PreDecode cs →
    b32decode false cs = none ∨ ∃ bs, Pre bs ∧ b32decode false cs = some bs

theorem DecodeTotal_thm (cs : List Nat) : DecodeTotal_prop cs := by
  intro _
  by_cases herr : ∃ c ∈ rstripEq cs, b32IndexOf c = none
  · exact Or.inl (decode_error cs herr)
  · push_neg at herr
    have h1 : b32decode false cs = (toIndices (rstripEq cs)).map (bitsToBytes 0 0) := by
      simp only [b32decode, map_casefold_false]
    have hs : ∃ is, toIndices (rstripEq cs) = some is := by
      by_contra hc
      push_neg at hc
      have hnone : toIndices (rstripEq cs) = none := by
        cases ho : toIndices (rstripEq cs) with
        | none => rfl
        | some is => exact absurd ho (hc is)
      rw [toIndices_none] at hnone
      obtain ⟨c, hc, hc2⟩ := hnone
      exact herr c hc hc2
    obtain ⟨is, his⟩ := hs
    exact Or.inr ⟨bitsToBytes 0 0 is,
      fun b hb => bitsToBytes_lt256 is 0 0 (by omega) (toIndices_lt32 _ _ his) b hb,
      by rw [h1, his]; rfl⟩

/-- Decoding always produces bytes. -/
def DecodeBytes_prop (cs : List Nat) : Prop :=
  ∀ bs, b32decode false cs = some bs → ∀ b ∈ bs, b < 256

theorem DecodeBytes_thm (cs : List Nat) : DecodeBytes_prop cs := by
  intro bs hbs b hb
  have h1 : b32decode false cs
      = (toIndices (rstripEq cs)).map (bitsToBytes 0 0) := by
    simp only [b32decode, map_casefold_false]
  rw [h1, Option.map_eq_some_iff] at hbs
  obtain ⟨is, his, hbs2⟩ := hbs
  have hb2 : b ∈ bitsToBytes 0 0 is := by rw [← hbs2] at hb; exact hb
  exact bitsToBytes_lt256 is 0 0 (by omega) (toIndices_lt32 _ _ his) b hb2

/-- Base32 encoding is injective on byte strings. -/
def Injective_prop : Prop :=
  ∀ a b : List Nat, Pre a → Pre b → b32encode a = b32encode b → a = b

theorem Injective_thm : Injective_prop :=
  fun a b ha hb hab => encode_injective a b ha hb hab

/-- Casefolding is what makes lower-case input decodable. -/
def CasefoldEncode_prop (s : List Nat) : Prop :=
  ((b32encode s).map toLowerByte).map (casefoldByte true) = b32encode s

theorem CasefoldEncode_thm (s : List Nat) : CasefoldEncode_prop s := casefold_lower_encode s

theorem mem_lstripEq_of_mem : ∀ (m : List Nat) (x : Nat), x ∈ m → x ≠ 61 → x ∈ lstripEq m := by
  intro m
  induction m with
  | nil => intro x hx _; simp at hx
  | cons c rest ih =>
      intro x hx hx2
      by_cases hc : c = 61
      · simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact absurd hc hx2
        · rw [lstripEq_cons, if_pos hc]
          exact ih x hx hx2
      · rw [lstripEq_cons, if_neg hc]
        exact hx

theorem mem_rstripEq_of_mem (x : Nat) (l : List Nat) (h1 : x ∈ l) (h2 : x ≠ 61) :
    x ∈ rstripEq l := by
  have h3 : x ∈ l.reverse := List.mem_reverse.mpr h1
  have h4 : x ∈ lstripEq l.reverse := mem_lstripEq_of_mem l.reverse x h3 h2
  show x ∈ (lstripEq l.reverse).reverse
  exact List.mem_reverse.mpr h4

/-- Without `casefold`, lower-cased Base32 text containing a letter is rejected. -/
def NoCasefoldLower_prop (s : List Nat) : Prop :=
  (∃ c ∈ b32encode s, 65 ≤ c ∧ c ≤ 90) →
    b32decode false ((b32encode s).map toLowerByte) = none

theorem NoCasefoldLower_thm (s : List Nat) : NoCasefoldLower_prop s := by
  intro h
  obtain ⟨c, hc, hc1, hc2⟩ := h
  have hlow : toLowerByte c = c + 32 := by
    have hz : 65 ≤ c ∧ c ≤ 90 := ⟨hc1, hc2⟩
    rw [toLowerByte, if_pos hz]
  have hmem : c + 32 ∈ (b32encode s).map toLowerByte :=
    List.mem_map.mpr ⟨c, hc, hlow⟩
  have hidx : b32IndexOf (c + 32) = none := by
    have hn1 : ¬(65 ≤ c + 32 ∧ c + 32 ≤ 90) := by omega
    have hn2 : ¬(50 ≤ c + 32 ∧ c + 32 ≤ 55) := by omega
    rw [b32IndexOf, if_neg hn1, if_neg hn2]
  have hne : c + 32 ≠ 61 := by omega
  have hstrip : c + 32 ∈ rstripEq ((b32encode s).map toLowerByte) :=
    mem_rstripEq_of_mem (c + 32) _ hmem hne
  exact decode_error _ ⟨c + 32, hstrip, hidx⟩

/-! ## Post-condition -/

def Post_prop (s : List Nat) : Prop :=
  EncodeLength_prop s ∧ EncodeCharset_prop s ∧ EncodePad_prop s ∧ EncodeSig_prop s ∧
    RoundTrip_prop s ∧ CasefoldRoundTrip_prop s ∧ CasefoldEncode_prop s ∧
    NoCasefoldLower_prop s ∧ DecodeBytes_prop (b32encode s) ∧
    DecodeSome_prop (b32encode s) ∧ Injective_prop

/-! ## Property-based tests -/

def genByte (i : Nat) : Nat := (i * 37 + 11) % 256

def genBytes (n k : Nat) : List Nat := (List.range n).map (fun j => genByte (k + j * 13))

-- PBT for `EncodeLength_prop`
example : (List.range 40).all (fun n =>
    (b32encode (genBytes n n)).length = 8 * ((n + 4) / 5)) = true := by native_decide

-- PBT for `EncodePad_prop`
example : (List.range 40).all (fun n =>
    (b32encode (genBytes n n)).count 61 = padCount (n % 5)) = true := by native_decide

-- PBT for `EncodeSig_prop`
example : (List.range 40).all (fun n =>
    (b32encode (genBytes n n)).length - (b32encode (genBytes n n)).count 61
      = (n * 8 + 4) / 5) = true := by native_decide

-- PBT for `RoundTrip_prop`
example : (List.range 40).all (fun n =>
    b32decode false (b32encode (genBytes n n)) = some (genBytes n n)) = true := by native_decide

-- PBT for `CasefoldRoundTrip_prop`
example : (List.range 40).all (fun n =>
    b32decode true ((b32encode (genBytes n n)).map toLowerByte)
      = some (genBytes n n)) = true := by native_decide

-- PBT for `EncodeCharset_prop`
example : (List.range 40).all (fun n =>
    (b32encode (genBytes n n)).all (fun c =>
      c == 61 || (decide (65 ≤ c) && decide (c ≤ 90))
        || (decide (50 ≤ c) && decide (c ≤ 55)))) = true := by native_decide

-- PBT for `DecodeError_prop`
example : (List.range 30).all (fun n =>
    b32decode false (genBytes n n ++ [33]) = none) = true := by native_decide

-- PBT for `Injective_prop`
example : (List.range 25).all (fun n =>
    (List.range 25).all (fun m =>
      decide (b32encode (genBytes n n) = b32encode (genBytes m m) → n = m))) = true
  := by native_decide

-- Randomized PBTs (Plausible): the post-condition's executable content
#eval Plausible.Testable.check
  (∀ s : List Nat, b32decode false (b32encode (s.map (· % 256))) = some (s.map (· % 256)))

#eval Plausible.Testable.check
  (∀ s : List Nat, (b32encode (s.map (· % 256))).length
      = 8 * (((s.map (· % 256)).length + 4) / 5))

#eval Plausible.Testable.check
  (∀ s : List Nat, b32decode true ((b32encode (s.map (· % 256))).map toLowerByte)
      = some (s.map (· % 256)))

#eval Plausible.Testable.check
  (∀ s : List Nat, ((b32encode (s.map (· % 256))).map toLowerByte).map (casefoldByte true)
      = b32encode (s.map (· % 256)))

#eval Plausible.Testable.check
  (∀ s : List Nat, (b32encode s).count 61 = padCount (s.length % 5))

/-! ## Correctness: `Pre → Post` -/

theorem correctness_thm (s : List Nat) (h : Pre s) : Post_prop s :=
  ⟨EncodeLength_thm s, EncodeCharset_thm s, EncodePad_thm s, EncodeSig_thm s,
    RoundTrip_thm s h, CasefoldRoundTrip_thm s h, CasefoldEncode_thm s,
    NoCasefoldLower_thm s, DecodeBytes_thm _, DecodeSome_thm _, Injective_thm⟩


/-! ## Equation lemmas used by the imperative development -/

theorem bitsToBytes_eq_ite (val bits i : Nat) (rest : List Nat) :
    bitsToBytes val bits (i :: rest)
      = if bits + 5 ≥ 8 then
          ((val * 32 + i) / 2 ^ (bits + 5 - 8)) % 256
            :: bitsToBytes (val * 32 + i) (bits + 5 - 8) rest
        else bitsToBytes (val * 32 + i) (bits + 5) rest := rfl

theorem bitsToBytes_cons_ge (val bits i : Nat) (rest : List Nat) (h : bits + 5 ≥ 8) :
    bitsToBytes val bits (i :: rest)
      = ((val * 32 + i) / 2 ^ (bits + 5 - 8)) % 256
        :: bitsToBytes (val * 32 + i) (bits + 5 - 8) rest := by
  rw [bitsToBytes_eq_ite, if_pos h]

theorem bitsToBytes_cons_lt (val bits i : Nat) (rest : List Nat) (h : ¬(bits + 5 ≥ 8)) :
    bitsToBytes val bits (i :: rest) = bitsToBytes (val * 32 + i) (bits + 5) rest := by
  rw [bitsToBytes_eq_ite, if_neg h]

theorem flatten_replicate_singleton : ∀ (k a : Nat),
    ((List.replicate k [a]).flatten) = List.replicate k a := by
  intro k
  induction k with
  | zero => intro a; simp
  | succ k ih =>
      intro a
      simp only [List.replicate_succ, List.flatten_cons, ih a]
      rfl

/-! ## Imperative implementation (`Id.run do` with mutable state) -/

/-- `chunk = chunk + b'\0' * (5 - len(chunk))`, imperatively. -/
def padTo5Imp (bs : List Nat) : List Nat :=
  Id.run do
    let mut padded : List Nat := bs
    for _ in List.replicate (5 - bs.length) 0 do
      padded := padded ++ [0]
    pure padded

/-- `val = int.from_bytes(chunk, 'big')`, imperatively. -/
def toValBEImp (bs : List Nat) : Nat :=
  Id.run do
    let mut val : Nat := 0
    for b in bs do
      val := val * 256 + b
    pure val

/-- The eight `encoded.append(_b32alphabet[...])` calls, imperatively. -/
def encIndicesImp (val : Nat) : List Nat :=
  Id.run do
    let mut chars : List Nat := []
    for k in [35, 30, 25, 20, 15, 10, 5, 0] do
      chars := chars ++ [b32Char ((val / 2 ^ k) % 32)]
    pure chars

/-- One encoded block, including the `=` fix-up, imperatively. -/
def encChunkImp (bs : List Nat) : List Nat :=
  Id.run do
    let padded := padTo5Imp bs
    let val := toValBEImp padded
    let chars := encIndicesImp val
    let mut out := chars.take (8 - padCount bs.length)
    for _ in List.replicate (padCount bs.length) 61 do
      out := out ++ [61]
    pure out

/-- `b32encode`, imperatively. -/
def b32encodeImp (s : List Nat) : List Nat :=
  Id.run do
    let mut encoded : List Nat := []
    for chunk in chunksOf5 s do
      encoded := encoded ++ encChunkImp chunk
    pure encoded

structure StripState where
  out : List Nat
  started : Bool

def stripStep (st : StripState) (c : Nat) : StripState :=
  if st.started || c ≠ 61 then { out := c :: st.out, started := true } else st

structure IdxState where
  out : List Nat
  bad : Bool

def idxStep (st : IdxState) (c : Nat) : IdxState :=
  match b32IndexOf c with
  | none => { st with bad := true }
  | some i => { out := st.out ++ [i], bad := st.bad }

structure DecState where
  val : Nat
  bits : Nat
  out : List Nat

def decStep (st : DecState) (i : Nat) : DecState :=
  let val' := st.val * 32 + i
  let bits' := st.bits + 5
  if bits' ≥ 8 then
    { val := val', bits := bits' - 8,
      out := st.out ++ [(val' / 2 ^ (bits' - 8)) % 256] }
  else
    { val := val', bits := bits', out := st.out }

/-- `s.encode('ascii')` followed by `s.upper()`, imperatively. -/
def casefoldImp (casefold : Bool) (s : List Nat) : List Nat :=
  Id.run do
    let mut t : List Nat := []
    for c in s do
      t := t ++ [casefoldByte casefold c]
    pure t

/-- `s.rstrip(b'=')`, imperatively. -/
def rstripEqImp (cs : List Nat) : List Nat :=
  Id.run do
    let mut rev : List Nat := []
    for c in cs do
      rev := c :: rev
    let mut st : StripState := { out := [], started := false }
    for c in rev do
      st := stripStep st c
    pure st.out

/-- The `rev_alphabet` lookup loop, imperatively. -/
def toIndicesImp (cs : List Nat) : Option (List Nat) :=
  Id.run do
    let mut st : IdxState := { out := [], bad := false }
    for c in cs do
      st := idxStep st c
    pure (if st.bad then none else some st.out)

/-- The `val`/`bits` accumulator loop, imperatively. -/
def bitsToBytesImp (is : List Nat) : List Nat :=
  Id.run do
    let mut st : DecState := { val := 0, bits := 0, out := [] }
    for i in is do
      st := decStep st i
    pure st.out

/-- `b32decode`, imperatively. -/
def b32decodeImp (casefold : Bool) (s : List Nat) : Option (List Nat) :=
  Id.run do
    let mut t := casefoldImp casefold s
    t := rstripEqImp t
    let mut res := toIndicesImp t
    res := res.map bitsToBytesImp
    pure res

def benchmark_b32encodeImp (s : List Nat) : List Nat := b32encodeImp s

def benchmark_b32decodeImp (casefold : Bool) (s : List Nat) : Option (List Nat) :=
  b32decodeImp casefold s

/-! ## Imperative unit tests -/

example : b32encodeImp [] = [] := by native_decide
example : b32encodeImp (strToBytes "f") = strToBytes "MY======" := by native_decide
example : b32encodeImp (strToBytes "fo") = strToBytes "MZXQ====" := by native_decide
example : b32encodeImp (strToBytes "foo") = strToBytes "MZXW6===" := by native_decide
example : b32encodeImp (strToBytes "foob") = strToBytes "MZXW6YQ=" := by native_decide
example : b32encodeImp (strToBytes "fooba") = strToBytes "MZXW6YTB" := by native_decide
example : b32encodeImp (strToBytes "foobar") = strToBytes "MZXW6YTBOI======" := by native_decide
example : b32decodeImp false (b32encodeImp (strToBytes "VeriBench"))
    = some (strToBytes "VeriBench") := by native_decide
example : b32decodeImp true (strToBytes "mzxw6ytb") = some (strToBytes "fooba") := by native_decide
example : b32decodeImp false (strToBytes "MZXW6!==") = none := by native_decide

#eval bytesToStr (b32encodeImp (strToBytes "foobar"))
#eval (b32decodeImp true (strToBytes "mzxw6ytb")).map bytesToStr

example : (List.range 25).all (fun n =>
    b32decodeImp false (b32encodeImp (genBytes n n)) = some (genBytes n n)) = true
  := by native_decide

/-! ## Functional / imperative equivalence -/

theorem padTo5Imp_eq (bs : List Nat) : padTo5Imp bs = padTo5 bs := by
  simp [padTo5Imp, padTo5, flatten_replicate_singleton, List.map_replicate]

theorem toValBEImp_eq (bs : List Nat) : toValBEImp bs = toValBE bs := by
  simp [toValBEImp, toValBE]

theorem encIndicesImp_eq (val : Nat) : encIndicesImp val = (encIndices val).map b32Char := by
  simp [encIndicesImp, encIndices, flatten_map_singleton]

theorem encChunkImp_eq (bs : List Nat) : encChunkImp bs = encChunk bs := by
  simp [encChunkImp, padTo5Imp_eq, toValBEImp_eq, encIndicesImp_eq, flatten_replicate_singleton,
    encChunk_eq, sigChunk_eq, sigIndices_eq, chunkVal, List.map_take]

theorem b32encodeImp_eq (s : List Nat) : b32encodeImp s = b32encode s := by
  simp [b32encodeImp, b32encode, encChunkImp_eq]

theorem casefoldImp_eq (casefold : Bool) (s : List Nat) :
    casefoldImp casefold s = s.map (casefoldByte casefold) := by
  simp [casefoldImp, flatten_map_singleton]

theorem revLoop_eq : ∀ (cs acc : List Nat),
    cs.foldl (fun rev c => c :: rev) acc = cs.reverse ++ acc := by
  intro cs
  induction cs with
  | nil => intro acc; simp
  | cons c rest ih =>
      intro acc
      simp [List.foldl_cons, ih, List.reverse_cons, List.append_assoc]

theorem foldl_stripStep_true : ∀ (l out : List Nat),
    (l.foldl stripStep { out := out, started := true }).out = l.reverse ++ out := by
  intro l
  induction l with
  | nil => intro out; simp [stripStep]
  | cons c rest ih =>
      intro out
      have hstep : stripStep { out := out, started := true } c
          = { out := c :: out, started := true } := by
        simp [stripStep]
      simp [List.foldl_cons, hstep, ih (c :: out), List.reverse_cons, List.append_assoc]

theorem foldl_stripStep_false : ∀ (l out : List Nat),
    (l.foldl stripStep { out := out, started := false }).out = (lstripEq l).reverse ++ out := by
  intro l
  induction l with
  | nil => intro out; simp [stripStep, lstripEq]
  | cons c rest ih =>
      intro out
      by_cases hc : c = 61
      · subst hc
        have hstep : stripStep { out := out, started := false } 61
            = { out := out, started := false } := by simp [stripStep]
        have hl : lstripEq (61 :: rest) = lstripEq rest := by simp [lstripEq]
        simp [List.foldl_cons, hstep, ih out, hl]
      · have hstep : stripStep { out := out, started := false } c
            = { out := c :: out, started := true } := by simp [stripStep, hc]
        have hl : lstripEq (c :: rest) = c :: rest := by simp [lstripEq, hc]
        simp [List.foldl_cons, hstep, foldl_stripStep_true rest (c :: out), hl,
          List.reverse_cons, List.append_assoc]

theorem rstripEqImp_eq (cs : List Nat) : rstripEqImp cs = rstripEq cs := by
  simp [rstripEqImp, revLoop_eq, foldl_stripStep_false, rstripEq]

theorem foldl_decStep_out : ∀ (l : List Nat) (st : DecState),
    (l.foldl decStep st).out = st.out ++ bitsToBytes st.val st.bits l := by
  intro l
  induction l with
  | nil => intro st; simp [bitsToBytes]
  | cons i rest ih =>
      intro st
      by_cases h8 : st.bits + 5 ≥ 8
      · have hstep : decStep st i
            = { val := st.val * 32 + i, bits := st.bits + 5 - 8,
                out := st.out ++ [((st.val * 32 + i) / 2 ^ (st.bits + 5 - 8)) % 256] } := by
          simp [decStep, h8]
        rw [List.foldl_cons, hstep, ih, bitsToBytes_cons_ge st.val st.bits i rest h8]
        simp [List.append_assoc]
      · have hstep : decStep st i
            = { val := st.val * 32 + i, bits := st.bits + 5, out := st.out } := by
          simp [decStep, h8]
        rw [List.foldl_cons, hstep, ih, bitsToBytes_cons_lt st.val st.bits i rest h8]

theorem bitsToBytesImp_eq (is : List Nat) : bitsToBytesImp is = bitsToBytes 0 0 is := by
  simp [bitsToBytesImp, foldl_decStep_out]

theorem foldl_idxStep_bad : ∀ (l : List Nat) (st : IdxState),
    ((l.foldl idxStep st).bad = true ↔ st.bad = true ∨ ∃ c ∈ l, b32IndexOf c = none) := by
  intro l
  induction l with
  | nil => intro st; simp
  | cons c rest ih =>
      intro st
      cases hidx : b32IndexOf c with
      | none =>
          have hstep : idxStep st c = { st with bad := true } := by simp [idxStep, hidx]
          simp only [List.foldl_cons, hstep, ih]
          constructor
          · intro h
            exact Or.inr ⟨c, by simp, hidx⟩
          · intro _
            simp
      | some i =>
          have hstep : (idxStep st c).bad = st.bad := by simp [idxStep, hidx]
          have hstep2 : idxStep st c = { out := st.out ++ [i], bad := st.bad } := by
            simp [idxStep, hidx]
          simp only [List.foldl_cons, hstep2, ih]
          constructor
          · intro h
            rcases h with h | ⟨x, hx, hx2⟩
            · exact Or.inl h
            · exact Or.inr ⟨x, List.mem_cons_of_mem c hx, hx2⟩
          · intro h
            rcases h with h | ⟨x, hx, hx2⟩
            · exact Or.inl h
            · rcases List.mem_cons.mp hx with rfl | hx
              · rw [hidx] at hx2; exact Option.noConfusion hx2
              · exact Or.inr ⟨x, hx, hx2⟩

theorem foldl_idxStep_out : ∀ (l is : List Nat), toIndices l = some is →
    ∀ (st : IdxState), (l.foldl idxStep st).out = st.out ++ is := by
  intro l
  induction l with
  | nil =>
      intro is hi st
      have h0 : toIndices [] = some [] := rfl
      have his : is = [] := by
        rw [h0] at hi
        exact (Option.some.inj hi).symm
      subst his
      simp
  | cons c rest ih =>
      intro is hi st
      cases hidx : b32IndexOf c with
      | none =>
          have hnn : toIndices (c :: rest) = none := by simp [toIndices, hidx]
          rw [hnn] at hi
          exact Option.noConfusion hi
      | some i =>
          have hcons : toIndices (c :: rest) = (toIndices rest).map (i :: ·) :=
            toIndices_cons_some c i hidx rest
          rw [hcons] at hi
          rw [Option.map_eq_some_iff] at hi
          obtain ⟨rest', hrest, his⟩ := hi
          have hstep : idxStep st c = { out := st.out ++ [i], bad := st.bad } := by
            simp [idxStep, hidx]
          rw [List.foldl_cons, hstep, ih rest' hrest]
          rw [← his]
          simp [List.append_assoc]

theorem toIndicesImp_eq (cs : List Nat) : toIndicesImp cs = toIndices cs := by
  by_cases herr : ∃ c ∈ cs, b32IndexOf c = none
  · have hb : ((cs.foldl idxStep { out := [], bad := false } : IdxState).bad) = true := by
      rw [foldl_idxStep_bad]
      simp [herr]
    have hn : toIndices cs = none := (toIndices_none cs).mpr herr
    simp [toIndicesImp, hb, hn]
  · push_neg at herr
    have hs : ∃ is, toIndices cs = some is := by
      by_contra hc
      push_neg at hc
      have hnone : toIndices cs = none := by
        cases ho : toIndices cs with
        | none => rfl
        | some is => exact absurd ho (hc is)
      rw [toIndices_none] at hnone
      obtain ⟨c, hc, hc2⟩ := hnone
      exact herr c hc hc2
    obtain ⟨is, his⟩ := hs
    have hb : ((cs.foldl idxStep { out := [], bad := false } : IdxState).bad) = false := by
      cases e : ((cs.foldl idxStep { out := [], bad := false } : IdxState).bad) with
      | false => rfl
      | true =>
          have h2 := (foldl_idxStep_bad cs { out := [], bad := false }).mp e
          simp at h2
          rcases h2 with ⟨c, hc, hc2⟩
          exact absurd hc2 (herr c hc)
    have ho : ((cs.foldl idxStep { out := [], bad := false } : IdxState).out) = is := by
      rw [foldl_idxStep_out cs is his]
      simp
    simp [toIndicesImp, hb, ho, his]

theorem b32decodeImp_eq (casefold : Bool) (s : List Nat) :
    b32decodeImp casefold s = b32decode casefold s := by
  have hfun : bitsToBytesImp = bitsToBytes 0 0 := by
    funext is
    exact bitsToBytesImp_eq is
  simp [b32decodeImp, casefoldImp_eq, rstripEqImp_eq, toIndicesImp_eq, hfun, b32decode]

theorem equivalence_encode (s : List Nat) : b32encodeImp s = b32encode s :=
  b32encodeImp_eq s

theorem equivalence_decode (casefold : Bool) (s : List Nat) :
    b32decodeImp casefold s = b32decode casefold s :=
  b32decodeImp_eq casefold s

theorem equivalence_benchmark_encode (s : List Nat) :
    benchmark_b32encodeImp s = benchmark_b32encode s := by
  simp [benchmark_b32encodeImp, benchmark_b32encode, b32encodeImp_eq]

theorem equivalence_benchmark_decode (casefold : Bool) (s : List Nat) :
    benchmark_b32decodeImp casefold s = benchmark_b32decode casefold s := by
  simp [benchmark_b32decodeImp, benchmark_b32decode, b32decodeImp_eq]

end B32Codec

/-! ## Axiom audit: every theorem above is kernel-checked from the three
permitted axioms only (`propext`, `Classical.choice`, `Quot.sound`). -/

#print axioms B32Codec.correctness_thm
#print axioms B32Codec.EncodeLength_thm
#print axioms B32Codec.EncodeCharset_thm
#print axioms B32Codec.EncodePad_thm
#print axioms B32Codec.EncodeSig_thm
#print axioms B32Codec.RoundTrip_thm
#print axioms B32Codec.CasefoldRoundTrip_thm
#print axioms B32Codec.CasefoldEncode_thm
#print axioms B32Codec.NoCasefoldLower_thm
#print axioms B32Codec.DecodeError_thm
#print axioms B32Codec.DecodeSome_thm
#print axioms B32Codec.DecodeTotal_thm
#print axioms B32Codec.DecodeBytes_thm
#print axioms B32Codec.Injective_thm
#print axioms B32Codec.equivalence_encode
#print axioms B32Codec.equivalence_decode
#print axioms B32Codec.equivalence_benchmark_encode
#print axioms B32Codec.equivalence_benchmark_decode
#print axioms B32Codec.b32decode_b32encode
#print axioms B32Codec.encode_length
#print axioms B32Codec.encode_pad
