import Mathlib

/-!
# Base32 Encoding and Decoding (`23_base32`)

Formalization of Python's `base64.b32encode` and `base64.b32decode` in Lean 4,
including:
- Functional implementations of Base32 encoding (`b32encode`, `benchmark_b32encode`)
  and decoding (`b32decode?`, `b32decode`, `benchmark_b32decode`) supporting
  `casefold` and `map01`.
- Unit tests covering all Python test cases (`check`).
- Pre-condition predicates (`pre_encode`, `pre_decode`, `Pre`).
- Formal property propositions (`_prop`) and kernel-checked proofs (`_thm`) for:
  1. Empty input behavior (`encode_empty`, `decode_empty`)
  2. Encoded output length and multiple-of-8 invariant (`encode_length`, `encode_length_mod8`)
  3. Output alphabet and ASCII validity (`encode_valid_chars`, `encode_is_valid_base32`)
  4. Padding structure and `rstripEq` recovery (`encode_padding`)
  5. 5-byte block homomorphism (`encode_append_mult5`)
  6. Round-trip decoding of encoded data (`decode_encode_roundtrip`, `decode?_encode_roundtrip`)
  7. Injectivity of Base32 encoding (`encode_injective`)
  8. Casefold insensitivity (`decode_casefold`, `decode_lowercase_roundtrip`)
  9. `map01` character mapping (`decode_map01`)
  10. Validity and error characterization (`decode_valid`, `decode_length`)
- Post-condition (`Post_prop`), property-based tests (Plausible randomized PBTs and bounded PBTs),
  and the main correctness theorem (`correctness_thm : Pre s → Post_prop s`).
- Imperative implementations (`b32encode_imp`, `b32decode?_imp`, `b32decode_imp`) using
  `Id.run do` with mutable state, imperative unit tests, and proven functional-imperative
  equivalence theorems (`b32encode_equiv_thm`, `b32decode?_equiv_thm`, `b32decode_equiv_thm`).
-/

namespace «23_base32»

/-! ## 1. Implementation (Functional Definitions) -/

/-- A sequence of bytes, representing Python's `bytes` / `bytearray`. -/
abbrev Bytes := List UInt8

/-- Convert a Lean `String` to `Bytes` via its UTF-8 byte representation. -/
def stringToBytes (s : String) : Bytes :=
  s.toUTF8.data.toList

instance : Coe String Bytes where
  coe := stringToBytes

/-- The standard Base32 alphabet `b'ABCDEFGHIJKLMNOPQRSTUVWXYZ234567'`. -/
def b32alphabet : Bytes :=
  stringToBytes "ABCDEFGHIJKLMNOPQRSTUVWXYZ234567"

/-- Direct formula for the `idx`-th character of the Base32 alphabet (`0 ≤ idx < 32`).
Indices `0..25` map to `'A'..'Z'` (`65..90`) and `26..31` map to `'2'..'7'` (`50..55`). -/
def b32Char (idx : Nat) : UInt8 :=
  if idx < 26 then UInt8.ofNat (65 + idx) else UInt8.ofNat (24 + idx)

/-- Reverse lookup table mapping a Base32 ASCII byte to its 5-bit index `0..31`,
or `none` if the byte is not in `_b32alphabet`. -/
def revAlphabet (b : UInt8) : Option Nat :=
  let n := b.toNat
  if 65 ≤ n ∧ n ≤ 90 then some (n - 65)
  else if 50 ≤ n ∧ n ≤ 55 then some (n - 24)
  else none

/-- Combine a 5-byte chunk into a 40-bit big-endian natural number (`int.from_bytes(chunk, 'big')`). -/
def chunkVal (b0 b1 b2 b3 b4 : UInt8) : Nat :=
  b0.toNat * 2^32 + b1.toNat * 2^24 + b2.toNat * 2^16 + b3.toNat * 2^8 + b4.toNat

/-- Encode a 5-byte chunk into 8 Base32 bytes by extracting eight 5-bit indices. -/
def encodeChunk5 (b0 b1 b2 b3 b4 : UInt8) : Bytes :=
  let val := chunkVal b0 b1 b2 b3 b4
  [ b32Char ((val / 2^35) % 32),
    b32Char ((val / 2^30) % 32),
    b32Char ((val / 2^25) % 32),
    b32Char ((val / 2^20) % 32),
    b32Char ((val / 2^15) % 32),
    b32Char ((val / 2^10) % 32),
    b32Char ((val / 2^5) % 32),
    b32Char (val % 32) ]

/-- Process 5-byte chunks of `s`, zero-padding any trailing chunk of `< 5` bytes to 5 bytes,
and emitting 8 Base32 characters per chunk prior to `=` padding replacement. -/
def b32encodeRaw : Bytes → Bytes
  | [] => []
  | [b0] => encodeChunk5 b0 0 0 0 0
  | [b0, b1] => encodeChunk5 b0 b1 0 0 0
  | [b0, b1, b2] => encodeChunk5 b0 b1 b2 0 0
  | [b0, b1, b2, b3] => encodeChunk5 b0 b1 b2 b3 0
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest => encodeChunk5 b0 b1 b2 b3 b4 ++ b32encodeRaw rest

/-- Number of trailing `'='` (`61`) padding bytes required for remainder `rem = len(s) % 5`. -/
def padCount (rem : Nat) : Nat :=
  if rem == 1 then 6
  else if rem == 2 then 4
  else if rem == 3 then 3
  else if rem == 4 then 1
  else 0

/-- Replace the trailing `padCount rem` bytes of `encoded` with `'='` (`61`). -/
def fixPadding (rem : Nat) (encoded : Bytes) : Bytes :=
  let p := padCount rem
  encoded.take (encoded.length - p) ++ List.replicate p 61

/-- Encode `s` using Base32 (`b32encode`). -/
def b32encode (s : Bytes) : Bytes :=
  fixPadding (s.length % 5) (b32encodeRaw s)

/-- Unpadded Base32 output (all non-`'='` characters emitted by `b32encode`). -/
def b32encodeUnpadded : Bytes → Bytes
  | [] => []
  | [b0] => (encodeChunk5 b0 0 0 0 0).take 2
  | [b0, b1] => (encodeChunk5 b0 b1 0 0 0).take 4
  | [b0, b1, b2] => (encodeChunk5 b0 b1 b2 0 0).take 5
  | [b0, b1, b2, b3] => (encodeChunk5 b0 b1 b2 b3 0).take 7
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest => encodeChunk5 b0 b1 b2 b3 b4 ++ b32encodeUnpadded rest

/-- Convert an ASCII lowercase byte (`'a'..'z'`, `97..122`) to uppercase (`'A'..'Z'`, `65..90`). -/
def toUpperByte (b : UInt8) : UInt8 :=
  if 97 ≤ b.toNat ∧ b.toNat ≤ 122 then UInt8.ofNat (b.toNat - 32) else b

/-- Convert an ASCII uppercase byte (`'A'..'Z'`, `65..90`) to lowercase (`'a'..'z'`, `97..122`). -/
def toLowerByte (b : UInt8) : UInt8 :=
  if 65 ≤ b.toNat ∧ b.toNat ≤ 90 then UInt8.ofNat (b.toNat + 32) else b

/-- Apply Python's `s.replace(b'0', b'O').replace(b'1', map01)` to a single byte. -/
def applyMap01Byte (m : UInt8) (c : UInt8) : UInt8 :=
  let c1 := if c == 48 then 79 else c
  if c1 == 49 then m else c1

/-- Strip trailing `'='` (`61`) bytes from the right end of a byte list (`s.rstrip(b'=')`). -/
def rstripEq : Bytes → Bytes
  | [] => []
  | x :: xs =>
    let r := rstripEq xs
    if r.isEmpty && x == 61 then [] else x :: r

/-- Pre-process input bytes for `b32decode`: apply optional `map01`, optional `casefold`,
and strip trailing `'='` padding. -/
def preprocessDecode (s : Bytes) (casefold : Bool := false) (map01 : Option UInt8 := none) : Bytes :=
  let s1 := match map01 with
    | none => s
    | some m => s.map (applyMap01Byte m)
  let s2 := if casefold then s1.map toUpperByte else s1
  rstripEq s2

/-- Bit-accumulation loop of `b32decode`. Returns `none` if any byte is outside `_b32alphabet`
(corresponding to `raise binascii.Error('Non-base32 digit found')`). -/
def decodeChars : Bytes → Nat → Nat → Bytes → Option Bytes
  | [], _, _, acc => some acc
  | c :: cs, val, bits, acc =>
    match revAlphabet c with
    | none => none
    | some d =>
      let val' := val * 32 + d
      let bits' := bits + 5
      if bits' ≥ 8 then
        let bits'' := bits' - 8
        let outByte := UInt8.ofNat ((val' / 2 ^ bits'') % 256)
        decodeChars cs val' bits'' (acc ++ [outByte])
      else
        decodeChars cs val' bits' acc

/-- Option-valued Base32 decoder (`b32decode?`): returns `some decoded` when all post-processed
bytes are valid Base32 digits, and `none` when a non-Base32 digit is encountered. -/
def b32decode? (s : Bytes) (casefold : Bool := false) (map01 : Option UInt8 := none) : Option Bytes :=
  decodeChars (preprocessDecode s casefold map01) 0 0 []

/-- Total Base32 decoder (`b32decode`): returns the decoded bytes for valid Base32 inputs
(and `[]` if `b32decode?` returns `none`). -/
def b32decode (s : Bytes) (casefold : Bool := false) (map01 : Option UInt8 := none) : Bytes :=
  (b32decode? s casefold map01).getD []

/-- Check whether every byte of `s` (after `map01`, `casefold`, and `rstripEq`) belongs to `_b32alphabet`. -/
def isValidBase32 (s : Bytes) (casefold : Bool := false) (map01 : Option UInt8 := none) : Bool :=
  (preprocessDecode s casefold map01).all (fun c => (revAlphabet c).isSome)

/-- Python's `pre_encode(s)`: true for any bytes-like object (`Bytes`). -/
def pre_encode (_s : Bytes) : Bool := true

/-- Python's `pre_decode(s)` for byte sequences / ASCII strings. -/
def pre_decode (s : Bytes) : Bool :=
  s.all (fun b => b.toNat < 256)

/-- Check if a `String` is pure ASCII (`s.isascii()`). -/
def isAsciiString (s : String) : Bool :=
  s.data.all (fun c => c.toNat < 128)

/-- Python's `benchmark_b32encode(s)`. -/
def benchmark_b32encode (s : Bytes) : Bytes :=
  if !pre_encode s then b32encode s else b32encode s

/-- Python's `benchmark_b32decode(s, casefold=False, map01=None)`. -/
def benchmark_b32decode (s : Bytes) (casefold : Bool := false) (map01 : Option UInt8 := none) : Bytes :=
  if !pre_decode s then b32decode s casefold map01 else b32decode s casefold map01

/-- Executable test suite matching Python's `check(enc, dec)`. -/
def check (enc : Bytes → Bytes) (dec : Bytes → Bool → Option UInt8 → Bytes) : Bool :=
  enc ("" : Bytes) == ("" : Bytes) &&
  enc ("f" : Bytes) == ("MY======" : Bytes) &&
  enc ("fo" : Bytes) == ("MZXQ====" : Bytes) &&
  enc ("foo" : Bytes) == ("MZXW6===" : Bytes) &&
  enc ("foob" : Bytes) == ("MZXW6YQ=" : Bytes) &&
  enc ("fooba" : Bytes) == ("MZXW6YTB" : Bytes) &&
  enc ("foobar" : Bytes) == ("MZXW6YTBOI======" : Bytes) &&
  let msg : Bytes := "VeriBench"
  dec (enc msg) false none == msg &&
  dec ("mzxw6ytb" : Bytes) true none == ("fooba" : Bytes)

/-! ## 2. Unit Tests -/

example : b32encode ("" : Bytes) = ("" : Bytes) := by native_decide
example : b32encode ("f" : Bytes) = ("MY======" : Bytes) := by native_decide
example : b32encode ("fo" : Bytes) = ("MZXQ====" : Bytes) := by native_decide
example : b32encode ("foo" : Bytes) = ("MZXW6===" : Bytes) := by native_decide
example : b32encode ("foob" : Bytes) = ("MZXW6YQ=" : Bytes) := by native_decide
example : b32encode ("fooba" : Bytes) = ("MZXW6YTB" : Bytes) := by native_decide
example : b32encode ("foobar" : Bytes) = ("MZXW6YTBOI======" : Bytes) := by native_decide

example : b32decode (b32encode ("VeriBench" : Bytes)) = ("VeriBench" : Bytes) := by native_decide
example : b32decode ("mzxw6ytb" : Bytes) true none = ("fooba" : Bytes) := by native_decide
example : b32decode? ("mzxw6ytb" : Bytes) false none = none := by native_decide
example : b32decode ("MZXW6YTB" : Bytes) false none = ("fooba" : Bytes) := by native_decide
example : b32decode ("01" : Bytes) false (some 73) = b32decode ("OI" : Bytes) false none := by native_decide
example : check benchmark_b32encode (fun s cf m => benchmark_b32decode s cf m) = true := by native_decide

#eval b32encode ("foobar" : Bytes)
#eval b32decode (b32encode ("VeriBench" : Bytes))
#eval b32decode ("mzxw6ytb" : Bytes) true none
#eval check benchmark_b32encode (fun s cf m => benchmark_b32decode s cf m)

/-! ## 3. Pre-condition Predicate -/

/-- Pre-condition for Base32 encoding and round-trip verification:
any byte sequence `s : Bytes` (`List UInt8`) is a valid bytes-like object. -/
def Pre (s : Bytes) : Prop :=
  ∀ b ∈ s, b.toNat < 256

theorem pre_holds (s : Bytes) : Pre s := by
  intro b _
  exact b.toNat_lt

/-! ## 4. Helper Lemmas for Verification -/

lemma b32Char_toNat (idx : Nat) (h : idx < 32) :
    (b32Char idx).toNat = if idx < 26 then 65 + idx else 24 + idx := by
  unfold b32Char
  split_ifs <;> simp <;> omega

lemma revAlphabet_b32Char (idx : Nat) (h : idx < 32) :
    revAlphabet (b32Char idx) = some idx := by
  unfold revAlphabet
  rw [b32Char_toNat idx h]
  by_cases h26 : idx < 26
  · rw [if_pos h26, if_pos (by omega)]
    congr 1; omega
  · rw [if_neg h26, if_neg (by omega), if_pos (by omega)]
    congr 1; omega

lemma revAlphabet_isSome_b32Char (idx : Nat) (h : idx < 32) :
    (revAlphabet (b32Char idx)).isSome = true := by
  rw [revAlphabet_b32Char idx h]
  rfl

lemma b32Char_lt_128 (idx : Nat) (h : idx < 32) :
    (b32Char idx).toNat < 128 := by
  rw [b32Char_toNat idx h]
  split_ifs <;> omega

lemma b32Char_ne_eq (idx : Nat) (h : idx < 32) :
    (b32Char idx == 61) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have h1 : (b32Char idx).toNat = (61 : UInt8).toNat := congrArg UInt8.toNat heq
  rw [b32Char_toNat idx h] at h1
  change (if idx < 26 then 65 + idx else 24 + idx) = 61 at h1
  split_ifs at h1 <;> omega

lemma toUpperByte_toNat (b : UInt8) :
    (toUpperByte b).toNat = if 97 ≤ b.toNat ∧ b.toNat ≤ 122 then b.toNat - 32 else b.toNat := by
  have hb : b.toNat < 256 := b.toNat_lt
  unfold toUpperByte
  split_ifs
  · simp; omega
  · rfl

lemma toLowerByte_toNat (b : UInt8) :
    (toLowerByte b).toNat = if 65 ≤ b.toNat ∧ b.toNat ≤ 90 then b.toNat + 32 else b.toNat := by
  have hb : b.toNat < 256 := b.toNat_lt
  unfold toLowerByte
  split_ifs
  · simp; omega
  · rfl

lemma toUpperByte_toLowerByte (b : UInt8) :
    toUpperByte (toLowerByte b) = toUpperByte b := by
  have hb : b.toNat < 256 := b.toNat_lt
  apply UInt8.ext
  rw [toUpperByte_toNat, toLowerByte_toNat, toUpperByte_toNat]
  split_ifs <;> omega

lemma toUpperByte_idempotent (b : UInt8) :
    toUpperByte (toUpperByte b) = toUpperByte b := by
  have hb : b.toNat < 256 := b.toNat_lt
  apply UInt8.ext
  rw [toUpperByte_toNat, toUpperByte_toNat]
  split_ifs <;> omega

lemma toUpperByte_b32Char (idx : Nat) (h : idx < 32) :
    toUpperByte (b32Char idx) = b32Char idx := by
  apply UInt8.ext
  rw [toUpperByte_toNat, b32Char_toNat idx h]
  split_ifs <;> omega

lemma toUpperByte_eq_char : toUpperByte 61 = 61 := rfl
lemma toLowerByte_eq_char : toLowerByte 61 = 61 := rfl

lemma encodeChunk5_length (b0 b1 b2 b3 b4 : UInt8) :
    (encodeChunk5 b0 b1 b2 b3 b4).length = 8 := rfl

lemma b32encodeRaw_length (s : Bytes) :
    (b32encodeRaw s).length = ((s.length + 4) / 5) * 8 := by
  induction s using b32encodeRaw.induct with
  | case1 => rfl
  | case2 b0 => simp [b32encodeRaw, encodeChunk5_length]
  | case3 b0 b1 => simp [b32encodeRaw, encodeChunk5_length]
  | case4 b0 b1 b2 => simp [b32encodeRaw, encodeChunk5_length]
  | case5 b0 b1 b2 b3 => simp [b32encodeRaw, encodeChunk5_length]
  | case6 b0 b1 b2 b3 b4 rest ih =>
    simp only [b32encodeRaw, List.length_append, encodeChunk5_length, ih, List.length_cons]
    omega

lemma b32encodeRaw_nonempty_length (s : Bytes) (hs : s ≠ []) :
    8 ≤ (b32encodeRaw s).length := by
  have hpos : 0 < s.length := List.length_pos_iff.mpr hs
  rw [b32encodeRaw_length]
  omega

lemma padCount_le_six (rem : Nat) : padCount rem ≤ 6 := by
  unfold padCount
  split_ifs <;> omega

lemma b32encode_cons5 (b0 b1 b2 b3 b4 : UInt8) (rest : Bytes) :
    b32encode (b0 :: b1 :: b2 :: b3 :: b4 :: rest) =
      encodeChunk5 b0 b1 b2 b3 b4 ++ b32encode rest := by
  by_cases hrest : rest = []
  · subst hrest
    simp [b32encode, fixPadding, padCount, b32encodeRaw]
  · have hlen : 8 ≤ (b32encodeRaw rest).length := b32encodeRaw_nonempty_length rest hrest
    have hmod : (b0 :: b1 :: b2 :: b3 :: b4 :: rest).length % 5 = rest.length % 5 := by
      simp only [List.length_cons]
      omega
    have hp : padCount (rest.length % 5) ≤ 6 := padCount_le_six _
    unfold b32encode fixPadding
    rw [hmod]
    dsimp only [b32encodeRaw]
    rw [List.length_append, List.take_append, encodeChunk5_length]
    have h1 : (encodeChunk5 b0 b1 b2 b3 b4).length ≤ 8 + (b32encodeRaw rest).length - padCount (rest.length % 5) := by
      rw [encodeChunk5_length]; omega
    rw [List.take_of_length_le h1]
    have h2 : 8 + (b32encodeRaw rest).length - padCount (rest.length % 5) - 8 =
        (b32encodeRaw rest).length - padCount (rest.length % 5) := by omega
    rw [h2, List.append_assoc]

lemma b32encode_eq_unpadded_append_pad (s : Bytes) :
    b32encode s = b32encodeUnpadded s ++ List.replicate (padCount (s.length % 5)) 61 := by
  induction s using b32encodeUnpadded.induct with
  | case1 => rfl
  | case2 b0 => rfl
  | case3 b0 b1 => rfl
  | case4 b0 b1 b2 => rfl
  | case5 b0 b1 b2 b3 => rfl
  | case6 b0 b1 b2 b3 b4 rest ih =>
    have hmod : (b0 :: b1 :: b2 :: b3 :: b4 :: rest).length % 5 = rest.length % 5 := by
      simp only [List.length_cons]; omega
    rw [b32encode_cons5, ih, hmod]
    simp [b32encodeUnpadded, List.append_assoc]

lemma mem_encodeChunk5_exists_idx (b0 b1 b2 b3 b4 : UInt8) (x : UInt8)
    (hx : x ∈ encodeChunk5 b0 b1 b2 b3 b4) :
    ∃ idx < 32, x = b32Char idx := by
  dsimp only [encodeChunk5] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, Nat.mod_lt _ (by decide), rfl⟩

lemma mem_b32encodeUnpadded_exists_idx (s : Bytes) (x : UInt8)
    (hx : x ∈ b32encodeUnpadded s) :
    ∃ idx < 32, x = b32Char idx := by
  induction s using b32encodeUnpadded.induct with
  | case1 => simp [b32encodeUnpadded] at hx
  | case2 b0 =>
    exact mem_encodeChunk5_exists_idx b0 0 0 0 0 x (List.mem_of_mem_take hx)
  | case3 b0 b1 =>
    exact mem_encodeChunk5_exists_idx b0 b1 0 0 0 x (List.mem_of_mem_take hx)
  | case4 b0 b1 b2 =>
    exact mem_encodeChunk5_exists_idx b0 b1 b2 0 0 x (List.mem_of_mem_take hx)
  | case5 b0 b1 b2 b3 =>
    exact mem_encodeChunk5_exists_idx b0 b1 b2 b3 0 x (List.mem_of_mem_take hx)
  | case6 b0 b1 b2 b3 b4 rest ih =>
    simp only [b32encodeUnpadded, List.mem_append] at hx
    rcases hx with hx1 | hx2
    · exact mem_encodeChunk5_exists_idx b0 b1 b2 b3 b4 x hx1
    · exact ih hx2

lemma mem_b32encodeUnpadded_ne_eq (s : Bytes) (x : UInt8) (hx : x ∈ b32encodeUnpadded s) :
    (x == 61) = false := by
  rcases mem_b32encodeUnpadded_exists_idx s x hx with ⟨idx, hidx, rfl⟩
  exact b32Char_ne_eq idx hidx

lemma rstripEq_replicate (k : Nat) : rstripEq (List.replicate k 61) = [] := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, rstripEq, ih]

lemma rstripEq_append_replicate (xs : Bytes) (k : Nat) (hxs : ∀ x ∈ xs, (x == 61) = false) :
    rstripEq (xs ++ List.replicate k 61) = xs := by
  induction xs with
  | nil => simp [rstripEq_replicate]
  | cons x xs ih =>
    have hx : (x == 61) = false := hxs x (by simp)
    have hrest : ∀ y ∈ xs, (y == 61) = false := fun y hy => hxs y (by simp [hy])
    simp [List.cons_append, rstripEq, hx, ih hrest]

lemma rstripEq_b32encode (s : Bytes) : rstripEq (b32encode s) = b32encodeUnpadded s := by
  rw [b32encode_eq_unpadded_append_pad]
  exact rstripEq_append_replicate _ _ (mem_b32encodeUnpadded_ne_eq s)

lemma map_eq_self_of_forall (xs : Bytes) (f : UInt8 → UInt8) (h : ∀ x ∈ xs, f x = x) :
    xs.map f = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

lemma map_toUpperByte_b32encodeUnpadded (s : Bytes) :
    (b32encodeUnpadded s).map toUpperByte = b32encodeUnpadded s := by
  apply map_eq_self_of_forall
  intro x hx
  rcases mem_b32encodeUnpadded_exists_idx s x hx with ⟨idx, hidx, rfl⟩
  exact toUpperByte_b32Char idx hidx

lemma map_toUpperByte_b32encode (s : Bytes) :
    (b32encode s).map toUpperByte = b32encode s := by
  rw [b32encode_eq_unpadded_append_pad, List.map_append, map_toUpperByte_b32encodeUnpadded]
  simp [List.map_replicate, toUpperByte_eq_char]

lemma map_toUpperByte_map_toLowerByte (xs : Bytes) :
    (xs.map toLowerByte).map toUpperByte = xs.map toUpperByte := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [toUpperByte_toLowerByte, ih]

lemma decodeChars_b32Char_lt (idx : Nat) (h : idx < 32) (cs : Bytes) (val bits : Nat) (acc : Bytes)
    (hb : ¬ (bits + 5 ≥ 8)) :
    decodeChars (b32Char idx :: cs) val bits acc =
      decodeChars cs (val * 32 + idx) (bits + 5) acc := by
  simp only [decodeChars, revAlphabet_b32Char idx h, hb, ↓reduceIte]

lemma decodeChars_b32Char_ge (idx : Nat) (h : idx < 32) (cs : Bytes) (val bits : Nat) (acc : Bytes)
    (hb : bits + 5 ≥ 8) :
    decodeChars (b32Char idx :: cs) val bits acc =
      decodeChars cs (val * 32 + idx) (bits + 5 - 8)
        (acc ++ [UInt8.ofNat (((val * 32 + idx) / 2 ^ (bits + 5 - 8)) % 256)]) := by
  simp only [decodeChars, revAlphabet_b32Char idx h, hb, ↓reduceIte]

lemma uint8_ofNat_div_mod_eq (x : Nat) (b : UInt8) (h : x % 256 = b.toNat) :
    UInt8.ofNat (x % 256) = b := by
  rw [h, UInt8.ofNat_toNat]

lemma decodeChars_encodeChunk1 (b0 : UInt8) (val : Nat) (acc : Bytes) :
    decodeChars ((encodeChunk5 b0 0 0 0 0).take 2) val 0 acc = some (acc ++ [b0]) := by
  have h0 : b0.toNat < 256 := b0.toNat_lt
  let v := chunkVal b0 0 0 0 0
  have hm (k : Nat) : (v / k) % 32 < 32 := Nat.mod_lt _ (by decide)
  dsimp only [encodeChunk5, List.take]
  rw [decodeChars_b32Char_lt _ (hm _) _ _ _ _ (by decide)]
  rw [decodeChars_b32Char_ge _ (hm _) _ _ _ _ (by decide)]
  dsimp only [decodeChars]
  have eb0 :
    let c0 := (v / 2^35) % 32
    let c1 := (v / 2^30) % 32
    let v0 := val * 32 + c0
    let v1 := v0 * 32 + c1
    (v1 / 2 ^ (0 + 5 + 5 - 8)) % 256 = b0.toNat := by
    dsimp only [v, chunkVal]
    have hzero : (0 : UInt8).toNat = 0 := rfl
    rw [hzero]
    omega
  rw [uint8_ofNat_div_mod_eq _ b0 eb0]

lemma decodeChars_encodeChunk2 (b0 b1 : UInt8) (val : Nat) (acc : Bytes) :
    decodeChars ((encodeChunk5 b0 b1 0 0 0).take 4) val 0 acc = some (acc ++ [b0, b1]) := by
  have h0 : b0.toNat < 256 := b0.toNat_lt
  have h1 : b1.toNat < 256 := b1.toNat_lt
  let v := chunkVal b0 b1 0 0 0
  have hm (k : Nat) : (v / k) % 32 < 32 := Nat.mod_lt _ (by decide)
  dsimp only [encodeChunk5, List.take]
  rw [decodeChars_b32Char_lt _ (hm _) _ _ _ _ (by decide)]
  rw [decodeChars_b32Char_ge _ (hm _) _ _ _ _ (by decide)]
  rw [decodeChars_b32Char_lt _ (hm _) _ _ _ _ (by decide)]
  rw [decodeChars_b32Char_ge _ (hm _) _ _ _ _ (by decide)]
  dsimp only [decodeChars]
  have hb :
    let c0 := (v / 2^35) % 32
    let c1 := (v / 2^30) % 32
    let c2 := (v / 2^25) % 32
    let c3 := (v / 2^20) % 32
    let v0 := val * 32 + c0
    let v1 := v0 * 32 + c1
    let v2 := v1 * 32 + c2
    let v3 := v2 * 32 + c3
    (v1 / 2 ^ (0 + 5 + 5 - 8)) % 256 = b0.toNat ∧
    (v3 / 2 ^ (0 + 5 + 5 - 8 + 5 + 5 - 8)) % 256 = b1.toNat := by
    dsimp only [v, chunkVal]
    have hzero : (0 : UInt8).toNat = 0 := rfl
    rw [hzero]
    omega
  rcases hb with ⟨eb0, eb1⟩
  rw [uint8_ofNat_div_mod_eq _ b0 eb0, uint8_ofNat_div_mod_eq _ b1 eb1]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

lemma decodeChars_encodeChunk3 (b0 b1 b2 : UInt8) (val : Nat) (acc : Bytes) :
    decodeChars ((encodeChunk5 b0 b1 b2 0 0).take 5) val 0 acc = some (acc ++ [b0, b1, b2]) := by
  have h0 : b0.toNat < 256 := b0.toNat_lt
  have h1 : b1.toNat < 256 := b1.toNat_lt
  have h2 : b2.toNat < 256 := b2.toNat_lt
  let v := chunkVal b0 b1 b2 0 0
  have hm (k : Nat) : (v / k) % 32 < 32 := Nat.mod_lt _ (by decide)
  dsimp only [encodeChunk5, List.take]
  rw [decodeChars_b32Char_lt _ (hm _) _ _ _ _ (by decide)]
  rw [decodeChars_b32Char_ge _ (hm _) _ _ _ _ (by decide)]
  rw [decodeChars_b32Char_lt _ (hm _) _ _ _ _ (by decide)]
  rw [decodeChars_b32Char_ge _ (hm _) _ _ _ _ (by decide)]
  rw [decodeChars_b32Char_ge _ (hm _) _ _ _ _ (by decide)]
  dsimp only [decodeChars]
  have hb :
    let c0 := (v / 2^35) % 32
    let c1 := (v / 2^30) % 32
    let c2 := (v / 2^25) % 32
    let c3 := (v / 2^20) % 32
    let c4 := (v / 2^15) % 32
    let v0 := val * 32 + c0
    let v1 := v0 * 32 + c1
    let v2 := v1 * 32 + c2
    let v3 := v2 * 32 + c3
    let v4 := v3 * 32 + c4
    (v1 / 2 ^ (0 + 5 + 5 - 8)) % 256 = b0.toNat ∧
    (v3 / 2 ^ (0 + 5 + 5 - 8 + 5 + 5 - 8)) % 256 = b1.toNat ∧
    (v4 / 2 ^ (0 + 5 + 5 - 8 + 5 + 5 - 8 + 5 - 8)) % 256 = b2.toNat := by
    dsimp only [v, chunkVal]
    have hzero : (0 : UInt8).toNat = 0 := rfl
    rw [hzero]
    omega
  rcases hb with ⟨eb0, eb1, eb2⟩
  rw [uint8_ofNat_div_mod_eq _ b0 eb0, uint8_ofNat_div_mod_eq _ b1 eb1, uint8_ofNat_div_mod_eq _ b2 eb2]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

lemma decodeChars_encodeChunk4 (b0 b1 b2 b3 : UInt8) (val : Nat) (acc : Bytes) :
    decodeChars ((encodeChunk5 b0 b1 b2 b3 0).take 7) val 0 acc = some (acc ++ [b0, b1, b2, b3]) := by
  have h0 : b0.toNat < 256 := b0.toNat_lt
  have h1 : b1.toNat < 256 := b1.toNat_lt
  have h2 : b2.toNat < 256 := b2.toNat_lt
  have h3 : b3.toNat < 256 := b3.toNat_lt
  let v := chunkVal b0 b1 b2 b3 0
  have hm (k : Nat) : (v / k) % 32 < 32 := Nat.mod_lt _ (by decide)
  dsimp only [encodeChunk5, List.take]
  rw [decodeChars_b32Char_lt _ (hm _) _ _ _ _ (by decide)]
  rw [decodeChars_b32Char_ge _ (hm _) _ _ _ _ (by decide)]
  rw [decodeChars_b32Char_lt _ (hm _) _ _ _ _ (by decide)]
  rw [decodeChars_b32Char_ge _ (hm _) _ _ _ _ (by decide)]
  rw [decodeChars_b32Char_ge _ (hm _) _ _ _ _ (by decide)]
  rw [decodeChars_b32Char_lt _ (hm _) _ _ _ _ (by decide)]
  rw [decodeChars_b32Char_ge _ (hm _) _ _ _ _ (by decide)]
  dsimp only [decodeChars]
  have hb :
    let c0 := (v / 2^35) % 32
    let c1 := (v / 2^30) % 32
    let c2 := (v / 2^25) % 32
    let c3 := (v / 2^20) % 32
    let c4 := (v / 2^15) % 32
    let c5 := (v / 2^10) % 32
    let c6 := (v / 2^5) % 32
    let v0 := val * 32 + c0
    let v1 := v0 * 32 + c1
    let v2 := v1 * 32 + c2
    let v3 := v2 * 32 + c3
    let v4 := v3 * 32 + c4
    let v5 := v4 * 32 + c5
    let v6 := v5 * 32 + c6
    (v1 / 2 ^ (0 + 5 + 5 - 8)) % 256 = b0.toNat ∧
    (v3 / 2 ^ (0 + 5 + 5 - 8 + 5 + 5 - 8)) % 256 = b1.toNat ∧
    (v4 / 2 ^ (0 + 5 + 5 - 8 + 5 + 5 - 8 + 5 - 8)) % 256 = b2.toNat ∧
    (v6 / 2 ^ (0 + 5 + 5 - 8 + 5 + 5 - 8 + 5 - 8 + 5 + 5 - 8)) % 256 = b3.toNat := by
    dsimp only [v, chunkVal]
    have hzero : (0 : UInt8).toNat = 0 := rfl
    rw [hzero]
    omega
  rcases hb with ⟨eb0, eb1, eb2, eb3⟩
  rw [uint8_ofNat_div_mod_eq _ b0 eb0, uint8_ofNat_div_mod_eq _ b1 eb1,
      uint8_ofNat_div_mod_eq _ b2 eb2, uint8_ofNat_div_mod_eq _ b3 eb3]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

lemma decodeChars_encodeChunk5 (b0 b1 b2 b3 b4 : UInt8) (cs : Bytes) (val : Nat) (acc : Bytes) :
    ∃ val', decodeChars (encodeChunk5 b0 b1 b2 b3 b4 ++ cs) val 0 acc =
      decodeChars cs val' 0 (acc ++ [b0, b1, b2, b3, b4]) := by
  have h0 : b0.toNat < 256 := b0.toNat_lt
  have h1 : b1.toNat < 256 := b1.toNat_lt
  have h2 : b2.toNat < 256 := b2.toNat_lt
  have h3 : b3.toNat < 256 := b3.toNat_lt
  have h4 : b4.toNat < 256 := b4.toNat_lt
  let v := chunkVal b0 b1 b2 b3 b4
  have hm (k : Nat) : (v / k) % 32 < 32 := Nat.mod_lt _ (by decide)
  have hm0 : v % 32 < 32 := Nat.mod_lt _ (by decide)
  dsimp only [encodeChunk5, List.cons_append, List.nil_append]
  rw [decodeChars_b32Char_lt _ (hm _) _ _ _ _ (by decide)]
  rw [decodeChars_b32Char_ge _ (hm _) _ _ _ _ (by decide)]
  rw [decodeChars_b32Char_lt _ (hm _) _ _ _ _ (by decide)]
  rw [decodeChars_b32Char_ge _ (hm _) _ _ _ _ (by decide)]
  rw [decodeChars_b32Char_ge _ (hm _) _ _ _ _ (by decide)]
  rw [decodeChars_b32Char_lt _ (hm _) _ _ _ _ (by decide)]
  rw [decodeChars_b32Char_ge _ (hm _) _ _ _ _ (by decide)]
  rw [decodeChars_b32Char_ge _ hm0 _ _ _ _ (by decide)]
  have hb :
    let c0 := (v / 2^35) % 32
    let c1 := (v / 2^30) % 32
    let c2 := (v / 2^25) % 32
    let c3 := (v / 2^20) % 32
    let c4 := (v / 2^15) % 32
    let c5 := (v / 2^10) % 32
    let c6 := (v / 2^5) % 32
    let c7 := v % 32
    let v0 := val * 32 + c0
    let v1 := v0 * 32 + c1
    let v2 := v1 * 32 + c2
    let v3 := v2 * 32 + c3
    let v4 := v3 * 32 + c4
    let v5 := v4 * 32 + c5
    let v6 := v5 * 32 + c6
    let v7 := v6 * 32 + c7
    (v1 / 2 ^ (0 + 5 + 5 - 8)) % 256 = b0.toNat ∧
    (v3 / 2 ^ (0 + 5 + 5 - 8 + 5 + 5 - 8)) % 256 = b1.toNat ∧
    (v4 / 2 ^ (0 + 5 + 5 - 8 + 5 + 5 - 8 + 5 - 8)) % 256 = b2.toNat ∧
    (v6 / 2 ^ (0 + 5 + 5 - 8 + 5 + 5 - 8 + 5 - 8 + 5 + 5 - 8)) % 256 = b3.toNat ∧
    (v7 / 2 ^ (0 + 5 + 5 - 8 + 5 + 5 - 8 + 5 - 8 + 5 + 5 - 8 + 5 - 8)) % 256 = b4.toNat := by
    dsimp only [v, chunkVal]
    omega
  rcases hb with ⟨eb0, eb1, eb2, eb3, eb4⟩
  rw [uint8_ofNat_div_mod_eq _ b0 eb0,
      uint8_ofNat_div_mod_eq _ b1 eb1,
      uint8_ofNat_div_mod_eq _ b2 eb2,
      uint8_ofNat_div_mod_eq _ b3 eb3,
      uint8_ofNat_div_mod_eq _ b4 eb4]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  exact ⟨_, rfl⟩

lemma decodeChars_b32encodeUnpadded (s : Bytes) (val : Nat) (acc : Bytes) :
    decodeChars (b32encodeUnpadded s) val 0 acc = some (acc ++ s) := by
  induction s using b32encodeUnpadded.induct generalizing val acc with
  | case1 => simp [b32encodeUnpadded, decodeChars]
  | case2 b0 => exact decodeChars_encodeChunk1 b0 val acc
  | case3 b0 b1 => exact decodeChars_encodeChunk2 b0 b1 val acc
  | case4 b0 b1 b2 => exact decodeChars_encodeChunk3 b0 b1 b2 val acc
  | case5 b0 b1 b2 b3 => exact decodeChars_encodeChunk4 b0 b1 b2 b3 val acc
  | case6 b0 b1 b2 b3 b4 rest ih =>
    dsimp only [b32encodeUnpadded]
    rcases decodeChars_encodeChunk5 b0 b1 b2 b3 b4 (b32encodeUnpadded rest) val acc with ⟨val', h5⟩
    rw [h5, ih val' (acc ++ [b0, b1, b2, b3, b4])]
    simp only [List.append_assoc, List.cons_append, List.nil_append]

lemma decodeChars_isSome_iff (cs : Bytes) (val bits : Nat) (acc : Bytes) :
    (decodeChars cs val bits acc).isSome = cs.all (fun c => (revAlphabet c).isSome) := by
  induction cs generalizing val bits acc with
  | nil => rfl
  | cons c cs ih =>
    simp only [decodeChars, List.all_cons]
    cases hrev : revAlphabet c with
    | none => rfl
    | some d =>
      simp only [Option.isSome_some, Bool.true_and]
      by_cases hb : bits + 5 ≥ 8 <;> simp only [hb, ↓reduceIte] <;> exact ih _ _ _

lemma decodeChars_length (cs : Bytes) (val bits : Nat) (acc out : Bytes)
    (hbits : bits < 8) (hdec : decodeChars cs val bits acc = some out) :
    out.length = acc.length + (bits + 5 * cs.length) / 8 := by
  induction cs generalizing val bits acc with
  | nil =>
    simp only [decodeChars, Option.some.injEq] at hdec
    subst hdec
    simp only [List.length_nil]
    omega
  | cons c cs ih =>
    simp only [decodeChars] at hdec
    cases hrev : revAlphabet c with
    | none => rw [hrev] at hdec; contradiction
    | some d =>
      rw [hrev] at hdec
      dsimp only [] at hdec
      by_cases hb : bits + 5 ≥ 8
      · simp only [hb, ↓reduceIte] at hdec
        have hlen := ih (val * 32 + d) (bits + 5 - 8)
          (acc ++ [UInt8.ofNat (((val * 32 + d) / 2 ^ (bits + 5 - 8)) % 256)])
          (by omega) hdec
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢
        omega
      · simp only [hb, ↓reduceIte] at hdec
        have hlen := ih (val * 32 + d) (bits + 5) acc (by omega) hdec
        simp only [List.length_cons] at hlen ⊢
        omega

/-! ## 5. Property Propositions and Theorems -/

/-- Property 1: Empty input encodes and decodes to empty bytes, and only empty input encodes to empty bytes. -/
def encode_empty_prop (s : Bytes) : Prop :=
  b32encode [] = [] ∧ b32decode [] = [] ∧ (b32encode s = [] ↔ s = [])

theorem encode_empty_thm (s : Bytes) : encode_empty_prop s := by
  refine ⟨rfl, rfl, ⟨?_, ?_⟩⟩
  · intro h
    by_contra hs
    have hlen : 8 ≤ (b32encodeRaw s).length := b32encodeRaw_nonempty_length s hs
    have hp : padCount (s.length % 5) ≤ 6 := padCount_le_six _
    have hlen2 : 0 < (b32encode s).length := by
      unfold b32encode fixPadding
      rw [List.length_append, List.length_take, List.length_replicate]
      omega
    rw [h] at hlen2
    contradiction
  · intro h
    subst h
    rfl

/-- Property 2: The length of `b32encode s` is `((s.length + 4) / 5) * 8`, which is always a multiple of 8. -/
def encode_length_prop (s : Bytes) : Prop :=
  (b32encode s).length = ((s.length + 4) / 5) * 8 ∧ (b32encode s).length % 8 = 0

theorem encode_length_thm (s : Bytes) : encode_length_prop s := by
  unfold encode_length_prop
  have h1 : (b32encode s).length = (b32encodeRaw s).length := by
    by_cases hs : s = []
    · subst hs; rfl
    · have hlen : 8 ≤ (b32encodeRaw s).length := b32encodeRaw_nonempty_length s hs
      have hp : padCount (s.length % 5) ≤ 6 := padCount_le_six _
      unfold b32encode fixPadding
      rw [List.length_append, List.length_take, List.length_replicate]
      omega
  rw [h1, b32encodeRaw_length]
  exact ⟨rfl, by omega⟩

/-- Property 3: Every byte in `b32encode s` is either a valid Base32 alphabet byte or `'='` (`61`),
is ASCII (`< 128`), and `b32encode s` is always a valid Base32 string for `b32decode`. -/
def encode_valid_chars_prop (s : Bytes) : Prop :=
  (∀ b ∈ b32encode s, ((revAlphabet b).isSome = true ∨ b = 61) ∧ b.toNat < 128) ∧
  isValidBase32 (b32encode s) false none = true

theorem encode_valid_chars_thm (s : Bytes) : encode_valid_chars_prop s := by
  refine ⟨?_, ?_⟩
  · intro b hb
    rw [b32encode_eq_unpadded_append_pad, List.mem_append] at hb
    rcases hb with hb1 | hb2
    · rcases mem_b32encodeUnpadded_exists_idx s b hb1 with ⟨idx, hidx, rfl⟩
      exact ⟨Or.inl (revAlphabet_isSome_b32Char idx hidx), b32Char_lt_128 idx hidx⟩
    · rw [List.mem_replicate] at hb2
      rcases hb2 with ⟨_, rfl⟩
      exact ⟨Or.inr rfl, by decide⟩
  · unfold isValidBase32 preprocessDecode
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [rstripEq_b32encode, List.all_eq_true]
    intro x hx
    rcases mem_b32encodeUnpadded_exists_idx s x hx with ⟨idx, hidx, rfl⟩
    exact revAlphabet_isSome_b32Char idx hidx

/-- Property 4: Padding structure of `b32encode s`: `b32encode s` decomposes into `b32encodeUnpadded s`
(which contains no `'='` bytes) followed by `padCount (s.length % 5)` `'='` bytes, and `rstripEq`
recovers `b32encodeUnpadded s`. -/
def encode_padding_prop (s : Bytes) : Prop :=
  b32encode s = b32encodeUnpadded s ++ List.replicate (padCount (s.length % 5)) 61 ∧
  rstripEq (b32encode s) = b32encodeUnpadded s ∧
  (∀ b ∈ b32encodeUnpadded s, b ≠ 61)

theorem encode_padding_thm (s : Bytes) : encode_padding_prop s := by
  refine ⟨b32encode_eq_unpadded_append_pad s, rstripEq_b32encode s, ?_⟩
  intro b hb heq
  have h := mem_b32encodeUnpadded_ne_eq s b hb
  rw [heq] at h
  contradiction

/-- Property 5: 5-byte block homomorphism: whenever `s1.length % 5 = 0`, encoding `s1 ++ s2`
equals `b32encode s1 ++ b32encode s2`. -/
def encode_append_mult5_prop (s1 s2 : Bytes) : Prop :=
  s1.length % 5 = 0 → b32encode (s1 ++ s2) = b32encode s1 ++ b32encode s2

theorem encode_append_mult5_thm (s1 s2 : Bytes) : encode_append_mult5_prop s1 s2 := by
  intro hmod
  induction s1 using b32encodeRaw.induct with
  | case1 => simp [b32encode, fixPadding, padCount, b32encodeRaw]
  | case2 b0 => simp at hmod
  | case3 b0 b1 => simp at hmod
  | case4 b0 b1 b2 => simp at hmod
  | case5 b0 b1 b2 b3 => simp at hmod
  | case6 b0 b1 b2 b3 b4 rest ih =>
    have hrest : rest.length % 5 = 0 := by
      simp only [List.length_cons] at hmod
      omega
    have hcons : (b0 :: b1 :: b2 :: b3 :: b4 :: rest) ++ s2 =
        b0 :: b1 :: b2 :: b3 :: b4 :: (rest ++ s2) := rfl
    rw [hcons, b32encode_cons5, ih hrest, b32encode_cons5, List.append_assoc]

/-- Property 6: Round-trip correctness: `b32decode` and `b32decode?` are left-inverses of `b32encode`
for all byte sequences `s`. -/
def decode_encode_roundtrip_prop (s : Bytes) : Prop :=
  b32decode? (b32encode s) false none = some s ∧
  b32decode (b32encode s) false none = s

theorem decode_encode_roundtrip_thm (s : Bytes) : decode_encode_roundtrip_prop s := by
  have h1 : b32decode? (b32encode s) false none = some s := by
    unfold b32decode? preprocessDecode
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [rstripEq_b32encode, decodeChars_b32encodeUnpadded, List.nil_append]
  refine ⟨h1, ?_⟩
  unfold b32decode
  rw [h1]
  rfl

/-- Property 7: `b32encode` is injective on all byte sequences. -/
def encode_injective_prop (s1 s2 : Bytes) : Prop :=
  b32encode s1 = b32encode s2 → s1 = s2

theorem encode_injective_thm (s1 s2 : Bytes) : encode_injective_prop s1 s2 := by
  intro h
  have h1 := (decode_encode_roundtrip_thm s1).2
  have h2 := (decode_encode_roundtrip_thm s2).2
  rw [← h1, ← h2, h]

/-- Property 8: Casefold decoding: `b32decode` with `casefold = true` decodes both normal
and lowercased `b32encode s` back to `s`, and equals `b32decode` on `s.map toUpperByte`. -/
def decode_casefold_prop (s : Bytes) : Prop :=
  b32decode (b32encode s) true none = s ∧
  b32decode ((b32encode s).map toLowerByte) true none = s ∧
  b32decode s true none = b32decode (s.map toUpperByte) false none

theorem decode_casefold_thm (s : Bytes) : decode_casefold_prop s := by
  have h_upper_false (xs : Bytes) :
      b32decode? xs true none = b32decode? (xs.map toUpperByte) false none := rfl
  have h1 : b32decode (b32encode s) true none = s := by
    unfold b32decode
    rw [h_upper_false, map_toUpperByte_b32encode, (decode_encode_roundtrip_thm s).1]
    rfl
  have h2 : b32decode ((b32encode s).map toLowerByte) true none = s := by
    unfold b32decode
    rw [h_upper_false, map_toUpperByte_map_toLowerByte, map_toUpperByte_b32encode,
        (decode_encode_roundtrip_thm s).1]
    rfl
  refine ⟨h1, h2, rfl⟩

/-- Property 9: `map01` decoding: decoding `s` with `map01 = some m` is equivalent to
mapping `'0' → 'O'` and `'1' → m` and decoding with `map01 = none`. -/
def decode_map01_prop (s : Bytes) (casefold : Bool) (m : UInt8) : Prop :=
  b32decode? s casefold (some m) = b32decode? (s.map (applyMap01Byte m)) casefold none ∧
  b32decode s casefold (some m) = b32decode (s.map (applyMap01Byte m)) casefold none

theorem decode_map01_thm (s : Bytes) (casefold : Bool) (m : UInt8) :
    decode_map01_prop s casefold m :=
  ⟨rfl, rfl⟩

/-- Property 10: Validity and decoded length characterization of `b32decode?` and `b32decode`. -/
def decode_valid_length_prop (s : Bytes) (casefold : Bool) (map01 : Option UInt8) : Prop :=
  (b32decode? s casefold map01).isSome = isValidBase32 s casefold map01 ∧
  (isValidBase32 s casefold map01 = false ↔ b32decode? s casefold map01 = none) ∧
  (isValidBase32 s casefold map01 = true →
    (b32decode s casefold map01).length = (5 * (preprocessDecode s casefold map01).length) / 8)

theorem decode_valid_length_thm (s : Bytes) (casefold : Bool) (map01 : Option UInt8) :
    decode_valid_length_prop s casefold map01 := by
  have his : (b32decode? s casefold map01).isSome = isValidBase32 s casefold map01 := by
    unfold b32decode? isValidBase32
    exact decodeChars_isSome_iff (preprocessDecode s casefold map01) 0 0 []
  refine ⟨his, ?_, ?_⟩
  · rw [← his, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]
  · intro hval
    rw [← his, Option.isSome_iff_exists] at hval
    rcases hval with ⟨out, hout⟩
    unfold b32decode
    rw [hout, Option.getD_some]
    have hlen := decodeChars_length (preprocessDecode s casefold map01) 0 0 [] out (by decide) hout
    simp only [List.length_nil, Nat.zero_add] at hlen
    exact hlen

/-! ## 6. Post-condition -/

/-- Full post-condition for a byte sequence `s`, combining the core encoding and decoding properties. -/
def Post_prop (s : Bytes) : Prop :=
  encode_empty_prop s ∧
  encode_length_prop s ∧
  encode_valid_chars_prop s ∧
  encode_padding_prop s ∧
  encode_append_mult5_prop (s ++ s ++ s ++ s ++ s) s ∧
  decode_encode_roundtrip_prop s ∧
  decode_casefold_prop s ∧
  decode_valid_length_prop (b32encode s) false none

/-! ## 7. Property-Based Tests (PBTs) -/

-- Randomized PBTs via Plausible
#eval Plausible.Testable.check (∀ s : Bytes,
  b32encode [] == [] && b32decode [] == [] && ((b32encode s == []) == (s == [])))

#eval Plausible.Testable.check (∀ s : Bytes,
  (b32encode s).length == ((s.length + 4) / 5) * 8 && (b32encode s).length % 8 == 0)

#eval Plausible.Testable.check (∀ s : Bytes,
  (b32encode s).all (fun b => ((revAlphabet b).isSome || b == 61) && decide (b.toNat < 128)) &&
  isValidBase32 (b32encode s) false none)

#eval Plausible.Testable.check (∀ s : Bytes,
  b32encode s == b32encodeUnpadded s ++ List.replicate (padCount (s.length % 5)) 61 &&
  rstripEq (b32encode s) == b32encodeUnpadded s &&
  (b32encodeUnpadded s).all (fun b => b != 61))

#eval Plausible.Testable.check (∀ b0 b1 b2 b3 b4 : UInt8, ∀ s2 : Bytes,
  let s1 : Bytes := [b0, b1, b2, b3, b4]
  b32encode (s1 ++ s2) == b32encode s1 ++ b32encode s2)

#eval Plausible.Testable.check (∀ s : Bytes,
  b32decode? (b32encode s) false none == some s &&
  b32decode (b32encode s) false none == s)

#eval Plausible.Testable.check (∀ s1 s2 : Bytes,
  (b32encode s1 == b32encode s2) == (s1 == s2))

#eval Plausible.Testable.check (∀ s : Bytes,
  b32decode (b32encode s) true none == s &&
  b32decode ((b32encode s).map toLowerByte) true none == s &&
  b32decode s true none == b32decode (s.map toUpperByte) false none)

#eval Plausible.Testable.check (∀ s : Bytes, ∀ casefold : Bool, ∀ m : UInt8,
  b32decode? s casefold (some m) == b32decode? (s.map (applyMap01Byte m)) casefold none &&
  b32decode s casefold (some m) == b32decode (s.map (applyMap01Byte m)) casefold none)

#eval Plausible.Testable.check (∀ s : Bytes, ∀ casefold : Bool,
  (b32decode? s casefold none).isSome == isValidBase32 s casefold none &&
  (!isValidBase32 s casefold none ||
    (b32decode s casefold none).length == (5 * (preprocessDecode s casefold none).length) / 8))

-- Post-condition PBT
#eval Plausible.Testable.check (∀ s : Bytes,
  (b32encode s).length == ((s.length + 4) / 5) * 8 &&
  isValidBase32 (b32encode s) false none &&
  b32decode (b32encode s) false none == s &&
  b32decode ((b32encode s).map toLowerByte) true none == s)

-- Bounded exhaustive PBTs
example : (List.range 20).all (fun n =>
  let s : Bytes := (List.range n).map UInt8.ofNat
  (b32encode s).length == ((s.length + 4) / 5) * 8 &&
  b32decode (b32encode s) false none == s &&
  b32decode ((b32encode s).map toLowerByte) true none == s) = true := by native_decide

/-! ## 8. Correctness Theorem (`Pre → Post`) -/

theorem correctness_thm (s : Bytes) (_hpre : Pre s) : Post_prop s :=
  ⟨encode_empty_thm s,
   encode_length_thm s,
   encode_valid_chars_thm s,
   encode_padding_thm s,
   encode_append_mult5_thm (s ++ s ++ s ++ s ++ s) s,
   decode_encode_roundtrip_thm s,
   decode_casefold_thm s,
   decode_valid_length_thm (b32encode s) false none⟩

/-! ## 9. Imperative Implementation (`Id.run do` with Mutable State) -/

/-- Partition a byte sequence into consecutive 5-byte chunks (`s[i:i+5]` for `i in range(0, len(s), 5)`). -/
def chunksOf5 : Bytes → List Bytes
  | [] => []
  | [b0] => [[b0]]
  | [b0, b1] => [[b0, b1]]
  | [b0, b1, b2] => [[b0, b1, b2]]
  | [b0, b1, b2, b3] => [[b0, b1, b2, b3]]
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest => [b0, b1, b2, b3, b4] :: chunksOf5 rest

/-- Imperative Base32 encoder following Python's `b32encode` loop and padding fix. -/
def b32encode_imp (s : Bytes) : Bytes := Id.run do
  let mut encoded : Bytes := []
  for chunk in chunksOf5 s do
    let padded :=
      if chunk.length < 5 then
        chunk ++ List.replicate (5 - chunk.length) 0
      else
        chunk
    let val :=
      (padded.getD 0 0).toNat * 2^32 +
      (padded.getD 1 0).toNat * 2^24 +
      (padded.getD 2 0).toNat * 2^16 +
      (padded.getD 3 0).toNat * 2^8 +
      (padded.getD 4 0).toNat
    encoded := encoded ++ [
      b32Char ((val / 2^35) % 32),
      b32Char ((val / 2^30) % 32),
      b32Char ((val / 2^25) % 32),
      b32Char ((val / 2^20) % 32),
      b32Char ((val / 2^15) % 32),
      b32Char ((val / 2^10) % 32),
      b32Char ((val / 2^5) % 32),
      b32Char (val % 32)
    ]
  let rem := s.length % 5
  if rem == 1 then
    encoded := encoded.take (encoded.length - 6) ++ List.replicate 6 61
  else if rem == 2 then
    encoded := encoded.take (encoded.length - 4) ++ List.replicate 4 61
  else if rem == 3 then
    encoded := encoded.take (encoded.length - 3) ++ List.replicate 3 61
  else if rem == 4 then
    encoded := encoded.take (encoded.length - 1) ++ List.replicate 1 61
  return encoded

/-- Single step of the imperative Base32 decoding loop over state `(decoded, val, bits, ok)`. -/
def decodeStepImp (state : Bytes × Nat × Nat × Bool) (c : UInt8) : Bytes × Nat × Nat × Bool :=
  let (decoded, val, bits, ok) := state
  if ok then
    match revAlphabet c with
    | none => (decoded, val, bits, false)
    | some d =>
      let val' := val * 32 + d
      let bits' := bits + 5
      if bits' ≥ 8 then
        let bits'' := bits' - 8
        (decoded ++ [UInt8.ofNat ((val' / 2 ^ bits'') % 256)], val', bits'', true)
      else
        (decoded, val', bits', true)
  else
    (decoded, val, bits, false)

/-- Imperative option-valued Base32 decoder following Python's `b32decode`. -/
def b32decode?_imp (s : Bytes) (casefold : Bool := false) (map01 : Option UInt8 := none) : Option Bytes := Id.run do
  let mut cs : Bytes := s
  if let some m := map01 then
    cs := cs.map (applyMap01Byte m)
  if casefold then
    cs := cs.map toUpperByte
  cs := rstripEq cs
  let mut state : Bytes × Nat × Nat × Bool := ([], 0, 0, true)
  for c in cs do
    state := decodeStepImp state c
  if state.2.2.2 then
    return some state.1
  else
    return none

/-- Imperative Base32 decoder returning `Bytes`. -/
def b32decode_imp (s : Bytes) (casefold : Bool := false) (map01 : Option UInt8 := none) : Bytes :=
  (b32decode?_imp s casefold map01).getD []

/-! ## 10. Imperative Tests -/

example : b32encode_imp ("" : Bytes) = ("" : Bytes) := by native_decide
example : b32encode_imp ("f" : Bytes) = ("MY======" : Bytes) := by native_decide
example : b32encode_imp ("fo" : Bytes) = ("MZXQ====" : Bytes) := by native_decide
example : b32encode_imp ("foo" : Bytes) = ("MZXW6===" : Bytes) := by native_decide
example : b32encode_imp ("foob" : Bytes) = ("MZXW6YQ=" : Bytes) := by native_decide
example : b32encode_imp ("fooba" : Bytes) = ("MZXW6YTB" : Bytes) := by native_decide
example : b32encode_imp ("foobar" : Bytes) = ("MZXW6YTBOI======" : Bytes) := by native_decide
example : b32decode_imp (b32encode_imp ("VeriBench" : Bytes)) = ("VeriBench" : Bytes) := by native_decide
example : b32decode_imp ("mzxw6ytb" : Bytes) true none = ("fooba" : Bytes) := by native_decide
example : check b32encode_imp (fun s cf m => b32decode_imp s cf m) = true := by native_decide

#eval check b32encode_imp (fun s cf m => b32decode_imp s cf m)

/-! ## 11. Equivalence Theorems (Functional = Imperative) -/

def encodeChunkPadded (chunk : Bytes) : Bytes :=
  let padded :=
    if chunk.length < 5 then
      chunk ++ List.replicate (5 - chunk.length) 0
    else
      chunk
  let val :=
    (padded.getD 0 0).toNat * 2^32 +
    (padded.getD 1 0).toNat * 2^24 +
    (padded.getD 2 0).toNat * 2^16 +
    (padded.getD 3 0).toNat * 2^8 +
    (padded.getD 4 0).toNat
  [ b32Char ((val / 2^35) % 32),
    b32Char ((val / 2^30) % 32),
    b32Char ((val / 2^25) % 32),
    b32Char ((val / 2^20) % 32),
    b32Char ((val / 2^15) % 32),
    b32Char ((val / 2^10) % 32),
    b32Char ((val / 2^5) % 32),
    b32Char (val % 32) ]

lemma foldl_chunksOf5 (s : Bytes) (acc : Bytes) :
    (chunksOf5 s).foldl (fun encoded chunk => encoded ++ encodeChunkPadded chunk) acc =
      acc ++ b32encodeRaw s := by
  induction s using chunksOf5.induct generalizing acc with
  | case1 => simp [chunksOf5, b32encodeRaw]
  | case2 b0 => rfl
  | case3 b0 b1 => rfl
  | case4 b0 b1 b2 => rfl
  | case5 b0 b1 b2 b3 => rfl
  | case6 b0 b1 b2 b3 b4 rest ih =>
    simp only [chunksOf5, List.foldl_cons, b32encodeRaw]
    rw [ih]
    simp only [List.append_assoc]
    rfl

set_option linter.deprecated false in
theorem b32encode_equiv_thm (s : Bytes) : b32encode_imp s = b32encode s := by
  unfold b32encode_imp b32encode fixPadding padCount
  simp only [Id.run, List.forIn_yield_eq_foldl, bind, pure]
  have hf : (List.foldl (fun b a => b ++ encodeChunkPadded a) [] (chunksOf5 s)) = b32encodeRaw s := by
    rw [foldl_chunksOf5, List.nil_append]
  change (
    let encoded := List.foldl (fun b a => b ++ encodeChunkPadded a) [] (chunksOf5 s)
    let rem := s.length % 5
    if (rem == 1) = true then encoded.take (encoded.length - 6) ++ List.replicate 6 61
    else if (rem == 2) = true then encoded.take (encoded.length - 4) ++ List.replicate 4 61
    else if (rem == 3) = true then encoded.take (encoded.length - 3) ++ List.replicate 3 61
    else if (rem == 4) = true then encoded.take (encoded.length - 1) ++ List.replicate 1 61
    else encoded) = _
  rw [hf]
  dsimp only []
  split_ifs <;> simp

lemma foldl_decodeStepImp_false (cs : Bytes) (decoded : Bytes) (val bits : Nat) :
    (cs.foldl decodeStepImp (decoded, val, bits, false)).2.2.2 = false := by
  induction cs generalizing decoded val bits with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldl_cons, decodeStepImp, Bool.false_eq_true, ↓reduceIte]
    exact ih decoded val bits

lemma foldl_decodeStepImp_true (cs : Bytes) (decoded : Bytes) (val bits : Nat) :
    (if (cs.foldl decodeStepImp (decoded, val, bits, true)).2.2.2 then
      some (cs.foldl decodeStepImp (decoded, val, bits, true)).1
    else none) = decodeChars cs val bits decoded := by
  induction cs generalizing decoded val bits with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldl_cons, decodeStepImp, ↓reduceIte, decodeChars]
    cases hrev : revAlphabet c with
    | none =>
      dsimp only []
      rw [foldl_decodeStepImp_false]
      rfl
    | some d =>
      dsimp only []
      by_cases hb : bits + 5 ≥ 8 <;> simp only [hb, ↓reduceIte] <;> exact ih _ _ _

set_option linter.deprecated false in
theorem b32decode?_equiv_thm (s : Bytes) (casefold : Bool) (map01 : Option UInt8) :
    b32decode?_imp s casefold map01 = b32decode? s casefold map01 := by
  unfold b32decode?_imp b32decode? preprocessDecode
  cases map01 <;> cases casefold <;>
    simp only [Id.run, List.forIn_yield_eq_foldl, bind, pure, ↓reduceIte, Bool.false_eq_true] <;>
    exact foldl_decodeStepImp_true _ [] 0 0

theorem b32decode_equiv_thm (s : Bytes) (casefold : Bool) (map01 : Option UInt8) :
    b32decode_imp s casefold map01 = b32decode s casefold map01 := by
  unfold b32decode_imp b32decode
  rw [b32decode?_equiv_thm]

end «23_base32»
