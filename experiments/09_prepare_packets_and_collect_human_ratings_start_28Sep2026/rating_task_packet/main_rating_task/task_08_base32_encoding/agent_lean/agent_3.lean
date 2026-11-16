import Mathlib
import Plausible

/-!
# Base32 Encoding and Decoding

Formalization of Python's `base64.b32encode` and `base64.b32decode`.
Provides Base32 encoding and decoding over byte sequences (`List UInt8`),
including `casefold` and `map01` normalization, padding handling,
unit tests, property-based tests, pre/post-conditions, correctness theorems,
and imperative-functional equivalence proofs.
-/

namespace «23_base32»

/-! ## 4. Implementation (Functional Definition) -/

/-- Byte sequence representation corresponding to Python `bytes` / `bytearray`. -/
abbrev Bytes := List UInt8

/-- Convert an ASCII `String` into `Bytes`. -/
def Bytes.ofString (s : String) : Bytes :=
  s.toList.map (fun c => UInt8.ofNat c.toNat)

/-- Convert `Bytes` into a `String` by interpreting each byte as a character code. -/
def Bytes.toString (bs : Bytes) : String :=
  String.ofList (bs.map (fun b => Char.ofNat b.toNat))

/-- The RFC 4648 Base32 alphabet: `b'ABCDEFGHIJKLMNOPQRSTUVWXYZ234567'`. -/
def _b32alphabet : Bytes :=
  Bytes.ofString "ABCDEFGHIJKLMNOPQRSTUVWXYZ234567"

/-- Map a 5-bit index `k` (`0 ≤ k < 32`) to its Base32 ASCII byte. -/
def b32Char (k : Nat) : UInt8 :=
  if k < 26 then UInt8.ofNat (k + 65) else UInt8.ofNat (k + 24)

/-- Inverse Base32 lookup table: returns `some k` (`0 ≤ k < 32`) for valid Base32 bytes,
    and `none` for non-Base32 bytes (corresponding to `raise binascii.Error`). -/
def revB32Char (c : UInt8) : Option Nat :=
  let n := c.toNat
  if 65 ≤ n ∧ n ≤ 90 then some (n - 65)
  else if 50 ≤ n ∧ n ≤ 55 then some (n - 24)
  else none

/-- Combine 5 bytes in big-endian order into a 40-bit natural number (`int.from_bytes(chunk, 'big')`). -/
def intFromBytes5 (b0 b1 b2 b3 b4 : UInt8) : Nat :=
  (((b0.toNat * 256 + b1.toNat) * 256 + b2.toNat) * 256 + b3.toNat) * 256 + b4.toNat

/-- Encode a full 5-byte chunk into 8 Base32 bytes. -/
def encodeChunk5 (b0 b1 b2 b3 b4 : UInt8) : Bytes :=
  let val := intFromBytes5 b0 b1 b2 b3 b4
  [ b32Char ((val / 2^35) % 32),
    b32Char ((val / 2^30) % 32),
    b32Char ((val / 2^25) % 32),
    b32Char ((val / 2^20) % 32),
    b32Char ((val / 2^15) % 32),
    b32Char ((val / 2^10) % 32),
    b32Char ((val / 2^5) % 32),
    b32Char (val % 32) ]

/-- Functional Base32 encoder (`b32encode`).
    Processes 5-byte chunks into 8-character Base32 blocks and pads the final
    incomplete block with `'='` (ASCII 61). -/
def b32encode : Bytes → Bytes
  | [] => []
  | [b0] =>
    let val := intFromBytes5 b0 0 0 0 0
    [ b32Char ((val / 2^35) % 32),
      b32Char ((val / 2^30) % 32),
      61, 61, 61, 61, 61, 61 ]
  | [b0, b1] =>
    let val := intFromBytes5 b0 b1 0 0 0
    [ b32Char ((val / 2^35) % 32),
      b32Char ((val / 2^30) % 32),
      b32Char ((val / 2^25) % 32),
      b32Char ((val / 2^20) % 32),
      61, 61, 61, 61 ]
  | [b0, b1, b2] =>
    let val := intFromBytes5 b0 b1 b2 0 0
    [ b32Char ((val / 2^35) % 32),
      b32Char ((val / 2^30) % 32),
      b32Char ((val / 2^25) % 32),
      b32Char ((val / 2^20) % 32),
      b32Char ((val / 2^15) % 32),
      61, 61, 61 ]
  | [b0, b1, b2, b3] =>
    let val := intFromBytes5 b0 b1 b2 b3 0
    [ b32Char ((val / 2^35) % 32),
      b32Char ((val / 2^30) % 32),
      b32Char ((val / 2^25) % 32),
      b32Char ((val / 2^20) % 32),
      b32Char ((val / 2^15) % 32),
      b32Char ((val / 2^10) % 32),
      b32Char ((val / 2^5) % 32),
      61 ]
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest =>
    encodeChunk5 b0 b1 b2 b3 b4 ++ b32encode rest

/-- Apply `s.replace(b'0', b'O').replace(b'1', map01)` to a single byte. -/
def applyMap01Byte (m : UInt8) (b : UInt8) : UInt8 :=
  let b1 := if b == 48 then 79 else b
  if b1 == 49 then m else b1

/-- Apply optional `map01` substitution across a byte sequence. -/
def applyMap01 (map01 : Option UInt8) (s : Bytes) : Bytes :=
  match map01 with
  | none => s
  | some m => s.map (applyMap01Byte m)

/-- Convert an ASCII lowercase byte (`'a'..'z'`) to uppercase (`'A'..'Z'`). -/
def toUpperByte (b : UInt8) : UInt8 :=
  if 97 ≤ b.toNat ∧ b.toNat ≤ 122 then UInt8.ofNat (b.toNat - 32) else b

/-- Convert an ASCII uppercase byte (`'A'..'Z'`) to lowercase (`'a'..'z'`). -/
def toLowerByte (b : UInt8) : UInt8 :=
  if 65 ≤ b.toNat ∧ b.toNat ≤ 90 then UInt8.ofNat (b.toNat + 32) else b

/-- Apply optional `casefold` (`s.upper()`) across a byte sequence. -/
def applyCasefold (casefold : Bool) (s : Bytes) : Bytes :=
  if casefold then s.map toUpperByte else s

/-- Strip trailing `'='` (ASCII 61) padding bytes (`s.rstrip(b'=')`). -/
def rstripEq : Bytes → Bytes
  | [] => []
  | b :: bs =>
    let rest := rstripEq bs
    if rest.isEmpty && b == 61 then [] else b :: rest

/-- Single 5-bit accumulation step of `b32decode`. -/
def decodeStep (val bits : Nat) (k : Nat) : Nat × Nat × Option UInt8 :=
  let val' := val * 32 + k
  let bits' := bits + 5
  if bits' ≥ 8 then
    let bits'' := bits' - 8
    (val', bits'', some (UInt8.ofNat ((val' / 2 ^ bits'') % 256)))
  else
    (val', bits', none)

/-- Recursive decoding loop over stripped Base32 characters.
    Returns `none` if any non-Base32 character is encountered. -/
def decodeLoop : Bytes → Nat → Nat → Option Bytes
  | [], _, _ => some []
  | c :: cs, val, bits =>
    match revB32Char c with
    | none => none
    | some k =>
      let step := decodeStep val bits k
      match decodeLoop cs step.1 step.2.1 with
      | none => none
      | some rest =>
        match step.2.2 with
        | none => some rest
        | some b => some (b :: rest)

/-- Option-returning Base32 decoder (`b32decode?`).
    Returns `none` iff a non-Base32 digit is encountered after `map01`, `casefold`, and `rstripEq`. -/
def b32decode? (s : Bytes) (casefold : Bool := false) (map01 : Option UInt8 := none) : Option Bytes :=
  let s1 := applyMap01 map01 s
  let s2 := applyCasefold casefold s1
  let s3 := rstripEq s2
  decodeLoop s3 0 0

/-- Total Base32 decoder (`b32decode`), returning `[]` if decoding fails. -/
def b32decode (s : Bytes) (casefold : Bool := false) (map01 : Option UInt8 := none) : Bytes :=
  (b32decode? s casefold map01).getD []

/-- Executable check for whether `s` is a valid Base32 byte sequence under `(casefold, map01)`. -/
def isValidBase32 (s : Bytes) (casefold : Bool := false) (map01 : Option UInt8 := none) : Bool :=
  (rstripEq (applyCasefold casefold (applyMap01 map01 s))).all (fun c => (revB32Char c).isSome)

/-- Executable pre-condition check for `b32encode`. -/
def pre_encode_bool (s : Bytes) : Bool :=
  s.all (fun b => b.toNat < 256)

/-- Executable pre-condition check for `b32decode`. -/
def pre_decode_bool (s : Bytes) : Bool :=
  s.all (fun b => b.toNat < 256)

/-- Main benchmark wrapper for `b32encode`. -/
def benchmark_b32encode (s : Bytes) : Bytes :=
  if !pre_encode_bool s then b32encode s else b32encode s

/-- Main benchmark wrapper for `b32decode`. -/
def benchmark_b32decode (s : Bytes) (casefold : Bool := false) (map01 : Option UInt8 := none) : Bytes :=
  if !pre_decode_bool s then b32decode s casefold map01 else b32decode s casefold map01

/-- Test suite function `check` corresponding to Python's `check(enc, dec)`. -/
def check (enc : Bytes → Bytes) (dec : Bytes → Bool → Option UInt8 → Bytes) : Bool :=
  enc (Bytes.ofString "") == Bytes.ofString "" &&
  enc (Bytes.ofString "f") == Bytes.ofString "MY======" &&
  enc (Bytes.ofString "fo") == Bytes.ofString "MZXQ====" &&
  enc (Bytes.ofString "foo") == Bytes.ofString "MZXW6===" &&
  enc (Bytes.ofString "foob") == Bytes.ofString "MZXW6YQ=" &&
  enc (Bytes.ofString "fooba") == Bytes.ofString "MZXW6YTB" &&
  enc (Bytes.ofString "foobar") == Bytes.ofString "MZXW6YTBOI======" &&
  let msg := Bytes.ofString "VeriBench"
  dec (enc msg) false none == msg &&
  dec (Bytes.ofString "mzxw6ytb") true none == Bytes.ofString "fooba"

/-! ## 5. Unit Tests -/

#eval Bytes.toString (b32encode (Bytes.ofString ""))
#eval Bytes.toString (b32encode (Bytes.ofString "f"))
#eval Bytes.toString (b32encode (Bytes.ofString "fo"))
#eval Bytes.toString (b32encode (Bytes.ofString "foo"))
#eval Bytes.toString (b32encode (Bytes.ofString "foob"))
#eval Bytes.toString (b32encode (Bytes.ofString "fooba"))
#eval Bytes.toString (b32encode (Bytes.ofString "foobar"))
#eval Bytes.toString (b32decode (b32encode (Bytes.ofString "VeriBench")))
#eval Bytes.toString (b32decode (Bytes.ofString "mzxw6ytb") true)
#eval check benchmark_b32encode (fun s c m => benchmark_b32decode s c m)

example : b32encode (Bytes.ofString "") = Bytes.ofString "" := by native_decide
example : b32encode (Bytes.ofString "f") = Bytes.ofString "MY======" := by native_decide
example : b32encode (Bytes.ofString "fo") = Bytes.ofString "MZXQ====" := by native_decide
example : b32encode (Bytes.ofString "foo") = Bytes.ofString "MZXW6===" := by native_decide
example : b32encode (Bytes.ofString "foob") = Bytes.ofString "MZXW6YQ=" := by native_decide
example : b32encode (Bytes.ofString "fooba") = Bytes.ofString "MZXW6YTB" := by native_decide
example : b32encode (Bytes.ofString "foobar") = Bytes.ofString "MZXW6YTBOI======" := by native_decide
example : b32decode (b32encode (Bytes.ofString "VeriBench")) = Bytes.ofString "VeriBench" := by native_decide
example : b32decode? (b32encode (Bytes.ofString "VeriBench")) = some (Bytes.ofString "VeriBench") := by native_decide
example : b32decode (Bytes.ofString "mzxw6ytb") true = Bytes.ofString "fooba" := by native_decide
example : b32decode? (Bytes.ofString "!") = none := by native_decide
example : check benchmark_b32encode (fun s c m => benchmark_b32decode s c m) = true := by native_decide

/-! ## 6. Pre-condition Predicate -/

/-- Pre-condition for `b32encode`: input is a valid sequence of bytes. -/
def pre_encode (s : Bytes) : Prop :=
  ∀ b ∈ s, b.toNat < 256

/-- Pre-condition for `b32decode`: input is a valid sequence of bytes. -/
def pre_decode (s : Bytes) : Prop :=
  ∀ b ∈ s, b.toNat < 256

/-- Combined pre-condition predicate `Pre`. -/
def Pre (s : Bytes) : Prop :=
  pre_encode s

theorem pre_encode_holds (s : Bytes) : pre_encode s :=
  fun b _ => b.toBitVec.isLt

/-! ## 7. Property Propositions and Theorems -/

/-- Helper lemma: `revB32Char` is a left inverse of `b32Char` on `0..31`. -/
theorem revB32Char_b32Char (k : Nat) (hk : k < 32) :
    revB32Char (b32Char k) = some k := by
  unfold b32Char revB32Char
  split_ifs <;> simp only [UInt8.toNat_ofNat'] at * <;> omega

/-- Helper lemma: `b32Char k` is never the padding byte `'='` (61). -/
theorem b32Char_ne_pad (k : Nat) (hk : k < 32) :
    (b32Char k == 61) = false := by
  rw [beq_eq_false_iff_ne]
  unfold b32Char
  intro h
  have h' := congrArg UInt8.toNat h
  split_ifs at h' <;> simp only [UInt8.toNat_ofNat, UInt8.toNat_ofNat'] at h' <;> omega

theorem b32Char_ne_48 (k : Nat) (hk : k < 32) : (b32Char k == 48) = false := by
  rw [beq_eq_false_iff_ne]; unfold b32Char; intro h
  have h' := congrArg UInt8.toNat h
  split_ifs at h' <;> simp only [UInt8.toNat_ofNat, UInt8.toNat_ofNat'] at h' <;> omega

theorem b32Char_ne_49 (k : Nat) (hk : k < 32) : (b32Char k == 49) = false := by
  rw [beq_eq_false_iff_ne]; unfold b32Char; intro h
  have h' := congrArg UInt8.toNat h
  split_ifs at h' <;> simp only [UInt8.toNat_ofNat, UInt8.toNat_ofNat'] at h' <;> omega

theorem applyMap01Byte_b32Char (m : UInt8) (k : Nat) (hk : k < 32) :
    applyMap01Byte m (b32Char k) = b32Char k := by
  simp [applyMap01Byte, b32Char_ne_48 k hk, b32Char_ne_49 k hk]

theorem toUpperByte_b32Char (k : Nat) (hk : k < 32) :
    toUpperByte (b32Char k) = b32Char k := by
  unfold toUpperByte b32Char
  split_ifs <;> simp only [UInt8.toNat_ofNat'] at * <;> omega

theorem toUpperByte_toLowerByte_b32Char (k : Nat) (hk : k < 32) :
    toUpperByte (toLowerByte (b32Char k)) = b32Char k := by
  unfold toUpperByte toLowerByte b32Char
  split_ifs <;> simp only [UInt8.toNat_ofNat'] at * <;> apply UInt8.ext <;> simp only [UInt8.toNat_ofNat'] <;> omega

theorem rstripEq_append_of_ne_nil (xs ys : Bytes) (h : rstripEq ys ≠ []) :
    rstripEq (xs ++ ys) = xs ++ rstripEq ys := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.cons_append, rstripEq, ih]
    have hne : (bs ++ rstripEq ys).isEmpty = false := by
      cases bs <;> simp [List.isEmpty_iff, h]
    simp [hne]

theorem rstripEq_encodeChunk5_append (b0 b1 b2 b3 b4 : UInt8) (ys : Bytes) :
    rstripEq (encodeChunk5 b0 b1 b2 b3 b4 ++ ys) = encodeChunk5 b0 b1 b2 b3 b4 ++ rstripEq ys := by
  by_cases h : rstripEq ys = []
  · have hp (n : Nat) : (b32Char (n % 32) == 61) = false :=
      b32Char_ne_pad (n % 32) (Nat.mod_lt _ (by decide))
    have h0 : rstripEq (encodeChunk5 b0 b1 b2 b3 b4 ++ ys) = rstripEq (encodeChunk5 b0 b1 b2 b3 b4) := by
      induction (encodeChunk5 b0 b1 b2 b3 b4) with
      | nil => exact h
      | cons x xs ih => simp only [List.cons_append, rstripEq, ih]
    rw [h0, h, List.append_nil]
    simp [encodeChunk5, rstripEq, hp]
  · exact rstripEq_append_of_ne_nil _ _ h

theorem mem_b32encode (s : Bytes) (c : UInt8) (hc : c ∈ b32encode s) :
    (∃ k < 32, c = b32Char k) ∨ c = 61 := by
  have hmod (n : Nat) : (∃ k < 32, b32Char (n % 32) = b32Char k) ∨ b32Char (n % 32) = 61 :=
    Or.inl ⟨n % 32, Nat.mod_lt _ (by decide), rfl⟩
  induction s using b32encode.induct with
  | case1 => simp [b32encode] at hc
  | case2 b0 =>
    simp only [b32encode, List.mem_cons, List.notMem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hmod _ | exact Or.inr rfl
  | case3 b0 b1 =>
    simp only [b32encode, List.mem_cons, List.notMem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hmod _ | exact Or.inr rfl
  | case4 b0 b1 b2 =>
    simp only [b32encode, List.mem_cons, List.notMem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hmod _ | exact Or.inr rfl
  | case5 b0 b1 b3 b4 =>
    simp only [b32encode, List.mem_cons, List.notMem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hmod _ | exact Or.inr rfl
  | case6 b0 b1 b2 b3 b4 rest ih =>
    simp only [b32encode, List.mem_append] at hc
    rcases hc with hc | hc
    · simp only [encodeChunk5, List.mem_cons, List.notMem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hmod _
    · exact ih hc

theorem mem_rstripEq_b32encode (s : Bytes) (c : UInt8) (hc : c ∈ rstripEq (b32encode s)) :
    ∃ k < 32, c = b32Char k := by
  have hp (n : Nat) : (b32Char (n % 32) == 61) = false :=
    b32Char_ne_pad (n % 32) (Nat.mod_lt _ (by decide))
  have hmod (n : Nat) : ∃ k < 32, b32Char (n % 32) = b32Char k :=
    ⟨n % 32, Nat.mod_lt _ (by decide), rfl⟩
  induction s using b32encode.induct with
  | case1 => simp [b32encode, rstripEq] at hc
  | case2 b0 =>
    simp only [b32encode, rstripEq, hp, Bool.and_false, Bool.and_true, List.isEmpty_cons,
      List.isEmpty_nil, beq_self_eq_true, ↓reduceIte, List.mem_cons, List.notMem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact hmod _
  | case3 b0 b1 =>
    simp only [b32encode, rstripEq, hp, Bool.and_false, Bool.and_true, List.isEmpty_cons,
      List.isEmpty_nil, beq_self_eq_true, ↓reduceIte, List.mem_cons, List.notMem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> exact hmod _
  | case4 b0 b1 b2 =>
    simp only [b32encode, rstripEq, hp, Bool.and_false, Bool.and_true, List.isEmpty_cons,
      List.isEmpty_nil, beq_self_eq_true, ↓reduceIte, List.mem_cons, List.notMem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> exact hmod _
  | case5 b0 b1 b2 b3 =>
    simp only [b32encode, rstripEq, hp, Bool.and_false, Bool.and_true, List.isEmpty_cons,
      List.isEmpty_nil, beq_self_eq_true, ↓reduceIte, List.mem_cons, List.notMem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hmod _
  | case6 b0 b1 b2 b3 b4 rest ih =>
    simp only [b32encode, rstripEq_encodeChunk5_append, List.mem_append] at hc
    rcases hc with hc | hc
    · simp only [encodeChunk5, List.mem_cons, List.notMem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hmod _
    · exact ih hc

/-- Property 0: `_b32alphabet` has length 32 and its `k`-th byte equals `b32Char k`. -/
def b32alphabet_lookup_prop : Prop :=
  _b32alphabet.length = 32 ∧ ∀ k : Fin 32, _b32alphabet[k.1]? = some (b32Char k.1)

theorem b32alphabet_lookup_thm : b32alphabet_lookup_prop := by
  decide

/-- Property 1: Encoding and decoding the empty byte sequence returns the empty byte sequence. -/
def empty_prop : Prop :=
  b32encode [] = [] ∧ b32decode [] = [] ∧ b32decode? [] = some []

theorem empty_thm : empty_prop := by
  decide

/-- Property 2: The length of `b32encode s` is `8 * ((s.length + 4) / 5)` and is always a multiple of 8. -/
def encode_length_prop (s : Bytes) : Prop :=
  (b32encode s).length = 8 * ((s.length + 4) / 5) ∧ (b32encode s).length % 8 = 0

theorem encode_length_thm (s : Bytes) : encode_length_prop s := by
  unfold encode_length_prop
  induction s using b32encode.induct with
  | case1 => simp [b32encode]
  | case2 b0 => simp [b32encode]
  | case3 b0 b1 => simp [b32encode]
  | case4 b0 b1 b2 => simp [b32encode]
  | case5 b0 b1 b2 b3 => simp [b32encode]
  | case6 b0 b1 b2 b3 b4 rest ih =>
    simp only [b32encode, encodeChunk5, List.length_append, List.length_cons, List.length_nil]
    omega

/-- Property 3: Every byte in `b32encode s` is either a valid Base32 character or `'='` (61),
    and every byte in `rstripEq (b32encode s)` is strictly a valid Base32 character. -/
def encode_alphabet_prop (s : Bytes) : Prop :=
  (∀ c ∈ b32encode s, (revB32Char c).isSome = true ∨ c = 61) ∧
  (∀ c ∈ rstripEq (b32encode s), (revB32Char c).isSome = true)

theorem encode_alphabet_thm (s : Bytes) : encode_alphabet_prop s := by
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · rcases mem_b32encode s c hc with ⟨k, hk, rfl⟩ | rfl
    · left; simp [revB32Char_b32Char k hk]
    · right; rfl
  · rcases mem_rstripEq_b32encode s c hc with ⟨k, hk, rfl⟩
    simp [revB32Char_b32Char k hk]

/-- Expected unpadded Base32 length for an input of `n` bytes. -/
def strippedLenSpec (n : Nat) : Nat :=
  let q := n / 5
  let r := n % 5
  if r == 0 then 8 * q
  else if r == 1 then 8 * q + 2
  else if r == 2 then 8 * q + 4
  else if r == 3 then 8 * q + 5
  else 8 * q + 7

/-- Expected number of trailing `'='` padding characters for an input of `n` bytes. -/
def padCount (n : Nat) : Nat :=
  let r := n % 5
  if r == 0 then 0
  else if r == 1 then 6
  else if r == 2 then 4
  else if r == 3 then 3
  else 1

/-- Property 4: The unpadded length of `b32encode s` matches the exact remainder specification
    (`0, 2, 4, 5, 7` characters for `s.length % 5 = 0, 1, 2, 3, 4`). -/
def encode_padding_prop (s : Bytes) : Prop :=
  (rstripEq (b32encode s)).length = strippedLenSpec s.length

theorem encode_padding_thm (s : Bytes) : encode_padding_prop s := by
  unfold encode_padding_prop
  have hp (n : Nat) : (b32Char (n % 32) == 61) = false :=
    b32Char_ne_pad (n % 32) (Nat.mod_lt _ (by decide))
  induction s using b32encode.induct with
  | case1 => rfl
  | case2 b0 => simp [b32encode, rstripEq, hp, strippedLenSpec]
  | case3 b0 b1 => simp [b32encode, rstripEq, hp, strippedLenSpec]
  | case4 b0 b1 b2 => simp [b32encode, rstripEq, hp, strippedLenSpec]
  | case5 b0 b1 b2 b3 => simp [b32encode, rstripEq, hp, strippedLenSpec]
  | case6 b0 b1 b2 b3 b4 rest ih =>
    simp only [b32encode, rstripEq_encodeChunk5_append, List.length_append, ih, encodeChunk5,
      List.length_cons, List.length_nil, strippedLenSpec, beq_iff_eq]
    split_ifs <;> omega

/-- Property 4b: `b32encode s` decomposes into `rstripEq (b32encode s)` followed by `padCount s.length` `'='` bytes. -/
def encode_pad_suffix_prop (s : Bytes) : Prop :=
  b32encode s = rstripEq (b32encode s) ++ List.replicate (padCount s.length) 61

theorem encode_pad_suffix_thm (s : Bytes) : encode_pad_suffix_prop s := by
  unfold encode_pad_suffix_prop
  have hp (n : Nat) : (b32Char (n % 32) == 61) = false :=
    b32Char_ne_pad (n % 32) (Nat.mod_lt _ (by decide))
  induction s using b32encode.induct with
  | case1 => rfl
  | case2 b0 => simp [b32encode, rstripEq, hp, padCount, List.replicate]
  | case3 b0 b1 => simp [b32encode, rstripEq, hp, padCount, List.replicate]
  | case4 b0 b1 b2 => simp [b32encode, rstripEq, hp, padCount, List.replicate]
  | case5 b0 b1 b2 b3 => simp [b32encode, rstripEq, hp, padCount, List.replicate]
  | case6 b0 b1 b2 b3 b4 rest ih =>
    have hmod : (b0 :: b1 :: b2 :: b3 :: b4 :: rest).length % 5 = rest.length % 5 := by
      simp only [List.length_cons]; omega
    have hpad : padCount (b0 :: b1 :: b2 :: b3 :: b4 :: rest).length = padCount rest.length := by
      simp only [padCount, hmod]
    simp only [b32encode, rstripEq_encodeChunk5_append, hpad, List.append_assoc]
    rw [← ih]

/-- Helper lemma: decoding an 8-byte encoded chunk prepends the 5 original bytes to the decoded tail. -/
theorem decodeLoop_encodeChunk5 (b0 b1 b2 b3 b4 : UInt8) (cs : Bytes) (v0 : Nat) :
    ∃ v1, decodeLoop (encodeChunk5 b0 b1 b2 b3 b4 ++ cs) v0 0 =
      (decodeLoop cs v1 0).map (fun rest => b0 :: b1 :: b2 :: b3 :: b4 :: rest) := by
  have hk (n : Nat) : revB32Char (b32Char (n % 32)) = some (n % 32) :=
    revB32Char_b32Char (n % 32) (Nat.mod_lt _ (by decide))
  have h_arith := by
    have h0 : b0.toNat < 256 := b0.toBitVec.isLt
    have h1 : b1.toNat < 256 := b1.toBitVec.isLt
    have h2 : b2.toNat < 256 := b2.toBitVec.isLt
    have h3 : b3.toNat < 256 := b3.toBitVec.isLt
    have h4 : b4.toNat < 256 := b4.toBitVec.isLt
    let val := intFromBytes5 b0 b1 b2 b3 b4
    let k0 := (val / 2^35) % 32
    let k1 := (val / 2^30) % 32
    let k2 := (val / 2^25) % 32
    let k3 := (val / 2^20) % 32
    let k4 := (val / 2^15) % 32
    let k5 := (val / 2^10) % 32
    let k6 := (val / 2^5) % 32
    let k7 := val % 32
    let a1 := (v0 * 32 + k0) * 32 + k1
    let a3 := (a1 * 32 + k2) * 32 + k3
    let a4 := a3 * 32 + k4
    let a6 := (a4 * 32 + k5) * 32 + k6
    let a7 := a6 * 32 + k7
    show (a1 / 4) % 256 = b0.toNat ∧ (a3 / 16) % 256 = b1.toNat ∧
         (a4 / 2) % 256 = b2.toNat ∧ (a6 / 8) % 256 = b3.toNat ∧
         a7 % 256 = b4.toNat
    dsimp only [val, intFromBytes5, k0, k1, k2, k3, k4, k5, k6, k7, a1, a3, a4, a6, a7]
    omega
  rcases h_arith with ⟨e0, e1, e2, e3, e4⟩
  simp only [Nat.reducePow] at e0 e1 e2 e3 e4
  refine ⟨_, ?_⟩
  simp only [encodeChunk5, List.cons_append, List.nil_append, decodeLoop, hk, decodeStep,
    ↓reduceIte, Nat.reduceAdd, Nat.reduceSub, Nat.reduceGe, Nat.reducePow]
  dsimp only
  rw [e0, e1, e2, e3, e4, UInt8.ofNat_toNat]
  cases decodeLoop cs _ 0 <;> rfl

/-- Helper lemma: `decodeLoop` on `rstripEq (b32encode s)` recovers `some s` from any initial accumulator `v0`. -/
theorem decodeLoop_rstripEq_b32encode (s : Bytes) :
    ∀ v0 : Nat, decodeLoop (rstripEq (b32encode s)) v0 0 = some s := by
  induction s using b32encode.induct with
  | case1 => intro v0; rfl
  | case2 b0 =>
    intro v0
    have hp (n : Nat) : (b32Char (n % 32) == 61) = false :=
      b32Char_ne_pad (n % 32) (Nat.mod_lt _ (by decide))
    have hk (n : Nat) : revB32Char (b32Char (n % 32)) = some (n % 32) :=
      revB32Char_b32Char (n % 32) (Nat.mod_lt _ (by decide))
    have e0 : (let val := intFromBytes5 b0 0 0 0 0
      (((v0 * 32 + (val / 2^35) % 32) * 32 + (val / 2^30) % 32) / 4) % 256) = b0.toNat := by
      have h0 : b0.toNat < 256 := b0.toBitVec.isLt
      dsimp only [intFromBytes5]; change _ = b0.toNat; omega
    dsimp only at e0
    simp only [Nat.reducePow] at e0
    simp only [b32encode, rstripEq, hp, Bool.and_false, Bool.and_true, List.isEmpty_cons,
      List.isEmpty_nil, beq_self_eq_true, ↓reduceIte, decodeLoop, hk, decodeStep,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceGe, Nat.reducePow]
    dsimp only
    rw [e0, UInt8.ofNat_toNat]
  | case3 b0 b1 =>
    intro v0
    have hp (n : Nat) : (b32Char (n % 32) == 61) = false :=
      b32Char_ne_pad (n % 32) (Nat.mod_lt _ (by decide))
    have hk (n : Nat) : revB32Char (b32Char (n % 32)) = some (n % 32) :=
      revB32Char_b32Char (n % 32) (Nat.mod_lt _ (by decide))
    have h_arith : (let val := intFromBytes5 b0 b1 0 0 0
      let a1 := (v0 * 32 + (val / 2^35) % 32) * 32 + (val / 2^30) % 32
      let a3 := (a1 * 32 + (val / 2^25) % 32) * 32 + (val / 2^20) % 32
      (a1 / 4) % 256 = b0.toNat ∧ (a3 / 16) % 256 = b1.toNat) := by
      have h0 : b0.toNat < 256 := b0.toBitVec.isLt
      have h1 : b1.toNat < 256 := b1.toBitVec.isLt
      dsimp only [intFromBytes5]; change _ ∧ _; omega
    dsimp only at h_arith
    rcases h_arith with ⟨e0, e1⟩
    simp only [Nat.reducePow] at e0 e1
    simp only [b32encode, rstripEq, hp, Bool.and_false, Bool.and_true, List.isEmpty_cons,
      List.isEmpty_nil, beq_self_eq_true, ↓reduceIte, decodeLoop, hk, decodeStep,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceGe, Nat.reducePow]
    dsimp only
    rw [e0, e1, UInt8.ofNat_toNat, UInt8.ofNat_toNat]
  | case4 b0 b1 b2 =>
    intro v0
    have hp (n : Nat) : (b32Char (n % 32) == 61) = false :=
      b32Char_ne_pad (n % 32) (Nat.mod_lt _ (by decide))
    have hk (n : Nat) : revB32Char (b32Char (n % 32)) = some (n % 32) :=
      revB32Char_b32Char (n % 32) (Nat.mod_lt _ (by decide))
    have h_arith : (let val := intFromBytes5 b0 b1 b2 0 0
      let a1 := (v0 * 32 + (val / 2^35) % 32) * 32 + (val / 2^30) % 32
      let a3 := (a1 * 32 + (val / 2^25) % 32) * 32 + (val / 2^20) % 32
      let a4 := a3 * 32 + (val / 2^15) % 32
      (a1 / 4) % 256 = b0.toNat ∧ (a3 / 16) % 256 = b1.toNat ∧ (a4 / 2) % 256 = b2.toNat) := by
      have h0 : b0.toNat < 256 := b0.toBitVec.isLt
      have h1 : b1.toNat < 256 := b1.toBitVec.isLt
      have h2 : b2.toNat < 256 := b2.toBitVec.isLt
      dsimp only [intFromBytes5]; change _ ∧ _ ∧ _; omega
    dsimp only at h_arith
    rcases h_arith with ⟨e0, e1, e2⟩
    simp only [Nat.reducePow] at e0 e1 e2
    simp only [b32encode, rstripEq, hp, Bool.and_false, Bool.and_true, List.isEmpty_cons,
      List.isEmpty_nil, beq_self_eq_true, ↓reduceIte, decodeLoop, hk, decodeStep,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceGe, Nat.reducePow]
    dsimp only
    rw [e0, e1, e2, UInt8.ofNat_toNat, UInt8.ofNat_toNat, UInt8.ofNat_toNat]
  | case5 b0 b1 b2 b3 =>
    intro v0
    have hp (n : Nat) : (b32Char (n % 32) == 61) = false :=
      b32Char_ne_pad (n % 32) (Nat.mod_lt _ (by decide))
    have hk (n : Nat) : revB32Char (b32Char (n % 32)) = some (n % 32) :=
      revB32Char_b32Char (n % 32) (Nat.mod_lt _ (by decide))
    have h_arith : (let val := intFromBytes5 b0 b1 b2 b3 0
      let a1 := (v0 * 32 + (val / 2^35) % 32) * 32 + (val / 2^30) % 32
      let a3 := (a1 * 32 + (val / 2^25) % 32) * 32 + (val / 2^20) % 32
      let a4 := a3 * 32 + (val / 2^15) % 32
      let a6 := (a4 * 32 + (val / 2^10) % 32) * 32 + (val / 2^5) % 32
      (a1 / 4) % 256 = b0.toNat ∧ (a3 / 16) % 256 = b1.toNat ∧
      (a4 / 2) % 256 = b2.toNat ∧ (a6 / 8) % 256 = b3.toNat) := by
      have h0 : b0.toNat < 256 := b0.toBitVec.isLt
      have h1 : b1.toNat < 256 := b1.toBitVec.isLt
      have h2 : b2.toNat < 256 := b2.toBitVec.isLt
      have h3 : b3.toNat < 256 := b3.toBitVec.isLt
      dsimp only [intFromBytes5]; change _ ∧ _ ∧ _ ∧ _; omega
    dsimp only at h_arith
    rcases h_arith with ⟨e0, e1, e2, e3⟩
    simp only [Nat.reducePow] at e0 e1 e2 e3
    simp only [b32encode, rstripEq, hp, Bool.and_false, Bool.and_true, List.isEmpty_cons,
      List.isEmpty_nil, beq_self_eq_true, ↓reduceIte, decodeLoop, hk, decodeStep,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceGe, Nat.reducePow]
    dsimp only
    rw [e0, e1, e2, e3, UInt8.ofNat_toNat, UInt8.ofNat_toNat, UInt8.ofNat_toNat, UInt8.ofNat_toNat]
  | case6 b0 b1 b2 b3 b4 rest ih =>
    intro v0
    simp only [b32encode, rstripEq_encodeChunk5_append]
    rcases decodeLoop_encodeChunk5 b0 b1 b2 b3 b4 (rstripEq (b32encode rest)) v0 with ⟨v1, hv1⟩
    rw [hv1, ih v1, Option.map_some]

theorem applyMap01_b32encode (map01 : Option UInt8) (s : Bytes) :
    applyMap01 map01 (b32encode s) = b32encode s := by
  cases map01 with
  | none => rfl
  | some m =>
    simp only [applyMap01, List.map_eq_self]
    intro c hc
    rcases mem_b32encode s c hc with ⟨k, hk, rfl⟩ | rfl
    · exact applyMap01Byte_b32Char m k hk
    · rfl

theorem applyCasefold_b32encode (casefold : Bool) (s : Bytes) :
    applyCasefold casefold (b32encode s) = b32encode s := by
  cases casefold with
  | false => rfl
  | true =>
    simp only [applyCasefold, ↓reduceIte, List.map_eq_self]
    intro c hc
    rcases mem_b32encode s c hc with ⟨k, hk, rfl⟩ | rfl
    · exact toUpperByte_b32Char k hk
    · rfl

/-- Property 5: Round-trip correctness (`b32decode (b32encode s) = s` and `b32decode? (b32encode s) = some s`). -/
def decode_encode_prop (s : Bytes) (casefold : Bool := false) (map01 : Option UInt8 := none) : Prop :=
  b32decode? (b32encode s) casefold map01 = some s ∧
  b32decode (b32encode s) casefold map01 = s

theorem decode_encode_thm (s : Bytes) (casefold : Bool := false) (map01 : Option UInt8 := none) :
    decode_encode_prop s casefold map01 := by
  have h1 : b32decode? (b32encode s) casefold map01 = some s := by
    unfold b32decode?
    rw [applyMap01_b32encode, applyCasefold_b32encode]
    exact decodeLoop_rstripEq_b32encode s 0
  exact ⟨h1, by unfold b32decode; rw [h1]; rfl⟩

/-- Corollary: `b32encode` is injective. -/
theorem b32encode_injective (s₁ s₂ : Bytes) (h : b32encode s₁ = b32encode s₂) : s₁ = s₂ := by
  have h1 := (decode_encode_thm s₁).2
  have h2 := (decode_encode_thm s₂).2
  rw [← h1, ← h2, h]

/-- Property 6: Lowercasing an encoded Base32 string and decoding with `casefold = true` recovers `s`. -/
def decode_casefold_prop (s : Bytes) : Prop :=
  b32decode? ((b32encode s).map toLowerByte) true none = some s ∧
  b32decode ((b32encode s).map toLowerByte) true none = s

theorem decode_casefold_thm (s : Bytes) : decode_casefold_prop s := by
  have hmap : ((b32encode s).map toLowerByte).map toUpperByte = b32encode s := by
    rw [List.map_map, List.map_eq_self]
    intro c hc
    rcases mem_b32encode s c hc with ⟨k, hk, rfl⟩ | rfl
    · exact toUpperByte_toLowerByte_b32Char k hk
    · rfl
  have h1 : b32decode? ((b32encode s).map toLowerByte) true none = some s := by
    unfold b32decode? applyMap01 applyCasefold
    simp only [↓reduceIte, hmap]
    exact decodeLoop_rstripEq_b32encode s 0
  exact ⟨h1, by unfold b32decode; rw [h1]; rfl⟩

/-- Property 7: Replacing `'O'` (79) with `'0'` (48) in `b32encode s` and decoding with `map01 = some m` recovers `s`. -/
def decode_map01_prop (s : Bytes) (m : UInt8) : Prop :=
  b32decode? ((b32encode s).map (fun c => if c == 79 then 48 else c)) false (some m) = some s ∧
  b32decode ((b32encode s).map (fun c => if c == 79 then 48 else c)) false (some m) = s

theorem decode_map01_thm (s : Bytes) (m : UInt8) : decode_map01_prop s m := by
  have hmap : applyMap01 (some m) ((b32encode s).map (fun c => if c == 79 then 48 else c)) = b32encode s := by
    simp only [applyMap01, List.map_map, List.map_eq_self]
    intro c hc
    rcases mem_b32encode s c hc with ⟨k, hk, rfl⟩ | rfl
    · simp only [Function.comp_apply]
      by_cases h79 : b32Char k == 79
      · simp only [h79, ↓reduceIte]
        have h79' : b32Char k = 79 := beq_iff_eq.mp h79
        rw [h79']
        rfl
      · simp only [h79, Bool.false_eq_true, ↓reduceIte]
        exact applyMap01Byte_b32Char m k hk
    · rfl
  have h1 : b32decode? ((b32encode s).map (fun c => if c == 79 then 48 else c)) false (some m) = some s := by
    unfold b32decode?
    rw [hmap, applyCasefold_b32encode]
    exact decodeLoop_rstripEq_b32encode s 0
  exact ⟨h1, by unfold b32decode; rw [h1]; rfl⟩

/-- Property 7b: Replacing `m` (`m ≠ 48`) with `'1'` (49) and `'O'` (79) with `'0'` (48) in `b32encode s`
    and decoding with `map01 = some m` recovers `s`. -/
def decode_map01_one_prop (s : Bytes) (m : UInt8) : Prop :=
  m ≠ 48 →
  b32decode? ((b32encode s).map (fun c => if c == m then 49 else if c == 79 then 48 else c)) false (some m) = some s ∧
  b32decode ((b32encode s).map (fun c => if c == m then 49 else if c == 79 then 48 else c)) false (some m) = s

theorem decode_map01_one_thm (s : Bytes) (m : UInt8) : decode_map01_one_prop s m := by
  intro _hm
  have hmap : applyMap01 (some m) ((b32encode s).map (fun c => if c == m then 49 else if c == 79 then 48 else c)) = b32encode s := by
    simp only [applyMap01, List.map_map, List.map_eq_self]
    intro c hc
    rcases mem_b32encode s c hc with ⟨k, hk, rfl⟩ | rfl
    · simp only [Function.comp_apply]
      by_cases hm_eq : b32Char k == m
      · simp only [hm_eq, ↓reduceIte, applyMap01Byte]
        exact (beq_iff_eq.mp hm_eq).symm
      · simp only [hm_eq, Bool.false_eq_true, ↓reduceIte]
        by_cases h79 : b32Char k == 79
        · simp only [h79, ↓reduceIte]
          have h79' : b32Char k = 79 := beq_iff_eq.mp h79
          rw [h79']
          rfl
        · simp only [h79, Bool.false_eq_true, ↓reduceIte]
          exact applyMap01Byte_b32Char m k hk
    · simp only [Function.comp_apply]
      by_cases hm61 : (61 : UInt8) == m
      · simp only [hm61, ↓reduceIte, applyMap01Byte]
        exact (beq_iff_eq.mp hm61).symm
      · simp only [hm61, Bool.false_eq_true, ↓reduceIte]
        rfl
  have h1 : b32decode? ((b32encode s).map (fun c => if c == m then 49 else if c == 79 then 48 else c)) false (some m) = some s := by
    unfold b32decode?
    rw [hmap, applyCasefold_b32encode]
    exact decodeLoop_rstripEq_b32encode s 0
  exact ⟨h1, by unfold b32decode; rw [h1]; rfl⟩

/-- Property 8: Encoding distributes over concatenation when the first byte list has length divisible by 5. -/
def encode_append_five_prop (xs ys : Bytes) : Prop :=
  xs.length % 5 = 0 → b32encode (xs ++ ys) = b32encode xs ++ b32encode ys

theorem encode_append_five_thm (xs ys : Bytes) : encode_append_five_prop xs ys := by
  intro h
  induction xs using b32encode.induct with
  | case1 => simp [b32encode]
  | case2 b0 => simp at h
  | case3 b0 b1 => simp at h
  | case4 b0 b1 b2 => simp at h
  | case5 b0 b1 b2 b3 => simp at h
  | case6 b0 b1 b2 b3 b4 rest ih =>
    have hrest : rest.length % 5 = 0 := by
      simp only [List.length_cons] at h; omega
    simp only [List.cons_append, b32encode, ih hrest, List.append_assoc]

/-- Property 9: `b32decode?` succeeds (`isSome = true`) iff all stripped normalized bytes are valid Base32 characters. -/
def decode_error_prop (s : Bytes) (casefold : Bool := false) (map01 : Option UInt8 := none) : Prop :=
  (b32decode? s casefold map01).isSome = isValidBase32 s casefold map01

theorem decodeLoop_isSome (cs : Bytes) (val bits : Nat) :
    (decodeLoop cs val bits).isSome = cs.all (fun c => (revB32Char c).isSome) := by
  induction cs generalizing val bits with
  | nil => rfl
  | cons c cs ih =>
    simp only [decodeLoop, List.all_cons]
    cases revB32Char c with
    | none => rfl
    | some k =>
      simp only [Option.isSome_some, Bool.true_and]
      rw [← ih (decodeStep val bits k).1 (decodeStep val bits k).2.1]
      cases decodeLoop cs (decodeStep val bits k).1 (decodeStep val bits k).2.1 <;> cases (decodeStep val bits k).2.2 <;> rfl

theorem decode_error_thm (s : Bytes) (casefold : Bool := false) (map01 : Option UInt8 := none) :
    decode_error_prop s casefold map01 := by
  unfold decode_error_prop b32decode? isValidBase32
  exact decodeLoop_isSome _ 0 0

/-! ## 8. Post-condition -/

/-- Post-condition conjunction of all core Base32 properties on input `s`. -/
def Post_prop (s : Bytes) : Prop :=
  encode_length_prop s ∧
  encode_alphabet_prop s ∧
  encode_padding_prop s ∧
  encode_pad_suffix_prop s ∧
  decode_encode_prop s false none ∧
  decode_casefold_prop s ∧
  decode_map01_prop s 73 ∧
  decode_map01_one_prop s 73 ∧
  decode_error_prop (b32encode s) false none

/-! ## 9. Property-Based Tests (PBTs) -/

-- PBT for `b32alphabet_lookup_prop`
example : (_b32alphabet.length == 32 && (List.range 32).all (fun k => _b32alphabet[k]? == some (b32Char k))) = true := by native_decide

-- PBT for `empty_prop`
example : (b32encode [] == [] && b32decode [] == [] && b32decode? [] == some []) = true := by native_decide

-- PBT for `encode_length_prop`
#eval Plausible.Testable.check (∀ s : Bytes,
  (b32encode s).length = 8 * ((s.length + 4) / 5) ∧ (b32encode s).length % 8 = 0)

-- PBT for `encode_alphabet_prop`
#eval Plausible.Testable.check (∀ s : Bytes,
  (b32encode s).all (fun c => (revB32Char c).isSome || c == 61) = true ∧
  (rstripEq (b32encode s)).all (fun c => (revB32Char c).isSome) = true)

-- PBT for `encode_padding_prop`
#eval Plausible.Testable.check (∀ s : Bytes,
  (rstripEq (b32encode s)).length = strippedLenSpec s.length)

-- PBT for `encode_pad_suffix_prop`
#eval Plausible.Testable.check (∀ s : Bytes,
  b32encode s = rstripEq (b32encode s) ++ List.replicate (padCount s.length) 61)

-- PBT for `decode_encode_prop`
#eval Plausible.Testable.check (∀ (s : Bytes) (casefold : Bool) (map01 : Option UInt8),
  b32decode? (b32encode s) casefold map01 = some s ∧
  b32decode (b32encode s) casefold map01 = s)

-- PBT for `decode_casefold_prop`
#eval Plausible.Testable.check (∀ s : Bytes,
  b32decode? ((b32encode s).map toLowerByte) true none = some s ∧
  b32decode ((b32encode s).map toLowerByte) true none = s)

-- PBT for `decode_map01_prop`
#eval Plausible.Testable.check (∀ (s : Bytes) (m : UInt8),
  b32decode? ((b32encode s).map (fun c => if c == 79 then 48 else c)) false (some m) = some s ∧
  b32decode ((b32encode s).map (fun c => if c == 79 then 48 else c)) false (some m) = s)

-- PBT for `decode_map01_one_prop`
#eval Plausible.Testable.check (∀ s : Bytes,
  b32decode? ((b32encode s).map (fun c => if c == 73 then 49 else if c == 79 then 48 else c)) false (some 73) = some s ∧
  b32decode ((b32encode s).map (fun c => if c == 73 then 49 else if c == 79 then 48 else c)) false (some 73) = s)

-- PBT for `encode_append_five_prop`
#eval Plausible.Testable.check (∀ (xs ys : Bytes),
  b32encode ((xs ++ xs ++ xs ++ xs ++ xs) ++ ys) =
    b32encode (xs ++ xs ++ xs ++ xs ++ xs) ++ b32encode ys)

-- PBT for `decode_error_prop`
#eval Plausible.Testable.check (∀ (s : Bytes) (casefold : Bool) (map01 : Option UInt8),
  (b32decode? s casefold map01).isSome = isValidBase32 s casefold map01)

-- PBT for `Post_prop`
#eval Plausible.Testable.check (∀ s : Bytes,
  (b32encode s).length = 8 * ((s.length + 4) / 5) ∧
  (b32encode s).length % 8 = 0 ∧
  (b32encode s).all (fun c => (revB32Char c).isSome || c == 61) = true ∧
  (rstripEq (b32encode s)).length = strippedLenSpec s.length ∧
  b32encode s = rstripEq (b32encode s) ++ List.replicate (padCount s.length) 61 ∧
  b32decode (b32encode s) = s ∧
  b32decode ((b32encode s).map toLowerByte) true = s)

/-! ## 10. Correctness Theorem: `Pre -> Post` -/

theorem b32_correctness_thm (s : Bytes) (_hpre : Pre s) : Post_prop s :=
  And.intro (encode_length_thm s) (
  And.intro (encode_alphabet_thm s) (
  And.intro (encode_padding_thm s) (
  And.intro (encode_pad_suffix_thm s) (
  And.intro (decode_encode_thm s false none) (
  And.intro (decode_casefold_thm s) (
  And.intro (decode_map01_thm s 73) (
  And.intro (decode_map01_one_thm s 73)
    (decode_error_thm (b32encode s) false none))))))))

theorem benchmark_b32encode_eq (s : Bytes) : benchmark_b32encode s = b32encode s := by
  unfold benchmark_b32encode; split_ifs <;> rfl

theorem benchmark_b32decode_eq (s : Bytes) (casefold : Bool := false) (map01 : Option UInt8 := none) :
    benchmark_b32decode s casefold map01 = b32decode s casefold map01 := by
  unfold benchmark_b32decode; split_ifs <;> rfl

/-! ## 11. Imperative Implementation -/

/-- Partition a byte list into 5-byte chunks. -/
def chunksOf5 : Bytes → List Bytes
  | [] => []
  | [b0] => [[b0]]
  | [b0, b1] => [[b0, b1]]
  | [b0, b1, b2] => [[b0, b1, b2]]
  | [b0, b1, b2, b3] => [[b0, b1, b2, b3]]
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest =>
    [b0, b1, b2, b3, b4] :: chunksOf5 rest

/-- Encode a single 1..5 byte chunk into 8 Base32 bytes with appropriate padding. -/
def encodeSingleChunk (chunk : Bytes) : Bytes :=
  match chunk with
  | [] => []
  | [b0] => b32encode [b0]
  | [b0, b1] => b32encode [b0, b1]
  | [b0, b1, b2] => b32encode [b0, b1, b2]
  | [b0, b1, b2, b3] => b32encode [b0, b1, b2, b3]
  | b0 :: b1 :: b2 :: b3 :: b4 :: _ => encodeChunk5 b0 b1 b2 b3 b4

/-- Imperative Base32 encoder using `Id.run do` and mutable state. -/
def b32encode_imp (s : Bytes) : Bytes := Id.run do
  let mut encoded : Bytes := []
  for chunk in chunksOf5 s do
    encoded := encoded ++ encodeSingleChunk chunk
  return encoded

/-- Mutable loop step for the imperative Base32 decoder. -/
def decodeImpStep (st : Option Bytes × Nat × Nat) (char : UInt8) : Option Bytes × Nat × Nat :=
  match st with
  | (none, val, bits) => (none, val, bits)
  | (some decoded, val, bits) =>
    match revB32Char char with
    | none => (none, val, bits)
    | some k =>
      let step := decodeStep val bits k
      match step.2.2 with
      | none => (some decoded, step.1, step.2.1)
      | some b => (some (decoded ++ [b]), step.1, step.2.1)

/-- Imperative option-returning Base32 decoder using `Id.run do` and mutable state. -/
def b32decode?_imp (s : Bytes) (casefold : Bool := false) (map01 : Option UInt8 := none) : Option Bytes := Id.run do
  let s1 := applyMap01 map01 s
  let s2 := applyCasefold casefold s1
  let s3 := rstripEq s2
  let mut st : Option Bytes × Nat × Nat := (some [], 0, 0)
  for char in s3 do
    st := decodeImpStep st char
  return st.1

/-- Imperative total Base32 decoder using `Id.run do` and mutable state. -/
def b32decode_imp (s : Bytes) (casefold : Bool := false) (map01 : Option UInt8 := none) : Bytes :=
  (b32decode?_imp s casefold map01).getD []

/-- Imperative benchmark wrapper for `b32encode`. -/
def benchmark_b32encode_imp (s : Bytes) : Bytes :=
  if !pre_encode_bool s then b32encode_imp s else b32encode_imp s

/-- Imperative benchmark wrapper for `b32decode`. -/
def benchmark_b32decode_imp (s : Bytes) (casefold : Bool := false) (map01 : Option UInt8 := none) : Bytes :=
  if !pre_decode_bool s then b32decode_imp s casefold map01 else b32decode_imp s casefold map01

/-! ## 12. Imperative Tests -/

#eval Bytes.toString (b32encode_imp (Bytes.ofString "foobar"))
#eval Bytes.toString (b32decode_imp (Bytes.ofString "mzxw6ytb") true)
#eval check benchmark_b32encode_imp (fun s c m => benchmark_b32decode_imp s c m)

example : b32encode_imp (Bytes.ofString "") = Bytes.ofString "" := by native_decide
example : b32encode_imp (Bytes.ofString "f") = Bytes.ofString "MY======" := by native_decide
example : b32encode_imp (Bytes.ofString "fo") = Bytes.ofString "MZXQ====" := by native_decide
example : b32encode_imp (Bytes.ofString "foo") = Bytes.ofString "MZXW6===" := by native_decide
example : b32encode_imp (Bytes.ofString "foob") = Bytes.ofString "MZXW6YQ=" := by native_decide
example : b32encode_imp (Bytes.ofString "fooba") = Bytes.ofString "MZXW6YTB" := by native_decide
example : b32encode_imp (Bytes.ofString "foobar") = Bytes.ofString "MZXW6YTBOI======" := by native_decide
example : b32decode_imp (b32encode_imp (Bytes.ofString "VeriBench")) = Bytes.ofString "VeriBench" := by native_decide
example : b32decode_imp (Bytes.ofString "mzxw6ytb") true = Bytes.ofString "fooba" := by native_decide
example : check benchmark_b32encode_imp (fun s c m => benchmark_b32decode_imp s c m) = true := by native_decide

#eval Plausible.Testable.check (∀ s : Bytes, b32encode s = b32encode_imp s)
#eval Plausible.Testable.check (∀ (s : Bytes) (casefold : Bool) (map01 : Option UInt8),
  b32decode? s casefold map01 = b32decode?_imp s casefold map01 ∧
  b32decode s casefold map01 = b32decode_imp s casefold map01)

/-! ## 13. Equivalence Theorems: Functional = Imperative -/

theorem foldl_chunksOf5 (s : Bytes) (acc : Bytes) :
    List.foldl (fun encoded chunk => encoded ++ encodeSingleChunk chunk) acc (chunksOf5 s) =
      acc ++ b32encode s := by
  induction s using b32encode.induct generalizing acc with
  | case1 => simp [chunksOf5, b32encode]
  | case2 b0 => simp [chunksOf5, encodeSingleChunk]
  | case3 b0 b1 => simp [chunksOf5, encodeSingleChunk]
  | case4 b0 b1 b2 => simp [chunksOf5, encodeSingleChunk]
  | case5 b0 b1 b2 b3 => simp [chunksOf5, encodeSingleChunk]
  | case6 b0 b1 b2 b3 b4 rest ih =>
    rw [chunksOf5, List.foldl_cons]
    change List.foldl (fun encoded chunk => encoded ++ encodeSingleChunk chunk) (acc ++ encodeChunk5 b0 b1 b2 b3 b4) (chunksOf5 rest) =
      acc ++ b32encode (b0 :: b1 :: b2 :: b3 :: b4 :: rest)
    rw [ih, b32encode, List.append_assoc]

/-- Functional-imperative equivalence for `b32encode`. -/
theorem b32encode_equiv (s : Bytes) : b32encode s = b32encode_imp s := by
  have hrun :
      b32encode_imp s =
      List.foldl (fun encoded chunk => encoded ++ encodeSingleChunk chunk) [] (chunksOf5 s) := by
    simp [b32encode_imp]
  rw [hrun, foldl_chunksOf5, List.nil_append]

theorem foldl_decodeImpStep_none (cs : Bytes) (val bits : Nat) :
    (List.foldl decodeImpStep (none, val, bits) cs).1 = none := by
  induction cs generalizing val bits with
  | nil => rfl
  | cons c cs ih => exact ih val bits

theorem foldl_decodeImpStep_some (cs : Bytes) (acc : Bytes) (val bits : Nat) :
    (List.foldl decodeImpStep (some acc, val, bits) cs).1 =
      (decodeLoop cs val bits).map (fun rest => acc ++ rest) := by
  induction cs generalizing acc val bits with
  | nil => simp [decodeLoop]
  | cons c cs ih =>
    simp only [List.foldl_cons, decodeImpStep, decodeLoop]
    cases revB32Char c with
    | none => simp [foldl_decodeImpStep_none]
    | some k =>
      dsimp only
      cases (decodeStep val bits k).2.2 with
      | none =>
        simp only [ih]
        cases decodeLoop cs (decodeStep val bits k).1 (decodeStep val bits k).2.1 <;> rfl
      | some b =>
        simp only [ih]
        cases decodeLoop cs (decodeStep val bits k).1 (decodeStep val bits k).2.1 <;> simp [List.append_assoc]

/-- Functional-imperative equivalence for `b32decode?`. -/
theorem b32decode?_equiv (s : Bytes) (casefold : Bool := false) (map01 : Option UInt8 := none) :
    b32decode? s casefold map01 = b32decode?_imp s casefold map01 := by
  simp only [b32decode?, b32decode?_imp]
  have hrun :
      (Id.run do
        let mut st : Option Bytes × Nat × Nat := (some [], 0, 0)
        for char in rstripEq (applyCasefold casefold (applyMap01 map01 s)) do
          st := decodeImpStep st char
        return st.1) =
      (List.foldl decodeImpStep (some [], 0, 0) (rstripEq (applyCasefold casefold (applyMap01 map01 s)))).1 := by
    simp
  rw [hrun, foldl_decodeImpStep_some]
  cases decodeLoop _ 0 0 <;> rfl

/-- Functional-imperative equivalence for `b32decode`. -/
theorem b32decode_equiv (s : Bytes) (casefold : Bool := false) (map01 : Option UInt8 := none) :
    b32decode s casefold map01 = b32decode_imp s casefold map01 := by
  simp [b32decode, b32decode_imp, b32decode?_equiv]

/-- Functional-imperative equivalence for `benchmark_b32encode`. -/
theorem benchmark_b32encode_equiv (s : Bytes) :
    benchmark_b32encode s = benchmark_b32encode_imp s := by
  simp [benchmark_b32encode, benchmark_b32encode_imp, b32encode_equiv]

/-- Functional-imperative equivalence for `benchmark_b32decode`. -/
theorem benchmark_b32decode_equiv (s : Bytes) (casefold : Bool := false) (map01 : Option UInt8 := none) :
    benchmark_b32decode s casefold map01 = benchmark_b32decode_imp s casefold map01 := by
  simp [benchmark_b32decode, benchmark_b32decode_imp, b32decode_equiv]

end «23_base32»
