import Mathlib

/-!
# Base32 encoding and decoding (`b32encode` / `b32decode`)

Lean 4 formalization of the Python program `23_base32.py`, a self-contained
version of `base64.b32encode` / `base64.b32decode` from the standard library.

* Python `bytes` are modelled as `List UInt8`.  Python strings passed to
  `b32decode` are ASCII-encoded first, so they are also represented by their
  byte list; the Python pre-conditions (`pre_encode`, `pre_decode`) are type
  checks that the Lean types enforce by construction.
* `b32encode` groups the input into 5-byte chunks (the last one padded with
  zero bytes), writes each 40-bit chunk as eight 5-bit alphabet indices and
  finally overwrites the last `6/4/3/1` characters with `=` when the input
  length is `1/2/3/4 (mod 5)`.
* `b32decode` optionally maps `0 ↦ O` and `1 ↦ map01`, optionally upper-cases
  (`casefold`), strips trailing `=`, and then streams the 5-bit values into a
  bit buffer, emitting a byte every time 8 bits are available.  A character
  outside the alphabet raises `binascii.Error('Non-base32 digit found')`, which
  is modelled by `Except.error "Non-base32 digit found"`.

The file contains the functional implementation, unit tests, the pre-condition,
properties with proofs (length, alphabet/padding shape, round trip
`decode (encode s) = ok s`, injectivity, concatenation, decode length,
error characterization, case-insensitivity, padding insensitivity), the
post-condition and correctness theorem, property-based tests, an imperative
implementation using `Id.run do` and the proof that it agrees with the
functional one.
-/

namespace «23_base32»

set_option maxRecDepth 10000

/-! ## Functional implementation -/

/-- `_b32alphabet = b'ABCDEFGHIJKLMNOPQRSTUVWXYZ234567'` as a list of bytes. -/
def b32alphabet : List UInt8 :=
  [65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90,
   50, 51, 52, 53, 54, 55]

/-- `rev_alphabet = {v: k for k, v in enumerate(_b32alphabet)}`: index of a byte in the
alphabet, `none` when the byte is not a Base32 digit. -/
def revAlphabet (c : UInt8) : Option Nat := b32alphabet.idxOf? c

/-- `int.from_bytes(chunk, 'big')`. -/
def bytesToNat (l : List UInt8) : Nat := l.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- One iteration of the encoding loop: a chunk of at most 5 bytes is zero-padded to
5 bytes, read as a 40-bit big-endian integer and written as eight 5-bit indices. -/
def encodeChunk (chunk : List UInt8) : List UInt8 :=
  let chunk := if chunk.length < 5 then chunk ++ List.replicate (5 - chunk.length) 0 else chunk
  let val := bytesToNat chunk
  [b32alphabet.getD ((val >>> 35) &&& 0x1F) 0,
   b32alphabet.getD ((val >>> 30) &&& 0x1F) 0,
   b32alphabet.getD ((val >>> 25) &&& 0x1F) 0,
   b32alphabet.getD ((val >>> 20) &&& 0x1F) 0,
   b32alphabet.getD ((val >>> 15) &&& 0x1F) 0,
   b32alphabet.getD ((val >>> 10) &&& 0x1F) 0,
   b32alphabet.getD ((val >>> 5) &&& 0x1F) 0,
   b32alphabet.getD (val &&& 0x1F) 0]

/-- `for i in range(0, len(s), 5): chunk = s[i:i+5]; ...` -/
def encodeChunks : List UInt8 → List UInt8
  | [] => []
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest => encodeChunk [b0, b1, b2, b3, b4] ++ encodeChunks rest
  | short => encodeChunk short

/-- Number of `=` characters written for `rem = len(s) % 5`. -/
def padCount (rem : Nat) : Nat :=
  match rem with
  | 1 => 6
  | 2 => 4
  | 3 => 3
  | 4 => 1
  | _ => 0

/-- "Fix padding": `encoded[-k:] = b'=' * k` with `k = padCount rem`. -/
def fixPadding (encoded : List UInt8) (rem : Nat) : List UInt8 :=
  let k := padCount rem
  encoded.take (encoded.length - k) ++ List.replicate k 61

/-- `b32encode(s)`: Base32-encode a bytes-like object. -/
def b32encode (s : List UInt8) : List UInt8 :=
  fixPadding (encodeChunks s) (s.length % 5)

/-- `bytes.upper()` on a single byte: ASCII `a-z` become `A-Z`. -/
def upperByte (c : UInt8) : UInt8 := if 97 ≤ c ∧ c ≤ 122 then c - 32 else c

/-- ASCII lower-casing of a single byte (used to state case-insensitivity). -/
def lowerByte (c : UInt8) : UInt8 := if 65 ≤ c ∧ c ≤ 90 then c + 32 else c

/-- `s.replace(b'0', b'O').replace(b'1', map01)` on a single byte. -/
def map01Byte (m : UInt8) (c : UInt8) : UInt8 := if c = 48 then 79 else if c = 49 then m else c

/-- `s.rstrip(b'=')`. -/
def rstripEq (s : List UInt8) : List UInt8 := (s.reverse.dropWhile (· == 61)).reverse

/-- The byte string that is actually fed to the decoding loop: `map01` substitution,
optional `upper()`, then stripping of trailing `=`. -/
def decodeInput (s : List UInt8) (casefold : Bool) (map01 : Option UInt8) : List UInt8 :=
  let s := match map01 with
    | some m => s.map (map01Byte m)
    | none => s
  let s := if casefold then s.map upperByte else s
  rstripEq s

/-- The decoding loop: `val` is the bit buffer, `bits` the number of pending bits and
`acc` the bytes produced so far. -/
def decodeLoop : List UInt8 → Nat → Nat → List UInt8 → Except String (List UInt8)
  | [], _, _, acc => .ok acc
  | c :: rest, val, bits, acc =>
    match revAlphabet c with
    | none => .error "Non-base32 digit found"
    | some k =>
      let val' := (val <<< 5) ||| k
      let bits' := bits + 5
      if bits' ≥ 8 then
        decodeLoop rest val' (bits' - 8) (acc ++ [UInt8.ofNat ((val' >>> (bits' - 8)) &&& 0xFF)])
      else
        decodeLoop rest val' bits' acc

/-- `b32decode(s, casefold=False, map01=None)`: decode a Base32 byte string.
`Except.error "Non-base32 digit found"` models `binascii.Error`. -/
def b32decode (s : List UInt8) (casefold : Bool := false) (map01 : Option UInt8 := none) :
    Except String (List UInt8) :=
  decodeLoop (decodeInput s casefold map01) 0 0 []

/-- `benchmark_b32encode`. -/
def benchmark_b32encode (s : List UInt8) : List UInt8 := b32encode s

/-- `benchmark_b32decode`. -/
def benchmark_b32decode (s : List UInt8) (casefold : Bool := false) (map01 : Option UInt8 := none) :
    Except String (List UInt8) :=
  b32decode s casefold map01

/-! ## Unit tests (from `check`) -/

/-- Bytes of an ASCII string literal (test helper). -/
def bytes (s : String) : List UInt8 := s.toUTF8.toList

/-- Render a byte list as a string (test helper). -/
def asString (l : List UInt8) : String := String.fromUTF8! ⟨l.toArray⟩

deriving instance DecidableEq for Except

example : benchmark_b32encode (bytes "") = bytes "" := by native_decide
example : benchmark_b32encode (bytes "f") = bytes "MY======" := by native_decide
example : benchmark_b32encode (bytes "fo") = bytes "MZXQ====" := by native_decide
example : benchmark_b32encode (bytes "foo") = bytes "MZXW6===" := by native_decide
example : benchmark_b32encode (bytes "foob") = bytes "MZXW6YQ=" := by native_decide
example : benchmark_b32encode (bytes "fooba") = bytes "MZXW6YTB" := by native_decide
example : benchmark_b32encode (bytes "foobar") = bytes "MZXW6YTBOI======" := by native_decide
example : benchmark_b32decode (benchmark_b32encode (bytes "VeriBench")) = .ok (bytes "VeriBench") := by
  native_decide
example : benchmark_b32decode (bytes "mzxw6ytb") true = .ok (bytes "fooba") := by native_decide
example : benchmark_b32decode (bytes "MZXW6YTB") = .ok (bytes "fooba") := by native_decide
example : benchmark_b32decode (bytes "MZXW6YTBOI======") = .ok (bytes "foobar") := by native_decide
example : benchmark_b32decode (bytes "mzxw6ytb") = .error "Non-base32 digit found" := by native_decide
example : benchmark_b32decode (bytes "MZXW6YTB0I======") false (some 73) = .ok (bytes "foobar") := by
  native_decide

#eval asString (benchmark_b32encode (bytes "foobar"))
#eval (benchmark_b32decode (bytes "MZXW6YTBOI======")).map asString
#eval benchmark_b32decode (bytes "mzxw6ytb")
#eval (benchmark_b32decode (bytes "mzxw6ytb") true).map asString

/-! ## Pre-condition -/

/-- `pre_encode(s)`: `s` is a bytes-like object.  Byte lists are bytes-like by construction. -/
def Pre_encode (_s : List UInt8) : Prop := True

/-- `pre_decode(s)`: `s` is a bytes-like object or an ASCII string.  The Lean function takes
the (ASCII-encoded) bytes, which are always admissible. -/
def Pre_decode (_s : List UInt8) (_casefold : Bool) (_map01 : Option UInt8) : Prop := True

/-- Combined pre-condition for the two benchmark functions. -/
def Pre (s t : List UInt8) (casefold : Bool) (map01 : Option UInt8) : Prop :=
  Pre_encode s ∧ Pre_decode t casefold map01

/-! ## Helper lemmas: alphabet -/

theorem getD_mem (i : Nat) (hi : i < 32) : b32alphabet.getD i 0 ∈ b32alphabet := by
  revert i; decide +kernel

theorem eq_not_mem_alphabet : (61 : UInt8) ∉ b32alphabet := by decide +kernel

theorem revAlphabet_getD (i : Nat) (hi : i < 32) : revAlphabet (b32alphabet.getD i 0) = some i := by
  revert i; decide +kernel

theorem revAlphabet_eq_none_iff (c : UInt8) : revAlphabet c = none ↔ c ∉ b32alphabet :=
  List.idxOf?_eq_none_iff

/-! ## Helper lemmas: bit arithmetic -/

theorem shr_and_31 (v k : Nat) : (v >>> k) &&& 31 = v / 2 ^ k % 32 := by
  rw [Nat.shiftRight_eq_div_pow]
  have : (31 : Nat) = 2 ^ 5 - 1 := by norm_num
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

theorem and_31 (v : Nat) : v &&& 31 = v % 32 := by
  have : (31 : Nat) = 2 ^ 5 - 1 := by norm_num
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

theorem shr_and_255 (v k : Nat) : (v >>> k) &&& 255 = v / 2 ^ k % 256 := by
  rw [Nat.shiftRight_eq_div_pow]
  have : (255 : Nat) = 2 ^ 8 - 1 := by norm_num
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

theorem shl5_or (v k : Nat) (hk : k < 32) : (v <<< 5) ||| k = v * 32 + k := by
  rw [Nat.shiftLeft_eq, mul_comm, ← Nat.two_pow_add_eq_or_of_lt (by norm_num; exact hk)]
  norm_num

/-! ## Helper lemmas: the encoder -/

theorem length_encodeChunk (c : List UInt8) : (encodeChunk c).length = 8 := rfl

theorem encodeChunk5_eq (b0 b1 b2 b3 b4 : UInt8) :
    encodeChunk [b0, b1, b2, b3, b4] =
      let V := bytesToNat [b0, b1, b2, b3, b4]
      [b32alphabet.getD (V / 2 ^ 35 % 32) 0, b32alphabet.getD (V / 2 ^ 30 % 32) 0,
       b32alphabet.getD (V / 2 ^ 25 % 32) 0, b32alphabet.getD (V / 2 ^ 20 % 32) 0,
       b32alphabet.getD (V / 2 ^ 15 % 32) 0, b32alphabet.getD (V / 2 ^ 10 % 32) 0,
       b32alphabet.getD (V / 2 ^ 5 % 32) 0, b32alphabet.getD (V % 32) 0] := by
  simp [encodeChunk, shr_and_31, and_31]

theorem bytesToNat5 (b0 b1 b2 b3 b4 : UInt8) :
    bytesToNat [b0, b1, b2, b3, b4] =
      (((b0.toNat * 256 + b1.toNat) * 256 + b2.toNat) * 256 + b3.toNat) * 256 + b4.toNat := by
  simp only [bytesToNat, List.foldl_cons, List.foldl_nil]; omega

theorem encodeChunk_mem (c : List UInt8) : ∀ x ∈ encodeChunk c, x ∈ b32alphabet := by
  intro x hx
  simp only [encodeChunk, shr_and_31, and_31, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact getD_mem _ (Nat.mod_lt _ (by norm_num))

theorem encodeChunk_short (short : List UInt8) (h : short.length < 5) :
    encodeChunk short = encodeChunk (short ++ List.replicate (5 - short.length) 0) := by
  simp [encodeChunk, h]

theorem encodeChunks_cons5 (b0 b1 b2 b3 b4 : UInt8) (rest : List UInt8) :
    encodeChunks (b0 :: b1 :: b2 :: b3 :: b4 :: rest) = encodeChunk [b0, b1, b2, b3, b4] ++ encodeChunks rest := by
  simp [encodeChunks]

theorem encodeChunks_short (short : List UInt8) (h0 : short ≠ []) (h5 : short.length < 5) :
    encodeChunks short = encodeChunk short := by
  rcases short with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, rest⟩⟩⟩⟩⟩
  · exact absurd rfl h0
  all_goals simp [encodeChunks] at h5 ⊢

theorem encodeChunks_eq_take_drop (s : List UInt8) (h : s ≠ []) :
    encodeChunks s = encodeChunk (s.take 5) ++ encodeChunks (s.drop 5) := by
  rcases s with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, rest⟩⟩⟩⟩⟩
  · exact absurd rfl h
  all_goals simp [encodeChunks]

theorem length_encodeChunks (s : List UInt8) : (encodeChunks s).length = 8 * ((s.length + 4) / 5) := by
  induction s using encodeChunks.induct with
  | case1 => simp [encodeChunks]
  | case2 b0 b1 b2 b3 b4 rest ih =>
    rw [encodeChunks_cons5, List.length_append, length_encodeChunk, ih]
    simp only [List.length_cons]
    omega
  | case3 short h0 h5 =>
    have hlen : short.length < 5 := by
      rcases short with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, rest⟩⟩⟩⟩⟩
      · exact absurd rfl h0
      · simp
      · simp
      · simp
      · simp
      · exact absurd rfl (h5 b0 b1 b2 b3 b4 rest)
    have hne : short ≠ [] := h0
    rw [encodeChunks_short short hne hlen, length_encodeChunk]
    have : 1 ≤ short.length := List.length_pos_of_ne_nil hne
    omega

theorem encodeChunks_mem (s : List UInt8) : ∀ x ∈ encodeChunks s, x ∈ b32alphabet := by
  induction s using encodeChunks.induct with
  | case1 => simp [encodeChunks]
  | case2 b0 b1 b2 b3 b4 rest ih =>
    rw [encodeChunks_cons5]
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact encodeChunk_mem _ x hx
    · exact ih x hx
  | case3 short h0 h5 =>
    have hlen : short.length < 5 := by
      rcases short with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, rest⟩⟩⟩⟩⟩
      · exact absurd rfl h0
      · simp
      · simp
      · simp
      · simp
      · exact absurd rfl (h5 b0 b1 b2 b3 b4 rest)
    rw [encodeChunks_short short h0 hlen]
    exact encodeChunk_mem short

theorem padCount_le_six (rem : Nat) : padCount rem ≤ 6 := by
  unfold padCount; split <;> omega

theorem padCount_le (s : List UInt8) : padCount (s.length % 5) ≤ (encodeChunks s).length := by
  rw [length_encodeChunks]
  rcases s with _ | ⟨b, rest⟩
  · simp [padCount]
  · have := padCount_le_six ((b :: rest).length % 5)
    simp only [List.length_cons]
    omega

theorem fixPadding_zero (e : List UInt8) : fixPadding e 0 = e := by
  simp [fixPadding, padCount]

theorem length_fixPadding (e : List UInt8) (rem : Nat) (h : padCount rem ≤ e.length) :
    (fixPadding e rem).length = e.length := by
  simp only [fixPadding, List.length_append, List.length_take, List.length_replicate]
  omega

theorem fixPadding_append (A B : List UInt8) (rem : Nat) (h : padCount rem ≤ B.length) :
    fixPadding (A ++ B) rem = A ++ fixPadding B rem := by
  simp only [fixPadding, List.length_append, List.take_append]
  rw [List.take_of_length_le (by omega)]
  have : A.length + B.length - padCount rem - A.length = B.length - padCount rem := by omega
  rw [this, List.append_assoc]

theorem encodeChunks_append (s t : List UInt8) (h : s.length % 5 = 0) :
    encodeChunks (s ++ t) = encodeChunks s ++ encodeChunks t := by
  induction s using encodeChunks.induct with
  | case1 => simp [encodeChunks]
  | case2 b0 b1 b2 b3 b4 rest ih =>
    simp only [List.cons_append, encodeChunks_cons5, List.append_assoc]
    rw [ih]
    simp only [List.length_cons] at h
    omega
  | case3 short h0 h5 =>
    exfalso
    rcases short with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, rest⟩⟩⟩⟩⟩
    · exact h0 rfl
    all_goals simp at h
    exact h5 b0 b1 b2 b3 b4 rest rfl

/-! ## Helper lemmas: rstrip -/

theorem dropWhile_eq_self_of_not_mem (l : List UInt8) (h : (61 : UInt8) ∉ l) :
    l.dropWhile (· == 61) = l := by
  cases l with
  | nil => rfl
  | cons x xs =>
    have hx : x ≠ 61 := fun hx => h (hx ▸ List.mem_cons_self)
    simp [List.dropWhile_cons, hx]

theorem rstripEq_append_replicate (X : List UInt8) (k : Nat) :
    rstripEq (X ++ List.replicate k 61) = rstripEq X := by
  simp [rstripEq, List.reverse_append, List.dropWhile_append, List.dropWhile_replicate]

theorem rstripEq_of_not_mem (A : List UInt8) (hA : (61 : UInt8) ∉ A) : rstripEq A = A := by
  have : (61 : UInt8) ∉ A.reverse := by simpa using hA
  simp [rstripEq, dropWhile_eq_self_of_not_mem _ this]

/-! ## Helper lemmas: the decoder -/

theorem decodeLoop_nil (val bits : Nat) (acc : List UInt8) : decodeLoop [] val bits acc = .ok acc := rfl

theorem decodeLoop_cons_none {c : UInt8} (rest : List UInt8) (val bits : Nat) (acc : List UInt8)
    (h : revAlphabet c = none) :
    decodeLoop (c :: rest) val bits acc = .error "Non-base32 digit found" := by
  simp [decodeLoop, h]

theorem decodeLoop_cons_some {c : UInt8} {k : Nat} (rest : List UInt8) (val bits : Nat) (acc : List UInt8)
    (h : revAlphabet c = some k) :
    decodeLoop (c :: rest) val bits acc =
      if 8 ≤ bits + 5 then
        decodeLoop rest ((val <<< 5) ||| k) (bits + 5 - 8)
          (acc ++ [UInt8.ofNat ((((val <<< 5) ||| k) >>> (bits + 5 - 8)) &&& 255)])
      else decodeLoop rest ((val <<< 5) ||| k) (bits + 5) acc := by
  simp [decodeLoop, h]

theorem decodeLoop_cons_some' {c : UInt8} {k : Nat} (rest : List UInt8) (val bits : Nat) (acc : List UInt8)
    (h : revAlphabet c = some k) (hk : k < 32) :
    decodeLoop (c :: rest) val bits acc =
      if 8 ≤ bits + 5 then
        decodeLoop rest (val * 32 + k) (bits + 5 - 8)
          (acc ++ [UInt8.ofNat ((val * 32 + k) / 2 ^ (bits + 5 - 8) % 256)])
      else decodeLoop rest (val * 32 + k) (bits + 5) acc := by
  rw [decodeLoop_cons_some rest val bits acc h, shl5_or _ _ hk, shr_and_255]

/-- Decoding the 8 characters of a full chunk appends exactly the 5 chunk bytes. -/
theorem decodeLoop_chunk8 (b0 b1 b2 b3 b4 : UInt8) (rest : List UInt8) (val : Nat) (acc : List UInt8) :
    decodeLoop (encodeChunk [b0, b1, b2, b3, b4] ++ rest) val 0 acc =
      decodeLoop rest (val * 2 ^ 40 + bytesToNat [b0, b1, b2, b3, b4]) 0 (acc ++ [b0, b1, b2, b3, b4]) := by
  have hV := bytesToNat5 b0 b1 b2 b3 b4
  have h0 := UInt8.toNat_lt b0
  have h1 := UInt8.toNat_lt b1
  have h2 := UInt8.toNat_lt b2
  have h3 := UInt8.toNat_lt b3
  have h4 := UInt8.toNat_lt b4
  rw [encodeChunk5_eq]
  simp only []
  generalize bytesToNat [b0, b1, b2, b3, b4] = V at *
  have m32 : ∀ x : Nat, x % 32 < 32 := fun x => Nat.mod_lt _ (by norm_num)
  simp only [List.cons_append, List.nil_append]
  rw [decodeLoop_cons_some' _ _ _ _ (revAlphabet_getD _ (m32 _)) (m32 _), if_neg (by norm_num)]
  rw [decodeLoop_cons_some' _ _ _ _ (revAlphabet_getD _ (m32 _)) (m32 _), if_pos (by norm_num)]
  rw [decodeLoop_cons_some' _ _ _ _ (revAlphabet_getD _ (m32 _)) (m32 _), if_neg (by norm_num)]
  rw [decodeLoop_cons_some' _ _ _ _ (revAlphabet_getD _ (m32 _)) (m32 _), if_pos (by norm_num)]
  rw [decodeLoop_cons_some' _ _ _ _ (revAlphabet_getD _ (m32 _)) (m32 _), if_pos (by norm_num)]
  rw [decodeLoop_cons_some' _ _ _ _ (revAlphabet_getD _ (m32 _)) (m32 _), if_neg (by norm_num)]
  rw [decodeLoop_cons_some' _ _ _ _ (revAlphabet_getD _ (m32 _)) (m32 _), if_pos (by norm_num)]
  rw [decodeLoop_cons_some' _ _ _ _ (revAlphabet_getD _ (m32 _)) (m32 _), if_pos (by norm_num)]
  congr 1
  · omega
  · simp only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append,
      List.append_cancel_left_eq, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (rw [UInt8.ext_iff, UInt8.toNat_ofNat']; omega)

/-- Decoding the first 2 characters of a chunk yields its first byte. -/
theorem decodeLoop_chunk_take2 (b0 b1 b2 b3 b4 : UInt8) (val : Nat) (acc : List UInt8) :
    decodeLoop ((encodeChunk [b0, b1, b2, b3, b4]).take 2) val 0 acc = .ok (acc ++ [b0]) := by
  have hV := bytesToNat5 b0 b1 b2 b3 b4
  have h0 := UInt8.toNat_lt b0
  have h1 := UInt8.toNat_lt b1
  have h2 := UInt8.toNat_lt b2
  have h3 := UInt8.toNat_lt b3
  have h4 := UInt8.toNat_lt b4
  rw [encodeChunk5_eq]
  simp only []
  generalize bytesToNat [b0, b1, b2, b3, b4] = V at *
  have m32 : ∀ x : Nat, x % 32 < 32 := fun x => Nat.mod_lt _ (by norm_num)
  simp only [List.take_succ_cons, List.take_zero]
  rw [decodeLoop_cons_some' _ _ _ _ (revAlphabet_getD _ (m32 _)) (m32 _), if_neg (by norm_num)]
  rw [decodeLoop_cons_some' _ _ _ _ (revAlphabet_getD _ (m32 _)) (m32 _), if_pos (by norm_num)]
  rw [decodeLoop_nil]
  congr 2
  rw [UInt8.ext_iff, UInt8.toNat_ofNat']; omega

/-- Decoding the first 4 characters of a chunk yields its first 2 bytes. -/
theorem decodeLoop_chunk_take4 (b0 b1 b2 b3 b4 : UInt8) (val : Nat) (acc : List UInt8) :
    decodeLoop ((encodeChunk [b0, b1, b2, b3, b4]).take 4) val 0 acc = .ok (acc ++ [b0, b1]) := by
  have hV := bytesToNat5 b0 b1 b2 b3 b4
  have h0 := UInt8.toNat_lt b0
  have h1 := UInt8.toNat_lt b1
  have h2 := UInt8.toNat_lt b2
  have h3 := UInt8.toNat_lt b3
  have h4 := UInt8.toNat_lt b4
  rw [encodeChunk5_eq]
  simp only []
  generalize bytesToNat [b0, b1, b2, b3, b4] = V at *
  have m32 : ∀ x : Nat, x % 32 < 32 := fun x => Nat.mod_lt _ (by norm_num)
  simp only [List.take_succ_cons, List.take_zero]
  rw [decodeLoop_cons_some' _ _ _ _ (revAlphabet_getD _ (m32 _)) (m32 _), if_neg (by norm_num)]
  rw [decodeLoop_cons_some' _ _ _ _ (revAlphabet_getD _ (m32 _)) (m32 _), if_pos (by norm_num)]
  rw [decodeLoop_cons_some' _ _ _ _ (revAlphabet_getD _ (m32 _)) (m32 _), if_neg (by norm_num)]
  rw [decodeLoop_cons_some' _ _ _ _ (revAlphabet_getD _ (m32 _)) (m32 _), if_pos (by norm_num)]
  rw [decodeLoop_nil]
  congr 1
  simp only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append,
    List.append_cancel_left_eq, List.cons.injEq, and_true]
  refine ⟨?_, ?_⟩ <;> (rw [UInt8.ext_iff, UInt8.toNat_ofNat']; omega)

/-- Decoding the first 5 characters of a chunk yields its first 3 bytes. -/
theorem decodeLoop_chunk_take5 (b0 b1 b2 b3 b4 : UInt8) (val : Nat) (acc : List UInt8) :
    decodeLoop ((encodeChunk [b0, b1, b2, b3, b4]).take 5) val 0 acc = .ok (acc ++ [b0, b1, b2]) := by
  have hV := bytesToNat5 b0 b1 b2 b3 b4
  have h0 := UInt8.toNat_lt b0
  have h1 := UInt8.toNat_lt b1
  have h2 := UInt8.toNat_lt b2
  have h3 := UInt8.toNat_lt b3
  have h4 := UInt8.toNat_lt b4
  rw [encodeChunk5_eq]
  simp only []
  generalize bytesToNat [b0, b1, b2, b3, b4] = V at *
  have m32 : ∀ x : Nat, x % 32 < 32 := fun x => Nat.mod_lt _ (by norm_num)
  simp only [List.take_succ_cons, List.take_zero]
  rw [decodeLoop_cons_some' _ _ _ _ (revAlphabet_getD _ (m32 _)) (m32 _), if_neg (by norm_num)]
  rw [decodeLoop_cons_some' _ _ _ _ (revAlphabet_getD _ (m32 _)) (m32 _), if_pos (by norm_num)]
  rw [decodeLoop_cons_some' _ _ _ _ (revAlphabet_getD _ (m32 _)) (m32 _), if_neg (by norm_num)]
  rw [decodeLoop_cons_some' _ _ _ _ (revAlphabet_getD _ (m32 _)) (m32 _), if_pos (by norm_num)]
  rw [decodeLoop_cons_some' _ _ _ _ (revAlphabet_getD _ (m32 _)) (m32 _), if_pos (by norm_num)]
  rw [decodeLoop_nil]
  congr 1
  simp only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append,
    List.append_cancel_left_eq, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_⟩ <;> (rw [UInt8.ext_iff, UInt8.toNat_ofNat']; omega)

/-- Decoding the first 7 characters of a chunk yields its first 4 bytes. -/
theorem decodeLoop_chunk_take7 (b0 b1 b2 b3 b4 : UInt8) (val : Nat) (acc : List UInt8) :
    decodeLoop ((encodeChunk [b0, b1, b2, b3, b4]).take 7) val 0 acc = .ok (acc ++ [b0, b1, b2, b3]) := by
  have hV := bytesToNat5 b0 b1 b2 b3 b4
  have h0 := UInt8.toNat_lt b0
  have h1 := UInt8.toNat_lt b1
  have h2 := UInt8.toNat_lt b2
  have h3 := UInt8.toNat_lt b3
  have h4 := UInt8.toNat_lt b4
  rw [encodeChunk5_eq]
  simp only []
  generalize bytesToNat [b0, b1, b2, b3, b4] = V at *
  have m32 : ∀ x : Nat, x % 32 < 32 := fun x => Nat.mod_lt _ (by norm_num)
  simp only [List.take_succ_cons, List.take_zero]
  rw [decodeLoop_cons_some' _ _ _ _ (revAlphabet_getD _ (m32 _)) (m32 _), if_neg (by norm_num)]
  rw [decodeLoop_cons_some' _ _ _ _ (revAlphabet_getD _ (m32 _)) (m32 _), if_pos (by norm_num)]
  rw [decodeLoop_cons_some' _ _ _ _ (revAlphabet_getD _ (m32 _)) (m32 _), if_neg (by norm_num)]
  rw [decodeLoop_cons_some' _ _ _ _ (revAlphabet_getD _ (m32 _)) (m32 _), if_pos (by norm_num)]
  rw [decodeLoop_cons_some' _ _ _ _ (revAlphabet_getD _ (m32 _)) (m32 _), if_pos (by norm_num)]
  rw [decodeLoop_cons_some' _ _ _ _ (revAlphabet_getD _ (m32 _)) (m32 _), if_neg (by norm_num)]
  rw [decodeLoop_cons_some' _ _ _ _ (revAlphabet_getD _ (m32 _)) (m32 _), if_pos (by norm_num)]
  rw [decodeLoop_nil]
  congr 1
  simp only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append,
    List.append_cancel_left_eq, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (rw [UInt8.ext_iff, UInt8.toNat_ofNat']; omega)

/-- Core of the round trip: decoding the unpadded encoding of `s` (started from any buffer
value with no pending bits) returns `acc ++ s`. -/
theorem decodeLoop_encodeChunks (s : List UInt8) : ∀ (val : Nat) (acc : List UInt8),
    decodeLoop ((encodeChunks s).take ((encodeChunks s).length - padCount (s.length % 5))) val 0 acc =
      .ok (acc ++ s) := by
  induction s using encodeChunks.induct with
  | case1 => intro val acc; simp [encodeChunks, decodeLoop]
  | case2 b0 b1 b2 b3 b4 rest ih =>
    intro val acc
    have hle := padCount_le rest
    have hmod : (b0 :: b1 :: b2 :: b3 :: b4 :: rest).length % 5 = rest.length % 5 := by
      simp only [List.length_cons]; omega
    rw [encodeChunks_cons5, hmod, List.length_append, length_encodeChunk, List.take_append,
      length_encodeChunk, List.take_of_length_le (by omega)]
    have : 8 + (encodeChunks rest).length - padCount (rest.length % 5) - 8 =
        (encodeChunks rest).length - padCount (rest.length % 5) := by omega
    rw [this, decodeLoop_chunk8, ih]
    simp
  | case3 short h0 h5 =>
    intro val acc
    rcases short with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, rest⟩⟩⟩⟩⟩
    · exact absurd rfl h0
    · rw [encodeChunks_short _ (by simp) (by simp), encodeChunk_short _ (by simp)]
      simp only [List.length_singleton, Nat.reduceSub, List.replicate, List.singleton_append,
        length_encodeChunk, padCount]
      exact decodeLoop_chunk_take2 b0 0 0 0 0 val acc
    · rw [encodeChunks_short _ (by simp) (by simp), encodeChunk_short _ (by simp)]
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, List.replicate,
        List.cons_append, List.nil_append, length_encodeChunk, padCount, Nat.reduceMod]
      exact decodeLoop_chunk_take4 b0 b1 0 0 0 val acc
    · rw [encodeChunks_short _ (by simp) (by simp), encodeChunk_short _ (by simp)]
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, List.replicate,
        List.cons_append, List.nil_append, length_encodeChunk, padCount, Nat.reduceMod]
      exact decodeLoop_chunk_take5 b0 b1 b2 0 0 val acc
    · rw [encodeChunks_short _ (by simp) (by simp), encodeChunk_short _ (by simp)]
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, List.replicate,
        List.cons_append, List.nil_append, length_encodeChunk, padCount, Nat.reduceMod]
      exact decodeLoop_chunk_take7 b0 b1 b2 b3 0 val acc
    · exact absurd rfl (h5 b0 b1 b2 b3 b4 rest)

theorem decodeLoop_length (l : List UInt8) : ∀ (val bits : Nat) (acc r : List UInt8), bits < 8 →
    decodeLoop l val bits acc = .ok r → r.length = acc.length + (5 * l.length + bits) / 8 := by
  induction l with
  | nil =>
    intro val bits acc r hb h
    rw [decodeLoop_nil, Except.ok.injEq] at h
    subst h
    simp only [List.length_nil, mul_zero, zero_add]
    omega
  | cons c rest ih =>
    intro val bits acc r hb h
    cases hc : revAlphabet c with
    | none => rw [decodeLoop_cons_none _ _ _ _ hc] at h; exact absurd h (by simp)
    | some k =>
      rw [decodeLoop_cons_some _ _ _ _ hc] at h
      split_ifs at h with h8
      · have := ih _ _ _ _ (by omega) h
        simp only [List.length_append, List.length_singleton, List.length_cons] at this ⊢
        omega
      · have := ih _ _ _ _ (by omega) h
        simp only [List.length_cons] at this ⊢
        omega

theorem decodeLoop_ok_of_mem (l : List UInt8) : ∀ (val bits : Nat) (acc : List UInt8),
    (∀ c ∈ l, c ∈ b32alphabet) → ∃ r, decodeLoop l val bits acc = .ok r := by
  induction l with
  | nil => intro val bits acc _; exact ⟨acc, rfl⟩
  | cons c rest ih =>
    intro val bits acc hmem
    have hc : c ∈ b32alphabet := hmem c List.mem_cons_self
    have hrest : ∀ c ∈ rest, c ∈ b32alphabet := fun x hx => hmem x (List.mem_cons_of_mem c hx)
    cases hk : revAlphabet c with
    | none => exact absurd hc ((revAlphabet_eq_none_iff c).mp hk)
    | some k =>
      rw [decodeLoop_cons_some _ _ _ _ hk]
      split_ifs
      · exact ih _ _ _ hrest
      · exact ih _ _ _ hrest

theorem decodeLoop_error_of_not_mem (l : List UInt8) : ∀ (val bits : Nat) (acc : List UInt8),
    (∃ c ∈ l, c ∉ b32alphabet) → decodeLoop l val bits acc = .error "Non-base32 digit found" := by
  induction l with
  | nil => intro val bits acc h; obtain ⟨c, hc, _⟩ := h; simp at hc
  | cons c rest ih =>
    intro val bits acc h
    cases hk : revAlphabet c with
    | none => exact decodeLoop_cons_none _ _ _ _ hk
    | some k =>
      have hc : c ∈ b32alphabet := by
        by_contra hn
        rw [← revAlphabet_eq_none_iff] at hn
        rw [hn] at hk
        exact Option.noConfusion hk
      have hrest : ∃ c ∈ rest, c ∉ b32alphabet := by
        obtain ⟨x, hx, hxn⟩ := h
        rcases List.mem_cons.mp hx with rfl | hx
        · exact absurd hc hxn
        · exact ⟨x, hx, hxn⟩
      rw [decodeLoop_cons_some _ _ _ _ hk]
      split_ifs
      · exact ih _ _ _ hrest
      · exact ih _ _ _ hrest

theorem upperByte_map01Byte_lowerByte (m c : UInt8) :
    upperByte (map01Byte m (lowerByte c)) = upperByte (map01Byte m c) := by
  have hc := UInt8.toNat_lt c
  have hm := UInt8.toNat_lt m
  unfold upperByte lowerByte map01Byte
  split_ifs <;> simp_all only [UInt8.le_iff_toNat_le, UInt8.ext_iff, UInt8.toNat_add, UInt8.toNat_sub,
    UInt8.toNat_ofNat, not_and, not_le, Nat.reducePow, Nat.reduceMod] <;> omega

theorem map01Byte_61 (m : UInt8) : map01Byte m 61 = 61 := by
  simp [map01Byte]

theorem upperByte_61 : upperByte 61 = 61 := by decide

/-! ## Properties and theorems -/

/-- The encoding of `n` bytes has exactly `8 * ⌈n / 5⌉` characters. -/
def encode_length_prop (s : List UInt8) : Prop :=
  (b32encode s).length = 8 * ((s.length + 4) / 5)

theorem encode_length_thm (s : List UInt8) : encode_length_prop s := by
  unfold encode_length_prop b32encode
  rw [length_fixPadding _ _ (padCount_le s), length_encodeChunks]

/-- The encoding consists of Base32 digits followed by exactly `padCount (len % 5)` padding
characters `=`. -/
def encode_padding_prop (s : List UInt8) : Prop :=
  ∃ body : List UInt8, b32encode s = body ++ List.replicate (padCount (s.length % 5)) 61 ∧
    ∀ c ∈ body, c ∈ b32alphabet

theorem encode_padding_thm (s : List UInt8) : encode_padding_prop s := by
  refine ⟨(encodeChunks s).take ((encodeChunks s).length - padCount (s.length % 5)), rfl, ?_⟩
  intro c hc
  exact encodeChunks_mem s c (List.mem_of_mem_take hc)

/-- Every output byte is a Base32 digit or the padding character `=`. -/
def encode_alphabet_prop (s : List UInt8) : Prop :=
  ∀ c ∈ b32encode s, c ∈ b32alphabet ∨ c = 61

theorem encode_alphabet_thm (s : List UInt8) : encode_alphabet_prop s := by
  intro c hc
  obtain ⟨body, hb, hmem⟩ := encode_padding_thm s
  rw [hb, List.mem_append] at hc
  rcases hc with hc | hc
  · exact Or.inl (hmem c hc)
  · exact Or.inr (List.mem_replicate.mp hc).2

/-- Round trip: decoding an encoding returns the original bytes (`dec(enc(msg)) == msg`). -/
def encode_decode_prop (s : List UInt8) : Prop :=
  b32decode (b32encode s) false none = .ok s

theorem encode_decode_thm (s : List UInt8) : encode_decode_prop s := by
  unfold encode_decode_prop b32decode decodeInput b32encode fixPadding
  simp only [Bool.false_eq_true, if_false]
  rw [rstripEq_append_replicate, rstripEq_of_not_mem]
  · rw [decodeLoop_encodeChunks]; simp
  · intro h
    exact eq_not_mem_alphabet (encodeChunks_mem s 61 (List.mem_of_mem_take h))

/-- Encoding is injective. -/
def encode_injective_prop (s t : List UInt8) : Prop :=
  b32encode s = b32encode t → s = t

theorem encode_injective_thm (s t : List UInt8) : encode_injective_prop s t := by
  intro h
  have hs := encode_decode_thm s
  have ht := encode_decode_thm t
  unfold encode_decode_prop at hs ht
  rw [h, ht, Except.ok.injEq] at hs
  exact hs.symm

/-- Encoding is compositional on 5-byte boundaries: if `s` has a multiple of 5 bytes then
`enc(s + t) = enc(s) + enc(t)`. -/
def encode_append_prop (s t : List UInt8) : Prop :=
  s.length % 5 = 0 → b32encode (s ++ t) = b32encode s ++ b32encode t

theorem encode_append_thm (s t : List UInt8) : encode_append_prop s t := by
  intro h
  unfold b32encode
  rw [encodeChunks_append s t h, List.length_append]
  have hmod : (s.length + t.length) % 5 = t.length % 5 := by omega
  rw [hmod, fixPadding_append _ _ _ (padCount_le t), h, fixPadding_zero]

/-- A successful decode of `n` (stripped) characters yields `⌊5n / 8⌋` bytes. -/
def decode_length_prop (t : List UInt8) (casefold : Bool) (map01 : Option UInt8) : Prop :=
  ∀ r, b32decode t casefold map01 = .ok r → r.length = 5 * (decodeInput t casefold map01).length / 8

theorem decode_length_thm (t : List UInt8) (casefold : Bool) (map01 : Option UInt8) :
    decode_length_prop t casefold map01 := by
  intro r h
  have := decodeLoop_length _ 0 0 [] r (by norm_num) h
  simpa using this

/-- Decoding succeeds iff every character left after stripping `=` is a Base32 digit. -/
def decode_ok_iff_prop (t : List UInt8) (casefold : Bool) (map01 : Option UInt8) : Prop :=
  (∃ r, b32decode t casefold map01 = .ok r) ↔ ∀ c ∈ decodeInput t casefold map01, c ∈ b32alphabet

theorem decode_ok_iff_thm (t : List UInt8) (casefold : Bool) (map01 : Option UInt8) :
    decode_ok_iff_prop t casefold map01 := by
  unfold decode_ok_iff_prop b32decode
  constructor
  · rintro ⟨r, hr⟩
    by_contra hn
    have : ∃ c ∈ decodeInput t casefold map01, c ∉ b32alphabet := by
      push_neg at hn; exact hn
    rw [decodeLoop_error_of_not_mem _ _ _ _ this] at hr
    exact absurd hr (by simp)
  · intro h
    exact decodeLoop_ok_of_mem _ _ _ _ h

/-- Decoding raises `binascii.Error('Non-base32 digit found')` iff some character left after
stripping `=` is not a Base32 digit. -/
def decode_error_iff_prop (t : List UInt8) (casefold : Bool) (map01 : Option UInt8) : Prop :=
  b32decode t casefold map01 = .error "Non-base32 digit found" ↔
    ∃ c ∈ decodeInput t casefold map01, c ∉ b32alphabet

theorem decode_error_iff_thm (t : List UInt8) (casefold : Bool) (map01 : Option UInt8) :
    decode_error_iff_prop t casefold map01 := by
  unfold decode_error_iff_prop b32decode
  constructor
  · intro h
    by_contra hn
    have hall : ∀ c ∈ decodeInput t casefold map01, c ∈ b32alphabet := by
      push_neg at hn; exact hn
    obtain ⟨r, hr⟩ := decodeLoop_ok_of_mem _ 0 0 [] hall
    rw [hr] at h
    exact absurd h (by simp)
  · intro h
    exact decodeLoop_error_of_not_mem _ _ _ _ h

/-- With `casefold=True`, decoding is case-insensitive: lower-casing the input does not
change the result. -/
def decode_casefold_prop (t : List UInt8) (map01 : Option UInt8) : Prop :=
  b32decode (t.map lowerByte) true map01 = b32decode t true map01

theorem decode_casefold_thm (t : List UInt8) (map01 : Option UInt8) : decode_casefold_prop t map01 := by
  unfold decode_casefold_prop b32decode decodeInput
  cases map01 with
  | none =>
    simp only [List.map_map, if_true]
    congr 2
    apply List.map_congr_left
    intro c _
    have := upperByte_map01Byte_lowerByte 48 c
    simpa [map01Byte] using this
  | some m =>
    simp only [List.map_map, if_true]
    congr 2
    apply List.map_congr_left
    intro c _
    exact upperByte_map01Byte_lowerByte m c

/-- `casefold` is irrelevant when the input contains no lower-case letters. -/
def decode_casefold_irrelevant_prop (t : List UInt8) : Prop :=
  (∀ c ∈ t, ¬ (97 ≤ c ∧ c ≤ 122)) → b32decode t true none = b32decode t false none

theorem decode_casefold_irrelevant_thm (t : List UInt8) : decode_casefold_irrelevant_prop t := by
  intro h
  unfold b32decode decodeInput
  simp only [if_true, Bool.false_eq_true, if_false]
  congr 2
  rw [List.map_eq_self_iff]
  intro c hc
  simp [upperByte, h c hc]

/-- Trailing `=` characters are ignored by the decoder. -/
def decode_padding_prop (t : List UInt8) (casefold : Bool) (map01 : Option UInt8) (k : Nat) : Prop :=
  b32decode (t ++ List.replicate k 61) casefold map01 = b32decode t casefold map01

theorem decode_padding_thm (t : List UInt8) (casefold : Bool) (map01 : Option UInt8) (k : Nat) :
    decode_padding_prop t casefold map01 k := by
  unfold decode_padding_prop b32decode decodeInput
  cases map01 <;> cases casefold <;>
    simp [List.map_append, List.map_replicate, map01Byte_61, upperByte_61, rstripEq_append_replicate]

/-- `map01` replaces `0` by `O` and `1` by `map01` before decoding. -/
def decode_map01_prop (t : List UInt8) (casefold : Bool) (m : UInt8) : Prop :=
  b32decode t casefold (some m) = b32decode (t.map (map01Byte m)) casefold none

theorem decode_map01_thm (t : List UInt8) (casefold : Bool) (m : UInt8) : decode_map01_prop t casefold m := rfl

/-! ## Post-condition -/

/-- Post-condition: all properties of `b32encode` (on `s`) and `b32decode` (on `t`). -/
def Post_prop (s t : List UInt8) (casefold : Bool) (map01 : Option UInt8) : Prop :=
  encode_length_prop s ∧ encode_padding_prop s ∧ encode_alphabet_prop s ∧ encode_decode_prop s ∧
  encode_injective_prop s t ∧ encode_append_prop s t ∧
  decode_length_prop t casefold map01 ∧ decode_ok_iff_prop t casefold map01 ∧
  decode_error_iff_prop t casefold map01 ∧ decode_casefold_prop t map01 ∧
  decode_casefold_irrelevant_prop t ∧ (∀ k, decode_padding_prop t casefold map01 k) ∧
  (∀ m, decode_map01_prop t casefold m)

/-! ## Property-based tests -/

/-- Executable form of `encode_padding_prop` (the witness is the unpadded prefix). -/
def encode_padding_check (s : List UInt8) : Bool :=
  let e := b32encode s
  let body := e.take (e.length - padCount (s.length % 5))
  e == body ++ List.replicate (padCount (s.length % 5)) 61 && body.all (· ∈ b32alphabet)

/-- Executable form of `decode_length_prop`. -/
def decode_length_check (t : List UInt8) (casefold : Bool) (map01 : Option UInt8) : Bool :=
  match b32decode t casefold map01 with
  | .ok r => r.length == 5 * (decodeInput t casefold map01).length / 8
  | .error _ => true

/-- Executable form of `decode_ok_iff_prop`. -/
def decode_ok_iff_check (t : List UInt8) (casefold : Bool) (map01 : Option UInt8) : Bool :=
  (b32decode t casefold map01).toOption.isSome == (decodeInput t casefold map01).all (· ∈ b32alphabet)

/-- Executable form of `decode_error_iff_prop`. -/
def decode_error_iff_check (t : List UInt8) (casefold : Bool) (map01 : Option UInt8) : Bool :=
  (b32decode t casefold map01 == .error "Non-base32 digit found") ==
    (decodeInput t casefold map01).any (fun c => !(c ∈ b32alphabet : Bool))

/-- Executable form of `Post_prop` (the two universally quantified parts are sampled at `k`, `m`). -/
def post_check (s t : List UInt8) (casefold : Bool) (map01 : Option UInt8) (k : Nat) (m : UInt8) : Bool :=
  ((b32encode s).length == 8 * ((s.length + 4) / 5)) &&
  encode_padding_check s &&
  (b32encode s).all (fun c => c ∈ b32alphabet || c == 61) &&
  (b32decode (b32encode s) false none == .ok s) &&
  (b32encode s != b32encode t || s == t) &&
  (s.length % 5 != 0 || b32encode (s ++ t) == b32encode s ++ b32encode t) &&
  decode_length_check t casefold map01 &&
  decode_ok_iff_check t casefold map01 &&
  decode_error_iff_check t casefold map01 &&
  (b32decode (t.map lowerByte) true map01 == b32decode t true map01) &&
  (t.any (fun c => 97 ≤ c && c ≤ 122) || b32decode t true none == b32decode t false none) &&
  (b32decode (t ++ List.replicate k 61) casefold map01 == b32decode t casefold map01) &&
  (b32decode t casefold (some m) == b32decode (t.map (map01Byte m)) casefold none)

-- encode_length_prop
#eval Plausible.Testable.check (∀ s : List UInt8, (b32encode s).length = 8 * ((s.length + 4) / 5))
-- encode_padding_prop
#eval Plausible.Testable.check (∀ s : List UInt8, encode_padding_check s = true)
-- encode_alphabet_prop
#eval Plausible.Testable.check (∀ s : List UInt8, ∀ c ∈ b32encode s, c ∈ b32alphabet ∨ c = 61)
-- encode_decode_prop
#eval Plausible.Testable.check (∀ s : List UInt8, b32decode (b32encode s) false none = .ok s)
-- encode_injective_prop
#eval Plausible.Testable.check (∀ s t : List UInt8, b32encode s = b32encode t → s = t)
-- encode_append_prop (restricted to inputs with a multiple of 5 bytes by truncation)
#eval Plausible.Testable.check (∀ s t : List UInt8,
  b32encode (s.take (5 * (s.length / 5)) ++ t) = b32encode (s.take (5 * (s.length / 5))) ++ b32encode t)
-- decode_length_prop (random inputs, and inputs built from alphabet indices so that decoding succeeds)
#eval Plausible.Testable.check (∀ (t : List UInt8) (cf : Bool) (m : Option UInt8), decode_length_check t cf m = true)
#eval Plausible.Testable.check (∀ (idx : List (Fin 32)) (cf : Bool),
  decode_length_check (idx.map (fun i => b32alphabet.getD i.val 0)) cf none = true)
-- decode_ok_iff_prop
#eval Plausible.Testable.check (∀ (t : List UInt8) (cf : Bool) (m : Option UInt8), decode_ok_iff_check t cf m = true)
#eval Plausible.Testable.check (∀ (idx : List (Fin 32)) (cf : Bool),
  decode_ok_iff_check (idx.map (fun i => b32alphabet.getD i.val 0)) cf none = true)
-- decode_error_iff_prop
#eval Plausible.Testable.check (∀ (t : List UInt8) (cf : Bool) (m : Option UInt8), decode_error_iff_check t cf m = true)
-- decode_casefold_prop
#eval Plausible.Testable.check (∀ (t : List UInt8) (m : Option UInt8),
  b32decode (t.map lowerByte) true m = b32decode t true m)
#eval Plausible.Testable.check (∀ (s : List UInt8), b32decode ((b32encode s).map lowerByte) true none = .ok s)
-- decode_casefold_irrelevant_prop
#eval Plausible.Testable.check (∀ (t : List UInt8), (∀ c ∈ t, ¬ (97 ≤ c ∧ c ≤ 122)) →
  b32decode t true none = b32decode t false none)
#eval Plausible.Testable.check (∀ (s : List UInt8), b32decode (b32encode s) true none = b32decode (b32encode s) false none)
-- decode_padding_prop
#eval Plausible.Testable.check (∀ (t : List UInt8) (cf : Bool) (m : Option UInt8) (k : Nat),
  b32decode (t ++ List.replicate k 61) cf m = b32decode t cf m)
-- decode_map01_prop
#eval Plausible.Testable.check (∀ (t : List UInt8) (cf : Bool) (m : UInt8),
  b32decode t cf (some m) = b32decode (t.map (map01Byte m)) cf none)
-- Post_prop
#eval Plausible.Testable.check (∀ (s t : List UInt8) (cf : Bool) (m : Option UInt8) (k : Nat) (m' : UInt8),
  post_check s t cf m k m' = true)

-- Bounded exhaustive checks: round trip on every 1-byte input and on a grid of 2- and 6-byte inputs.
example : (List.range 256).all (fun b => b32decode (b32encode [UInt8.ofNat b]) false none = .ok [UInt8.ofNat b]) =
    true := by native_decide
example : ((List.range 16).flatMap fun a => (List.range 16).map fun b => [UInt8.ofNat (17 * a), UInt8.ofNat (17 * b)]).all
    (fun s => b32decode (b32encode s) false none = .ok s && (b32encode s).length = 8) = true := by native_decide
example : (List.range 256).all (fun b =>
    let s := [UInt8.ofNat b, UInt8.ofNat (255 - b), UInt8.ofNat (b / 2), UInt8.ofNat (b * 3), UInt8.ofNat (b + 7), 0]
    b32decode (b32encode s) false none = .ok s && encode_padding_check s) = true := by native_decide
example : (List.range 11).all (fun n => (b32encode (List.replicate n 0xAB)).length = 8 * ((n + 4) / 5)) = true := by
  native_decide

/-! ## Correctness theorem -/

theorem correctness_thm (s t : List UInt8) (casefold : Bool) (map01 : Option UInt8) :
    Pre s t casefold map01 → Post_prop s t casefold map01 := by
  intro _
  exact ⟨encode_length_thm s, encode_padding_thm s, encode_alphabet_thm s, encode_decode_thm s,
    encode_injective_thm s t, encode_append_thm s t, decode_length_thm t casefold map01,
    decode_ok_iff_thm t casefold map01, decode_error_iff_thm t casefold map01,
    decode_casefold_thm t map01, decode_casefold_irrelevant_thm t,
    fun k => decode_padding_thm t casefold map01 k, fun m => decode_map01_thm t casefold m⟩

/-! ## Imperative implementation -/

/-- Imperative `b32encode`, following the Python loop structure. -/
def b32encodeImp (s : List UInt8) : List UInt8 := Id.run do
  let mut encoded : Array UInt8 := #[]
  -- Process 5-byte chunks: `for i in range(0, len(s), 5)`
  for i in List.range' 0 ((s.length + 4) / 5) 5 do
    let mut chunk := (s.drop i).take 5
    -- Pad chunk to 5 bytes with 0 for bit calculation
    if chunk.length < 5 then
      chunk := chunk ++ List.replicate (5 - chunk.length) 0
    -- Combine into a 40-bit integer and extract 8 5-bit indices
    let val := bytesToNat chunk
    encoded := encoded.push (b32alphabet.getD ((val >>> 35) &&& 0x1F) 0)
    encoded := encoded.push (b32alphabet.getD ((val >>> 30) &&& 0x1F) 0)
    encoded := encoded.push (b32alphabet.getD ((val >>> 25) &&& 0x1F) 0)
    encoded := encoded.push (b32alphabet.getD ((val >>> 20) &&& 0x1F) 0)
    encoded := encoded.push (b32alphabet.getD ((val >>> 15) &&& 0x1F) 0)
    encoded := encoded.push (b32alphabet.getD ((val >>> 10) &&& 0x1F) 0)
    encoded := encoded.push (b32alphabet.getD ((val >>> 5) &&& 0x1F) 0)
    encoded := encoded.push (b32alphabet.getD (val &&& 0x1F) 0)
  -- Fix padding
  let rem := s.length % 5
  let mut out := encoded.toList
  if rem == 1 then out := out.take (out.length - 6) ++ List.replicate 6 61
  else if rem == 2 then out := out.take (out.length - 4) ++ List.replicate 4 61
  else if rem == 3 then out := out.take (out.length - 3) ++ List.replicate 3 61
  else if rem == 4 then out := out.take (out.length - 1) ++ List.replicate 1 61
  return out

/-- Imperative `b32decode`, following the Python loop structure (`raise` becomes an early
`return .error`). -/
def b32decodeImp (s : List UInt8) (casefold : Bool := false) (map01 : Option UInt8 := none) :
    Except String (List UInt8) := Id.run do
  let mut s := s
  if let some m := map01 then
    s := s.map (map01Byte m)
  if casefold then
    s := s.map upperByte
  s := rstripEq s
  let mut decoded : Array UInt8 := #[]
  let mut val : Nat := 0
  let mut bits : Nat := 0
  for c in s do
    match revAlphabet c with
    | none => return .error "Non-base32 digit found"
    | some k =>
      val := (val <<< 5) ||| k
      bits := bits + 5
      if bits ≥ 8 then
        bits := bits - 8
        decoded := decoded.push (UInt8.ofNat ((val >>> bits) &&& 0xFF))
  return .ok decoded.toList

/-! ## Imperative tests -/

example : b32encodeImp (bytes "") = bytes "" := by native_decide
example : b32encodeImp (bytes "f") = bytes "MY======" := by native_decide
example : b32encodeImp (bytes "fo") = bytes "MZXQ====" := by native_decide
example : b32encodeImp (bytes "foo") = bytes "MZXW6===" := by native_decide
example : b32encodeImp (bytes "foob") = bytes "MZXW6YQ=" := by native_decide
example : b32encodeImp (bytes "fooba") = bytes "MZXW6YTB" := by native_decide
example : b32encodeImp (bytes "foobar") = bytes "MZXW6YTBOI======" := by native_decide
example : b32decodeImp (b32encodeImp (bytes "VeriBench")) = .ok (bytes "VeriBench") := by native_decide
example : b32decodeImp (bytes "mzxw6ytb") true = .ok (bytes "fooba") := by native_decide
example : b32decodeImp (bytes "mzxw6ytb") = .error "Non-base32 digit found" := by native_decide

#eval asString (b32encodeImp (bytes "foobar"))
#eval (b32decodeImp (bytes "mzxw6ytb") true).map asString

#eval Plausible.Testable.check (∀ s : List UInt8, b32encodeImp s = b32encode s)
#eval Plausible.Testable.check (∀ (t : List UInt8) (cf : Bool) (m : Option UInt8), b32decodeImp t cf m = b32decode t cf m)

/-! ## Equivalence theorems -/

/-- State of the imperative decoding loop (`return` slot, `bits`, `decoded`, `val`). -/
abbrev DecodeState := MProd (Option (Except String (List UInt8))) (MProd Nat (MProd (Array UInt8) Nat))

theorem forIn_decode (l : List UInt8) (val bits : Nat) (decoded : Array UInt8) :
    (let r := forIn (m := Id) l (⟨none, bits, decoded, val⟩ : DecodeState) fun c r =>
          have r := r.snd;
          have bits := r.fst;
          have x := r.snd;
          have decoded := x.fst;
          have val := x.snd;
          match revAlphabet c with
          | none => pure (ForInStep.done ⟨some (Except.error "Non-base32 digit found"), bits, decoded, val⟩)
          | some k =>
            have val := val <<< 5 ||| k;
            have bits := bits + 5;
            if bits ≥ 8 then
              have bits := bits - 8;
              have decoded := decoded.push (UInt8.ofNat (val >>> bits &&& 255));
              pure (ForInStep.yield ⟨none, bits, decoded, val⟩)
            else
              pure (ForInStep.yield ⟨none, bits, decoded, val⟩)
     match r.fst with
     | none => Except.ok r.snd.snd.fst.toList
     | some a => a) = decodeLoop l val bits decoded.toList := by
  induction l generalizing val bits decoded with
  | nil => rfl
  | cons c rest ih =>
    rw [List.forIn_cons]
    simp only [decodeLoop]
    cases h : revAlphabet c with
    | none => simp
    | some k =>
      split_ifs with hb
      · have := ih (val <<< 5 ||| k) (bits + 5 - 8)
          (decoded.push (UInt8.ofNat ((val <<< 5 ||| k) >>> (bits + 5 - 8) &&& 255)))
        simp only [Array.toList_push] at this
        simpa using this
      · have := ih (val <<< 5 ||| k) (bits + 5) decoded
        simpa using this

theorem b32decode_imp_eq (s : List UInt8) (casefold : Bool) (map01 : Option UInt8) :
    b32decodeImp s casefold map01 = b32decode s casefold map01 := by
  have h := forIn_decode (decodeInput s casefold map01) 0 0 #[]
  unfold b32decode
  rw [← h]
  unfold b32decodeImp decodeInput
  cases map01 <;> cases casefold <;> rfl

theorem forIn_encode (t : List UInt8) (q : Nat) : ∀ (off : Nat) (acc : Array UInt8),
    q = ((t.drop off).length + 4) / 5 →
    (forIn (m := Id) (List.range' off q 5) acc fun i r =>
        have encoded := r;
        have chunk := List.take 5 (List.drop i t);
        have __do_jp := fun chunk encoded (_y : PUnit) =>
          have val := bytesToNat chunk;
          have encoded := encoded.push (b32alphabet.getD (val >>> 35 &&& 31) 0);
          have encoded := encoded.push (b32alphabet.getD (val >>> 30 &&& 31) 0);
          have encoded := encoded.push (b32alphabet.getD (val >>> 25 &&& 31) 0);
          have encoded := encoded.push (b32alphabet.getD (val >>> 20 &&& 31) 0);
          have encoded := encoded.push (b32alphabet.getD (val >>> 15 &&& 31) 0);
          have encoded := encoded.push (b32alphabet.getD (val >>> 10 &&& 31) 0);
          have encoded := encoded.push (b32alphabet.getD (val >>> 5 &&& 31) 0);
          have encoded := encoded.push (b32alphabet.getD (val &&& 31) 0);
          (pure (ForInStep.yield encoded) : Id (ForInStep (Array UInt8)));
        if chunk.length < 5 then
          have chunk := chunk ++ List.replicate (5 - chunk.length) 0;
          __do_jp chunk encoded PUnit.unit
        else
          __do_jp chunk encoded PUnit.unit).toList = acc.toList ++ encodeChunks (t.drop off) := by
  induction q with
  | zero =>
    intro off acc hq
    have : (t.drop off).length = 0 := by omega
    rw [List.length_eq_zero_iff] at this
    simp [this, encodeChunks]
  | succ q ih =>
    intro off acc hq
    have hne : t.drop off ≠ [] := by
      intro h
      rw [h] at hq
      simp at hq
    rw [List.range'_succ, List.forIn_cons]
    rw [encodeChunks_eq_take_drop _ hne, List.drop_drop]
    have hq' : q = ((t.drop (off + 5)).length + 4) / 5 := by
      simp only [List.length_drop] at hq ⊢; omega
    simp only []
    split_ifs with hc
    · simp only [Id.run, bind, pure]
      rw [ih (off + 5) _ hq']
      simp [Array.toList_push, encodeChunk, hc]
    · simp only [Id.run, bind, pure]
      rw [ih (off + 5) _ hq']
      simp [Array.toList_push, encodeChunk, hc]

theorem b32encode_imp_eq (s : List UInt8) : b32encodeImp s = b32encode s := by
  have h := forIn_encode s ((s.length + 4) / 5) 0 #[] (by simp)
  simp only [List.drop_zero, Array.toList_empty, List.nil_append] at h
  unfold b32encodeImp b32encode fixPadding
  sorry

end «23_base32»
