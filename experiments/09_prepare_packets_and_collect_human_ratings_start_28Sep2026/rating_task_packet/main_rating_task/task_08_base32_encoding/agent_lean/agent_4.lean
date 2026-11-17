import Mathlib
import Plausible

/-!
# Base32 encoding and decoding

Lean 4 formalization of a Base32 codec, following the supplied Python program
(itself a simplified reading of Python's `base64.b32encode` / `b32decode`).

Bytes are modelled as `List Nat`. A list is a bytes-like object when every
element is `< 256` (`Pre`). Encoding always emits the RFC 4648 alphabet
`ABCDEFGHIJKLMNOPQRSTUVWXYZ234567` with `=` padding. Decoding accepts raw
bytes (or an ASCII string), optionally case-folds and applies the `map01`
substitution, strips trailing `=`, and raises the Python error
`Non-base32 digit found` on any other character. Bit accumulation matches the
Python loop (`val = (val << 5) | idx`, emit a byte whenever `bits ≥ 8`).
-/

namespace «23_base32»

/-- Base32 alphabet `ABCDEFGHIJKLMNOPQRSTUVWXYZ234567`. -/
def b32alphabet : List Nat :=
  [65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80,
   81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 50, 51, 52, 53, 54, 55]

/-- ASCII `'='`, the Base32 padding character. -/
def eqByte : Nat := 61

/-- ASCII `'0'`. -/
def zeroByte : Nat := 48

/-- ASCII `'O'`, the image of `'0'` under `map01`. -/
def ohByte : Nat := 79

/-- ASCII `'1'`. -/
def oneByte : Nat := 49

theorem alphabet_length : b32alphabet.length = 32 := by decide

/-- Map a 5-bit index to its alphabet character. Out-of-range indices yield `0`. -/
def alphabetAt (i : Nat) : Nat :=
  b32alphabet.getD i 0

/-- Inverse alphabet lookup, matching `{ch: i for i, ch in enumerate(alphabet)}`. -/
def revIndex (c : Nat) : Option Nat :=
  b32alphabet.idxOf? c

/-- Eight 5-bit indices of `v`, most-significant group first.
    Mirrors `(v >> 35) & 0x1F`, …, `v & 0x1F`. -/
def indicesOf40 (v : Nat) : List Nat :=
  [(v >>> 35) &&& 31, (v >>> 30) &&& 31, (v >>> 25) &&& 31, (v >>> 20) &&& 31,
   (v >>> 15) &&& 31, (v >>> 10) &&& 31, (v >>> 5) &&& 31, v &&& 31]

/-- Big-endian integer value of a byte string (`int.from_bytes(..., 'big')`). -/
def bytesToNat : List Nat → Nat
  | [] => 0
  | b :: bs => b * 256 ^ bs.length + bytesToNat bs

/-- How many non-padding characters a final chunk of `k` bytes produces. -/
def sigCount : Nat → Nat
  | 1 => 2
  | 2 => 4
  | 3 => 5
  | 4 => 7
  | _ => 8

/-- How many trailing `'='` bytes Python writes for `len(s) % 5 = r`. -/
def padCount : Nat → Nat
  | 1 => 6
  | 2 => 4
  | 3 => 3
  | 4 => 1
  | _ => 0

/-- Eight alphabet characters for one (already length-≤5) chunk, before padding. -/
def chunkRaw (chunk : List Nat) : List Nat :=
  let padded := chunk ++ List.replicate (5 - chunk.length) 0
  (indicesOf40 (bytesToNat padded)).map alphabetAt

/-- Raw 8-character groups for every 5-byte block, with no `'='` substitution yet. -/
def rawGroups : List Nat → List Nat
  | [] => []
  | x :: xs =>
    chunkRaw ((x :: xs).take 5) ++ rawGroups ((x :: xs).drop 5)
termination_by l => l.length
decreasing_by
  simp [List.length_drop]
  omega

/-- Python's final slice assignment that overwrites the unused tail with `'='`. -/
def applyTailPadding (encoded : List Nat) (rem : Nat) : List Nat :=
  match rem with
  | 1 => encoded.take (encoded.length - 6) ++ List.replicate 6 eqByte
  | 2 => encoded.take (encoded.length - 4) ++ List.replicate 4 eqByte
  | 3 => encoded.take (encoded.length - 3) ++ List.replicate 3 eqByte
  | 4 => encoded.take (encoded.length - 1) ++ [eqByte]
  | _ => encoded

/-- `b32encode`: Base32-encode a byte string. -/
def b32encode (s : List Nat) : List Nat :=
  applyTailPadding (rawGroups s) (s.length % 5)

/-- Replace every `a` in `s` by the byte string `rep` (Python `bytes.replace`). -/
def replaceAll (s : List Nat) (a : Nat) (rep : List Nat) : List Nat :=
  s.flatMap fun c => if c = a then rep else [c]

/-- `map01` substitution. `none` and `some []` are falsy, as in Python. -/
def applyMap01 (s : List Nat) (map01 : Option (List Nat)) : List Nat :=
  match map01 with
  | none => s
  | some m =>
    if m.isEmpty then s
    else replaceAll (replaceAll s zeroByte [ohByte]) oneByte m

/-- ASCII `bytes.upper` / `str.upper`: only `a`–`z` move. -/
def asciiUpper (n : Nat) : Nat :=
  if n ≥ 97 ∧ n ≤ 122 then n - 32 else n

/-- ASCII lowercase, used to state the case-fold round-trip. -/
def asciiLower (n : Nat) : Nat :=
  if n ≥ 65 ∧ n ≤ 90 then n + 32 else n

/-- `bytes.rstrip(b'=')`. -/
def rstripEq (s : List Nat) : List Nat :=
  (s.reverse.dropWhile (· == eqByte)).reverse

/-- Normalize a decode input: `map01`, then optional case-fold, then strip `=`. -/
def normalize (s : List Nat) (casefold : Bool) (map01 : Option (List Nat)) : List Nat :=
  let s1 := applyMap01 s map01
  let s2 := if casefold then s1.map asciiUpper else s1
  rstripEq s2

/-- Streaming bit accumulator from the Python decoder.
    Returns `(output, finalVal, finalBits)`. -/
def decodeGo (val bits : Nat) (acc : List Nat) : List Nat → List Nat × Nat × Nat
  | [] => (acc, val, bits)
  | c :: cs =>
    let val' := (val <<< 5) ||| c
    let bits' := bits + 5
    if bits' ≥ 8 then
      let bits'' := bits' - 8
      let b := (val' >>> bits'') &&& 255
      decodeGo val' bits'' (acc ++ [b]) cs
    else
      decodeGo val' bits' acc cs

/-- Bytes emitted by the bit accumulator. -/
def decodeAcc (idxs : List Nat) : List Nat :=
  (decodeGo 0 0 [] idxs).1

/-- Look up every character. `none` if any character is outside the alphabet. -/
def lookupAll : List Nat → Option (List Nat)
  | [] => some []
  | c :: cs =>
    match revIndex c, lookupAll cs with
    | some i, some is => some (i :: is)
    | _, _ => none

/-- Error string used by the Python program (`binascii.Error`). -/
def nonBase32Msg : String := "Non-base32 digit found"

/-- `b32decode`. `casefold` uppercases first; `map01` rewrites `'0'`/`'1'`. -/
def b32decode (s : List Nat) (casefold : Bool := false) (map01 : Option (List Nat) := none) :
    Except String (List Nat) :=
  match lookupAll (normalize s casefold map01) with
  | none => .error nonBase32Msg
  | some idxs => .ok (decodeAcc idxs)

/-- ASCII check used by the string entry point (`str.encode('ascii')`). -/
def isAsciiString (s : String) : Bool :=
  s.toList.all (fun c => decide (c.toNat < 128))

/-- Decode an ASCII string, or fail the way `str.encode('ascii')` fails. -/
def b32decodeString (s : String) (casefold : Bool := false) (map01 : Option (List Nat) := none) :
    Except String (List Nat) :=
  if isAsciiString s then
    b32decode (s.toList.map (fun c => c.toNat)) casefold map01
  else
    .error "UnicodeEncodeError"

/-- Python `benchmark_b32encode`. The `pre_encode` guard is a no-op (`pass`). -/
def benchmark_b32encode (s : List Nat) : List Nat :=
  b32encode s

/-- Python `benchmark_b32decode`. The `pre_decode` guard is a no-op (`pass`). -/
def benchmark_b32decode (s : List Nat) (casefold : Bool := false)
    (map01 : Option (List Nat) := none) : Except String (List Nat) :=
  b32decode s casefold map01

/-- Byte codes of an ASCII string. -/
def bytesOf (s : String) : List Nat :=
  s.toList.map (fun c => c.toNat)

/-! ## Unit tests -/

example : b32encode (bytesOf "") = bytesOf "" := by native_decide
example : b32encode (bytesOf "f") = bytesOf "MY======" := by native_decide
example : b32encode (bytesOf "fo") = bytesOf "MZXQ====" := by native_decide
example : b32encode (bytesOf "foo") = bytesOf "MZXW6===" := by native_decide
example : b32encode (bytesOf "foob") = bytesOf "MZXW6YQ=" := by native_decide
example : b32encode (bytesOf "fooba") = bytesOf "MZXW6YTB" := by native_decide
example : b32encode (bytesOf "foobar") = bytesOf "MZXW6YTBOI======" := by native_decide

example : b32decode (b32encode (bytesOf "VeriBench")) false none = .ok (bytesOf "VeriBench") := by
  native_decide

example : b32decode (bytesOf "mzxw6ytb") true none = .ok (bytesOf "fooba") := by
  native_decide

example : b32decode (bytesOf "MY======") false none = .ok (bytesOf "f") := by
  native_decide

example : b32decodeString "MY======" false none = .ok (bytesOf "f") := by
  native_decide

example : b32decode (bytesOf "M!") false none = .error nonBase32Msg := by
  native_decide

/-- Python `check`, packaged as a Boolean. -/
def check : Bool :=
  b32encode (bytesOf "") == bytesOf "" &&
  b32encode (bytesOf "f") == bytesOf "MY======" &&
  b32encode (bytesOf "fo") == bytesOf "MZXQ====" &&
  b32encode (bytesOf "foo") == bytesOf "MZXW6===" &&
  b32encode (bytesOf "foob") == bytesOf "MZXW6YQ=" &&
  b32encode (bytesOf "fooba") == bytesOf "MZXW6YTB" &&
  b32encode (bytesOf "foobar") == bytesOf "MZXW6YTBOI======" &&
  (match b32decode (b32encode (bytesOf "VeriBench")) false none with
    | .ok r => r == bytesOf "VeriBench"
    | .error _ => false) &&
  (match b32decode (bytesOf "mzxw6ytb") true none with
    | .ok r => r == bytesOf "fooba"
    | .error _ => false)

example : check = true := by native_decide

#eval b32encode (bytesOf "foobar")
#eval check

/-! ## Pre-condition

Python `pre_encode` holds exactly for bytes-like objects, and `pre_decode`
holds for bytes-like objects or ASCII strings. In this model a bytes-like
object is a `List Nat` whose elements are bytes (`< 256`). The string
restriction is `PreStr`.
-/

/-- Input is a bytes-like object: every element is a single byte. -/
def Pre (s : List Nat) : Prop :=
  ∀ x ∈ s, x < 256

/-- Input string is ASCII, so `str.encode('ascii')` succeeds. -/
def PreStr (s : String) : Prop :=
  ∀ c ∈ s.toList, c.toNat < 128

/-! ## Properties -/

/-- Decoding an encoding recovers the original bytes. -/
def roundtrip_prop (s : List Nat) : Prop :=
  b32decode (b32encode s) false none = Except.ok s

/-- Encoded length is `8 * ceil(n / 5)`, and `0` when `n = 0`. -/
def encode_length_prop (s : List Nat) : Prop :=
  (b32encode s).length = 8 * ((s.length + 4) / 5)

/-- The tail of `'='` has the Python padding width, and the head is alphabet. -/
def padding_prop (s : List Nat) : Prop :=
  let e := b32encode s
  let p := padCount (s.length % 5)
  p ≤ e.length ∧
    e.drop (e.length - p) = List.replicate p eqByte ∧
    ∀ c ∈ e.take (e.length - p), c ∈ b32alphabet

/-- Every encoded byte is an alphabet character or `'='`. -/
def alphabet_prop (s : List Nat) : Prop :=
  ∀ c ∈ b32encode s, c ∈ b32alphabet ∨ c = eqByte

/-- Case-folding accepts the lowercased encoding. -/
def casefold_roundtrip_prop (s : List Nat) : Prop :=
  b32decode ((b32encode s).map asciiLower) true none = Except.ok s

/-- With a truthy `map01`, rewriting `'O'` to `'0'` still decodes. -/
def map01_roundtrip_prop (s : List Nat) : Prop :=
  ∀ m : List Nat, m ≠ [] →
    b32decode ((b32encode s).map fun c => if c = ohByte then zeroByte else c)
        false (some m) =
      Except.ok s

/-- Extra trailing `'='` does not change a canonical decoding. -/
def extra_pad_prop (s : List Nat) : Prop :=
  ∀ n : Nat,
    b32decode (b32encode s ++ List.replicate n eqByte) false none = Except.ok s

/-- A non-alphabet character after normalization is the Python error. -/
def invalid_digit_prop (s : List Nat) (casefold : Bool) (map01 : Option (List Nat)) : Prop :=
  (∃ c ∈ normalize s casefold map01, revIndex c = none) →
    b32decode s casefold map01 = Except.error nonBase32Msg

/-- `'0'` becomes `'O'` under a truthy `map01` when `'1'` is absent. -/
def map01_zero_prop (s : List Nat) (m : List Nat) : Prop :=
  m ≠ [] → oneByte ∉ s →
    b32decode s false (some m) =
      b32decode (s.map fun c => if c = zeroByte then ohByte else c) false none

/-- A block whose length is a multiple of 5 encodes independently of the suffix. -/
def chunk_concat_prop (s t : List Nat) : Prop :=
  s.length % 5 = 0 → b32encode (s ++ t) = b32encode s ++ b32encode t

/-- An ASCII string decodes as its byte codes. -/
def string_ascii_prop (s : String) (casefold : Bool) (map01 : Option (List Nat)) : Prop :=
  b32decodeString s casefold map01 =
    b32decode (s.toList.map (fun c => c.toNat)) casefold map01

/-! ## Lemmas -/

lemma two_pow_5 : 2 ^ 5 = 32 := rfl
lemma two_pow_8 : 2 ^ 8 = 256 := rfl

lemma shift5_or (val c : Nat) (hc : c < 32) :
    (val <<< 5) ||| c = val * 32 + c := by
  have hc' : c < 2 ^ 5 := by simpa [two_pow_5] using hc
  have h := Nat.two_pow_add_eq_or_of_lt hc' val
  rw [Nat.shiftLeft_eq, Nat.mul_comm, two_pow_5]
  simpa [two_pow_5, Nat.mul_comm] using h.symm

lemma shr_and_byte (v n : Nat) :
    (v >>> n) &&& 255 = v / 2 ^ n % 256 := by
  rw [Nat.shiftRight_eq_div_pow]
  have h := Nat.and_two_pow_sub_one_eq_mod (v / 2 ^ n) 8
  simpa [two_pow_8] using h

lemma pow32 (k : Nat) : 32 ^ k = 2 ^ (5 * k) := by
  rw [← two_pow_5, ← Nat.pow_mul]

lemma and31_lt (v s : Nat) : (v >>> s) &&& 31 < 32 := by
  have h := Nat.and_lt_two_pow ((v >>> s)) (y := 31) (n := 5) (by decide : 31 < 2 ^ 5)
  simpa [two_pow_5] using h

lemma indices_lt (v : Nat) : ∀ i ∈ indicesOf40 v, i < 32 := by
  intro i hi
  simp only [indicesOf40, List.mem_cons, List.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact and31_lt _ _

lemma bytesToNat_append (xs ys : List Nat) :
    bytesToNat (xs ++ ys) = bytesToNat xs * 256 ^ ys.length + bytesToNat ys := by
  induction xs with
  | nil => simp [bytesToNat]
  | cons b xs ih =>
    simp only [List.cons_append, bytesToNat, List.length_append, ih, Nat.pow_add]
    have :
        b * (256 ^ xs.length * 256 ^ ys.length) +
            (bytesToNat xs * 256 ^ ys.length + bytesToNat ys) =
          (b * 256 ^ xs.length + bytesToNat xs) * 256 ^ ys.length + bytesToNat ys := by
      ring
    simpa [Nat.mul_assoc] using this

lemma bytesToNat_replicate_zero (n : Nat) : bytesToNat (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, bytesToNat, ih]

lemma bytesToNat_pad (bs : List Nat) (z : Nat) :
    bytesToNat (bs ++ List.replicate z 0) = bytesToNat bs * 256 ^ z := by
  rw [bytesToNat_append, bytesToNat_replicate_zero, List.length_replicate, Nat.add_zero]

lemma bytesToNat_singleton_append (acc : List Nat) (b : Nat) :
    bytesToNat (acc ++ [b]) = bytesToNat acc * 256 + b := by
  simpa [Nat.pow_one] using bytesToNat_append acc [b]

lemma bytesToNat_lt {bs : List Nat} (h : ∀ x ∈ bs, x < 256) :
    bytesToNat bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp [bytesToNat]
  | cons b bs ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    obtain ⟨hb, hbs⟩ := h
    have ih := ih hbs
    have hp : 0 < 256 ^ bs.length := Nat.pow_pos (by decide : 0 < 256)
    have hle : b ≤ 255 := Nat.le_pred_of_lt hb
    have hr : bytesToNat bs ≤ 256 ^ bs.length - 1 := Nat.le_pred_of_lt ih
    have hsum :
        b * 256 ^ bs.length + bytesToNat bs ≤
          255 * 256 ^ bs.length + (256 ^ bs.length - 1) := by
      exact Nat.add_le_add (Nat.mul_le_mul_right _ hle) hr
    have hcollapse :
        255 * 256 ^ bs.length + (256 ^ bs.length - 1) = 256 * 256 ^ bs.length - 1 := by
      have h1 : 255 * 256 ^ bs.length + 256 ^ bs.length = 256 * 256 ^ bs.length := by ring
      have h2 : 256 ^ bs.length ≤ 255 * 256 ^ bs.length + 256 ^ bs.length :=
        Nat.le_add_left _ _
      omega
    have hfin :
        255 * 256 ^ bs.length + (256 ^ bs.length - 1) < 256 * 256 ^ bs.length := by
      rw [hcollapse]
      exact Nat.sub_lt (Nat.mul_pos (by decide : 0 < 256) hp) (by decide)
    have : b * 256 ^ bs.length + bytesToNat bs < 256 * 256 ^ bs.length :=
      Nat.lt_of_le_of_lt hsum hfin
    simpa [bytesToNat, Nat.pow_succ, Nat.mul_comm] using this

lemma add_mul_mod_lt (m x r : Nat) (hm : 0 < m) (hr : r < m) :
    (x * m + r) % m = r := by
  rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

lemma mul_add_unique (m x r y s : Nat) (hm : 0 < m) (hr : r < m) (hs : s < m)
    (h : x * m + r = y * m + s) : x = y ∧ r = s := by
  have hr' : r = (x * m + r) % m := (add_mul_mod_lt m x r hm hr).symm
  have hs' : s = (y * m + s) % m := (add_mul_mod_lt m y s hm hs).symm
  have hrs : r = s := by rw [hr', h, ← hs']
  subst hrs
  have hmul : x * m = y * m := Nat.add_right_cancel h
  exact ⟨Nat.mul_right_cancel hm hmul, rfl⟩

lemma bytesToNat_inj {xs ys : List Nat}
    (hxs : ∀ x ∈ xs, x < 256) (hys : ∀ y ∈ ys, y < 256)
    (hl : xs.length = ys.length) (hv : bytesToNat xs = bytesToNat ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      simp only [List.length_cons, Nat.add_left_cancel_iff] at hl
      simp only [List.mem_cons, forall_eq_or_imp] at hxs hys
      obtain ⟨hx, hxs⟩ := hxs
      obtain ⟨hy, hys⟩ := hys
      simp only [bytesToNat] at hv
      have hxlt := bytesToNat_lt hxs
      have hylt := bytesToNat_lt hys
      have hm : 0 < 256 ^ xs.length := Nat.pow_pos (by decide : 0 < 256)
      have ⟨hxy, hrest⟩ :=
        mul_add_unique (256 ^ xs.length) x (bytesToNat xs) y (bytesToNat ys) hm hxlt hylt hv
      have hlen : xs.length = ys.length := hl
      rw [hxy]
      have htail : xs = ys := ih hxs hys hlen (by simpa [hlen] using hrest)
      exact congrArg (y :: ·) htail

/-- Big-endian fold: `d0 * base^{n-1} + … + d_{n-1}`. -/
def foldBE (base : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds => d * base ^ ds.length + foldBE base ds

lemma foldBE_append (base : Nat) (xs ys : List Nat) :
    foldBE base (xs ++ ys) = foldBE base xs * base ^ ys.length + foldBE base ys := by
  induction xs with
  | nil => simp [foldBE]
  | cons d xs ih =>
    simp only [List.cons_append, foldBE, List.length_append, ih, Nat.pow_add]
    ring

lemma foldBE_replicate_zero (base k : Nat) : foldBE base (List.replicate k 0) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, foldBE, ih]

lemma foldBE_lt {base : Nat} {ds : List Nat} (hb : 0 < base) (h : ∀ d ∈ ds, d < base) :
    foldBE base ds < base ^ ds.length := by
  induction ds with
  | nil => simp [foldBE]
  | cons d ds ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    obtain ⟨hd, hds⟩ := h
    have ih := ih hds
    have hp : 0 < base ^ ds.length := Nat.pow_pos hb
    have hle : d ≤ base - 1 := Nat.le_pred_of_lt hd
    have hr : foldBE base ds ≤ base ^ ds.length - 1 := Nat.le_pred_of_lt ih
    have hsum :
        d * base ^ ds.length + foldBE base ds ≤
          (base - 1) * base ^ ds.length + (base ^ ds.length - 1) :=
      Nat.add_le_add (Nat.mul_le_mul_right _ hle) hr
    have hcollapse :
        (base - 1) * base ^ ds.length + (base ^ ds.length - 1) =
          base * base ^ ds.length - 1 := by
      have hb1 : 1 ≤ base := hb
      omega
    have hfin :
        (base - 1) * base ^ ds.length + (base ^ ds.length - 1) <
          base * base ^ ds.length := by
      rw [hcollapse]
      exact Nat.sub_lt (Nat.mul_pos hb hp) (by decide)
    have : d * base ^ ds.length + foldBE base ds < base * base ^ ds.length :=
      Nat.lt_of_le_of_lt hsum hfin
    simpa [foldBE, Nat.pow_succ, Nat.mul_comm] using this

lemma mod_pow_succ (base k n : Nat) (hb : 0 < base) :
    n % base ^ (k + 1) = (n / base ^ k % base) * base ^ k + n % base ^ k := by
  have hk : 0 < base ^ k := Nat.pow_pos hb
  set q := n / base ^ k
  set r := n % base ^ k
  have hn : n = q * base ^ k + r := by
    simpa [q, r, Nat.mul_comm] using (Nat.div_add_mod n (base ^ k)).symm
  have hr : r < base ^ k := Nat.mod_lt _ hk
  have hq : q % base < base := Nat.mod_lt _ hb
  have hlow : (q % base) * base ^ k + r < base ^ (k + 1) := by
    have h1 : (q % base) * base ^ k + r < (q % base) * base ^ k + base ^ k :=
      Nat.add_lt_add_left hr _
    have h2 : (q % base) * base ^ k + base ^ k = (q % base + 1) * base ^ k := by ring
    have h3 : q % base + 1 ≤ base := Nat.succ_le_of_lt hq
    have h4 : (q % base + 1) * base ^ k ≤ base * base ^ k :=
      Nat.mul_le_mul_right _ h3
    have h5 : base * base ^ k = base ^ (k + 1) := by rw [Nat.pow_succ']
    omega
  have hsplit : q * base ^ k = (q / base) * base ^ (k + 1) + (q % base) * base ^ k := by
    have hqdiv : q = base * (q / base) + q % base := by
      simpa [Nat.mul_comm] using (Nat.div_add_mod q base).symm
    calc
      q * base ^ k = (base * (q / base) + q % base) * base ^ k := by rw [hqdiv]
      _ = base * (q / base) * base ^ k + (q % base) * base ^ k := by ring
      _ = (q / base) * (base * base ^ k) + (q % base) * base ^ k := by ring
      _ = (q / base) * base ^ (k + 1) + (q % base) * base ^ k := by rw [Nat.pow_succ']
  have hn' : n = (q / base) * base ^ (k + 1) + ((q % base) * base ^ k + r) := by
    calc
      n = q * base ^ k + r := hn
      _ = (q / base) * base ^ (k + 1) + (q % base) * base ^ k + r := by rw [hsplit]
      _ = (q / base) * base ^ (k + 1) + ((q % base) * base ^ k + r) := by ring
  have hmod : n % base ^ (k + 1) = (q % base) * base ^ k + r := by
    rw [hn']
    exact add_mul_mod_lt (base ^ (k + 1)) (q / base) ((q % base) * base ^ k + r)
      (Nat.pow_pos hb) hlow
  simpa [q, r] using hmod

def digitsBE (base k n : Nat) : List Nat :=
  (List.range k).map fun i => n / base ^ (k - 1 - i) % base

lemma digitsBE_length (base k n : Nat) : (digitsBE base k n).length = k := by
  simp [digitsBE]

lemma range_succ_cons (k : Nat) :
    List.range (k + 1) = 0 :: (List.range k).map (· + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [List.range_succ, ih, List.map_append, List.map_cons, List.map_nil]
    rfl

lemma digitsBE_succ (base k n : Nat) (hb : 0 < base) :
    digitsBE base (k + 1) n = (n / base ^ k % base) :: digitsBE base k n := by
  simp only [digitsBE, range_succ_cons, List.map_cons, Nat.add_sub_cancel]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' : i < k := by simpa using hi
  have hsub : k + 1 - 1 - (i + 1) = k - 1 - i := by omega
  simp [hsub]

lemma foldBE_digitsBE (base k n : Nat) (hb : 1 ≤ base) :
    foldBE base (digitsBE base k n) = n % base ^ k := by
  induction k with
  | zero => simp [digitsBE, foldBE]
  | succ k ih =>
    have hb0 : 0 < base := hb
    rw [digitsBE_succ _ _ _ hb0, foldBE, digitsBE_length, ih]
    exact (mod_pow_succ base k n hb0).symm

lemma shr_and_31 (v s : Nat) : (v >>> s) &&& 31 = v / 2 ^ s % 32 := by
  rw [Nat.shiftRight_eq_div_pow]
  have h := Nat.and_two_pow_sub_one_eq_mod (v / 2 ^ s) 5
  simpa [two_pow_5] using h

lemma indices_eq_digits (v : Nat) : indicesOf40 v = digitsBE 32 8 v := by
  simp only [indicesOf40, digitsBE]
  apply List.ext_getElem
  · simp [digitsBE_length]
  · intro i hi hi2
    simp only [List.length_cons, List.length_nil] at hi
    -- indicesOf40 is a concrete 8-element list; digitsBE is range 8
    fin_cases i <;>
      simp [List.getElem_cons, shr_and_31, pow32, Nat.mul_comm, two_pow_5]

theorem roundtrip_thm (s : List Nat) (h : Pre s) : roundtrip_prop s := by
  sorry

theorem encode_length_thm (s : List Nat) : encode_length_prop s := by
  sorry

theorem padding_thm (s : List Nat) : padding_prop s := by
  sorry

theorem alphabet_thm (s : List Nat) : alphabet_prop s := by
  sorry

theorem casefold_roundtrip_thm (s : List Nat) (h : Pre s) : casefold_roundtrip_prop s := by
  sorry

theorem map01_roundtrip_thm (s : List Nat) (h : Pre s) : map01_roundtrip_prop s := by
  sorry

theorem extra_pad_thm (s : List Nat) (h : Pre s) : extra_pad_prop s := by
  sorry

theorem invalid_digit_thm (s : List Nat) (casefold : Bool) (map01 : Option (List Nat)) :
    invalid_digit_prop s casefold map01 := by
  sorry

theorem map01_zero_thm (s m : List Nat) : map01_zero_prop s m := by
  sorry

theorem chunk_concat_thm (s t : List Nat) : chunk_concat_prop s t := by
  sorry

theorem string_ascii_thm (s : String) (h : PreStr s) (casefold : Bool)
    (map01 : Option (List Nat)) : string_ascii_prop s casefold map01 := by
  sorry

/-- Post-condition: the observable Base32 laws for one byte string. -/
def Post_prop (s : List Nat) : Prop :=
  roundtrip_prop s ∧
    encode_length_prop s ∧
    padding_prop s ∧
    alphabet_prop s ∧
    casefold_roundtrip_prop s ∧
    map01_roundtrip_prop s ∧
    extra_pad_prop s

/-! ## Property-based tests -/

/-- Executable form of `roundtrip_prop` on every byte (`n % 256`). -/
#eval Plausible.Testable.check
  (∀ xs : List Nat,
    b32decode (b32encode (xs.map (· % 256))) false none = Except.ok (xs.map (· % 256)))

example : (List.range 256).all (fun n =>
    b32decode (b32encode [n]) false none == Except.ok [n]) = true := by
  native_decide

example : (List.range 40).all (fun n =>
    (b32encode (List.replicate n (n % 256))).length = 8 * ((n + 4) / 5)) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ xs : List Nat, (b32encode xs).length = 8 * ((xs.length + 4) / 5))

private def padOk (s : List Nat) : Bool :=
  let e := b32encode s
  let p := padCount (s.length % 5)
  (e.drop (e.length - p) == List.replicate p eqByte) &&
    (e.take (e.length - p)).all (fun c => b32alphabet.contains c)

example : ((List.range 30).flatMap fun n =>
    (List.range 8).map fun b => padOk (List.replicate n b)) .all id = true := by
  native_decide

#eval Plausible.Testable.check (∀ xs : List Nat, padOk xs = true)

private def alphaOk (s : List Nat) : Bool :=
  (b32encode s).all fun c => b32alphabet.contains c || c == eqByte

example : (List.range 64).all (fun n => alphaOk (List.replicate n (n % 256))) = true := by
  native_decide

#eval Plausible.Testable.check (∀ xs : List Nat, alphaOk xs = true)

#eval Plausible.Testable.check
  (∀ xs : List Nat,
    b32decode (((b32encode (xs.map (· % 256))).map asciiLower)) true none =
      Except.ok (xs.map (· % 256)))

example : (List.range 256).all (fun n =>
    b32decode ((b32encode [n]).map asciiLower) true none == Except.ok [n]) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ xs ys : List Nat,
    let s := xs.map (· % 256)
    let m := ys ++ [76]
    b32decode ((b32encode s).map fun c => if c = ohByte then zeroByte else c) false (some m) =
      Except.ok s)

example : (List.range 128).all (fun n =>
    b32decode ((b32encode [n]).map fun c => if c = ohByte then zeroByte else c)
        false (some [76]) ==
      Except.ok [n]) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ xs : List Nat, ∀ n : Fin 6,
    b32decode (b32encode (xs.map (· % 256)) ++ List.replicate n.val eqByte) false none =
      Except.ok (xs.map (· % 256)))

private def postOk (s : List Nat) : Bool :=
  match b32decode (b32encode s) false none with
  | .error _ => false
  | .ok r =>
    r == s &&
      (b32encode s).length == 8 * ((s.length + 4) / 5) &&
      padOk s && alphaOk s &&
        (match b32decode ((b32encode s).map asciiLower) true none with
          | .ok t => t == s
          | .error _ => false) &&
        (match b32decode ((b32encode s).map fun c => if c = ohByte then zeroByte else c)
            false (some [76]) with
          | .ok t => t == s
          | .error _ => false) &&
        (match b32decode (b32encode s ++ [eqByte, eqByte]) false none with
          | .ok t => t == s
          | .error _ => false)

example : ((List.range 20).flatMap fun n =>
    (List.range 5).map fun b => postOk (List.replicate n b)) .all id = true := by
  native_decide

#eval Plausible.Testable.check (∀ xs : List Nat, postOk (xs.map (· % 256)) = true)

#eval Plausible.Testable.check
  (∀ xs : List Nat,
    let s := xs.map (· % 256) ++ [33]
    b32decode s false none = Except.error nonBase32Msg)

#eval Plausible.Testable.check
  (∀ xs : List Nat,
    let s := xs.map (· % 256)
    let s0 := s.map fun c => if c = zeroByte then zeroByte else c
    oneByte ∉ s →
      b32decode s false (some [76]) =
        b32decode (s.map fun c => if c = zeroByte then ohByte else c) false none)

example : (List.range 20).all (fun n =>
    let s := List.range n
    let t := List.range (n % 3)
    b32encode (s ++ t) == b32encode s ++ b32encode t) = true := by
  native_decide

#eval Plausible.Testable.check
  (∀ xs ys : List Nat,
    let s := List.replicate (5 * (xs.length % 4)) (xs.head?.getD 0 % 256)
    b32encode (s ++ ys.map (· % 256)) = b32encode s ++ b32encode (ys.map (· % 256)))

/-- PBT: `string_ascii_prop` on ASCII strings built from byte codes. -/
example : (List.range 64).all (fun n =>
    let ch := Char.ofNat (n % 128)
    b32decodeString (String.singleton ch) false none ==
      b32decode [ch.toNat] false none) = true := by
  native_decide

theorem correctness_thm (s : List Nat) (h : Pre s) : Post_prop s := by
  sorry

/-! ## Imperative implementation -/

/-- Append `xs` onto `acc` with a mutable cursor, one element at a time. -/
def appendAll (acc xs : List Nat) : List Nat :=
  Id.run do
    let mut a := acc
    for x in xs do
      a := a ++ [x]
    return a

/-- Imperative `b32encode`, following the Python loop and the final padding fix. -/
def b32encodeImp (s : List Nat) : List Nat :=
  let encoded : List Nat := Id.run do
    let mut acc : List Nat := []
    for i in List.range ((s.length + 4) / 5) do
      let chunk := (s.drop (5 * i)).take 5
      acc := appendAll acc (chunkRaw chunk)
    return acc
  applyTailPadding encoded (s.length % 5)

/-- Mutable decoder state, corresponding to `val`, `bits`, and `decoded`. -/
structure DecSt where
  val : Nat
  bits : Nat
  out : List Nat
  err : Bool
deriving Repr, DecidableEq

def emptySt : DecSt := { val := 0, bits := 0, out := [], err := false }

/-- One iteration of the Python decode loop, including the invalid-digit exit. -/
def decStep (st : DecSt) (c : Nat) : DecSt :=
  if st.err then st
  else
    match revIndex c with
    | none => { st with err := true }
    | some idx =>
      let val' := (st.val <<< 5) ||| idx
      let bits' := st.bits + 5
      if bits' ≥ 8 then
        let bits'' := bits' - 8
        let b := (val' >>> bits'') &&& 255
        { val := val', bits := bits'', out := st.out ++ [b], err := false }
      else
        { val := val', bits := bits', out := st.out, err := false }

/-- Imperative `b32decode`. -/
def b32decodeImp (s : List Nat) (casefold : Bool := false) (map01 : Option (List Nat) := none) :
    Except String (List Nat) :=
  Id.run do
    let t := normalize s casefold map01
    let mut st : DecSt := emptySt
    for c in t do
      st := decStep st c
    if st.err then
      return .error nonBase32Msg
    else
      return .ok st.out

/-- Imperative string entry. -/
def b32decodeStringImp (s : String) (casefold : Bool := false)
    (map01 : Option (List Nat) := none) : Except String (List Nat) :=
  if isAsciiString s then
    b32decodeImp (s.toList.map (fun c => c.toNat)) casefold map01
  else
    .error "UnicodeEncodeError"

/-! ## Imperative tests -/

example : b32encodeImp (bytesOf "foobar") = bytesOf "MZXW6YTBOI======" := by native_decide
example : b32encodeImp (bytesOf "") = [] := by native_decide
example : b32encodeImp (bytesOf "f") = b32encode (bytesOf "f") := by native_decide
example : b32encodeImp (bytesOf "VeriBench") = b32encode (bytesOf "VeriBench") := by native_decide

example : b32decodeImp (bytesOf "mzxw6ytb") true none = .ok (bytesOf "fooba") := by native_decide
example : b32decodeImp (b32encode (bytesOf "VeriBench")) false none =
    .ok (bytesOf "VeriBench") := by native_decide
example : b32decodeImp (bytesOf "M!") false none = .error nonBase32Msg := by native_decide

#eval b32encodeImp (bytesOf "fooba")
#eval b32decodeImp (bytesOf "MY======") false none

/-! ## Equivalence -/

def encode_equiv_prop (s : List Nat) : Prop :=
  b32encode s = b32encodeImp s

def decode_equiv_prop (s : List Nat) (casefold : Bool) (map01 : Option (List Nat)) : Prop :=
  b32decode s casefold map01 = b32decodeImp s casefold map01

theorem encode_equiv_thm (s : List Nat) : encode_equiv_prop s := by
  sorry

theorem decode_equiv_thm (s : List Nat) (casefold : Bool) (map01 : Option (List Nat)) :
    decode_equiv_prop s casefold map01 := by
  sorry

end «23_base32»
