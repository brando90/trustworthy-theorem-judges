import Mathlib

/-!
# Base32 encoding and decoding (VeriBench task 23)

Lean 4 formalization of the Python module providing `b32encode` / `b32decode`
(sourced from Python's standard `base64` library).

* Bytes-like objects are modelled as `List UInt8`.
* `b32encode` returns the Base32 text as a byte list (ASCII codes, like Python `bytes`).
* `b32decode` returns `Option (List UInt8)`; `none` models the exception
  `binascii.Error('Non-base32 digit found')`.  An ASCII `str` input of the Python
  function corresponds to the list of its (ASCII) bytes.
* The Python bit tricks `(val >> k) & 0x1F` are written `val / 2^k % 32` and
  `(val << 5) | idx` is written `val * 32 + idx` (identical values on naturals,
  since `idx < 32`); `(val >> bits) & 0xFF` is written `val / 2^bits % 256`.
-/

namespace «23_base32»

/-! ## Functional implementation -/

/-- The Base32 alphabet `b'ABCDEFGHIJKLMNOPQRSTUVWXYZ234567'` as ASCII codes. -/
def b32alphabet : List UInt8 :=
  [65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86,
   87, 88, 89, 90, 50, 51, 52, 53, 54, 55]

/-- The padding character `b'='`. -/
def padByte : UInt8 := 61

/-- `int.from_bytes(chunk, 'big')`. -/
def fromBytesBE (l : List UInt8) : Nat := l.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Encode one (possibly short, zero padded) chunk of at most 5 bytes into 8 Base32 symbols. -/
def encodeChunk (chunk : List UInt8) : List UInt8 :=
  let padded := chunk ++ List.replicate (5 - chunk.length) (0 : UInt8)
  let val := fromBytesBE padded
  [ b32alphabet.getD (val / 2 ^ 35 % 32) 0,
    b32alphabet.getD (val / 2 ^ 30 % 32) 0,
    b32alphabet.getD (val / 2 ^ 25 % 32) 0,
    b32alphabet.getD (val / 2 ^ 20 % 32) 0,
    b32alphabet.getD (val / 2 ^ 15 % 32) 0,
    b32alphabet.getD (val / 2 ^ 10 % 32) 0,
    b32alphabet.getD (val / 2 ^ 5 % 32) 0,
    b32alphabet.getD (val % 32) 0 ]

/-- The `for i in range(0, len(s), 5)` loop: 8 symbols per (partial) 5-byte chunk. -/
def encodeBody : List UInt8 → List UInt8
  | [] => []
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest => encodeChunk [b0, b1, b2, b3, b4] ++ encodeBody rest
  | chunk => encodeChunk chunk

/-- Number of `=` padding symbols for `len(s) % 5 = rem`. -/
def padLen (rem : Nat) : Nat :=
  if rem = 1 then 6 else if rem = 2 then 4 else if rem = 3 then 3 else if rem = 4 then 1 else 0

/-- "Fix padding": overwrite the last `padLen (n % 5)` symbols with `=`. -/
def fixPadding (n : Nat) (encoded : List UInt8) : List UInt8 :=
  encoded.take (encoded.length - padLen (n % 5)) ++ List.replicate (padLen (n % 5)) padByte

/-- `b32encode`: encode the bytes `s` using Base32. -/
def b32encode (s : List UInt8) : List UInt8 := fixPadding s.length (encodeBody s)

/-- `rev_alphabet` lookup: index of a symbol in the alphabet, if any. -/
def b32index (c : UInt8) : Option Nat := b32alphabet.idxOf? c

/-- ASCII uppercase of one byte (`bytes.upper()`). -/
def asciiUpper (c : UInt8) : UInt8 := if 97 ≤ c ∧ c ≤ 122 then c - 32 else c

/-- ASCII lowercase of one byte (used only to state the casefold property). -/
def asciiLower (c : UInt8) : UInt8 := if 65 ≤ c ∧ c ≤ 90 then c + 32 else c

/-- `s.replace(b'0', b'O').replace(b'1', map01)` on a single byte. -/
def map01Replace (map01 : UInt8) (c : UInt8) : UInt8 :=
  if c = 48 then 79 else if c = 49 then map01 else c

/-- `s.rstrip(b'=')`. -/
def rstripPad : List UInt8 → List UInt8
  | [] => []
  | c :: rest =>
    match rstripPad rest with
    | [] => if c = padByte then [] else [c]
    | r => c :: r

/-- The decoding loop with state `(val, bits)` and accumulated output `acc`. -/
def decodeSymbols : List UInt8 → Nat → Nat → List UInt8 → Option (List UInt8)
  | [], _, _, acc => some acc
  | c :: rest, val, bits, acc =>
    match b32index c with
    | none => none
    | some v =>
      let val' := val * 32 + v
      let bits' := bits + 5
      if 8 ≤ bits' then
        decodeSymbols rest val' (bits' - 8) (acc ++ [UInt8.ofNat (val' / 2 ^ (bits' - 8) % 256)])
      else
        decodeSymbols rest val' bits' acc

/-- `b32decode`: decode Base32 bytes `s` (`none` = `binascii.Error`). -/
def b32decode (s : List UInt8) (casefold : Bool := false) (map01 : Option UInt8 := none) :
    Option (List UInt8) :=
  let s₁ := match map01 with
    | some m => s.map (map01Replace m)
    | none => s
  let s₂ := if casefold then s₁.map asciiUpper else s₁
  decodeSymbols (rstripPad s₂) 0 0 []

/-! ## Unit tests -/

/-- Bytes of an ASCII string literal. -/
def bytes (s : String) : List UInt8 := s.toUTF8.toList

/-- Display a byte list as a string. -/
def toStr (l : List UInt8) : String := String.mk (l.map (fun b => Char.ofNat b.toNat))

example : b32encode (bytes "") = bytes "" := by native_decide
example : b32encode (bytes "f") = bytes "MY======" := by native_decide
example : b32encode (bytes "fo") = bytes "MZXQ====" := by native_decide
example : b32encode (bytes "foo") = bytes "MZXW6===" := by native_decide
example : b32encode (bytes "foob") = bytes "MZXW6YQ=" := by native_decide
example : b32encode (bytes "fooba") = bytes "MZXW6YTB" := by native_decide
example : b32encode (bytes "foobar") = bytes "MZXW6YTBOI======" := by native_decide
example : b32decode (b32encode (bytes "VeriBench")) = some (bytes "VeriBench") := by native_decide
example : b32decode (bytes "mzxw6ytb") true = some (bytes "fooba") := by native_decide
example : b32decode (bytes "MZXW6YTB") = some (bytes "fooba") := by native_decide
example : b32decode (bytes "mzxw6ytb") = none := by native_decide
example : b32decode (bytes "MZXW6YTB0I======") false (some 73) = some (bytes "foobar") := by native_decide

#eval toStr (b32encode (bytes "foobar"))
#eval (b32decode (bytes "MZXW6YTBOI======")).map toStr


/-! ## Helper lemmas -/

theorem toNat_lt256 (b : UInt8) : b.toNat < 256 := UInt8.toNat_lt b

theorem ofNat_eq_of_mod (e : Nat) (b : UInt8) (h : e % 256 = b.toNat) : UInt8.ofNat e = b := by
  apply UInt8.ext
  rw [UInt8.toNat_ofNat']
  exact h

/-- Every byte is `UInt8.ofNat n` for some `n < 256`. -/
theorem forall_uint8 {P : UInt8 → Prop} (h : ∀ n, n < 256 → P (UInt8.ofNat n)) : ∀ c, P c := by
  intro c
  have := h c.toNat (toNat_lt256 c)
  rwa [UInt8.ofNat_toNat] at this

theorem b32alphabet_length : b32alphabet.length = 32 := rfl

theorem index_getD (i : Nat) (hi : i < 32) : b32index (b32alphabet.getD i 0) = some i := by
  revert i; decide

theorem index_getD_mod (x : Nat) : b32index (b32alphabet.getD (x % 32) 0) = some (x % 32) :=
  index_getD _ (Nat.mod_lt _ (by norm_num))

theorem getD_mod_mem (x : Nat) : b32alphabet.getD (x % 32) 0 ∈ b32alphabet := by
  have h : x % 32 < b32alphabet.length := Nat.mod_lt _ (by decide)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

theorem pad_not_mem : padByte ∉ b32alphabet := by decide

theorem b32index_eq_none_iff (c : UInt8) : b32index c = none ↔ c ∉ b32alphabet :=
  List.idxOf?_eq_none_iff

theorem encodeChunk_length (ch : List UInt8) : (encodeChunk ch).length = 8 := rfl

theorem encodeChunk_mem (ch : List UInt8) : ∀ c ∈ encodeChunk ch, c ∈ b32alphabet := by
  intro c hc
  simp only [encodeChunk, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact getD_mod_mem _

theorem encodeChunk_ne_pad (ch : List UInt8) : ∀ c ∈ encodeChunk ch, c ≠ padByte :=
  fun c hc heq => pad_not_mem (heq ▸ encodeChunk_mem ch c hc)

theorem encodeBody_cons5 (b0 b1 b2 b3 b4 : UInt8) (rest : List UInt8) :
    encodeBody (b0 :: b1 :: b2 :: b3 :: b4 :: rest) =
      encodeChunk [b0, b1, b2, b3, b4] ++ encodeBody rest := rfl

theorem encodeBody_length : ∀ s : List UInt8, (encodeBody s).length = 8 * ((s.length + 4) / 5)
  | [] => rfl
  | [a] => by show (encodeChunk [a]).length = _; simp [encodeChunk_length]
  | [a, b] => by show (encodeChunk [a, b]).length = _; simp [encodeChunk_length]
  | [a, b, c] => by show (encodeChunk [a, b, c]).length = _; simp [encodeChunk_length]
  | [a, b, c, d] => by show (encodeChunk [a, b, c, d]).length = _; simp [encodeChunk_length]
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest => by
    rw [encodeBody_cons5, List.length_append, encodeChunk_length, encodeBody_length rest]
    simp only [List.length_cons]
    omega

theorem encodeBody_mem : ∀ s : List UInt8, ∀ c ∈ encodeBody s, c ∈ b32alphabet
  | [] => by simp [encodeBody]
  | [_] => encodeChunk_mem _
  | [_, _] => encodeChunk_mem _
  | [_, _, _] => encodeChunk_mem _
  | [_, _, _, _] => encodeChunk_mem _
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest => by
    intro c hc
    rw [encodeBody_cons5, List.mem_append] at hc
    rcases hc with hc | hc
    · exact encodeChunk_mem _ c hc
    · exact encodeBody_mem rest c hc

theorem padLen_le (r : Nat) : padLen r ≤ 6 := by
  unfold padLen; split_ifs <;> omega

theorem b32encode_cons5 (b0 b1 b2 b3 b4 : UInt8) (rest : List UInt8) :
    b32encode (b0 :: b1 :: b2 :: b3 :: b4 :: rest) =
      encodeChunk [b0, b1, b2, b3, b4] ++ b32encode rest := by
  have hmod : (b0 :: b1 :: b2 :: b3 :: b4 :: rest).length % 5 = rest.length % 5 := by
    simp only [List.length_cons]; omega
  unfold b32encode fixPadding
  rw [hmod, encodeBody_cons5, List.length_append, encodeChunk_length]
  rcases rest with _ | ⟨c, rest'⟩
  · simp [encodeBody, padLen, encodeChunk_length, List.take_of_length_le]
  · have hB : 8 ≤ (encodeBody (c :: rest')).length := by
      rw [encodeBody_length]; simp only [List.length_cons]; omega
    have hp : padLen ((c :: rest').length % 5) ≤ 6 := padLen_le _
    rw [List.take_append, encodeChunk_length,
      List.take_of_length_le (by rw [encodeChunk_length]; omega), List.append_assoc]
    congr 3
    omega

/-! ### `rstripPad` lemmas -/

theorem rstripPad_replicate (n : Nat) : rstripPad (List.replicate n padByte) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, rstripPad, ih]

theorem rstripPad_append_replicate (l : List UInt8) (n : Nat) :
    rstripPad (l ++ List.replicate n padByte) = rstripPad l := by
  induction l with
  | nil => simp [rstripPad_replicate, rstripPad]
  | cons c l ih => simp [rstripPad, ih]

theorem rstripPad_eq_self_of_no_pad : ∀ l : List UInt8, (∀ c ∈ l, c ≠ padByte) → rstripPad l = l
  | [], _ => rfl
  | c :: l, h => by
    have ih := rstripPad_eq_self_of_no_pad l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hc : c ≠ padByte := h c (by simp)
    rw [rstripPad, ih]
    cases l with
    | nil => simp [hc]
    | cons x xs => rfl

theorem rstripPad_append_of_no_pad : ∀ (l1 l2 : List UInt8), (∀ c ∈ l1, c ≠ padByte) →
    rstripPad (l1 ++ l2) = l1 ++ rstripPad l2
  | [], _, _ => rfl
  | c :: l1, l2, h => by
    have ih := rstripPad_append_of_no_pad l1 l2 (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hc : c ≠ padByte := h c (by simp)
    rw [List.cons_append, rstripPad, ih]; simp only [List.cons_append]
    cases h' : l1 ++ rstripPad l2 with
    | nil => simp [hc]
    | cons x xs => rfl

theorem mem_rstripPad : ∀ (l : List UInt8) (c : UInt8), c ∈ l → c ≠ padByte → c ∈ rstripPad l
  | [], _, h, _ => absurd h List.not_mem_nil
  | a :: l, c, h, hc => by
    rw [rstripPad]
    rcases List.mem_cons.mp h with rfl | hl
    · cases h' : rstripPad l with
      | nil => simp [hc]
      | cons x xs => simp
    · have ih := mem_rstripPad l c hl hc
      cases h' : rstripPad l with
      | nil => rw [h'] at ih; exact absurd ih List.not_mem_nil
      | cons x xs => rw [h'] at ih; simp [ih]

/-! ### `decodeSymbols` lemmas -/

theorem decodeSymbols_none_of_mem : ∀ (t : List UInt8) (c : UInt8) (val bits : Nat)
    (acc : List UInt8), c ∈ t → b32index c = none → decodeSymbols t val bits acc = none
  | [], _, _, _, _, h, _ => absurd h List.not_mem_nil
  | a :: t, c, val, bits, acc, h, hc => by
    rw [decodeSymbols]
    rcases List.mem_cons.mp h with rfl | ht
    · rw [hc]
    · cases ha : b32index a with
      | none => rfl
      | some v =>
        dsimp only
        split_ifs <;> exact decodeSymbols_none_of_mem t c _ _ _ ht hc

theorem decodeSymbols_isSome : ∀ (t : List UInt8) (val bits : Nat) (acc : List UInt8),
    (∀ c ∈ t, c ∈ b32alphabet) → (decodeSymbols t val bits acc).isSome
  | [], _, _, _, _ => rfl
  | a :: t, val, bits, acc, h => by
    rw [decodeSymbols]
    have ha : a ∈ b32alphabet := h a (by simp)
    obtain ⟨v, hv⟩ : ∃ v, b32index a = some v := by
      cases hb : b32index a with
      | none => exact absurd ((b32index_eq_none_iff a).mp hb) (not_not.mpr ha)
      | some v => exact ⟨v, rfl⟩
    rw [hv]
    dsimp only
    split_ifs <;> exact decodeSymbols_isSome t _ _ _ (fun c hc => h c (List.mem_cons_of_mem _ hc))

theorem decodeSymbols_length : ∀ (t : List UInt8) (val bits : Nat) (acc l : List UInt8),
    bits < 8 → decodeSymbols t val bits acc = some l →
      l.length = acc.length + (bits + 5 * t.length) / 8
  | [], val, bits, acc, l, hb, h => by
    simp only [decodeSymbols, Option.some.injEq] at h
    subst h
    simp only [List.length_nil, Nat.mul_zero, Nat.add_zero]
    omega
  | a :: t, val, bits, acc, l, hb, h => by
    rw [decodeSymbols] at h
    cases ha : b32index a with
    | none => rw [ha] at h; exact absurd h (by simp)
    | some v =>
      rw [ha] at h
      dsimp only at h
      split_ifs at h with h8
      · have := decodeSymbols_length t _ _ _ l (by omega) h
        rw [this]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      · have := decodeSymbols_length t _ _ _ l (by omega) h
        rw [this]
        simp only [List.length_cons]
        omega


/-! ### Round trip: decoding the symbols of a full chunk -/

set_option maxHeartbeats 1000000 in
theorem decodeSymbols_encodeChunk5 (b0 b1 b2 b3 b4 : UInt8) (rest : List UInt8) (val : Nat)
    (acc : List UInt8) :
    decodeSymbols (encodeChunk [b0, b1, b2, b3, b4] ++ rest) val 0 acc =
      decodeSymbols rest (val * 2 ^ 40 + fromBytesBE [b0, b1, b2, b3, b4]) 0
        (acc ++ [b0, b1, b2, b3, b4]) := by
  have h0 := toNat_lt256 b0
  have h1 := toNat_lt256 b1
  have h2 := toNat_lt256 b2
  have h3 := toNat_lt256 b3
  have h4 := toNat_lt256 b4
  simp only [encodeChunk, fromBytesBE, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.sub_self, List.replicate_zero, List.append_nil, List.foldl_cons, List.foldl_nil,
    List.cons_append, List.nil_append]
  simp only [decodeSymbols, index_getD_mod, Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceSub,
    Nat.reducePow, ↓reduceIte]
  congr 1
  · omega
  · simp only [List.append_assoc, List.cons_append, List.nil_append,
      List.append_cancel_left_eq, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (apply ofNat_eq_of_mod; omega)


/-! ### Round trip: partial final chunks and the main induction -/

set_option maxHeartbeats 2000000 in
theorem roundtrip_aux : ∀ (s : List UInt8) (val : Nat) (acc : List UInt8),
    decodeSymbols (rstripPad (b32encode s)) val 0 acc = some (acc ++ s)
  | [], val, acc => by
    simp [b32encode, fixPadding, encodeBody, padLen, rstripPad, decodeSymbols]
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest, val, acc => by
    rw [b32encode_cons5, rstripPad_append_of_no_pad _ _ (encodeChunk_ne_pad _),
      decodeSymbols_encodeChunk5, roundtrip_aux rest, List.append_assoc]
    rfl
  | [b0], val, acc => by
    have h0 := toNat_lt256 b0
    have e : b32encode [b0] = (encodeChunk [b0]).take 2 ++ List.replicate 6 padByte := by
      rw [b32encode, fixPadding, show encodeBody [b0] = encodeChunk [b0] from rfl,
        encodeChunk_length]
      simp [padLen]
    rw [e, rstripPad_append_replicate, rstripPad_eq_self_of_no_pad _
      (fun c hc => encodeChunk_ne_pad _ c (List.mem_of_mem_take hc))]
    simp only [encodeChunk, fromBytesBE, List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append,
      List.foldl_cons, List.foldl_nil, List.take_succ_cons, List.take_zero, UInt8.toNat_zero]
    simp only [decodeSymbols, index_getD_mod, Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceSub,
      Nat.reducePow, ↓reduceIte]
    simp only [Option.some.injEq, List.append_cancel_left_eq, List.cons.injEq, and_true]
    apply ofNat_eq_of_mod; omega
  | [b0, b1], val, acc => by
    have h0 := toNat_lt256 b0
    have h1 := toNat_lt256 b1
    have e : b32encode [b0, b1] = (encodeChunk [b0, b1]).take 4 ++ List.replicate 4 padByte := by
      rw [b32encode, fixPadding, show encodeBody [b0, b1] = encodeChunk [b0, b1] from rfl,
        encodeChunk_length]
      simp [padLen]
    rw [e, rstripPad_append_replicate, rstripPad_eq_self_of_no_pad _
      (fun c hc => encodeChunk_ne_pad _ c (List.mem_of_mem_take hc))]
    simp only [encodeChunk, fromBytesBE, List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append,
      List.foldl_cons, List.foldl_nil, List.take_succ_cons, List.take_zero, UInt8.toNat_zero]
    simp only [decodeSymbols, index_getD_mod, Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceSub,
      Nat.reducePow, ↓reduceIte]
    simp only [List.append_assoc, List.cons_append, List.nil_append, Option.some.injEq,
      List.append_cancel_left_eq, List.cons.injEq, and_true]
    refine ⟨?_, ?_⟩ <;> (apply ofNat_eq_of_mod; omega)
  | [b0, b1, b2], val, acc => by
    have h0 := toNat_lt256 b0
    have h1 := toNat_lt256 b1
    have h2 := toNat_lt256 b2
    have e : b32encode [b0, b1, b2] =
        (encodeChunk [b0, b1, b2]).take 5 ++ List.replicate 3 padByte := by
      rw [b32encode, fixPadding, show encodeBody [b0, b1, b2] = encodeChunk [b0, b1, b2] from rfl,
        encodeChunk_length]
      simp [padLen]
    rw [e, rstripPad_append_replicate, rstripPad_eq_self_of_no_pad _
      (fun c hc => encodeChunk_ne_pad _ c (List.mem_of_mem_take hc))]
    simp only [encodeChunk, fromBytesBE, List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append,
      List.foldl_cons, List.foldl_nil, List.take_succ_cons, List.take_zero, UInt8.toNat_zero]
    simp only [decodeSymbols, index_getD_mod, Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceSub,
      Nat.reducePow, ↓reduceIte]
    simp only [List.append_assoc, List.cons_append, List.nil_append, Option.some.injEq,
      List.append_cancel_left_eq, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_⟩ <;> (apply ofNat_eq_of_mod; omega)
  | [b0, b1, b2, b3], val, acc => by
    have h0 := toNat_lt256 b0
    have h1 := toNat_lt256 b1
    have h2 := toNat_lt256 b2
    have h3 := toNat_lt256 b3
    have e : b32encode [b0, b1, b2, b3] =
        (encodeChunk [b0, b1, b2, b3]).take 7 ++ List.replicate 1 padByte := by
      rw [b32encode, fixPadding,
        show encodeBody [b0, b1, b2, b3] = encodeChunk [b0, b1, b2, b3] from rfl,
        encodeChunk_length]
      simp [padLen]
    rw [e, rstripPad_append_replicate, rstripPad_eq_self_of_no_pad _
      (fun c hc => encodeChunk_ne_pad _ c (List.mem_of_mem_take hc))]
    simp only [encodeChunk, fromBytesBE, List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append,
      List.foldl_cons, List.foldl_nil, List.take_succ_cons, List.take_zero, UInt8.toNat_zero]
    simp only [decodeSymbols, index_getD_mod, Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceSub,
      Nat.reducePow, ↓reduceIte]
    simp only [List.append_assoc, List.cons_append, List.nil_append, Option.some.injEq,
      List.append_cancel_left_eq, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (apply ofNat_eq_of_mod; omega)

/-- Decoding an encoding gives back the original bytes. -/
theorem b32decode_b32encode (s : List UInt8) : b32decode (b32encode s) false none = some s := by
  unfold b32decode
  simpa using roundtrip_aux s 0 []


/-! ## Pre-condition -/

/-- `pre_encode` / `pre_decode`: the input is a bytes-like object (an ASCII `str` is
represented by its bytes).  Inputs are typed as byte lists, so every input is admissible. -/
def Pre (_s : List UInt8) : Prop := True

/-! ## Properties and theorems -/

/-- The encoded length is `8 * ceil(len(s) / 5)`. -/
def encode_length_prop (s : List UInt8) : Prop :=
  (b32encode s).length = 8 * ((s.length + 4) / 5)

theorem encode_length_thm (s : List UInt8) : encode_length_prop s := by
  unfold encode_length_prop b32encode fixPadding
  rw [List.length_append, List.length_take, List.length_replicate, encodeBody_length]
  have hp := padLen_le (s.length % 5)
  rcases s with _ | ⟨c, s'⟩
  · simp [padLen]
  · have : 8 ≤ 8 * (((c :: s').length + 4) / 5) := by simp only [List.length_cons]; omega
    omega

/-- Every output byte is an alphabet symbol or the pad `=`. -/
def encode_alphabet_prop (s : List UInt8) : Prop :=
  ∀ c ∈ b32encode s, c ∈ b32alphabet ∨ c = padByte

theorem encode_alphabet_thm (s : List UInt8) : encode_alphabet_prop s := by
  intro c hc
  unfold b32encode fixPadding at hc
  rw [List.mem_append] at hc
  rcases hc with hc | hc
  · exact Or.inl (encodeBody_mem s c (List.mem_of_mem_take hc))
  · exact Or.inr (List.eq_of_mem_replicate hc)

/-- The encoding is a run of alphabet symbols followed by exactly `padLen (len s % 5)` pads
(6, 4, 3, 1 or 0 for `len % 5 = 1, 2, 3, 4, 0`). -/
def encode_padding_prop (s : List UInt8) : Prop :=
  b32encode s = rstripPad (b32encode s) ++ List.replicate (padLen (s.length % 5)) padByte

theorem encode_padding_thm (s : List UInt8) : encode_padding_prop s := by
  unfold encode_padding_prop
  have key : ∃ syms : List UInt8, (∀ c ∈ syms, c ≠ padByte) ∧
      b32encode s = syms ++ List.replicate (padLen (s.length % 5)) padByte := by
    refine ⟨(encodeBody s).take ((encodeBody s).length - padLen (s.length % 5)), ?_, rfl⟩
    intro c hc heq
    exact pad_not_mem (heq ▸ encodeBody_mem s c (List.mem_of_mem_take hc))
  obtain ⟨syms, hsyms, hs⟩ := key
  rw [hs, rstripPad_append_replicate, rstripPad_eq_self_of_no_pad _ hsyms]

/-- Decoding an encoding returns the original bytes (`dec(enc(msg)) == msg`). -/
def decode_encode_prop (s : List UInt8) : Prop :=
  b32decode (b32encode s) false none = some s

theorem decode_encode_thm (s : List UInt8) : decode_encode_prop s := b32decode_b32encode s

/-- Decoding ignores any amount of trailing `=` padding (`s.rstrip(b'=')`), for all options. -/
def decode_pad_prop (s : List UInt8) : Prop :=
  ∀ (casefold : Bool) (map01 : Option UInt8) (n : Nat),
    b32decode (s ++ List.replicate n padByte) casefold map01 = b32decode s casefold map01

theorem asciiUpper_pad : asciiUpper padByte = padByte := by decide

theorem map01Replace_pad (m : UInt8) : map01Replace m padByte = padByte := by
  unfold map01Replace padByte
  rw [if_neg (by decide), if_neg (by decide)]

theorem decode_pad_thm (s : List UInt8) : decode_pad_prop s := by
  intro cf m n
  unfold b32decode
  cases m <;> cases cf <;>
    simp [List.map_append, List.map_replicate, asciiUpper_pad, map01Replace_pad,
      rstripPad_append_replicate]

/-- A successful decoding has `5 * (number of symbols) / 8` bytes. -/
def decode_length_prop (s : List UInt8) : Prop :=
  ∀ l, b32decode s false none = some l → l.length = 5 * (rstripPad s).length / 8

theorem decode_length_thm (s : List UInt8) : decode_length_prop s := by
  intro l h
  have := decodeSymbols_length (rstripPad s) 0 0 [] l (by norm_num) h
  simpa using this

/-- A byte that is neither `=` nor an alphabet symbol makes decoding fail
(`binascii.Error('Non-base32 digit found')`). -/
def decode_invalid_prop (s : List UInt8) : Prop :=
  ∀ c ∈ s, c ≠ padByte → c ∉ b32alphabet → b32decode s false none = none

theorem decode_invalid_thm (s : List UInt8) : decode_invalid_prop s := by
  intro c hc hpad halpha
  exact decodeSymbols_none_of_mem _ c 0 0 [] (mem_rstripPad s c hc hpad)
    ((b32index_eq_none_iff c).mpr halpha)

/-- If all symbols (after stripping `=`) are alphabet symbols, decoding succeeds. -/
def decode_valid_prop (s : List UInt8) : Prop :=
  (∀ c ∈ rstripPad s, c ∈ b32alphabet) → (b32decode s false none).isSome

theorem decode_valid_thm (s : List UInt8) : decode_valid_prop s := fun h =>
  decodeSymbols_isSome (rstripPad s) 0 0 [] h

/-- `casefold=True` decodes like decoding the upper-cased input. -/
def decode_casefold_prop (s : List UInt8) : Prop :=
  b32decode s true none = b32decode (s.map asciiUpper) false none

theorem decode_casefold_thm (s : List UInt8) : decode_casefold_prop s := rfl

/-- With `casefold=True`, lower-casing the input does not change the result. -/
def decode_casefold_lower_prop (s : List UInt8) : Prop :=
  b32decode (s.map asciiLower) true none = b32decode s true none

theorem asciiUpper_asciiLower (c : UInt8) : asciiUpper (asciiLower c) = asciiUpper c :=
  forall_uint8 (P := fun c => asciiUpper (asciiLower c) = asciiUpper c) (by decide +kernel) c

theorem map_upper_lower (s : List UInt8) :
    (s.map asciiLower).map asciiUpper = s.map asciiUpper := by
  induction s with
  | nil => rfl
  | cons c s ih => simp [ih, asciiUpper_asciiLower]

theorem decode_casefold_lower_thm (s : List UInt8) : decode_casefold_lower_prop s := by
  show decodeSymbols (rstripPad ((s.map asciiLower).map asciiUpper)) 0 0 [] =
    decodeSymbols (rstripPad (s.map asciiUpper)) 0 0 []
  rw [map_upper_lower]

/-- `map01` replaces `0 ↦ O` and `1 ↦ map01` before anything else. -/
def decode_map01_prop (s : List UInt8) : Prop :=
  ∀ (casefold : Bool) (m : UInt8),
    b32decode s casefold (some m) = b32decode (s.map (map01Replace m)) casefold none

theorem decode_map01_thm (s : List UInt8) : decode_map01_prop s := fun _ _ => rfl

/-- Encoding is injective (a consequence of the round trip). -/
def encode_injective_prop (s : List UInt8) : Prop :=
  ∀ t : List UInt8, b32encode s = b32encode t → s = t

theorem encode_injective_thm (s : List UInt8) : encode_injective_prop s := by
  intro t h
  have h1 := b32decode_b32encode s
  rw [h, b32decode_b32encode t] at h1
  exact (Option.some.inj h1).symm

/-- Encoding works chunk-wise: a prefix whose length is a multiple of 5 is encoded
independently of what follows. -/
def encode_append_prop (s : List UInt8) : Prop :=
  ∀ t : List UInt8, s.length % 5 = 0 → b32encode (s ++ t) = b32encode s ++ b32encode t

theorem b32encode_nil : b32encode [] = [] := by decide

theorem encode_append_thm : ∀ s : List UInt8, encode_append_prop s
  | [], t, _ => by rw [List.nil_append, b32encode_nil, List.nil_append]
  | [_], _, h => by simp at h
  | [_, _], _, h => by simp at h
  | [_, _, _], _, h => by simp at h
  | [_, _, _, _], _, h => by simp at h
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest, t, h => by
    have h' : rest.length % 5 = 0 := by simp only [List.length_cons] at h; omega
    simp only [List.cons_append]
    rw [b32encode_cons5, b32encode_cons5, encode_append_thm rest t h', List.append_assoc]

/-! ## Post-condition -/

def Post_prop (s : List UInt8) : Prop :=
  encode_length_prop s ∧ encode_alphabet_prop s ∧ encode_padding_prop s ∧ decode_encode_prop s ∧
  encode_injective_prop s ∧ encode_append_prop s ∧
  decode_pad_prop s ∧ decode_length_prop s ∧ decode_invalid_prop s ∧ decode_valid_prop s ∧
  decode_casefold_prop s ∧ decode_casefold_lower_prop s ∧ decode_map01_prop s

/-! ## Property-based tests -/

-- encode_length_prop
#eval Plausible.Testable.check (∀ s : List UInt8, (b32encode s).length = 8 * ((s.length + 4) / 5))
-- encode_alphabet_prop
#eval Plausible.Testable.check (∀ s : List UInt8,
  (b32encode s).all (fun c => c ∈ b32alphabet || c = padByte) = true)
-- encode_padding_prop
#eval Plausible.Testable.check (∀ s : List UInt8,
  b32encode s = rstripPad (b32encode s) ++ List.replicate (padLen (s.length % 5)) padByte)
-- decode_encode_prop
#eval Plausible.Testable.check (∀ s : List UInt8, b32decode (b32encode s) false none = some s)
-- encode_injective_prop (stated without a precondition, as a decidable disjunction)
#eval Plausible.Testable.check (∀ s t : List UInt8, s = t ∨ b32encode s ≠ b32encode t)
-- encode_append_prop (stated without a precondition, as a decidable disjunction)
#eval Plausible.Testable.check (∀ s t : List UInt8,
  s.length % 5 ≠ 0 ∨ b32encode (s ++ t) = b32encode s ++ b32encode t)
#eval Plausible.Testable.check (∀ (a b c d e : UInt8) (t : List UInt8),
  b32encode ([a, b, c, d, e] ++ t) = b32encode [a, b, c, d, e] ++ b32encode t)
-- decode_pad_prop
#eval Plausible.Testable.check (∀ (s : List UInt8) (cf : Bool) (m : Option UInt8) (n : Nat),
  b32decode (s ++ List.replicate n padByte) cf m = b32decode s cf m)
-- decode_length_prop (executable form)
#eval Plausible.Testable.check (∀ s : List UInt8,
  (b32decode s false none).all (fun l => l.length = 5 * (rstripPad s).length / 8))
-- decode_invalid_prop
#eval Plausible.Testable.check (∀ s : List UInt8,
  (!s.any (fun c => c ≠ padByte && c ∉ b32alphabet) || b32decode s false none = none) = true)
-- decode_valid_prop
#eval Plausible.Testable.check (∀ s : List UInt8,
  (!(rstripPad s).all (fun c => c ∈ b32alphabet) || (b32decode s false none).isSome) = true)
#eval Plausible.Testable.check (∀ (idx : List (Fin 32)) (n : Nat),
  (b32decode (idx.map (fun i => b32alphabet.getD i.val 0) ++ List.replicate n padByte)
    false none).isSome)
-- decode_casefold_prop
#eval Plausible.Testable.check (∀ s : List UInt8,
  b32decode s true none = b32decode (s.map asciiUpper) false none)
-- decode_casefold_lower_prop
#eval Plausible.Testable.check (∀ s : List UInt8,
  b32decode (s.map asciiLower) true none = b32decode s true none)
-- decode_map01_prop
#eval Plausible.Testable.check (∀ (s : List UInt8) (cf : Bool) (m : UInt8),
  b32decode s cf (some m) = b32decode (s.map (map01Replace m)) cf none)

/-- Executable (bounded) form of `Post_prop`, used for property-based testing. -/
def postCheck (s : List UInt8) : Bool :=
  ((b32encode s).length = 8 * ((s.length + 4) / 5)) &&
  (b32encode s).all (fun c => c ∈ b32alphabet || c = padByte) &&
  (b32encode s = rstripPad (b32encode s) ++ List.replicate (padLen (s.length % 5)) padByte) &&
  (b32decode (b32encode s) false none = some s) &&
  ((List.range 8).all fun k =>
    let t := (List.range k).map (fun i => UInt8.ofNat (i * 53 + 7))
    (b32encode s ≠ b32encode t || s = t) &&
    (s.length % 5 ≠ 0 || b32encode (s ++ t) = b32encode s ++ b32encode t)) &&
  ([false, true].all fun cf => [none, some 73, some 76].all fun m => (List.range 10).all fun n =>
    b32decode (s ++ List.replicate n padByte) cf m = b32decode s cf m) &&
  (b32decode s false none).all (fun l => l.length = 5 * (rstripPad s).length / 8) &&
  s.all (fun c => !(c ≠ padByte && c ∉ b32alphabet) || b32decode s false none = none) &&
  (!(rstripPad s).all (fun c => c ∈ b32alphabet) || (b32decode s false none).isSome) &&
  (b32decode s true none = b32decode (s.map asciiUpper) false none) &&
  (b32decode (s.map asciiLower) true none = b32decode s true none) &&
  ([false, true].all fun cf => (List.range 256).all fun m =>
    b32decode s cf (some (UInt8.ofNat m)) = b32decode (s.map (map01Replace (UInt8.ofNat m))) cf none)

-- Post_prop (executable bounded form)
#eval Plausible.Testable.check (∀ s : List UInt8, postCheck s = true)

-- Bounded exhaustive tests: all single bytes round-trip, pseudo-random inputs of lengths 0..59,
-- valid symbol strings of all lengths 0..63 decode successfully.
example : (List.range 256).all (fun n =>
    b32decode (b32encode [UInt8.ofNat n]) false none = some [UInt8.ofNat n]) = true := by
  native_decide
example : (List.range 60).all (fun n =>
    let s := (List.range n).map (fun i => UInt8.ofNat (i * 37 + n * 11 + 5))
    postCheck s) = true := by native_decide
example : (List.range 64).all (fun n =>
    let s := (List.range n).map (fun i => b32alphabet.getD ((i * 7 + n) % 32) 0)
    (b32decode s false none).isSome &&
      (b32decode s false none).all (fun l => l.length = 5 * n / 8)) = true := by native_decide

/-! ## Correctness theorem -/

theorem correctness (s : List UInt8) (_ : Pre s) : Post_prop s :=
  ⟨encode_length_thm s, encode_alphabet_thm s, encode_padding_thm s, decode_encode_thm s,
   encode_injective_thm s, encode_append_thm s, decode_pad_thm s, decode_length_thm s, decode_invalid_thm s, decode_valid_thm s,
   decode_casefold_thm s, decode_casefold_lower_thm s, decode_map01_thm s⟩

/-! ## Imperative implementation -/

/-- The encoding loop `for i in range(0, len(s), 5)`, with mutable `encoded` (a growing byte
array) and `rest` (the not yet consumed input); starts from `encoded0`. -/
def encodeLoopImp (s : List UInt8) (encoded0 : Array UInt8) : Array UInt8 := Id.run do
  let mut encoded := encoded0
  let mut rest := s
  for _ in List.range ((s.length + 4) / 5) do
    let chunk := rest.take 5
    rest := rest.drop 5
    -- Pad chunk to 5 bytes with 0 for bit calculation
    let padded := chunk ++ List.replicate (5 - chunk.length) (0 : UInt8)
    -- Combine into a 40-bit integer and extract 8 5-bit indices
    let val := fromBytesBE padded
    encoded := encoded.push (b32alphabet.getD (val / 2 ^ 35 % 32) 0)
    encoded := encoded.push (b32alphabet.getD (val / 2 ^ 30 % 32) 0)
    encoded := encoded.push (b32alphabet.getD (val / 2 ^ 25 % 32) 0)
    encoded := encoded.push (b32alphabet.getD (val / 2 ^ 20 % 32) 0)
    encoded := encoded.push (b32alphabet.getD (val / 2 ^ 15 % 32) 0)
    encoded := encoded.push (b32alphabet.getD (val / 2 ^ 10 % 32) 0)
    encoded := encoded.push (b32alphabet.getD (val / 2 ^ 5 % 32) 0)
    encoded := encoded.push (b32alphabet.getD (val % 32) 0)
  return encoded

/-- Imperative `b32encode`. -/
def b32encodeImp (s : List UInt8) : List UInt8 := Id.run do
  let encoded := encodeLoopImp s #[]
  -- Fix padding
  let rem := s.length % 5
  let mut out := encoded.toList
  if rem = 1 then out := out.take (out.length - 6) ++ List.replicate 6 padByte
  else if rem = 2 then out := out.take (out.length - 4) ++ List.replicate 4 padByte
  else if rem = 3 then out := out.take (out.length - 3) ++ List.replicate 3 padByte
  else if rem = 4 then out := out.take (out.length - 1) ++ List.replicate 1 padByte
  return out

/-- The decoding loop over the (stripped) symbols, with mutable `decoded`, `val`, `bits`;
starts from the given state.  `return none` models raising `binascii.Error`. -/
def decodeLoopImp (t : List UInt8) (val0 bits0 : Nat) (decoded0 : Array UInt8) :
    Option (List UInt8) := Id.run do
  let mut decoded := decoded0
  let mut val := val0
  let mut bits := bits0
  for c in t do
    match b32index c with
    | none => return none  -- raise binascii.Error('Non-base32 digit found')
    | some v =>
      val := val * 32 + v
      bits := bits + 5
      if bits ≥ 8 then
        bits := bits - 8
        decoded := decoded.push (UInt8.ofNat (val / 2 ^ bits % 256))
  return some decoded.toList

/-- Imperative `b32decode`. -/
def b32decodeImp (s : List UInt8) (casefold : Bool := false) (map01 : Option UInt8 := none) :
    Option (List UInt8) := Id.run do
  let mut s := s
  if let some m := map01 then
    s := s.map (map01Replace m)
  if casefold then
    s := s.map asciiUpper
  s := rstripPad s
  return decodeLoopImp s 0 0 #[]

/-! ## Imperative tests -/

example : b32encodeImp (bytes "") = bytes "" := by native_decide
example : b32encodeImp (bytes "f") = bytes "MY======" := by native_decide
example : b32encodeImp (bytes "fo") = bytes "MZXQ====" := by native_decide
example : b32encodeImp (bytes "foo") = bytes "MZXW6===" := by native_decide
example : b32encodeImp (bytes "foob") = bytes "MZXW6YQ=" := by native_decide
example : b32encodeImp (bytes "fooba") = bytes "MZXW6YTB" := by native_decide
example : b32encodeImp (bytes "foobar") = bytes "MZXW6YTBOI======" := by native_decide
example : b32decodeImp (b32encodeImp (bytes "VeriBench")) = some (bytes "VeriBench") := by
  native_decide
example : b32decodeImp (bytes "mzxw6ytb") true = some (bytes "fooba") := by native_decide
example : b32decodeImp (bytes "mzxw6ytb") = none := by native_decide
example : b32decodeImp (bytes "MZXW6YTB0I======") false (some 73) = some (bytes "foobar") := by
  native_decide
#eval Plausible.Testable.check (∀ s : List UInt8, b32encodeImp s = b32encode s)
#eval Plausible.Testable.check (∀ (s : List UInt8) (cf : Bool) (m : Option UInt8),
  b32decodeImp s cf m = b32decode s cf m)

/-! ## Equivalence: functional = imperative -/

theorem encodeLoopImp_toList : ∀ (s : List UInt8) (acc : Array UInt8),
    (encodeLoopImp s acc).toList = acc.toList ++ encodeBody s
  | [], acc => by
    simp [encodeLoopImp, encodeBody]
  | [b0], acc => by
    rw [show encodeBody [b0] = encodeChunk [b0] from rfl]
    simp [encodeLoopImp, List.range_succ_eq_map, Id.run_pure, Array.toList_push, encodeChunk]
  | [b0, b1], acc => by
    rw [show encodeBody [b0, b1] = encodeChunk [b0, b1] from rfl]
    simp [encodeLoopImp, List.range_succ_eq_map, Id.run_pure, Array.toList_push, encodeChunk]
  | [b0, b1, b2], acc => by
    rw [show encodeBody [b0, b1, b2] = encodeChunk [b0, b1, b2] from rfl]
    simp [encodeLoopImp, List.range_succ_eq_map, Id.run_pure, Array.toList_push, encodeChunk]
  | [b0, b1, b2, b3], acc => by
    rw [show encodeBody [b0, b1, b2, b3] = encodeChunk [b0, b1, b2, b3] from rfl]
    simp [encodeLoopImp, List.range_succ_eq_map, Id.run_pure, Array.toList_push, encodeChunk]
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest, acc => by
    have hn : ((b0 :: b1 :: b2 :: b3 :: b4 :: rest).length + 4) / 5 = (rest.length + 4) / 5 + 1 := by
      simp only [List.length_cons]; omega
    rw [encodeBody_cons5, encodeLoopImp]
    dsimp only
    rw [hn, List.range_succ_eq_map, List.forIn_cons]
    simp only [Id.run_bind, Id.run_pure, List.forIn_map, List.take_succ_cons, List.take_zero,
      List.drop_succ_cons, List.drop_zero]
    change (encodeLoopImp rest _).toList = _
    rw [encodeLoopImp_toList rest]
    simp [Array.toList_push, encodeChunk]

theorem decodeLoopImp_eq : ∀ (t : List UInt8) (val bits : Nat) (decoded : Array UInt8),
    decodeLoopImp t val bits decoded = decodeSymbols t val bits decoded.toList
  | [], val, bits, decoded => by
    simp [decodeLoopImp, decodeSymbols]
  | c :: t, val, bits, decoded => by
    rw [decodeLoopImp]
    dsimp only
    rw [List.forIn_cons, decodeSymbols]
    simp only [Id.run_bind]
    cases hc : b32index c with
    | none => simp
    | some v =>
      dsimp only
      simp only [ge_iff_le]
      by_cases h8 : 8 ≤ bits + 5
      · simp only [h8, ↓reduceIte, Id.run_bind, Id.run_pure]
        change decodeLoopImp t _ _ _ = _
        rw [decodeLoopImp_eq t, Array.toList_push]
      · simp only [h8, ↓reduceIte, Id.run_bind, Id.run_pure]
        change decodeLoopImp t _ _ _ = _
        rw [decodeLoopImp_eq t]

/-- The imperative encoder agrees with the functional one. -/
theorem b32encodeImp_eq (s : List UInt8) : b32encodeImp s = b32encode s := by
  unfold b32encodeImp b32encode fixPadding
  simp only [encodeLoopImp_toList, List.nil_append]
  have hr : s.length % 5 < 5 := Nat.mod_lt _ (by norm_num)
  generalize s.length % 5 = r at hr ⊢
  interval_cases r <;> simp [padLen]

/-- The imperative decoder agrees with the functional one. -/
theorem b32decodeImp_eq (s : List UInt8) (casefold : Bool) (map01 : Option UInt8) :
    b32decodeImp s casefold map01 = b32decode s casefold map01 := by
  cases map01 <;> cases casefold <;> simp [b32decodeImp, b32decode, decodeLoopImp_eq]

/-- Functional/imperative equivalence for both entry points. -/
theorem functional_eq_imperative :
    (∀ s : List UInt8, b32encode s = b32encodeImp s) ∧
    (∀ (s : List UInt8) (casefold : Bool) (map01 : Option UInt8),
      b32decode s casefold map01 = b32decodeImp s casefold map01) :=
  ⟨fun s => (b32encodeImp_eq s).symm, fun s cf m => (b32decodeImp_eq s cf m).symm⟩

end «23_base32»
