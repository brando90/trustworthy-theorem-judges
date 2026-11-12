import Mathlib

/-!
# Base32 encoding / decoding (translation of Python's `base64.b32encode` / `b32decode`)

This file is a Lean 4 translation of the Python program that provides Base32 encoding
and decoding, as found in Python's standard `base64` library.

Bytes-like objects are modelled as `List Nat` where every element is a byte value
(`< 256`); this is exactly what the Python pre-conditions `pre_encode` / `pre_decode`
express (an ASCII `str` is a list of values `< 128`, hence also a valid input).

* `b32encode` maps a byte list to the list of ASCII codes of the Base32 encoding.
* `b32decode` is partial (Python raises `binascii.Error` on a non-base32 digit), so it
  returns `Option (List Nat)`, with `none` standing for the raised exception.
-/

namespace Base32

/-! ## Implementation (functional) -/

/-- `_b32alphabet = b'ABCDEFGHIJKLMNOPQRSTUVWXYZ234567'` as ASCII codes. -/
def b32alphabet : List Nat :=
  [65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86,
   87, 88, 89, 90, 50, 51, 52, 53, 54, 55]

/-- ASCII code of the padding character `'='`. -/
def padByte : Nat := 61

/-- `_b32alphabet[d]`, in closed form (valid for `d < 32`). -/
def digitToChar (d : Nat) : Nat := if d < 26 then 65 + d else 50 + (d - 26)

/-- `rev_alphabet.get(c)`: the reverse alphabet lookup, `none` on a non-base32 digit. -/
def charToDigit (c : Nat) : Option Nat :=
  if 65 ≤ c ∧ c ≤ 90 then some (c - 65)
  else if 50 ≤ c ∧ c ≤ 55 then some (c - 50 + 26)
  else none

/-- `chunk + b'\0' * (5 - len(chunk))`: pad a chunk to five bytes. -/
def padChunk (c : List Nat) : List Nat := c ++ List.replicate (5 - c.length) 0

/-- `int.from_bytes(chunk, 'big')`. -/
def chunkValue (c : List Nat) : Nat := c.foldl (fun a b => a * 256 + b) 0

/-- The eight 5-bit groups `(val >> 35) & 0x1F, ..., val & 0x1F` of a 40-bit value. -/
def chunkDigits (val : Nat) : List Nat :=
  [val / 34359738368 % 32,   -- (val >> 35) & 0x1F
   val / 1073741824 % 32,    -- (val >> 30) & 0x1F
   val / 33554432 % 32,      -- (val >> 25) & 0x1F
   val / 1048576 % 32,       -- (val >> 20) & 0x1F
   val / 32768 % 32,         -- (val >> 15) & 0x1F
   val / 1024 % 32,          -- (val >> 10) & 0x1F
   val / 32 % 32,            -- (val >>  5) & 0x1F
   val % 32]                 --  val        & 0x1F

/-- `[s[i:i+5] for i in range(0, len(s), 5)]`. -/
def chunksOf5 : List Nat → List (List Nat)
  | [] => []
  | b :: rest => ((b :: rest).take 5) :: chunksOf5 ((b :: rest).drop 5)
termination_by s => s.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

/-- All the Base32 digits produced by the encoding loop, before the padding fix-up. -/
def encodeDigits (s : List Nat) : List Nat :=
  (chunksOf5 s).flatMap (fun c => chunkDigits (chunkValue (padChunk c)))

/-- Number of `'='` characters appended by the "fix padding" step, from `len(s) % 5`. -/
def padCount (n : Nat) : Nat :=
  if n % 5 = 1 then 6
  else if n % 5 = 2 then 4
  else if n % 5 = 3 then 3
  else if n % 5 = 4 then 1
  else 0

/-- `b32encode(s)`. -/
def b32encode (s : List Nat) : List Nat :=
  let e := (encodeDigits s).map digitToChar
  e.take (e.length - padCount s.length) ++ List.replicate (padCount s.length) padByte

/-- `bytes.upper()` on a single byte. -/
def upperByte (c : Nat) : Nat := if 97 ≤ c ∧ c ≤ 122 then c - 32 else c

/-- `s.replace(b'0', b'O').replace(b'1', map01)`, applied only when `map01` is truthy. -/
def applyMap01 (m : Option Nat) (s : List Nat) : List Nat :=
  match m with
  | none => s
  | some c => s.map (fun x => if x = 48 then 79 else if x = 49 then c else x)

/-- `s.rstrip(b'=')`. -/
def rstripPad (s : List Nat) : List Nat :=
  (s.reverse.dropWhile (fun c => c = padByte)).reverse

/-- Look up every character; `none` as soon as a non-base32 digit is found
(`raise binascii.Error('Non-base32 digit found')`). -/
def mapDigits : List Nat → Option (List Nat)
  | [] => some []
  | c :: cs => (charToDigit c).bind (fun d => (mapDigits cs).map (fun ds => d :: ds))

/-- The decoding loop: `val` is the bit accumulator, `bits` the number of pending bits. -/
def decLoop (val bits : Nat) : List Nat → List Nat
  | [] => []
  | d :: ds =>
    if bits + 5 ≥ 8 then
      ((val * 32 + d) / 2 ^ (bits + 5 - 8) % 256) :: decLoop (val * 32 + d) (bits + 5 - 8) ds
    else decLoop (val * 32 + d) (bits + 5) ds

/-- `b32decode(s, casefold, map01)`; `none` models the raised `binascii.Error`. -/
def b32decode (s : List Nat) (casefold : Bool := false) (map01 : Option Nat := none) :
    Option (List Nat) :=
  let s := applyMap01 map01 s
  let s := if casefold then s.map upperByte else s
  let s := rstripPad s
  (mapDigits s).map (decLoop 0 0)

/-! ## Unit tests -/

/-- ASCII string to byte list. -/
def ofString (t : String) : List Nat := t.toList.map Char.toNat

/-- Byte list back to a string, for display. -/
def toStr (l : List Nat) : String := String.mk (l.map Char.ofNat)

example : b32encode (ofString "") = ofString "" := by native_decide
example : b32encode (ofString "f") = ofString "MY======" := by native_decide
example : b32encode (ofString "fo") = ofString "MZXQ====" := by native_decide
example : b32encode (ofString "foo") = ofString "MZXW6===" := by native_decide
example : b32encode (ofString "foob") = ofString "MZXW6YQ=" := by native_decide
example : b32encode (ofString "fooba") = ofString "MZXW6YTB" := by native_decide
example : b32encode (ofString "foobar") = ofString "MZXW6YTBOI======" := by native_decide

example : b32decode (b32encode (ofString "VeriBench")) = some (ofString "VeriBench") := by
  native_decide
example : b32decode (ofString "mzxw6ytb") true none = some (ofString "fooba") := by native_decide

/-- A non-base32 digit makes the decoder raise (`none` here). -/
example : b32decode (ofString "M!") = none := by native_decide

#eval toStr (b32encode (ofString "foobar"))
#eval (b32decode (ofString "MZXW6YTBOI======")).map toStr

/-! ## Pre-conditions -/

/-- `pre_encode`: the argument is a bytes-like object, i.e. a list of byte values. -/
def Pre (s : List Nat) : Prop := ∀ b ∈ s, b < 256

/-- `pre_decode`: a bytes-like object or an ASCII string (both are lists of byte values). -/
def Pre_decode (s : List Nat) : Prop := ∀ b ∈ s, b < 256

/-! ## Auxiliary lemmas -/

theorem digitToChar_alphabet : ∀ d < 32, b32alphabet.getD d 0 = digitToChar d := by decide

theorem charToDigit_digitToChar : ∀ d < 32, charToDigit (digitToChar d) = some d := by decide

theorem digitToChar_mem : ∀ d < 32, digitToChar d ∈ b32alphabet := by decide

theorem b32alphabet_lt : ∀ b ∈ b32alphabet, b < 256 := by decide

theorem digitToChar_ne_pad : ∀ d < 32, digitToChar d ≠ padByte := by decide

theorem chunkDigits_lt (val : Nat) : ∀ d ∈ chunkDigits val, d < 32 := by
  intro d hd
  simp only [chunkDigits, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with h | h | h | h | h | h | h | h <;> subst h <;> omega

theorem encodeDigits_lt (s : List Nat) : ∀ d ∈ encodeDigits s, d < 32 := by
  intro d hd
  simp only [encodeDigits, List.mem_flatMap] at hd
  obtain ⟨c, _, hc⟩ := hd
  exact chunkDigits_lt _ d hc

theorem chunkDigits_length (val : Nat) : (chunkDigits val).length = 8 := by
  simp [chunkDigits]

theorem chunksOf5_cons (b : Nat) (rest : List Nat) :
    chunksOf5 (b :: rest) = ((b :: rest).take 5) :: chunksOf5 ((b :: rest).drop 5) := by
  rw [chunksOf5]

theorem chunksOf5_nil : chunksOf5 [] = [] := by rw [chunksOf5]

theorem encodeDigits_nil : encodeDigits [] = [] := by
  simp [encodeDigits, chunksOf5_nil]

theorem encodeDigits_cons5 (b0 b1 b2 b3 b4 : Nat) (t : List Nat) :
    encodeDigits (b0 :: b1 :: b2 :: b3 :: b4 :: t)
      = chunkDigits (chunkValue [b0, b1, b2, b3, b4]) ++ encodeDigits t := by
  simp only [encodeDigits, chunksOf5_cons, List.flatMap_cons]
  norm_num [padChunk]

theorem encodeDigits_length (s : List Nat) :
    (encodeDigits s).length = 8 * ((s.length + 4) / 5) := by
  induction s using chunksOf5.induct with
  | case1 => simp [encodeDigits_nil]
  | case2 b rest ih =>
    simp only [encodeDigits, chunksOf5_cons, List.flatMap_cons, List.length_append,
      chunkDigits_length] at *
    simp only [List.length_drop, List.length_cons] at *
    omega

theorem padCount_add5 (n : Nat) : padCount (n + 5) = padCount n := by
  simp [padCount, Nat.add_mod_right]

theorem padCount_le_len (n : Nat) : padCount n ≤ 8 * ((n + 4) / 5) := by
  unfold padCount; split_ifs <;> omega

/-! ### The decoding loop -/

theorem decLoop_nil (val bits : Nat) : decLoop val bits [] = [] := by simp [decLoop]

/-- Only the `bits` pending low bits of the accumulator influence the output. -/
theorem decLoop_norm : ∀ (ds : List Nat) (v w b : Nat), b < 8 → v % 2 ^ b = w % 2 ^ b →
    decLoop v b ds = decLoop w b ds := by
  intro ds
  induction ds with
  | nil => intro v w b _ _; simp [decLoop]
  | cons d ds ih =>
    intro v w b hb hvw
    rcases Nat.lt_or_ge (b + 5) 8 with h | h
    · rw [decLoop, decLoop, if_neg (by omega), if_neg (by omega)]
      refine ih _ _ _ (by omega) ?_
      interval_cases b <;> norm_num at hvw ⊢ <;> omega
    · rw [decLoop, decLoop, if_pos (by omega), if_pos (by omega)]
      have h1 : (v * 32 + d) / 2 ^ (b + 5 - 8) % 256 = (w * 32 + d) / 2 ^ (b + 5 - 8) % 256 := by
        interval_cases b <;> norm_num at hvw ⊢ <;> omega
      rw [h1]
      refine congrArg _ (ih _ _ _ (by omega) ?_)
      interval_cases b <;> norm_num at hvw ⊢ <;> omega

/-- With no pending bits the accumulator is irrelevant. -/
theorem decLoop_zero (v : Nat) (ds : List Nat) : decLoop v 0 ds = decLoop 0 0 ds :=
  decLoop_norm ds v 0 0 (by norm_num) (by omega)

/-- Decoding the eight digits of a full five byte chunk gives those five bytes back. -/
theorem decLoop_chunk (b0 b1 b2 b3 b4 : Nat)
    (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) (h3 : b3 < 256) (h4 : b4 < 256)
    (ds : List Nat) :
    decLoop 0 0 (chunkDigits (chunkValue [b0, b1, b2, b3, b4]) ++ ds)
      = b0 :: b1 :: b2 :: b3 :: b4 :: decLoop 0 0 ds := by
  simp only [chunkValue, chunkDigits, List.foldl_cons, List.foldl_nil, List.cons_append,
    List.nil_append]
  norm_num [decLoop]
  refine ⟨?_, ?_, ?_, ?_, ?_, decLoop_zero _ ds⟩ <;> omega

/-- Length of the decoder output. -/
theorem decLoop_length : ∀ (ds : List Nat) (val bits : Nat), bits < 8 →
    (decLoop val bits ds).length = (bits + 5 * ds.length) / 8 := by
  intro ds
  induction ds with
  | nil => intro val bits h; simp [decLoop]; omega
  | cons d ds ih =>
    intro val bits h
    rcases Nat.lt_or_ge (bits + 5) 8 with hb | hb
    · rw [decLoop, if_neg (by omega), ih _ _ (by omega)]
      simp only [List.length_cons]; omega
    · rw [decLoop, if_pos (by omega)]
      rw [List.length_cons, ih _ _ (by omega)]
      simp only [List.length_cons]; omega

/-! ### `mapDigits` -/

theorem mapDigits_map (ds : List Nat) (h : ∀ d ∈ ds, d < 32) :
    mapDigits (ds.map digitToChar) = some ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    have hd : d < 32 := h d (by simp)
    have ht : ∀ x ∈ ds, x < 32 := fun x hx => h x (by simp [hx])
    simp [mapDigits, charToDigit_digitToChar d hd, ih ht]

theorem mapDigits_length : ∀ (t ds : List Nat), mapDigits t = some ds → ds.length = t.length := by
  intro t
  induction t with
  | nil => intro ds h; simp [mapDigits] at h; simp [← h]
  | cons c cs ih =>
    intro ds h
    cases hc : charToDigit c with
    | none => simp [mapDigits, hc] at h
    | some e =>
      cases hcs : mapDigits cs with
      | none => simp [mapDigits, hc, hcs] at h
      | some ds' =>
        simp only [mapDigits, hc, hcs, Option.bind_some, Option.map_some,
          Option.some.injEq] at h
        simp [← h, ih ds' hcs]

/-! ### `rstrip` -/

theorem dropWhile_all_false (p : Nat → Bool) :
    ∀ (l : List Nat), (∀ x ∈ l, p x = false) → l.dropWhile p = l := by
  intro l
  cases l with
  | nil => intro _; rfl
  | cons a t => intro h; simp [List.dropWhile, h a (by simp)]

theorem dropWhile_replicate_append (p : Nat → Bool) (c : Nat) (hc : p c = true) :
    ∀ (k : Nat) (l : List Nat), (List.replicate k c ++ l).dropWhile p = l.dropWhile p := by
  intro k
  induction k with
  | zero => intro l; simp
  | succ k ih => intro l; simp [List.replicate_succ, hc, ih]

theorem rstripPad_append (xs : List Nat) (k : Nat) (h : ∀ x ∈ xs, x ≠ padByte) :
    rstripPad (xs ++ List.replicate k padByte) = xs := by
  unfold rstripPad
  rw [List.reverse_append, List.reverse_replicate,
    dropWhile_replicate_append _ padByte (by simp) k,
    dropWhile_all_false _ _ (by
      intro x hx
      simp only [decide_eq_false_iff_not]
      exact h x (List.mem_reverse.mp hx)),
    List.reverse_reverse]

/-! ### Splitting a `take` over an append -/

theorem take_append_len {α : Type} (l₁ l₂ : List α) (i : Nat) :
    (l₁ ++ l₂).take (l₁.length + i) = l₁ ++ l₂.take i := by
  induction l₁ with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, List.cons_append,
      show t.length + 1 + i = (t.length + i) + 1 from by omega, List.take_succ_cons, ih,
      List.cons_append]

/-! ## Properties and theorems -/

/-- The digits kept by `b32encode` decode back to the original byte list. -/
theorem decode_encodeDigits : ∀ (s : List Nat), (∀ b ∈ s, b < 256) →
    decLoop 0 0 ((encodeDigits s).take ((encodeDigits s).length - padCount s.length)) = s := by
  intro s
  induction s using chunksOf5.induct with
  | case1 => intro _; simp [encodeDigits_nil, decLoop]
  | case2 b rest ih =>
    rcases rest with _ | ⟨b1, rest⟩
    · intro hb
      have h0 : b < 256 := hb b (by simp)
      simp [encodeDigits, chunksOf5_cons, chunksOf5_nil, padChunk, chunkValue, chunkDigits,
        padCount, decLoop]
      omega
    rcases rest with _ | ⟨b2, rest⟩
    · intro hb
      have h0 : b < 256 := hb b (by simp)
      have h1 : b1 < 256 := hb b1 (by simp)
      simp [encodeDigits, chunksOf5_cons, chunksOf5_nil, padChunk, chunkValue, chunkDigits,
        padCount, decLoop]
      omega
    rcases rest with _ | ⟨b3, rest⟩
    · intro hb
      have h0 : b < 256 := hb b (by simp)
      have h1 : b1 < 256 := hb b1 (by simp)
      have h2 : b2 < 256 := hb b2 (by simp)
      simp [encodeDigits, chunksOf5_cons, chunksOf5_nil, padChunk, chunkValue, chunkDigits,
        padCount, decLoop]
      omega
    rcases rest with _ | ⟨b4, t⟩
    · intro hb
      have h0 : b < 256 := hb b (by simp)
      have h1 : b1 < 256 := hb b1 (by simp)
      have h2 : b2 < 256 := hb b2 (by simp)
      have h3 : b3 < 256 := hb b3 (by simp)
      simp [encodeDigits, chunksOf5_cons, chunksOf5_nil, padChunk, chunkValue, chunkDigits,
        padCount, decLoop]
      omega
    · intro hb
      have h0 : b < 256 := hb b (by simp)
      have h1 : b1 < 256 := hb b1 (by simp)
      have h2 : b2 < 256 := hb b2 (by simp)
      have h3 : b3 < 256 := hb b3 (by simp)
      have h4 : b4 < 256 := hb b4 (by simp)
      have ht : ∀ x ∈ t, x < 256 := fun x hx => hb x (by simp [hx])
      simp only [List.drop_succ_cons, List.drop_zero] at ih
      have iht := ih ht
      have hklen : padCount t.length ≤ (encodeDigits t).length := by
        rw [encodeDigits_length]; exact padCount_le_len _
      have hidx : (chunkDigits (chunkValue [b, b1, b2, b3, b4]) ++ encodeDigits t).length
            - padCount (b :: b1 :: b2 :: b3 :: b4 :: t).length
          = (chunkDigits (chunkValue [b, b1, b2, b3, b4])).length
            + ((encodeDigits t).length - padCount t.length) := by
        simp only [List.length_append, chunkDigits_length, List.length_cons]
        rw [show t.length + 1 + 1 + 1 + 1 + 1 = t.length + 5 from by omega, padCount_add5]
        omega
      rw [encodeDigits_cons5, hidx, take_append_len,
        decLoop_chunk b b1 b2 b3 b4 h0 h1 h2 h3 h4, iht]

/-- The encoded length is `8 * ceil(len(s) / 5)`. -/
def encode_length_prop (s : List Nat) : Prop :=
  (b32encode s).length = 8 * ((s.length + 4) / 5)

/-- The output consists of alphabet characters followed by exactly `padCount (len s)`
`'='` characters (the "fix padding" step of the Python code). -/
def encode_shape_prop (s : List Nat) : Prop :=
  ∃ body, b32encode s = body ++ List.replicate (padCount s.length) padByte ∧
    (∀ c ∈ body, c ∈ b32alphabet) ∧
    body.length = (b32encode s).length - padCount s.length

/-- The encoder returns an ASCII bytes object, i.e. a legal input for the decoder. -/
def encode_ascii_prop (s : List Nat) : Prop := Pre_decode (b32encode s)

/-- `b32decode(b32encode(s)) == s`. -/
def roundtrip_prop (s : List Nat) : Prop := b32decode (b32encode s) = some s

/-- `casefold=True` decodes the upper-cased input. -/
def casefold_prop (s : List Nat) : Prop :=
  b32decode s true none = b32decode (s.map upperByte) false none

/-- A non-base32 digit makes the decoder raise `binascii.Error` (modelled by `none`). -/
def decode_reject_prop (s : List Nat) : Prop :=
  (∃ c ∈ rstripPad s, charToDigit c = none) → b32decode s = none

/-- Every successfully decoded output has length `5 * ndigits / 8`. -/
def decode_length_prop (s : List Nat) : Prop :=
  ∀ out, b32decode s = some out → out.length = 5 * (rstripPad s).length / 8

theorem encode_length_thm (s : List Nat) : encode_length_prop s := by
  unfold encode_length_prop b32encode
  simp only [List.length_append, List.length_take, List.length_replicate, List.length_map,
    encodeDigits_length]
  have := padCount_le_len s.length
  omega

theorem encode_shape_thm (s : List Nat) : encode_shape_prop s := by
  have hlen := encode_length_thm s
  unfold encode_length_prop at hlen
  refine ⟨((encodeDigits s).map digitToChar).take
    (((encodeDigits s).map digitToChar).length - padCount s.length), rfl, ?_, ?_⟩
  · intro c hc
    have hc' : c ∈ (encodeDigits s).map digitToChar := List.mem_of_mem_take hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc'
    exact digitToChar_mem d (encodeDigits_lt s d hd)
  · have hp := padCount_le_len s.length
    simp only [List.length_take, List.length_map, encodeDigits_length, hlen]
    omega

theorem encode_ascii_thm (s : List Nat) : encode_ascii_prop s := by
  obtain ⟨body, heq, hmem, -⟩ := encode_shape_thm s
  intro b hb
  rw [heq] at hb
  rcases List.mem_append.mp hb with h | h
  · exact b32alphabet_lt b (hmem b h)
  · rw [List.eq_of_mem_replicate h]; unfold padByte; omega

theorem roundtrip_thm (s : List Nat) (h : Pre s) : roundtrip_prop s := by
  unfold roundtrip_prop b32decode b32encode Pre at *
  have hlt : ∀ d ∈ encodeDigits s, d < 32 := encodeDigits_lt s
  set E := encodeDigits s with hE
  set m := (E.map digitToChar).length - padCount s.length with hm
  have hbody : ∀ x ∈ (E.map digitToChar).take m, x ≠ padByte := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hx)
    exact digitToChar_ne_pad d (hlt d hd)
  simp only [applyMap01, Bool.false_eq_true, if_false]
  rw [rstripPad_append _ _ hbody]
  rw [show (E.map digitToChar).take m = (E.take m).map digitToChar from by
    simp [List.map_take]]
  rw [mapDigits_map _ (fun d hd => hlt d (List.mem_of_mem_take hd))]
  simp only [Option.map_some, Option.some.injEq]
  have : m = E.length - padCount s.length := by simp [hm]
  rw [this, hE]
  exact decode_encodeDigits s h

theorem casefold_thm (s : List Nat) : casefold_prop s := by
  unfold casefold_prop b32decode applyMap01
  simp

theorem mapDigits_none : ∀ (t : List Nat), (∃ c ∈ t, charToDigit c = none) → mapDigits t = none := by
  intro t
  induction t with
  | nil => intro h; simp at h
  | cons c cs ih =>
    intro h
    obtain ⟨x, hx, hxn⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx'
    · simp [mapDigits, hxn]
    · have hcs := ih ⟨x, hx', hxn⟩
      cases hc : charToDigit c <;> simp [mapDigits, hc, hcs]

theorem decode_reject_thm (s : List Nat) : decode_reject_prop s := by
  intro h
  unfold b32decode
  simp only [applyMap01, Bool.false_eq_true, if_false]
  rw [mapDigits_none _ h]
  rfl

theorem decode_length_thm (s : List Nat) : decode_length_prop s := by
  unfold decode_length_prop b32decode
  intro out hout
  simp only [applyMap01, Bool.false_eq_true, if_false] at hout
  cases hmd : mapDigits (rstripPad s) with
  | none => rw [hmd] at hout; simp at hout
  | some ds =>
    rw [hmd] at hout
    simp only [Option.map_some, Option.some.injEq] at hout
    rw [← hout, decLoop_length ds 0 0 (by norm_num), mapDigits_length _ ds hmd]
    simp

/-- The post-condition of `benchmark_b32encode` / `benchmark_b32decode`. -/
def Post_prop (s : List Nat) : Prop :=
  encode_length_prop s ∧ encode_shape_prop s ∧ encode_ascii_prop s ∧ roundtrip_prop s ∧
    casefold_prop s ∧ decode_reject_prop s ∧ decode_length_prop s

/-- Correctness: the pre-condition implies the post-condition. -/
theorem correctness (s : List Nat) (h : Pre s) : Post_prop s :=
  ⟨encode_length_thm s, encode_shape_thm s, encode_ascii_thm s, roundtrip_thm s h,
    casefold_thm s, decode_reject_thm s, decode_length_thm s⟩

/-! ## Imperative implementation -/

/-- `b32encode` written with mutable state, mirroring the Python loops. -/
def b32encodeImp (s : List Nat) : List Nat := Id.run do
  let mut encoded : List Nat := []
  for chunk in chunksOf5 s do
    let padded : List Nat := chunk ++ List.replicate (5 - chunk.length) 0
    let mut val : Nat := 0
    for b in padded do
      val := val * 256 + b
    encoded := encoded ++ (chunkDigits val).map digitToChar
  let k := padCount s.length
  return encoded.take (encoded.length - k) ++ List.replicate k padByte

/-- The decoding loop of `b32decode`, with mutable state. -/
def decodeLoopImp (ds : List Nat) : List Nat := Id.run do
  let mut decoded : List Nat := []
  let mut val : Nat := 0
  let mut bits : Nat := 0
  for d in ds do
    val := val * 32 + d
    bits := bits + 5
    decoded := if bits ≥ 8 then decoded ++ [val / 2 ^ (bits - 8) % 256] else decoded
    bits := if bits ≥ 8 then bits - 8 else bits
  return decoded

/-- `b32decode` written with mutable state, mirroring the Python loop. -/
def b32decodeImp (s : List Nat) (casefold : Bool := false) (map01 : Option Nat := none) :
    Option (List Nat) := Id.run do
  let mut t := applyMap01 map01 s
  t := if casefold then t.map upperByte else t
  t := rstripPad t
  match mapDigits t with
  | none => return none
  | some ds => return some (decodeLoopImp ds)

/-! ## Imperative unit tests -/

example : b32encodeImp (ofString "") = ofString "" := by native_decide
example : b32encodeImp (ofString "f") = ofString "MY======" := by native_decide
example : b32encodeImp (ofString "fo") = ofString "MZXQ====" := by native_decide
example : b32encodeImp (ofString "foo") = ofString "MZXW6===" := by native_decide
example : b32encodeImp (ofString "foob") = ofString "MZXW6YQ=" := by native_decide
example : b32encodeImp (ofString "fooba") = ofString "MZXW6YTB" := by native_decide
example : b32encodeImp (ofString "foobar") = ofString "MZXW6YTBOI======" := by native_decide
example : b32decodeImp (b32encodeImp (ofString "VeriBench")) = some (ofString "VeriBench") := by
  native_decide
example : b32decodeImp (ofString "mzxw6ytb") true none = some (ofString "fooba") := by
  native_decide

#eval toStr (b32encodeImp (ofString "foobar"))

/-! ## Equivalence of the functional and imperative implementations -/

theorem encodeImp_aux : ∀ (cs : List (List Nat)) (acc : List Nat),
    cs.foldl (fun a c => a ++ (chunkDigits (List.foldl (fun a b => a * 256 + b) 0
        (c ++ List.replicate (5 - c.length) 0))).map digitToChar) acc
      = acc ++ (cs.flatMap (fun c => chunkDigits (chunkValue (padChunk c)))).map digitToChar := by
  intro cs
  induction cs with
  | nil => intro acc; simp
  | cons c cs ih =>
    intro acc
    simp only [List.foldl_cons, ih, List.flatMap_cons, List.map_append, List.append_assoc,
      chunkValue, padChunk]

theorem b32encodeImp_eq (s : List Nat) : b32encodeImp s = b32encode s := by
  simp only [b32encodeImp, b32encode, Id.run, Id.pure_eq, Id.bind_eq, List.forIn_yield_eq_foldl]
  rw [encodeImp_aux]
  simp [encodeDigits]

theorem decodeImp_aux : ∀ (ds : List Nat) (dec : List Nat) (val bits : Nat),
    (ds.foldl (fun (st : MProd Nat (MProd (List Nat) Nat)) d =>
        ⟨if st.1 + 5 ≥ 8 then st.1 + 5 - 8 else st.1 + 5,
         if st.1 + 5 ≥ 8 then st.2.1 ++ [(st.2.2 * 32 + d) / 2 ^ (st.1 + 5 - 8) % 256] else st.2.1,
         st.2.2 * 32 + d⟩) ⟨bits, dec, val⟩).2.1
      = dec ++ decLoop val bits ds := by
  intro ds
  induction ds with
  | nil => intro dec val bits; simp [decLoop]
  | cons d ds ih =>
    intro dec val bits
    rcases Nat.lt_or_ge (bits + 5) 8 with h | h
    · simp only [List.foldl_cons, if_neg (by omega : ¬ (bits + 5 ≥ 8))]
      rw [ih, decLoop, if_neg (by omega)]
    · simp only [List.foldl_cons, if_pos (by omega : bits + 5 ≥ 8)]
      rw [ih, decLoop, if_pos (by omega)]
      simp

theorem decodeLoopImp_eq (ds : List Nat) : decodeLoopImp ds = decLoop 0 0 ds := by
  simp only [decodeLoopImp, Id.run, Id.pure_eq, Id.bind_eq, List.forIn_yield_eq_foldl]
  rw [decodeImp_aux]
  simp

theorem b32decodeImp_eq (s : List Nat) (casefold : Bool) (map01 : Option Nat) :
    b32decodeImp s casefold map01 = b32decode s casefold map01 := by
  simp only [b32decodeImp, b32decode, Id.run, Id.pure_eq, decodeLoopImp_eq]
  cases hmd : mapDigits (rstripPad (if casefold then (applyMap01 map01 s).map upperByte
      else applyMap01 map01 s)) with
  | none => simp
  | some ds => simp

end Base32
