import Mathlib

/-!
# Base32, following the supplied Python program

Bytes-like values are represented by lists of `Fin 256`; the input constructors
retain the distinction between bytes, bytearray, memoryview, and strings.
The codec uses big-endian groups of five bits.  Decoding deliberately accepts
missing/excess trailing `=`, ignores leftover bits, and rejects an interior `=`.
The source's memoryview decoding AttributeError is retained, despite its permissive
precondition; byte content extraction is separate from method availability.
`map01` is an optional byte string, including empty and multi-byte replacements;
replacement precedes ASCII case folding, just as in the source.
-/

namespace Base32

deriving instance DecidableEq for Except

abbrev Byte := Fin 256
abbrev Digit := Fin 32
abbrev Bytes := List Byte

def byte (n : Nat) : Byte := ⟨n % 256, Nat.mod_lt _ (by decide)⟩
def digit (n : Nat) : Digit := ⟨n % 32, Nat.mod_lt _ (by decide)⟩
/-- Literal convenience; the text-input adapter checks ASCII before using it. -/
def ascii (s : String) : Bytes := s.toList.map (fun c => byte c.toNat)
def showBytes (s : Bytes) : String := String.mk (s.map (fun b => Char.ofNat b.val))

def alphabet (d : Digit) : Byte :=
  byte (if d.val < 26 then 65 + d.val else 50 + (d.val - 26))

def unalphabet (b : Byte) : Option Digit :=
  if 65 ≤ b.val ∧ b.val ≤ 90 then some (digit (b.val - 65))
  else if 50 ≤ b.val ∧ b.val ≤ 55 then some (digit (b.val - 24))
  else none

def g0 (a : Byte) : Digit := digit (a.val / 8)
def g1 (a b : Byte) : Digit := digit (a.val % 8 * 4 + b.val / 64)
def g2 (b : Byte) : Digit := digit (b.val / 2 % 32)
def g3 (b c : Byte) : Digit := digit (b.val % 2 * 16 + c.val / 16)
def g4 (c d : Byte) : Digit := digit (c.val % 16 * 2 + d.val / 128)
def g5 (d : Byte) : Digit := digit (d.val / 4 % 32)
def g6 (d e : Byte) : Digit := digit (d.val % 4 * 8 + e.val / 32)
def g7 (e : Byte) : Digit := digit (e.val % 32)

def p0 (a b : Digit) : Byte := byte (a.val * 8 + b.val / 4)
def p1 (b c d : Digit) : Byte := byte (b.val % 4 * 64 + c.val * 2 + d.val / 16)
def p2 (d e : Digit) : Byte := byte (d.val % 16 * 16 + e.val / 2)
def p3 (e f g : Digit) : Byte := byte (e.val % 2 * 128 + f.val * 4 + g.val / 8)
def p4 (g h : Digit) : Byte := byte (g.val % 8 * 32 + h.val)

/-- Extract the significant symbols of zero-extended five-byte chunks. -/
def encodeDigits : Bytes → List Digit
  | [] => []
  | [a] => [g0 a, g1 a (byte 0)]
  | [a,b] => [g0 a, g1 a b, g2 b, g3 b (byte 0)]
  | [a,b,c] => [g0 a, g1 a b, g2 b, g3 b c, g4 c (byte 0)]
  | [a,b,c,d] => [g0 a, g1 a b, g2 b, g3 b c, g4 c d, g5 d, g6 d (byte 0)]
  | a::b::c::d::e::rest =>
      [g0 a, g1 a b, g2 b, g3 b c, g4 c d, g5 d, g6 d e, g7 e] ++ encodeDigits rest

/-- Emit only complete bytes; residual low bits are discarded. -/
def decodeDigits : List Digit → Bytes
  | [] | [_] => []
  | [a,b] | [a,b,_] => [p0 a b]
  | [a,b,c,d] => [p0 a b, p1 b c d]
  | [a,b,c,d,e] | [a,b,c,d,e,_] => [p0 a b, p1 b c d, p2 d e]
  | [a,b,c,d,e,f,g] => [p0 a b, p1 b c d, p2 d e, p3 e f g]
  | a::b::c::d::e::f::g::h::rest =>
      [p0 a b, p1 b c d, p2 d e, p3 e f g, p4 g h] ++ decodeDigits rest

def padding (n : Nat) : Nat :=
  match n % 5 with
  | 1 => 6 | 2 => 4 | 3 => 3 | 4 => 1 | _ => 0

def b32encode (s : Bytes) : Bytes :=
  (encodeDigits s).map alphabet ++ List.replicate (padding s.length) (byte 61)

inductive Error where
  | expectedBytesLike | nonAsciiString | nonBase32Digit
  | missingMethod (method : String)
  deriving DecidableEq, Repr

/-- Python's two successive, non-recursive byte replacements. -/
def mapAmbiguous (s : Bytes) (map01 : Option Bytes) : Bytes :=
  match map01 with
  | none | some [] => s
  | some replacement =>
      (s.map (fun b => if b = byte 48 then byte 79 else b)).flatMap
        (fun b => if b = byte 49 then replacement else [b])

def upper (b : Byte) : Byte :=
  if 97 ≤ b.val ∧ b.val ≤ 122 then byte (b.val - 32) else b

def stripPadding (s : Bytes) : Bytes :=
  (s.reverse.dropWhile (fun b => b == byte 61)).reverse

def prepare (s : Bytes) (casefold : Bool) (map01 : Option Bytes) : Bytes :=
  stripPadding (if casefold then (mapAmbiguous s map01).map upper else mapAmbiguous s map01)

def parseDigits : Bytes → Except Error (List Digit)
  | [] => .ok []
  | b :: rest => match unalphabet b with
    | none => .error .nonBase32Digit
    | some d => (parseDigits rest).map (d :: ·)

def b32decode (s : Bytes) (casefold : Bool := false) (map01 : Option Bytes := none) :
    Except Error Bytes :=
  (parseDigits (prepare s casefold map01)).map decodeDigits

/-- The source decoder's integer accumulator, written recursively.
Multiplication by 32 and addition append a five-bit digit without overlap. -/
def decodeStream : List Digit → Nat → Nat → Bytes
  | [], _, _ => []
  | d :: ds, val, bits =>
      let val' := val * 32 + d.val
      let bits' := bits + 5
      if bits' ≥ 8 then
        byte (val' / 2 ^ (bits' - 8)) :: decodeStream ds val' (bits' - 8)
      else decodeStream ds val' bits'

inductive Input where
  | bytes (value : Bytes) | bytearray (value : Bytes) | memoryview (value : Bytes)
  | text (value : String) | other
  deriving DecidableEq, Repr

def encodeInput : Input → Except Error Bytes
  | .bytes s | .bytearray s | .memoryview s => .ok s
  | _ => .error .expectedBytesLike

def decodeInput : Input → Except Error Bytes
  | .bytes s | .bytearray s | .memoryview s => .ok s
  | .text s => if s.toList.all (fun c => c.toNat < 128) then .ok (ascii s)
      else .error .nonAsciiString
  | .other => .error .expectedBytesLike

def benchmark_b32encode (s : Input) : Except Error Bytes := (encodeInput s).map b32encode

/-- A memoryview passes the source precondition but has none of these methods. -/
def memoryviewError (casefold : Bool) (map01 : Option Bytes) : Error :=
  .missingMethod (if map01.any (fun bs => !bs.isEmpty) then "replace"
    else if casefold then "upper" else "rstrip")

def objectDecodeResult (s : Input) (payload : Bytes) (casefold : Bool)
    (map01 : Option Bytes) : Except Error Bytes :=
  match s with
  | .memoryview _ => .error (memoryviewError casefold map01)
  | _ => b32decode payload casefold map01

def benchmark_b32decode (s : Input) (casefold : Bool := false)
    (map01 : Option Bytes := none) : Except Error Bytes :=
  (decodeInput s).bind (fun t => objectDecodeResult s t casefold map01)

-- Unit tests: RFC vectors and the supplied VeriBench cases.
example : b32encode (ascii "") = ascii "" := by native_decide
example : b32encode (ascii "f") = ascii "MY======" := by native_decide
example : b32encode (ascii "fo") = ascii "MZXQ====" := by native_decide
example : b32encode (ascii "foo") = ascii "MZXW6===" := by native_decide
example : b32encode (ascii "foob") = ascii "MZXW6YQ=" := by native_decide
example : b32encode (ascii "fooba") = ascii "MZXW6YTB" := by native_decide
example : b32encode (ascii "foobar") = ascii "MZXW6YTBOI======" := by native_decide
example : b32decode (b32encode (ascii "VeriBench")) = .ok (ascii "VeriBench") := by native_decide
example : b32decode (ascii "mzxw6ytb") true = .ok (ascii "fooba") := by native_decide
example : b32decode (ascii "MY") = .ok (ascii "f") := by native_decide
example : b32decode (ascii "MY=========") = .ok (ascii "f") := by native_decide
example : b32decode (ascii "MZ======") = .ok (ascii "f") := by native_decide
example : b32decode (ascii "A") = .ok [] := by native_decide
example : b32decode (ascii "========") = .ok [] := by native_decide
example : b32decode (ascii "M=Y") = .error .nonBase32Digit := by native_decide
example : b32decode (ascii "my") = .error .nonBase32Digit := by native_decide
example : b32decode (ascii "M1") true (some (ascii "y")) = .ok (ascii "f") := by native_decide
example : b32decode (ascii "1") false (some (ascii "MY")) = .ok (ascii "f") := by native_decide
example : b32decode (ascii "1") false (some []) = .error .nonBase32Digit := by native_decide
example : benchmark_b32decode (.text "MY======") = .ok (ascii "f") := by native_decide
example : benchmark_b32encode (.memoryview (ascii "f")) = .ok (ascii "MY======") := by native_decide
example : benchmark_b32decode (.memoryview (ascii "MY")) =
    .error (.missingMethod "rstrip") := by native_decide
example : benchmark_b32decode (.memoryview []) true =
    .error (.missingMethod "upper") := by native_decide
example : benchmark_b32decode (.memoryview []) true (some (ascii "I")) =
    .error (.missingMethod "replace") := by native_decide
example : benchmark_b32decode (.text "é") = .error .nonAsciiString := by native_decide
example : benchmark_b32encode (.text "foo") = .error .expectedBytesLike := by native_decide
#eval showBytes (b32encode (ascii "VeriBench"))
#eval (b32decode (ascii "mzxw6ytb") true).map showBytes

-- Preconditions concern input types, never padding, alphabet, or length.
def pre_encode (s : Input) : Prop := ∃ bs, encodeInput s = .ok bs

def pre_decode (s : Input) : Prop := ∃ bs, decodeInput s = .ok bs

def Pre (enc dec : Input) : Prop := pre_encode enc ∧ pre_decode dec

private theorem alphabet_inverse (d : Digit) : unalphabet (alphabet d) = some d := by
  fin_cases d <;> decide

private theorem alphabet_ne_pad (d : Digit) : alphabet d ≠ byte 61 := by
  fin_cases d <;> decide

private theorem p0_inverse (a b : Byte) : p0 (g0 a) (g1 a b) = a := by
  apply Fin.ext
  simp only [p0, g0, g1, digit, byte]
  have ha := a.isLt
  have hb := b.isLt
  omega

private theorem p1_inverse (a b c : Byte) : p1 (g1 a b) (g2 b) (g3 b c) = b := by
  apply Fin.ext
  simp only [p1, g1, g2, g3, digit, byte]
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  omega

private theorem p2_inverse (b c d : Byte) : p2 (g3 b c) (g4 c d) = c := by
  apply Fin.ext
  simp only [p2, g3, g4, digit, byte]
  have hb := b.isLt
  have hc := c.isLt
  have hd := d.isLt
  omega

private theorem p3_inverse (c d e : Byte) : p3 (g4 c d) (g5 d) (g6 d e) = d := by
  apply Fin.ext
  simp only [p3, g4, g5, g6, digit, byte]
  have hc := c.isLt
  have hd := d.isLt
  have he := e.isLt
  omega

private theorem p4_inverse (d e : Byte) : p4 (g6 d e) (g7 e) = e := by
  apply Fin.ext
  simp only [p4, g6, g7, digit, byte]
  have hd := d.isLt
  have he := e.isLt
  omega

private theorem digits_roundtrip (s : Bytes) : decodeDigits (encodeDigits s) = s := by
  induction s using encodeDigits.induct <;>
    simp_all [encodeDigits, decodeDigits, p0_inverse, p1_inverse, p2_inverse,
      p3_inverse, p4_inverse]

private theorem stream_eq_digits (ds : List Digit) (v : Nat) :
    decodeStream ds v 0 = decodeDigits ds := by
  induction ds using decodeDigits.induct generalizing v <;>
    simp_all [decodeStream, decodeDigits]
  all_goals repeat' apply And.intro
  all_goals
    apply Fin.ext
    simp only [byte, p0, p1, p2, p3, p4]
    omega

private theorem strip_append_padding (s : Bytes) (n : Nat) :
    stripPadding (s ++ List.replicate n (byte 61)) = stripPadding s := by
  simp only [stripPadding, List.reverse_append, List.reverse_replicate]
  rw [List.dropWhile_append_of_pos (by simp)]

private theorem dropWhile_alphabet (ds : List Digit) :
    (ds.map alphabet).dropWhile (fun b => b == byte 61) = ds.map alphabet := by
  cases ds <;> simp [alphabet_ne_pad]

private theorem strip_alphabet (ds : List Digit) :
    stripPadding (ds.map alphabet) = ds.map alphabet := by
  rw [stripPadding, ← List.map_reverse, dropWhile_alphabet, List.map_reverse, List.reverse_reverse]

private theorem strip_encode (s : Bytes) :
    stripPadding (b32encode s) = (encodeDigits s).map alphabet := by
  rw [b32encode, strip_append_padding, strip_alphabet]

private theorem parse_alphabet (ds : List Digit) :
    parseDigits (ds.map alphabet) = .ok ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [parseDigits, alphabet_inverse, ih, Except.map]

private theorem encodeDigits_length (s : Bytes) :
    (encodeDigits s).length = (s.length * 8 + 4) / 5 := by
  induction s using encodeDigits.induct <;> simp_all [encodeDigits]
  omega

private theorem padding_length (n : Nat) :
    (n * 8 + 4) / 5 + padding n = (n + 4) / 5 * 8 := by
  have hm : n % 5 < 5 := Nat.mod_lt _ (by decide)
  interval_cases h : n % 5 <;> simp [padding, h] <;> omega

private theorem decodeDigits_length (ds : List Digit) :
    (decodeDigits ds).length = ds.length * 5 / 8 := by
  induction ds using decodeDigits.induct <;> simp_all [decodeDigits]
  omega

private theorem parse_error (s : Bytes) :
    parseDigits s = .error .nonBase32Digit ↔ ∃ b ∈ s, unalphabet b = none := by
  induction s with
  | nil => simp [parseDigits]
  | cons b bs ih =>
    cases hb : unalphabet b with
    | none => simp [parseDigits, hb]
    | some d =>
      cases hs : parseDigits bs <;> simp_all [parseDigits, Except.map]

private theorem parse_only_error (s : Bytes) (e : Error)
    (h : parseDigits s = .error e) : e = .nonBase32Digit := by
  induction s with
  | nil => simp [parseDigits] at h
  | cons b bs ih =>
    cases hb : unalphabet b with
    | none => simpa [parseDigits, hb] using h.symm
    | some d =>
      cases hs : parseDigits bs <;> simp_all [parseDigits, Except.map]

private theorem parse_length (s : Bytes) (ds : List Digit)
    (h : parseDigits s = .ok ds) : ds.length = s.length := by
  induction s generalizing ds with
  | nil => simpa [parseDigits] using h.symm
  | cons b bs ih =>
    cases hb : unalphabet b with
    | none => simp [parseDigits, hb] at h
    | some d =>
      cases hs : parseDigits bs with
      | error e => simp [parseDigits, hb, hs, Except.map] at h
      | ok tail =>
        simp [parseDigits, hb, hs, Except.map] at h
        subst ds
        simp [ih tail hs]

/-- Every byte string, of arbitrary length and byte values, round-trips. -/
def roundtrip_prop (s : Bytes) : Prop := b32decode (b32encode s) = .ok s

theorem roundtrip_thm (s : Bytes) : roundtrip_prop s := by
  simp [roundtrip_prop, b32decode, prepare, mapAmbiguous, strip_encode,
    parse_alphabet, Except.map, digits_roundtrip]

/-- The encoded size is eight times the number of five-byte chunks. -/
def encoded_size_prop (s : Bytes) : Prop :=
  (b32encode s).length = (s.length + 4) / 5 * 8 ∧ (b32encode s).length % 8 = 0

theorem encoded_size_thm (s : Bytes) : encoded_size_prop s := by
  have h : (b32encode s).length = (s.length + 4) / 5 * 8 := by
    simp [b32encode, encodeDigits_length, padding_length]
  exact ⟨h, by rw [h]; omega⟩

/-- Alphabet, significant-symbol count, and the exact Python padding suffix. -/
def encoded_format_prop (s : Bytes) : Prop :=
  let payload := stripPadding (b32encode s)
  payload.all (fun b => (unalphabet b).isSome) = true ∧
  payload.length = (s.length * 8 + 4) / 5 ∧
  b32encode s = payload ++ List.replicate (padding s.length) (byte 61)

theorem encoded_format_thm (s : Bytes) : encoded_format_prop s := by
  unfold encoded_format_prop
  rw [strip_encode]
  simp [List.all_map, alphabet_inverse, encodeDigits_length, b32encode]

/-- Error exactly when the preprocessed, unpadded input contains a bad digit. -/
def decode_error_prop (s : Bytes) (cf : Bool) (mp : Option Bytes) : Prop :=
  b32decode s cf mp = .error .nonBase32Digit ↔
    ∃ b ∈ prepare s cf mp, unalphabet b = none

theorem decode_error_thm (s : Bytes) (cf : Bool) (mp : Option Bytes) :
    decode_error_prop s cf mp := by
  unfold decode_error_prop b32decode
  rw [← parse_error]
  cases parseDigits (prepare s cf mp) <;> simp [Except.map]

/-- All complete octets are emitted, with no validation of leftover low bits. -/
def decoded_size_prop (s : Bytes) (cf : Bool) (mp : Option Bytes) : Prop :=
  ∀ out, b32decode s cf mp = .ok out → out.length = (prepare s cf mp).length * 5 / 8

theorem decoded_size_thm (s : Bytes) (cf : Bool) (mp : Option Bytes) :
    decoded_size_prop s cf mp := by
  intro out h
  unfold b32decode at h
  cases hp : parseDigits (prepare s cf mp) with
  | error e => simp [hp, Except.map] at h
  | ok ds =>
    simp [hp, Except.map] at h
    subst out
    rw [decodeDigits_length, parse_length _ _ hp]

/-- Correspondence with the source's unbounded integer/bit-counter decoder. -/
def streaming_prop (s : Bytes) (cf : Bool) (mp : Option Bytes) : Prop :=
  b32decode s cf mp =
    (parseDigits (prepare s cf mp)).map (fun ds => decodeStream ds 0 0)

theorem streaming_thm (s : Bytes) (cf : Bool) (mp : Option Bytes) :
    streaming_prop s cf mp := by
  simp [streaming_prop, stream_eq_digits, b32decode]

/-- Extra trailing padding is ignored even for malformed input. -/
def trailing_padding_prop (s : Bytes) (n : Nat) : Prop :=
  b32decode (s ++ List.replicate n (byte 61)) = b32decode s

theorem trailing_padding_thm (s : Bytes) (n : Nat) : trailing_padding_prop s n := by
  simp [trailing_padding_prop, b32decode, prepare, mapAmbiguous, strip_append_padding]

/-- Preconditions guarantee successful coercion, not successful decoding.
The postcondition includes the observable benchmark results and all codec laws. -/
def Post_prop (enc dec : Input) (cf : Bool) (mp : Option Bytes) (n : Nat) : Prop :=
  ∃ s t, encodeInput enc = .ok s ∧ decodeInput dec = .ok t ∧
    benchmark_b32encode enc = .ok (b32encode s) ∧
    benchmark_b32decode dec cf mp = objectDecodeResult dec t cf mp ∧
    roundtrip_prop s ∧ encoded_size_prop s ∧ encoded_format_prop s ∧
    decode_error_prop t cf mp ∧ decoded_size_prop t cf mp ∧ streaming_prop t cf mp ∧
    trailing_padding_prop t n

-- Property-based tests. Boolean counterparts avoid quantifying over output lists.
def roundtripCheck (s : Bytes) : Bool := b32decode (b32encode s) == .ok s

def sizeCheck (s : Bytes) : Bool :=
  (b32encode s).length == (s.length + 4) / 5 * 8 && (b32encode s).length % 8 == 0

def formatCheck (s : Bytes) : Bool :=
  let payload := stripPadding (b32encode s)
  payload.all (fun b => (unalphabet b).isSome) &&
    payload.length == (s.length * 8 + 4) / 5 &&
    b32encode s == payload ++ List.replicate (padding s.length) (byte 61)

def errorCheck (s : Bytes) (cf : Bool) (mp : Option Bytes) : Bool :=
  (b32decode s cf mp == .error .nonBase32Digit) ==
    (prepare s cf mp).any (fun b => (unalphabet b).isNone)

def decodedSizeCheck (s : Bytes) (cf : Bool) (mp : Option Bytes) : Bool :=
  match b32decode s cf mp with
  | .ok out => out.length == (prepare s cf mp).length * 5 / 8
  | .error _ => true

def streamingCheck (s : Bytes) (cf : Bool) (mp : Option Bytes) : Bool :=
  b32decode s cf mp == (parseDigits (prepare s cf mp)).map (fun ds => decodeStream ds 0 0)

def paddingCheck (s : Bytes) (n : Nat) : Bool :=
  b32decode (s ++ List.replicate n (byte 61)) == b32decode s

/-- The executable implication `Pre → Post`; inadmissible types are skipped. -/
def postCheck (enc dec : Input) (cf : Bool) (mp : Option Bytes) (n : Nat) : Bool :=
  match encodeInput enc, decodeInput dec with
  | .ok s, .ok t =>
    benchmark_b32encode enc == .ok (b32encode s) &&
    benchmark_b32decode dec cf mp == objectDecodeResult dec t cf mp &&
    roundtripCheck s && sizeCheck s && formatCheck s && errorCheck t cf mp &&
    decodedSizeCheck t cf mp && streamingCheck t cf mp && paddingCheck t n
  | _, _ => true

/-- All 256 single bytes, all 65,536 byte pairs, and patterned longer messages
covering every chunk remainder, zeros, high bytes, and repeated/mixed values. -/
def byteSamples : List Bytes :=
  [[]] ++ (List.range 256).map (fun a => [byte a]) ++
  (List.range 256).flatMap (fun a => (List.range 256).map (fun b => [byte a, byte b])) ++
  (List.range 65).flatMap (fun len => (List.range 16).map (fun seed =>
    (List.range len).map (fun i => byte (seed * 73 + i * (seed + 1)))))

/-- Valid, lowercase, malformed, unpadded and excessive-padding inputs. -/
def decodeSamples : List Bytes :=
  (List.range 256).map (fun b => [byte b]) ++
  (List.range 41).flatMap (fun len => (List.range 12).flatMap (fun seed =>
    let s := (List.range len).map (fun i => byte (seed * 73 + i * 29))
    [s, b32encode s, stripPadding (b32encode s), b32encode s ++ ascii "===",
      (b32encode s).map (fun b => if 65 ≤ b.val ∧ b.val ≤ 90 then byte (b.val + 32) else b)])) ++
  [ascii "0", ascii "1", ascii "M1", ascii "01", ascii "M=Y", ascii "m1", ascii "MY "]

def optionSamples : List (Option Bytes) :=
  [none, some [], some (ascii "I"), some (ascii "L"), some (ascii "y"),
   some (ascii "MY"), some (ascii "="), some (ascii "M0"), some [byte 255]]

-- PBT: roundtrip_prop, encoded_size_prop, encoded_format_prop.
example : byteSamples.all roundtripCheck = true := by native_decide
example : byteSamples.all sizeCheck = true := by native_decide
example : byteSamples.all formatCheck = true := by native_decide

-- PBT: decode_error_prop, decoded_size_prop, streaming_prop; both casefold
-- settings and empty, single-byte, multi-byte, and invalid replacements.
example : decodeSamples.all (fun s => [false, true].all (fun cf =>
    optionSamples.all (errorCheck s cf))) = true := by native_decide
example : decodeSamples.all (fun s => [false, true].all (fun cf =>
    optionSamples.all (decodedSizeCheck s cf))) = true := by native_decide
example : decodeSamples.all (fun s => [false, true].all (fun cf =>
    optionSamples.all (streamingCheck s cf))) = true := by native_decide

-- PBT: trailing_padding_prop, including malformed inputs.
example : decodeSamples.all (fun s => (List.range 17).all (paddingCheck s)) = true := by native_decide

-- PBT: Post_prop on all input kinds admitted by Pre, including memoryview's
-- runtime method error. Non-ASCII strings and other objects test the guard.
def inputSamples : List Input :=
  [Input.text "", .text "MY======", .text "mzxw6ytb", .text "é", .other] ++
  (decodeSamples.take 320).flatMap (fun s => [.bytes s, .bytearray s, .memoryview s])
example : inputSamples.all (fun dec => [false, true].all (fun cf =>
    optionSamples.all (fun mp =>
      [Input.bytes (ascii "VeriBench"), .bytearray [byte 0, byte 255], .memoryview []].all
        (fun enc => postCheck enc dec cf mp 9)))) = true := by native_decide

-- Randomized PBTs also cover arbitrary lists and independently varying options.
#eval Plausible.Testable.check (∀ ns : List Nat, roundtripCheck (ns.map byte) = true)
#eval Plausible.Testable.check (∀ ns : List Nat, sizeCheck (ns.map byte) = true)
#eval Plausible.Testable.check (∀ ns : List Nat, formatCheck (ns.map byte) = true)
#eval Plausible.Testable.check (∀ (ns rs : List Nat) (cf : Bool),
  errorCheck (ns.map byte) cf (some (rs.map byte)) = true)
#eval Plausible.Testable.check (∀ (ns rs : List Nat) (cf : Bool),
  decodedSizeCheck (ns.map byte) cf (some (rs.map byte)) = true)
#eval Plausible.Testable.check (∀ (ns rs : List Nat) (cf : Bool),
  streamingCheck (ns.map byte) cf (some (rs.map byte)) = true)
#eval Plausible.Testable.check (∀ (ns : List Nat) (n : Nat),
  paddingCheck (ns.map byte) (n % 65) = true)
#eval Plausible.Testable.check (∀ (ns ts rs : List Nat) (cf : Bool) (n : Nat),
  postCheck (.bytes (ns.map byte)) (.bytes (ts.map byte)) cf (some (rs.map byte)) (n % 65) = true)

/-- Correctness on precisely the source's admitted input types. -/
theorem correctness_thm (enc dec : Input) (cf : Bool) (mp : Option Bytes) (n : Nat) :
    Pre enc dec → Post_prop enc dec cf mp n := by
  rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
  refine ⟨s, t, hs, ht, ?_, ?_, roundtrip_thm s, encoded_size_thm s,
    encoded_format_thm s, decode_error_thm t cf mp, decoded_size_thm t cf mp,
    streaming_thm t cf mp, trailing_padding_thm t n⟩
  · simp [benchmark_b32encode, hs, Except.map]
  · simp [benchmark_b32decode, ht, Except.bind]

-- Imperative implementation: five-byte arithmetic for encoding and the
-- source's unbounded accumulator/bit counter for decoding.
def chunks5 : Bytes → List Bytes
  | [] => []
  | [a] => [[a]]
  | [a,b] => [[a,b]]
  | [a,b,c] => [[a,b,c]]
  | [a,b,c,d] => [[a,b,c,d]]
  | a::b::c::d::e::rest => [a,b,c,d,e] :: chunks5 rest

/-- Numeric interpretation of a zero-padded chunk and its significant indices.
Indices that the source would overwrite with `=` are omitted here; the same
padding suffix is appended after processing the chunks. -/
def numericBlock (chunk : Bytes) : List Digit :=
  let padded := chunk ++ List.replicate (5 - chunk.length) (byte 0)
  let val := padded.foldl (fun v b => v * 256 + b.val) 0
  (List.range ((chunk.length * 8 + 4) / 5)).map
    (fun i => digit (val / 2 ^ (35 - i * 5)))

def encodeChunkImperative (chunk : Bytes) : Bytes := Id.run do
  let mut val := 0
  for b in chunk ++ List.replicate (5 - chunk.length) (byte 0) do
    val := val * 256 + b.val
  let mut encoded := []
  for i in List.range ((chunk.length * 8 + 4) / 5) do
    encoded := encoded ++ [alphabet (digit (val / 2 ^ (35 - i * 5)))]
  return encoded

def b32encodeImperative (s : Bytes) : Bytes := Id.run do
  let mut encoded := []
  for chunk in chunks5 s do
    encoded := encoded ++ encodeChunkImperative chunk
  encoded := encoded ++ List.replicate (padding s.length) (byte 61)
  return encoded

structure DecodeState where
  val : Nat := 0
  bits : Nat := 0
  out : Bytes := []

def decodeStep (st : DecodeState) (d : Digit) : DecodeState :=
  let val := st.val * 32 + d.val
  let bits := st.bits + 5
  if bits ≥ 8 then
    ⟨val, bits - 8, st.out ++ [byte (val / 2 ^ (bits - 8))]⟩
  else ⟨val, bits, st.out⟩

def scanByte (result : Except Error DecodeState) (b : Byte) : Except Error DecodeState :=
  match result with
  | .error e => .error e
  | .ok st => match unalphabet b with
    | none => .error .nonBase32Digit
    | some d => .ok (decodeStep st d)

def b32decodeImperative (s : Bytes) (casefold : Bool := false)
    (map01 : Option Bytes := none) : Except Error Bytes := Id.run do
  let mut state : Except Error DecodeState := .ok {}
  for b in prepare s casefold map01 do
    state := scanByte state b
  return state.map (fun st => st.out)

def benchmark_b32encodeImperative (s : Input) : Except Error Bytes :=
  (encodeInput s).map b32encodeImperative

def benchmark_b32decodeImperative (s : Input) (casefold : Bool := false)
    (map01 : Option Bytes := none) : Except Error Bytes :=
  (decodeInput s).bind (fun t => match s with
    | .memoryview _ => .error (memoryviewError casefold map01)
    | _ => b32decodeImperative t casefold map01)

-- Imperative unit and property-based tests, before the equivalence proof.
example : b32encodeImperative (ascii "") = ascii "" := by native_decide
example : b32encodeImperative (ascii "f") = ascii "MY======" := by native_decide
example : b32encodeImperative (ascii "fo") = ascii "MZXQ====" := by native_decide
example : b32encodeImperative (ascii "foo") = ascii "MZXW6===" := by native_decide
example : b32encodeImperative (ascii "foob") = ascii "MZXW6YQ=" := by native_decide
example : b32encodeImperative (ascii "fooba") = ascii "MZXW6YTB" := by native_decide
example : b32encodeImperative (ascii "foobar") = ascii "MZXW6YTBOI======" := by native_decide
example : b32decodeImperative (b32encodeImperative (ascii "VeriBench")) =
    .ok (ascii "VeriBench") := by native_decide
example : b32decodeImperative (ascii "mzxw6ytb") true = .ok (ascii "fooba") := by native_decide
example : b32decodeImperative (ascii "M=Y") = .error .nonBase32Digit := by native_decide
example : b32decodeImperative (ascii "M1") true (some (ascii "y")) = .ok (ascii "f") := by native_decide
example : benchmark_b32decodeImperative (.memoryview []) =
    .error (.missingMethod "rstrip") := by native_decide
example : byteSamples.all (fun s => b32encodeImperative s == b32encode s) = true := by native_decide
example : decodeSamples.all (fun s => [false, true].all (fun cf =>
    optionSamples.all (fun mp => b32decodeImperative s cf mp == b32decode s cf mp))) = true := by
  native_decide
#eval showBytes (b32encodeImperative (ascii "VeriBench"))
#eval (b32decodeImperative (ascii "mzxw6ytb") true).map showBytes

private theorem fold_append_map {α β : Type} (f : α → β) (xs : List α) (acc : List β) :
    xs.foldl (fun out x => out ++ [f x]) acc = acc ++ xs.map f := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih => simp [ih, List.append_assoc]

private theorem fold_append_flatMap {α β : Type} (f : α → List β) (xs : List α)
    (acc : List β) : xs.foldl (fun out x => out ++ f x) acc = acc ++ xs.flatMap f := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih => simp [ih, List.append_assoc]

private theorem encodeChunkImperative_eq (chunk : Bytes) :
    encodeChunkImperative chunk = (numericBlock chunk).map alphabet := by
  simp [encodeChunkImperative, numericBlock, List.map_map]
  simp only [← List.flatMap_def, ← List.map_eq_flatMap]
  rfl

private theorem numericBlock_eq (s : Bytes) (h : s.length ≤ 5) :
    numericBlock s = encodeDigits s := by
  rcases s with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, rest⟩⟩⟩⟩⟩
  all_goals try (have hr : rest = [] := List.eq_nil_of_length_eq_zero (by simpa using h); subst rest)
  all_goals
    simp [numericBlock, encodeDigits, List.range_succ, List.replicate_succ, byte]
  all_goals repeat' apply And.intro
  all_goals
    apply Fin.ext
    simp only [digit, g0, g1, g2, g3, g4, g5, g6, g7]
    omega

private theorem chunks5_flatMap (s : Bytes) :
    (chunks5 s).flatMap (fun c => (numericBlock c).map alphabet) = (encodeDigits s).map alphabet := by
  induction s using chunks5.induct <;>
    simp only [chunks5, List.flatMap_cons, List.flatMap_nil]
  all_goals try rw [numericBlock_eq _ (by simp)]
  all_goals simp_all [encodeDigits]

/-- Functional encoding equals the mutable five-byte, big-endian calculation. -/
theorem encode_equivalence_thm (s : Bytes) : b32encode s = b32encodeImperative s := by
  simp [b32encodeImperative, encodeChunkImperative_eq, b32encode]
  exact (chunks5_flatMap s).symm

private theorem fold_decodeStream (ds : List Digit) (st : DecodeState) :
    (ds.foldl decodeStep st).out = st.out ++ decodeStream ds st.val st.bits := by
  induction ds generalizing st with
  | nil => simp [decodeStream]
  | cons d ds ih =>
    rw [List.foldl_cons, ih]
    simp only [decodeStep, decodeStream]
    split <;> simp_all [List.append_assoc]

private theorem scan_error (bs : Bytes) (e : Error) :
    bs.foldl scanByte (.error e) = .error e := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simpa [scanByte] using ih

private theorem scan_parse (bs : Bytes) (st : DecodeState) :
    bs.foldl scanByte (.ok st) = (parseDigits bs).map (fun ds => ds.foldl decodeStep st) := by
  induction bs generalizing st with
  | nil => rfl
  | cons b bs ih =>
    cases hb : unalphabet b with
    | none => simp [scanByte, parseDigits, hb, scan_error, Except.map]
    | some d =>
      simp only [List.foldl_cons, scanByte, hb]
      rw [ih]
      cases hs : parseDigits bs <;> simp [parseDigits, hb, hs, Except.map]

/-- Functional decoding equals the mutable accumulator on every input and option,
including malformed data and multi-byte replacements. -/
theorem decode_equivalence_thm (s : Bytes) (cf : Bool) (mp : Option Bytes) :
    b32decode s cf mp = b32decodeImperative s cf mp := by
  have hi : b32decodeImperative s cf mp =
      ((prepare s cf mp).foldl scanByte (.ok {})).map (fun st => st.out) := by
    simp [b32decodeImperative]
  rw [hi, scan_parse]
  cases hp : parseDigits (prepare s cf mp) <;>
    simp [b32decode, hp, Except.map, fold_decodeStream, stream_eq_digits]

/-- Both benchmark entry points agree, retaining all input-coercion errors. -/
theorem equivalence_thm (enc dec : Input) (cf : Bool) (mp : Option Bytes) :
    benchmark_b32encode enc = benchmark_b32encodeImperative enc ∧
    benchmark_b32decode dec cf mp = benchmark_b32decodeImperative dec cf mp := by
  constructor
  · unfold benchmark_b32encode benchmark_b32encodeImperative
    rw [show b32encode = b32encodeImperative from funext encode_equivalence_thm]
  · cases dec <;>
      simp [benchmark_b32decode, benchmark_b32decodeImperative, objectDecodeResult,
        decode_equivalence_thm]

end Base32
