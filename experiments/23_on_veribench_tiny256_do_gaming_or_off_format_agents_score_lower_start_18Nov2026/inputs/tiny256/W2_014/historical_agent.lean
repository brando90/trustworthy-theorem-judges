import Mathlib
namespace Agent

/-!
# Base32

An exact byte-oriented translation of the supplied Python program. Bytes, bytearrays
and memoryviews are represented by their contents (there is no aliasing here).
The encoder converts memoryviews; the decoder preserves the source's missing-method
exception for memoryviews despite its permissive precondition. Strings are
admitted by the decoder precisely when they are ASCII.
`Except` represents Python's type, Unicode, and non-alphabet exceptions.

The functional codec uses a big-endian bit stream: grouping the bits in fives is
exactly extraction of the eight five-bit fields of a zero-extended 40-bit chunk.
The last alphabet symbols are replaced by `=` by padding the output to a multiple
of eight. The decoder intentionally does NOT validate padding counts or discarded
low bits: like the supplied program, it strips trailing `=` and ignores a final
incomplete byte. `map01` is an arbitrary byte string, not just a single character.
-/
namespace Base32

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
deriving instance DecidableEq for Except

abbrev Byte := Fin 256
abbrev Bytes := List Byte

def byte (n : Nat) : Byte := ⟨n % 256, Nat.mod_lt _ (by decide)⟩
def ascii (s : String) : Bytes := s.toList.map (fun c => byte c.toNat)
def text (s : Bytes) : String := String.mk (s.map (fun b => Char.ofNat b.val))
def pad : Byte := byte 61

def bit (n k : Nat) : Bool := n / 2^k % 2 == 1
def byteBits (b : Byte) : List Bool :=
  [bit b.val 7, bit b.val 6, bit b.val 5, bit b.val 4,
   bit b.val 3, bit b.val 2, bit b.val 1, bit b.val 0]
def pack8 (a b c d e f g h : Bool) : Byte :=
  byte (128*a.toNat + 64*b.toNat + 32*c.toNat + 16*d.toNat +
        8*e.toNat + 4*f.toNat + 2*g.toNat + h.toNat)
def digit (a b c d e : Bool) : Byte :=
  let n := 16*a.toNat + 8*b.toNat + 4*c.toNat + 2*d.toNat + e.toNat
  byte (if n < 26 then 65+n else 24+n)
def unDigit (b : Byte) : Option (List Bool) :=
  let n := b.val
  let v := if 65 ≤ n ∧ n ≤ 90 then some (n-65)
           else if 50 ≤ n ∧ n ≤ 55 then some (n-24) else none
  v.map (fun k => [bit k 4, bit k 3, bit k 2, bit k 1, bit k 0])

def emit5 : List Bool → Bytes
  | [] => []
  | [a] => [digit a false false false false]
  | [a,b] => [digit a b false false false]
  | [a,b,c] => [digit a b c false false]
  | [a,b,c,d] => [digit a b c d false]
  | a::b::c::d::e::xs => digit a b c d e :: emit5 xs

def read8 : List Bool → Bytes
  | a::b::c::d::e::f::g::h::xs => pack8 a b c d e f g h :: read8 xs
  | _ => []

def parseDigits : Bytes → Option (List Bool)
  | [] => some []
  | b::bs => do
    let bits ← unDigit b
    let rest ← parseDigits bs
    return bits ++ rest

/-- Right stripping, not removal of internal padding. -/
def stripPad : Bytes → Bytes
  | [] => []
  | b::bs => let rest := stripPad bs
             if b = pad ∧ rest = [] then [] else b::rest

def upper (b : Byte) : Byte :=
  if 97 ≤ b.val ∧ b.val ≤ 122 then byte (b.val-32) else b

def lower (b : Byte) : Byte :=
  if 65 ≤ b.val ∧ b.val ≤ 90 then byte (b.val+32) else b

def replace01 (s : Bytes) (map01 : Option Bytes) : Bytes :=
  match map01 with
  | none => s
  | some [] => s
  | some replacement => s.flatMap (fun b =>
      if b = byte 48 then [byte 79]
      else if b = byte 49 then replacement else [b])

def preprocess (s : Bytes) (casefold : Bool) (map01 : Option Bytes) : Bytes :=
  let s := replace01 s map01
  if casefold then s.map upper else s

def b32encode (s : Bytes) : Bytes :=
  let out := emit5 (s.flatMap byteBits)
  out ++ List.replicate ((8 - out.length % 8) % 8) pad

def b32decode (s : Bytes) (casefold : Bool := false)
    (map01 : Option Bytes := none) : Except String Bytes :=
  match parseDigits (stripPad (preprocess s casefold map01)) with
  | none => .error "Non-base32 digit found"
  | some bits => .ok (read8 bits)

inductive Input where
  | bytes : Bytes → Input
  | bytearray : Bytes → Input
  | memoryview : Bytes → Input
  | string : String → Input
  | other : Input
  deriving Repr, DecidableEq

def pre_encode : Input → Bool
  | .bytes _ | .bytearray _ | .memoryview _ => true
  | _ => false

def pre_decode : Input → Bool
  | .string s => s.toList.all (fun c => c.toNat < 128)
  | s => pre_encode s

def asBytes : Input → Except String Bytes
  | .bytes s | .bytearray s | .memoryview s => .ok s
  | _ => .error "expected bytes-like object"

def decodeInput : Input → Except String Bytes
  | .string s => if s.toList.all (fun c => c.toNat < 128) then .ok (ascii s)
                 else .error "non-ASCII string"
  | s => asBytes s

def benchmark_b32encode (s : Input) : Except String Bytes := do
  return b32encode (← asBytes s)

def benchmark_b32decode (s : Input) (casefold : Bool := false)
    (map01 : Option Bytes := none) : Except String Bytes :=
  match s with
  | .memoryview _ =>
      if (map01.getD []).isEmpty = false then
        .error "memoryview has no attribute 'replace'"
      else if casefold then .error "memoryview has no attribute 'upper'"
      else .error "memoryview has no attribute 'rstrip'"
  | _ => do b32decode (← decodeInput s) casefold map01

-- The source decoder does not convert memoryviews before calling bytes methods.
example : pre_decode (.memoryview (ascii "MY======")) = true := by native_decide
example : benchmark_b32decode (.memoryview (ascii "MY======")) =
    .error "memoryview has no attribute 'rstrip'" := by native_decide
example : benchmark_b32encode (.memoryview (ascii "f")) = .ok (ascii "MY======") := by native_decide
-- Fixed tests, including every public Python test.
example : b32encode [] = [] := by native_decide
example : b32encode (ascii "f") = ascii "MY======" := by native_decide
example : b32encode (ascii "fo") = ascii "MZXQ====" := by native_decide
example : b32encode (ascii "foo") = ascii "MZXW6===" := by native_decide
example : b32encode (ascii "foob") = ascii "MZXW6YQ=" := by native_decide
example : b32encode (ascii "fooba") = ascii "MZXW6YTB" := by native_decide
example : b32encode (ascii "foobar") = ascii "MZXW6YTBOI======" := by native_decide
example : b32decode (b32encode (ascii "VeriBench")) = .ok (ascii "VeriBench") := by native_decide
example : b32decode (ascii "mzxw6ytb") true = .ok (ascii "fooba") := by native_decide
example : b32decode (ascii "M=Y") = .error "Non-base32 digit found" := by native_decide
example : b32decode (ascii "MZ") = .ok (ascii "f") := by native_decide
example : b32decode (ascii "A======") = .ok [] := by native_decide
example : b32decode (ascii "01======") false (some (ascii "I")) = .ok (ascii "r") := by native_decide
example : b32decode (ascii "1") false (some (ascii "MY")) = .ok (ascii "f") := by native_decide
example : benchmark_b32decode (.string "MY======") = .ok (ascii "f") := by native_decide
example : benchmark_b32decode (.string "é") = .error "non-ASCII string" := by native_decide
example : benchmark_b32encode (.string "f") = .error "expected bytes-like object" := by native_decide
#eval text (b32encode (ascii "VeriBench"))
#eval b32decode (ascii "mzxw6ytb") true

/-- The encoder's exact dynamic precondition. Byte values are intrinsically bounded. -/
def Pre (s : Input) : Prop := pre_encode s = true

-- Finite truth tables here are checked by the kernel, not by native_decide.
theorem unDigit_digit : ∀ a b c d e : Bool,
    unDigit (digit a b c d e) = some [a,b,c,d,e] := by decide

theorem digit_ne_pad : ∀ a b c d e : Bool,
    digit a b c d e ≠ pad := by decide

def alphabetByte (b : Byte) : Prop :=
  (65 ≤ b.val ∧ b.val ≤ 90) ∨ (50 ≤ b.val ∧ b.val ≤ 55)
instance (b : Byte) : Decidable (alphabetByte b) := inferInstanceAs (Decidable (_ ∨ _))

theorem digit_alphabet : ∀ a b c d e : Bool,
    alphabetByte (digit a b c d e) := by decide

theorem pack8_bits : ∀ b : Byte,
    pack8 (bit b.val 7) (bit b.val 6) (bit b.val 5) (bit b.val 4)
      (bit b.val 3) (bit b.val 2) (bit b.val 1) (bit b.val 0) = b := by decide

theorem bits_length (s : Bytes) : (s.flatMap byteBits).length = 8 * s.length := by
  induction s with
  | nil => rfl
  | cons b bs ih => simp [List.flatMap_cons, byteBits, ih, Nat.mul_add]

theorem read8_one (b : Byte) (rest : List Bool) :
    read8 (byteBits b ++ rest) = b :: read8 rest := by
  change pack8 _ _ _ _ _ _ _ _ :: read8 rest = b :: read8 rest
  rw [pack8_bits]

theorem read8_bytes (s : Bytes) (rest : List Bool) :
    read8 (s.flatMap byteBits ++ rest) = s ++ read8 rest := by
  induction s with
  | nil => rfl
  | cons b bs ih => simp only [List.flatMap_cons, List.append_assoc, read8_one,
                              ih, List.cons_append]

theorem read8_short (xs : List Bool) (h : xs.length < 8) : read8 xs = [] := by
  fun_cases read8 xs <;> simp_all
  omega

theorem emit5_length (xs : List Bool) : (emit5 xs).length = (xs.length + 4) / 5 := by
  induction xs using emit5.induct <;> simp_all [emit5]
  omega

theorem emit5_alphabet (xs : List Bool) : ∀ b ∈ emit5 xs, alphabetByte b := by
  induction xs using emit5.induct <;> simp_all [emit5, digit_alphabet]

theorem emit5_no_pad (xs : List Bool) : ∀ b ∈ emit5 xs, b ≠ pad := by
  induction xs using emit5.induct <;> simp_all [emit5, digit_ne_pad]

/-- Encoding a bitstream only adds at most four zero bits. -/
theorem parse_emit5 (xs : List Bool) :
    ∃ tail : List Bool, tail.length < 5 ∧
      parseDigits (emit5 xs) = some (xs ++ tail) := by
  induction xs using emit5.induct with
  | case1 => exact ⟨[], by decide, rfl⟩
  | case2 a => exact ⟨[false,false,false,false], by decide, by simp [emit5, parseDigits, unDigit_digit]⟩
  | case3 a b => exact ⟨[false,false,false], by decide, by simp [emit5, parseDigits, unDigit_digit]⟩
  | case4 a b c => exact ⟨[false,false], by decide, by simp [emit5, parseDigits, unDigit_digit]⟩
  | case5 a b c d => exact ⟨[false], by decide, by simp [emit5, parseDigits, unDigit_digit]⟩
  | case6 a b c d e xs ih =>
      obtain ⟨tail, ht, hp⟩ := ih
      exact ⟨tail, ht, by simp [emit5, parseDigits, unDigit_digit, hp]⟩

theorem stripPad_replicate (n : Nat) : stripPad (List.replicate n pad) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, stripPad, ih]

theorem stripPad_append (s : Bytes) (n : Nat) :
    stripPad (s ++ List.replicate n pad) = stripPad s := by
  induction s with
  | nil => exact stripPad_replicate n
  | cons b bs ih => simp only [List.cons_append, stripPad, ih]

theorem stripPad_clean (s : Bytes) (h : ∀ b ∈ s, b ≠ pad) : stripPad s = s := by
  induction s with
  | nil => rfl
  | cons b bs ih =>
      have hb : b ≠ pad := h b (by simp)
      have ht : ∀ x ∈ bs, x ≠ pad := fun x hx => h x (by simp [hx])
      simp [stripPad, hb, ih ht]

theorem stripPad_encoded (s : Bytes) :
    stripPad (b32encode s) = emit5 (s.flatMap byteBits) := by
  rw [b32encode, stripPad_append, stripPad_clean _ (emit5_no_pad _)]

def roundtrip_prop (s : Bytes) : Prop := b32decode (b32encode s) = .ok s

theorem roundtrip_thm (s : Bytes) : roundtrip_prop s := by
  obtain ⟨tail, ht, hp⟩ := parse_emit5 (s.flatMap byteBits)
  have hr : read8 tail = [] := read8_short tail (by omega)
  simp [roundtrip_prop, b32decode, preprocess, replace01, stripPad_encoded, hp,
        read8_bytes, hr]

def length_prop (s : Bytes) : Prop :=
  (b32encode s).length = 8 * ((s.length + 4) / 5)

theorem length_thm (s : Bytes) : length_prop s := by
  unfold length_prop b32encode
  simp only [List.length_append, List.length_replicate, emit5_length, bits_length]
  omega

def alphabet_prop (s : Bytes) : Prop :=
  ∀ b ∈ b32encode s, alphabetByte b ∨ b = pad

theorem alphabet_thm (s : Bytes) : alphabet_prop s := by
  intro b hb
  simp only [b32encode, List.mem_append, List.mem_replicate] at hb
  rcases hb with hb | ⟨_, hb⟩
  · exact Or.inl (emit5_alphabet _ b hb)
  · exact Or.inr hb

def paddingCount (r : Nat) : Nat :=
  if r = 1 then 6 else if r = 2 then 4 else if r = 3 then 3 else if r = 4 then 1 else 0

def padding_prop (s : Bytes) : Prop :=
  b32encode s = emit5 (s.flatMap byteBits) ++ List.replicate (paddingCount (s.length % 5)) pad

theorem padding_thm (s : Bytes) : padding_prop s := by
  unfold padding_prop b32encode
  dsimp only
  congr 2
  rw [emit5_length, bits_length]
  unfold paddingCount
  split_ifs <;> omega

/-- All trailing padding is ignored, including nonstandard padding counts. -/
def trailing_padding_prop (s : Bytes) (n : Nat) : Prop :=
  b32decode (s ++ List.replicate n pad) = b32decode s

theorem trailing_padding_thm (s : Bytes) (n : Nat) : trailing_padding_prop s n := by
  simp [trailing_padding_prop, b32decode, preprocess, replace01, stripPad_append]

theorem unDigit_none_iff : ∀ b : Byte, unDigit b = none ↔ ¬ alphabetByte b := by decide

theorem parseDigits_none_iff (s : Bytes) :
    parseDigits s = none ↔ ∃ b ∈ s, ¬ alphabetByte b := by
  induction s with
  | nil => simp [parseDigits]
  | cons b bs ih =>
      simp only [List.mem_cons, or_and_right, exists_or, exists_eq_left]
      rw [← unDigit_none_iff, ← ih]
      cases hd : unDigit b <;> cases ht : parseDigits bs <;> simp [parseDigits, hd, ht]

def decode_error_prop (s : Bytes) (cf : Bool) (m : Option Bytes) : Prop :=
  b32decode s cf m = .error "Non-base32 digit found" ↔
    ∃ b ∈ stripPad (preprocess s cf m), ¬ alphabetByte b

theorem decode_error_thm (s : Bytes) (cf : Bool) (m : Option Bytes) :
    decode_error_prop s cf m := by
  unfold decode_error_prop b32decode
  rw [← parseDigits_none_iff]
  cases parseDigits (stripPad (preprocess s cf m)) <;> simp

theorem unDigit_length (b : Byte) (bits : List Bool) (h : unDigit b = some bits) :
    bits.length = 5 := by
  unfold unDigit at h
  dsimp only at h
  split at h
  · simp only [Option.map_some, Option.some.injEq] at h
    subst bits
    rfl
  · split at h
    · simp only [Option.map_some, Option.some.injEq] at h
      subst bits
      rfl
    · simp at h

theorem parseDigits_length (s : Bytes) (bits : List Bool)
    (h : parseDigits s = some bits) : bits.length = 5 * s.length := by
  induction s generalizing bits with
  | nil => simp [parseDigits] at h; subst bits; rfl
  | cons b bs ih =>
      cases hd : unDigit b with
      | none => simp [parseDigits, hd] at h
      | some part =>
          cases ht : parseDigits bs with
          | none => simp [parseDigits, hd, ht] at h
          | some rest =>
              simp [parseDigits, hd, ht] at h
              subst bits
              simp [unDigit_length b part hd, ih rest ht, Nat.mul_add, Nat.add_comm]

theorem read8_length (bits : List Bool) : (read8 bits).length = bits.length / 8 := by
  match bits with
  | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | [_,_,_,_,_] |
    [_,_,_,_,_,_] | [_,_,_,_,_,_,_] => simp [read8]
  | a::b::c::d::e::f::g::h::rest =>
      simp only [read8, List.length_cons, read8_length rest]
      omega
termination_by bits.length

/-- A valid unpadded prefix of length n produces exactly floor(5*n/8) bytes. -/
def decode_length_prop (s : Bytes) (cf : Bool) (m : Option Bytes) : Prop :=
  ∀ out, b32decode s cf m = .ok out →
    out.length = 5 * (stripPad (preprocess s cf m)).length / 8

theorem decode_length_thm (s : Bytes) (cf : Bool) (m : Option Bytes) :
    decode_length_prop s cf m := by
  intro out h
  unfold b32decode at h
  cases hp : parseDigits (stripPad (preprocess s cf m)) with
  | none => simp [hp] at h
  | some bits =>
      simp [hp] at h
      subst out
      rw [read8_length, parseDigits_length _ _ hp]

theorem upper_lower_alphabet : ∀ b : Byte,
    alphabetByte b ∨ b = pad → upper (lower b) = b := by decide

def casefold_prop (s : Bytes) : Prop :=
  b32decode ((b32encode s).map lower) true = .ok s

theorem casefold_thm (s : Bytes) : casefold_prop s := by
  have h : ((b32encode s).map lower).map upper = b32encode s := by
    rw [List.map_map]
    calc
      _ = (b32encode s).map id := by
        apply List.map_congr_left
        intro b hb
        exact upper_lower_alphabet b (alphabet_thm s b hb)
      _ = _ := List.map_id _
  unfold casefold_prop b32decode preprocess
  simp only [replace01, ↓reduceIte, h]
  exact roundtrip_thm s

/-- A literal one-byte replacement, used to specify Python's two `.replace` calls. -/
def replaceByte (s : Bytes) (old : Byte) (replacement : Bytes) : Bytes :=
  s.flatMap (fun b => if b = old then replacement else [b])

def mappedInput (s : Bytes) (m : Option Bytes) : Bytes :=
  match m with
  | none => s
  | some r => if r = [] then s else replaceByte (replaceByte s (byte 48) [byte 79]) (byte 49) r

theorem replace01_two_pass (s : Bytes) (r : Bytes) :
    replace01 s (some r) =
      if r = [] then s else replaceByte (replaceByte s (byte 48) [byte 79]) (byte 49) r := by
  cases r with
  | nil => rfl
  | cons x xs =>
      simp only [List.cons_ne_nil, ↓reduceIte]
      have h01 : byte 48 ≠ byte 49 := by decide
      have hO1 : byte 79 ≠ byte 49 := by decide
      induction s with
      | nil => rfl
      | cons b bs ih =>
          by_cases h0 : b = byte 48
          · simp_all [replace01, replaceByte]
          · by_cases h1 : b = byte 49 <;>
              simp_all [replace01, replaceByte]

theorem replace01_mapped (s : Bytes) (m : Option Bytes) : replace01 s m = mappedInput s m := by
  cases m with
  | none => rfl
  | some r => exact replace01_two_pass s r

/-- Replacements are performed before case folding; newly inserted zeroes are NOT
replaced again. Empty replacements are false in Python, so disable both mappings. -/
def map01_prop (s : Bytes) (cf : Bool) (m : Option Bytes) : Prop :=
  b32decode s cf m = b32decode (mappedInput s m) cf none

theorem map01_thm (s : Bytes) (cf : Bool) (m : Option Bytes) : map01_prop s cf m := by
  unfold map01_prop b32decode preprocess
  rw [replace01_mapped s m]
  rfl

/-- Contents used in the encoder contract. The error branch cannot occur under Pre. -/
def contents (s : Input) : Bytes := (asBytes s).toOption.getD []

/-- Encoding and decoding contracts, including the exact dynamic encoder interface. -/
def Post_prop (s : Input) (cf : Bool) (m : Option Bytes) (n : Nat) : Prop :=
  let bs := contents s
  asBytes s = .ok bs ∧
  benchmark_b32encode s = .ok (b32encode bs) ∧
  benchmark_b32decode (.bytes (b32encode bs)) = .ok bs ∧
  roundtrip_prop bs ∧ length_prop bs ∧ alphabet_prop bs ∧ padding_prop bs ∧
  casefold_prop bs ∧ trailing_padding_prop bs n ∧
  decode_error_prop bs cf m ∧ decode_length_prop bs cf m ∧ map01_prop bs cf m

/-! ## Bounded property-based tests

These are executable checks, not premises of any theorem. `samples` includes
all single bytes and 1,024 deterministic multi-byte inputs of lengths 0..15,
plus long all-zero/all-one inputs. `decodeSamples` includes malformed inputs,
internal padding, every possible byte value, canonical encodings and lowercase.
Every `_prop` above has an explicit Boolean test below, including `Post_prop`.
-/
def samples : List Bytes :=
  [[]] ++ (List.range 256).map (fun n => [byte n]) ++
  (List.range 64).flatMap (fun seed => (List.range 16).map (fun len =>
    (List.range len).map (fun i => byte (37*seed + 53*i)))) ++
  (List.range 30).flatMap (fun n => [List.replicate n (byte 0), List.replicate n (byte 255)])

def decodeSamples : List Bytes :=
  (List.range 256).flatMap (fun n => [[byte n], [byte 65, byte n, pad], [pad, byte n]]) ++
  (samples.take 320).flatMap (fun s => [b32encode s, (b32encode s).map lower]) ++
  [ascii "", ascii "=====", ascii "MY", ascii "MZ", ascii "M=Y", ascii "01======",
   ascii "mzxw6ytb", ascii "MZXW6YTBOI======"]

def replacements : List (Option Bytes) :=
  [none, some [], some (ascii "I"), some (ascii "L"), some (ascii "i"),
   some (ascii "MY"), some [byte 0], some (ascii "0")]

def roundtripCheck (s : Bytes) : Bool := decide (b32decode (b32encode s) = .ok s)
def lengthCheck (s : Bytes) : Bool := decide ((b32encode s).length = 8*((s.length+4)/5))
def alphabetCheck (s : Bytes) : Bool :=
  (b32encode s).all (fun b => decide (alphabetByte b ∨ b = pad))
def paddingCheck (s : Bytes) : Bool :=
  decide (b32encode s = emit5 (s.flatMap byteBits) ++ List.replicate (paddingCount (s.length%5)) pad)
def casefoldCheck (s : Bytes) : Bool :=
  decide (b32decode ((b32encode s).map lower) true = .ok s)
def trailingCheck (s : Bytes) (n : Nat) : Bool :=
  decide (b32decode (s ++ List.replicate n pad) = b32decode s)
def errorCheck (s : Bytes) (cf : Bool) (m : Option Bytes) : Bool :=
  decide (b32decode s cf m = .error "Non-base32 digit found") ==
    (stripPad (preprocess s cf m)).any (fun b => !decide (alphabetByte b))
def decodeLengthCheck (s : Bytes) (cf : Bool) (m : Option Bytes) : Bool :=
  match b32decode s cf m with
  | .error _ => true
  | .ok out => decide (out.length = 5*(stripPad (preprocess s cf m)).length/8)

def map01Check (s : Bytes) (cf : Bool) (m : Option Bytes) : Bool :=
  decide (b32decode s cf m = b32decode (mappedInput s m) cf none)

def postCheck (s : Input) (cf : Bool) (m : Option Bytes) (n : Nat) : Bool :=
  let bs := contents s
  decide (asBytes s = .ok bs) &&
  decide (benchmark_b32encode s = .ok (b32encode bs)) &&
  decide (benchmark_b32decode (.bytes (b32encode bs)) = .ok bs) &&
  roundtripCheck bs && lengthCheck bs && alphabetCheck bs && paddingCheck bs &&
  casefoldCheck bs && trailingCheck bs n && errorCheck bs cf m && decodeLengthCheck bs cf m &&
  map01Check bs cf m

-- PBT: roundtrip_prop
example : samples.all roundtripCheck = true := by native_decide
-- PBT: length_prop
example : samples.all lengthCheck = true := by native_decide
-- PBT: alphabet_prop
example : samples.all alphabetCheck = true := by native_decide
-- PBT: padding_prop
example : samples.all paddingCheck = true := by native_decide
-- PBT: casefold_prop
example : samples.all casefoldCheck = true := by native_decide
-- PBT: trailing_padding_prop (all counts 0..11, even for invalid inputs).
example : decodeSamples.all (fun s => (List.range 12).all (trailingCheck s)) = true := by native_decide
-- PBT: decode_error_prop (both casefold settings and eight map01 choices).
example : decodeSamples.all (fun s => [false,true].all (fun cf =>
    replacements.all (errorCheck s cf))) = true := by native_decide
-- PBT: decode_length_prop
example : decodeSamples.all (fun s => [false,true].all (fun cf =>
    replacements.all (decodeLengthCheck s cf))) = true := by native_decide
-- PBT: map01_prop, including replacements that contain zeroes or lowercase letters.
example : decodeSamples.all (fun s => [false,true].all (fun cf =>
    replacements.all (map01Check s cf))) = true := by native_decide
-- PBT: Post_prop, on all three dynamically admissible encoder input variants.
example : samples.all (fun bs => [Input.bytes bs, .bytearray bs, .memoryview bs].all (fun s =>
    [false,true].all (fun cf => replacements.all (fun m =>
      postCheck s cf m (bs.length % 12))))) = true := by native_decide
#eval (samples.length, decodeSamples.length, samples.all roundtripCheck)

theorem pre_contents (s : Input) (h : Pre s) : asBytes s = .ok (contents s) := by
  cases s <;> simp_all [Pre, pre_encode, asBytes, contents, Except.toOption]

/-- All properties hold on the entire encoder precondition, with arbitrary decoder
options and arbitrary added padding counts. -/
theorem correctness (s : Input) (cf : Bool) (m : Option Bytes) (n : Nat) :
    Pre s → Post_prop s cf m n := by
  intro h
  have hs := pre_contents s h
  refine ⟨hs, ?_, ?_, roundtrip_thm _, length_thm _, alphabet_thm _, padding_thm _,
    casefold_thm _, trailing_padding_thm _ _, decode_error_thm _ _ _, decode_length_thm _ _ _,
    map01_thm _ _ _⟩
  · simp [benchmark_b32encode, hs]
  · change b32decode (b32encode (contents s)) = .ok (contents s)
    exact roundtrip_thm _

/-! ## Imperative implementation

The loops below use mutable buffers. In particular the parser is a left-to-right
state machine with an absorbing error state, whereas `parseDigits` above is a
recursive right-associated traversal. The accumulator lemmas prove these different
traversals equivalent for all inputs, including malformed inputs.
-/
def emit5Acc (xs : List Bool) (initial : Bytes) : Bytes := Id.run do
  let mut out := initial
  match xs with
  | [] => pure ()
  | [a] => out := out ++ [digit a false false false false]
  | [a,b] => out := out ++ [digit a b false false false]
  | [a,b,c] => out := out ++ [digit a b c false false]
  | [a,b,c,d] => out := out ++ [digit a b c d false]
  | a::b::c::d::e::rest =>
      out := out ++ [digit a b c d e]
      out := emit5Acc rest out
  return out
termination_by xs.length

def read8Acc (xs : List Bool) (initial : Bytes) : Bytes := Id.run do
  let mut out := initial
  match xs with
  | a::b::c::d::e::f::g::h::rest =>
      out := out ++ [pack8 a b c d e f g h]
      out := read8Acc rest out
  | _ => pure ()
  return out
termination_by xs.length

def parseStep (acc : Option (List Bool)) (b : Byte) : Option (List Bool) := do
  let before ← acc
  let more ← unDigit b
  return before ++ more

def parseDigitsImperative (s : Bytes) : Option (List Bool) := Id.run do
  let mut acc : Option (List Bool) := some []
  for b in s do
    acc := parseStep acc b
  return acc

def b32encodeImperative (s : Bytes) : Bytes := Id.run do
  let mut bits : List Bool := []
  for b in s do
    bits := bits ++ byteBits b
  let mut out := emit5Acc bits []
  let count := (8 - out.length % 8) % 8
  for _ in List.range count do
    out := out ++ [pad]
  return out

def b32decodeImperative (s : Bytes) (casefold : Bool := false)
    (map01 : Option Bytes := none) : Except String Bytes := Id.run do
  let mut input := replace01 s map01
  if casefold then
    input := input.map upper
  input := stripPad input
  let mut result : Except String Bytes := .error "Non-base32 digit found"
  match parseDigitsImperative input with
  | none => pure ()
  | some bits => result := .ok (read8Acc bits [])
  return result

def benchmark_b32encodeImperative (s : Input) : Except String Bytes := Id.run do
  let mut result := asBytes s
  match result with
  | .error _ => pure ()
  | .ok bs => result := .ok (b32encodeImperative bs)
  return result

def benchmark_b32decodeImperative (s : Input) (casefold : Bool := false)
    (map01 : Option Bytes := none) : Except String Bytes := Id.run do
  match s with
  | .memoryview _ =>
      if (map01.getD []).isEmpty = false then
        return .error "memoryview has no attribute 'replace'"
      else if casefold then return .error "memoryview has no attribute 'upper'"
      else return .error "memoryview has no attribute 'rstrip'"
  | _ =>
      let mut result := decodeInput s
      match result with
      | .error _ => pure ()
      | .ok bs => result := b32decodeImperative bs casefold map01
      return result

-- Imperative fixed examples and bounded cross-checks.
example : b32encodeImperative (ascii "foobar") = ascii "MZXW6YTBOI======" := by native_decide
example : b32decodeImperative (ascii "mzxw6ytb") true = .ok (ascii "fooba") := by native_decide
example : b32decodeImperative (ascii "M=Y") = .error "Non-base32 digit found" := by native_decide
example : benchmark_b32decodeImperative (.string "MY======") = .ok (ascii "f") := by native_decide
#eval text (b32encodeImperative (ascii "VeriBench"))

example : samples.all (fun s => decide (b32encode s = b32encodeImperative s)) = true := by native_decide
example : decodeSamples.all (fun s => [false,true].all (fun cf => replacements.all (fun m =>
    decide (b32decode s cf m = b32decodeImperative s cf m)))) = true := by native_decide

-- Generalized loop invariants (arbitrary initial accumulators).
theorem emit5Acc_invariant (xs : List Bool) (out : Bytes) :
    emit5Acc xs out = out ++ emit5 xs := by
  induction xs using emit5.induct generalizing out with
  | case1 => rw [emit5Acc]; simp [emit5]
  | case2 a => rw [emit5Acc]; simp [emit5]
  | case3 a b => rw [emit5Acc]; simp [emit5]
  | case4 a b c => rw [emit5Acc]; simp [emit5]
  | case5 a b c d => rw [emit5Acc]; simp [emit5]
  | case6 a b c d e xs ih =>
      rw [emit5Acc]
      change emit5Acc xs (out ++ [digit a b c d e]) = out ++ digit a b c d e :: emit5 xs
      rw [ih]
      simp

theorem read8Acc_invariant (xs : List Bool) (out : Bytes) :
    read8Acc xs out = out ++ read8 xs := by
  match xs with
  | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | [_,_,_,_,_] |
    [_,_,_,_,_,_] | [_,_,_,_,_,_,_] => rw [read8Acc]; simp [read8]
  | a::b::c::d::e::f::g::h::rest =>
      rw [read8Acc]
      change read8Acc rest (out ++ [pack8 a b c d e f g h]) =
        out ++ pack8 a b c d e f g h :: read8 rest
      rw [read8Acc_invariant]
      simp
termination_by xs.length

theorem bitBuffer_invariant (s : Bytes) (bits : List Bool) :
    s.foldl (fun acc b => acc ++ byteBits b) bits = bits ++ s.flatMap byteBits := by
  induction s generalizing bits with
  | nil => simp
  | cons b bs ih => simp [List.foldl_cons, ih, List.append_assoc]

theorem paddingBuffer_invariant (ns : List Nat) (out : Bytes) :
    ns.foldl (fun acc _ => acc ++ [pad]) out = out ++ List.replicate ns.length pad := by
  induction ns generalizing out with
  | nil => simp
  | cons n ns ih => simp [List.foldl_cons, ih, List.replicate_succ, List.append_assoc]

theorem parseBuffer_invariant (s : Bytes) (acc : Option (List Bool)) :
    s.foldl parseStep acc = (do
      let initBits ← acc
      let rest ← parseDigits s
      return initBits ++ rest) := by
  induction s generalizing acc with
  | nil => cases acc <;> simp [parseDigits]
  | cons b bs ih =>
      rw [List.foldl_cons, ih]
      cases acc <;> cases hd : unDigit b <;> cases ht : parseDigits bs <;>
        simp [parseStep, parseDigits, hd, ht, List.append_assoc]

theorem parseDigits_equivalence (s : Bytes) : parseDigits s = parseDigitsImperative s := by
  simp [parseDigitsImperative, parseBuffer_invariant]

theorem encode_equivalence (s : Bytes) : b32encode s = b32encodeImperative s := by
  simp [b32encodeImperative, emit5Acc_invariant, b32encode, List.flatMap_def]

theorem decode_equivalence (s : Bytes) (cf : Bool) (m : Option Bytes) :
    b32decode s cf m = b32decodeImperative s cf m := by
  cases cf <;>
    simp [b32decodeImperative, b32decode, preprocess, ← parseDigits_equivalence,
      read8Acc_invariant] <;> rfl

theorem benchmark_encode_equivalence (s : Input) :
    benchmark_b32encode s = benchmark_b32encodeImperative s := by
  cases hs : asBytes s <;>
    simp [benchmark_b32encode, benchmark_b32encodeImperative, hs, ← encode_equivalence]

theorem benchmark_decode_equivalence (s : Input) (cf : Bool) (m : Option Bytes) :
    benchmark_b32decode s cf m = benchmark_b32decodeImperative s cf m := by
  cases s <;> simp [benchmark_b32decode, benchmark_b32decodeImperative,
    decodeInput, asBytes, ← decode_equivalence] <;> try rfl
  split <;> rfl

/-- Equivalence includes errors, dynamic input variants, and all decoder options. -/
theorem equivalence (s : Input) (cf : Bool) (m : Option Bytes) :
    benchmark_b32encode s = benchmark_b32encodeImperative s ∧
    benchmark_b32decode s cf m = benchmark_b32decodeImperative s cf m :=
  ⟨benchmark_encode_equivalence s, benchmark_decode_equivalence s cf m⟩

end Base32
end Agent
