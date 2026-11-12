import Mathlib

/-!
# Base32 encoding and decoding

This file gives an executable Lean model of the Python Base32 program.  Byte
strings are represented by `List UInt8`; this makes the Python bytes-like
precondition part of the type.  Decoding is totalized with `Except String`,
using the error branch for a non-Base32 digit.
-/

namespace Base32

abbrev Bytes := List UInt8

deriving instance DecidableEq for Except

def ascii (s : String) : Bytes := s.toUTF8.toList

def alphabet : Bytes := ascii "ABCDEFGHIJKLMNOPQRSTUVWXYZ234567"

def pad : UInt8 := UInt8.ofNat 61

def alphabetAt (n : Nat) : UInt8 := alphabet.getD n 0

/-- Encode one (possibly zero-padded) five-byte block. -/
def encodeBlock (a b c d e : UInt8) : Bytes :=
  let a := a.toNat
  let b := b.toNat
  let c := c.toNat
  let d := d.toNat
  let e := e.toNat
  [ alphabetAt (a / 8),
    alphabetAt ((a % 8) * 4 + b / 64),
    alphabetAt ((b / 2) % 32),
    alphabetAt ((b % 2) * 16 + c / 16),
    alphabetAt ((c % 16) * 2 + d / 128),
    alphabetAt ((d / 4) % 32),
    alphabetAt ((d % 4) * 8 + e / 32),
    alphabetAt (e % 32) ]

/-- Functional Base32 encoder, including RFC 4648 `=` padding. -/
def b32encode : Bytes → Bytes
  | [] => []
  | [a] => (encodeBlock a 0 0 0 0).take 2 ++ List.replicate 6 pad
  | [a, b] => (encodeBlock a b 0 0 0).take 4 ++ List.replicate 4 pad
  | [a, b, c] => (encodeBlock a b c 0 0).take 5 ++ List.replicate 3 pad
  | [a, b, c, d] => (encodeBlock a b c d 0).take 7 ++ [pad]
  | a :: b :: c :: d :: e :: rest =>
      encodeBlock a b c d e ++ b32encode rest

def upperAscii (b : UInt8) : UInt8 :=
  if 97 ≤ b.toNat ∧ b.toNat ≤ 122 then UInt8.ofNat (b.toNat - 32) else b

def mapAmbiguous (map01 : Option UInt8) (b : UInt8) : UInt8 :=
  match map01 with
  | none => b
  | some one => if b.toNat = 48 then UInt8.ofNat 79
                else if b.toNat = 49 then one else b

def normalize (s : Bytes) (casefold : Bool) (map01 : Option UInt8) : Bytes :=
  s.map fun b =>
    let b := mapAmbiguous map01 b
    if casefold then upperAscii b else b

def stripPadding (s : Bytes) : Bytes :=
  (s.reverse.dropWhile (· = pad)).reverse

def reverseAlphabet (b : UInt8) : Option Nat :=
  let n := b.toNat
  if 65 ≤ n ∧ n ≤ 90 then some (n - 65)
  else if 50 ≤ n ∧ n ≤ 55 then some (n - 50 + 26)
  else none

def decodeLoop : Bytes → Nat → Nat → Except String Bytes
  | [], _, _ => .ok []
  | char :: rest, val, bits =>
      match reverseAlphabet char with
      | none => .error "Non-base32 digit found"
      | some digit =>
          let val' := val * 32 + digit
          let bits' := bits + 5
          if 8 ≤ bits' then
            match decodeLoop rest val' (bits' - 8) with
            | .error e => .error e
            | .ok tail =>
                .ok (UInt8.ofNat ((val' / (2 ^ (bits' - 8))) % 256) :: tail)
          else
            decodeLoop rest val' bits'

/-- Functional decoder.  The option models Python's `map01` argument. -/
def b32decode (s : Bytes) (casefold : Bool := false)
    (map01 : Option UInt8 := none) : Except String Bytes :=
  decodeLoop (stripPadding (normalize s casefold map01)) 0 0

def benchmark_b32encode (s : Bytes) : Bytes := b32encode s

def benchmark_b32decode (s : Bytes) (casefold : Bool := false)
    (map01 : Option UInt8 := none) : Except String Bytes :=
  b32decode s casefold map01

/-! ## Executable unit tests -/

example : b32encode (ascii "") = ascii "" := by native_decide
example : b32encode (ascii "f") = ascii "MY======" := by native_decide
example : b32encode (ascii "fo") = ascii "MZXQ====" := by native_decide
example : b32encode (ascii "foo") = ascii "MZXW6===" := by native_decide
example : b32encode (ascii "foob") = ascii "MZXW6YQ=" := by native_decide
example : b32encode (ascii "fooba") = ascii "MZXW6YTB" := by native_decide
example : b32encode (ascii "foobar") = ascii "MZXW6YTBOI======" := by native_decide
example : b32decode (b32encode (ascii "VeriBench")) = .ok (ascii "VeriBench") := by
  native_decide
example : b32decode (ascii "mzxw6ytb") true = .ok (ascii "fooba") := by
  native_decide

#eval b32encode (ascii "foobar")
#eval b32decode (b32encode (ascii "VeriBench"))

/-! ## Preconditions and verified properties -/

/-- On the typed Lean interface every value is bytes-like, so the Python
`pre_encode` check is represented by this always-satisfied predicate. -/
def Pre (_s : Bytes) : Prop := True

def encode_length_prop (s : Bytes) : Prop :=
  (b32encode s).length = 8 * ((s.length + 4) / 5)

theorem encode_length_thm (s : Bytes) : encode_length_prop s := by
  induction s using b32encode.induct <;>
    simp_all [encode_length_prop, b32encode, encodeBlock] <;> omega

def rfc4648_vectors_prop : Prop :=
  b32encode (ascii "") = ascii "" ∧
  b32encode (ascii "f") = ascii "MY======" ∧
  b32encode (ascii "fo") = ascii "MZXQ====" ∧
  b32encode (ascii "foo") = ascii "MZXW6===" ∧
  b32encode (ascii "foob") = ascii "MZXW6YQ=" ∧
  b32encode (ascii "fooba") = ascii "MZXW6YTB" ∧
  b32encode (ascii "foobar") = ascii "MZXW6YTBOI======"

theorem rfc4648_vectors_thm : rfc4648_vectors_prop := by
  unfold rfc4648_vectors_prop
  native_decide

def sample_roundtrip_prop : Prop :=
  b32decode (b32encode (ascii "VeriBench")) = .ok (ascii "VeriBench")

theorem sample_roundtrip_thm : sample_roundtrip_prop := by
  unfold sample_roundtrip_prop
  native_decide

def casefold_prop : Prop :=
  b32decode (ascii "mzxw6ytb") true = .ok (ascii "fooba")

theorem casefold_thm : casefold_prop := by
  unfold casefold_prop
  native_decide

def decode_error_prop : Prop :=
  b32decode (ascii "MZXW6!===") = .error "Non-base32 digit found"

theorem decode_error_thm : decode_error_prop := by
  unfold decode_error_prop
  native_decide

def decode_wrapper_prop (s : Bytes) (casefold : Bool) (map01 : Option UInt8) : Prop :=
  benchmark_b32decode s casefold map01 = b32decode s casefold map01

theorem decode_wrapper_thm (s : Bytes) (casefold : Bool) (map01 : Option UInt8) :
    decode_wrapper_prop s casefold map01 := by
  rfl

/-- The postcondition combines wrapper fidelity with the principal structural
fact about padded Base32 output. -/
def Post_prop (s : Bytes) : Prop :=
  benchmark_b32encode s = b32encode s ∧ encode_length_prop s

theorem benchmark_b32encode_correct (s : Bytes) : Pre s → Post_prop s := by
  intro _
  exact ⟨rfl, encode_length_thm s⟩

/-! ## Imperative implementation -/

/-- An `Id`-based encoder which builds the result through mutable state. -/
def b32encodeImperative : Bytes → Bytes
  | [] => Id.run do
      let mut encoded : Bytes := []
      return encoded
  | [a] => Id.run do
      let mut encoded : Bytes := []
      encoded := (encodeBlock a 0 0 0 0).take 2
      encoded := encoded ++ List.replicate 6 pad
      return encoded
  | [a, b] => Id.run do
      let mut encoded : Bytes := []
      encoded := (encodeBlock a b 0 0 0).take 4
      encoded := encoded ++ List.replicate 4 pad
      return encoded
  | [a, b, c] => Id.run do
      let mut encoded : Bytes := []
      encoded := (encodeBlock a b c 0 0).take 5
      encoded := encoded ++ List.replicate 3 pad
      return encoded
  | [a, b, c, d] => Id.run do
      let mut encoded : Bytes := []
      encoded := (encodeBlock a b c d 0).take 7
      encoded := encoded ++ [pad]
      return encoded
  | a :: b :: c :: d :: e :: rest => Id.run do
      let mut encoded : Bytes := encodeBlock a b c d e
      encoded := encoded ++ b32encodeImperative rest
      return encoded

def benchmark_b32encodeImperative (s : Bytes) : Bytes := Id.run do
  let mut result := b32encodeImperative s
  return result

def b32decodeImperative (s : Bytes) (casefold : Bool := false)
    (map01 : Option UInt8 := none) : Except String Bytes := Id.run do
  let mut input := normalize s casefold map01
  input := stripPadding input
  let mut result := decodeLoop input 0 0
  return result

example : b32encodeImperative (ascii "foobar") = ascii "MZXW6YTBOI======" := by
  native_decide
example : b32decodeImperative (ascii "mzxw6ytb") true = .ok (ascii "fooba") := by
  native_decide

#eval b32encodeImperative (ascii "VeriBench")
#eval b32decodeImperative (b32encodeImperative (ascii "VeriBench"))

theorem b32encode_equiv_thm (s : Bytes) :
    b32encode s = b32encodeImperative s := by
  fun_induction b32encode s <;> simp_all [b32encodeImperative]

theorem benchmark_b32encode_equiv_thm (s : Bytes) :
    benchmark_b32encode s = benchmark_b32encodeImperative s := by
  simp [benchmark_b32encode, benchmark_b32encodeImperative, b32encode_equiv_thm]

theorem b32decode_equiv_thm (s : Bytes) (casefold : Bool) (map01 : Option UInt8) :
    b32decode s casefold map01 = b32decodeImperative s casefold map01 := by
  rfl

end Base32
