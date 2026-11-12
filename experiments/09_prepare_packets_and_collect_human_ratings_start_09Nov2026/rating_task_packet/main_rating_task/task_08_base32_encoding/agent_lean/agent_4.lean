import Mathlib

/-!
# Base32 encoding and decoding

Lean 4 formalization of the Python Base32 codec in the task statement
(sourced from Python's standard `base64` library).

Bytes are represented as `List Nat` of integer code points. Encoding returns
the ASCII codes of the Base32 text (including `=` padding). Decoding returns
`Option`: `none` models `binascii.Error` on a non-Base32 digit, and `some`
is a successful decode. Strings are handled by first taking ASCII code points,
matching `str.encode('ascii')`.
-/

namespace «23_base32»

/-- Base32 alphabet `ABCDEFGHIJKLMNOPQRSTUVWXYZ234567`. -/
def b32alphabet : List Nat :=
  [ 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77
  , 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90
  , 50, 51, 52, 53, 54, 55 ]

/-- Padding character `=`. -/
def padChar : Nat := 61

/-- Character `0`. -/
def char0 : Nat := 48

/-- Character `1`. -/
def char1 : Nat := 49

/-- Character `O`. -/
def charO : Nat := 79

/-- Character `I`, the usual `map01` target. -/
def charI : Nat := 73

theorem b32alphabet_length : b32alphabet.length = 32 := rfl

/-- Alphabet symbol at index `i` (0 outside the alphabet). -/
def alphabetAt (i : Nat) : Nat :=
  b32alphabet.getD i 0

/-- Lookup a code point in the Base32 alphabet. -/
def listIndex : List Nat → Nat → Nat → Option Nat
  | [], _, _ => none
  | x :: xs, c, i => if x = c then some i else listIndex xs c (i + 1)

def indexInAlphabet (c : Nat) : Option Nat :=
  listIndex b32alphabet c 0

/-- ASCII `bytes.upper` / `str.upper` on a single code point. -/
def toUpperAscii (c : Nat) : Nat :=
  if 97 ≤ c ∧ c ≤ 122 then c - 32 else c

/-- ASCII `bytes.lower` on a single code point. -/
def toLowerAscii (c : Nat) : Nat :=
  if 65 ≤ c ∧ c ≤ 90 then c + 32 else c

/-- Pack bytes, most-significant byte first, as `int.from_bytes(..., 'big')`. -/
def packBytes (bs : List Nat) : Nat :=
  bs.foldl (fun acc b => acc * 256 + b) 0

/-- Number of significant Base32 characters produced by a chunk of length `n`. -/
def sigCount : Nat → Nat
  | 1 => 2
  | 2 => 4
  | 3 => 5
  | 4 => 7
  | _ => 8

/-- Number of `=` padding characters for a chunk of length `n` (`n = 0` or `5` means none). -/
def padCount : Nat → Nat
  | 1 => 6
  | 2 => 4
  | 3 => 3
  | 4 => 1
  | _ => 0

/-- Encode one chunk of at most 5 bytes, including `=` padding. -/
def encodeChunk (chunk : List Nat) : List Nat :=
  let n := chunk.length
  let padded := chunk ++ List.replicate (5 - n) 0
  let val := packBytes padded
  let chars := (List.range 8).map fun i =>
    alphabetAt ((val >>> (35 - 5 * i)) &&& 31)
  chars.take (sigCount n) ++ List.replicate (padCount n) padChar

/-- Split into successive 5-byte groups (structural, so it reduces in the kernel). -/
def chunksOf5 : List Nat → List (List Nat)
  | [] => []
  | [a] => [[a]]
  | [a, b] => [[a, b]]
  | [a, b, c] => [[a, b, c]]
  | [a, b, c, d] => [[a, b, c, d]]
  | a :: b :: c :: d :: e :: rest => [a, b, c, d, e] :: chunksOf5 rest

/--
Encode a bytes-like object using Base32.

Mirrors `b32encode`: 5-byte groups are packed big-endian into a 40-bit integer,
eight 5-bit alphabet indices are emitted, and the tail is replaced by `=`
according to `len(s) % 5`.
-/
def b32encode (s : List Nat) : List Nat :=
  (chunksOf5 s).foldl (fun acc c => acc ++ encodeChunk c) []

/-- Strip trailing `=` characters (`bytes.rstrip(b'=')`). -/
def rstripPad (s : List Nat) : List Nat :=
  (s.reverse.dropWhile (fun c => c == padChar)).reverse

/-- Apply the optional `map01` substitution: `0 → O`, `1 → map01`. -/
def applyMap01 (s : List Nat) (map01 : Option Nat) : List Nat :=
  match map01 with
  | none => s
  | some m => s.map fun c => if c = char0 then charO else if c = char1 then m else c

/-- Normalize a decode input the way `b32decode` does before the bit loop. -/
def normalize (s : List Nat) (casefold : Bool) (map01 : Option Nat) : List Nat :=
  let s := applyMap01 s map01
  let s := if casefold then s.map toUpperAscii else s
  rstripPad s

/-- Incremental Base32 bit accumulator, matching the Python decode loop. -/
def decodeGo (val bits : Nat) (acc : List Nat) : List Nat → Option (List Nat)
  | [] => some acc
  | c :: cs =>
    match indexInAlphabet c with
    | none => none
    | some idx =>
      let val' := (val <<< 5) ||| idx
      let bits' := bits + 5
      if bits' ≥ 8 then
        let bits'' := bits' - 8
        let byte := (val' >>> bits'') &&& 255
        decodeGo val' bits'' (acc ++ [byte]) cs
      else
        decodeGo val' bits' acc cs

/--
Decode a Base32 bytes-like object or ASCII code-point list.

`casefold = true` uppercases first (Python `casefold`).
`map01 = some m` maps `0` to `O` and `1` to `m` before case folding.
Returns `none` if a non-alphabet digit remains after stripping padding.
-/
def b32decode (s : List Nat) (casefold : Bool := false) (map01 : Option Nat := none) :
    Option (List Nat) :=
  decodeGo 0 0 [] (normalize s casefold map01)

/-- Decode an ASCII string by encoding it to code points first. -/
def b32decodeString (s : String) (casefold : Bool := false) (map01 : Option Nat := none) :
    Option (List Nat) :=
  if s.all (fun c => decide (c.toNat < 128)) then
    b32decode (s.toList.map (·.toNat)) casefold map01
  else
    none

/-- Main encode entry point (Python `benchmark_b32encode`). -/
def benchmark_b32encode (s : List Nat) : List Nat :=
  b32encode s

/-- Main decode entry point (Python `benchmark_b32decode`). -/
def benchmark_b32decode (s : List Nat) (casefold : Bool := false) (map01 : Option Nat := none) :
    Option (List Nat) :=
  b32decode s casefold map01

def strBytes (s : String) : List Nat :=
  s.toList.map (·.toNat)

-- Unit tests (Python `check`)

example : b32encode (strBytes "") = strBytes "" := by native_decide
example : b32encode (strBytes "f") = strBytes "MY======" := by native_decide
example : b32encode (strBytes "fo") = strBytes "MZXQ====" := by native_decide
example : b32encode (strBytes "foo") = strBytes "MZXW6===" := by native_decide
example : b32encode (strBytes "foob") = strBytes "MZXW6YQ=" := by native_decide
example : b32encode (strBytes "fooba") = strBytes "MZXW6YTB" := by native_decide
example : b32encode (strBytes "foobar") = strBytes "MZXW6YTBOI======" := by native_decide

example : b32decode (b32encode (strBytes "VeriBench")) false none = some (strBytes "VeriBench") := by
  native_decide

example : b32decode (strBytes "mzxw6ytb") true none = some (strBytes "fooba") := by
  native_decide

example : b32decode (strBytes "MY======") false none = some (strBytes "f") := by native_decide
example : b32decode (strBytes "0") false none = none := by native_decide

#eval strBytes "MY======"
#eval b32encode (strBytes "foobar")
#eval b32decode (b32encode (strBytes "VeriBench")) false none

/-- Input is a bytes-like object: every element is a byte in `0 .. 255`. -/
def Pre (s : List Nat) : Prop :=
  ∀ b ∈ s, b < 256

/-- Decode input is bytes-like, or an ASCII string already encoded to code points. -/
def Pre_decode (s : List Nat) : Prop :=
  ∀ b ∈ s, b < 256

/-- ASCII-string precondition of `pre_decode`. -/
def Pre_decode_string (s : String) : Prop :=
  ∀ c ∈ s.toList, c.toNat < 128

-- Placeholder theorems filled in after the implementation is checked.
theorem roundtrip_thm (s : List Nat) (h : Pre s) :
    b32decode (b32encode s) false none = some s := by
  sorry

end «23_base32»
