import Mathlib

/-!
# Base32

A byte-exact model of the supplied Python program. Byte containers have a common
`List (Fin 256)` payload. Text inputs are admitted by the decoder exactly when
ASCII. Errors are explicit. In particular, decoding removes *all* trailing `=`,
does not check padding length, and discards an incomplete final byte. `map01`
accepts an optional byte string (including multi-byte replacements).
-/
namespace Base32

deriving instance DecidableEq for Except

abbrev Byte := Fin 256
abbrev Bytes := List Byte
abbrev Digit := Fin 32

def byte (n : Nat) : Byte := ⟨n % 256, Nat.mod_lt _ (by decide)⟩
def digit (n : Nat) : Digit := ⟨n % 32, Nat.mod_lt _ (by decide)⟩
def ascii (s : String) : Bytes := s.toUTF8.data.toList.map (fun b => byte b.toNat)
def pad : Byte := byte 61

def alphabet (d : Digit) : Byte :=
  byte (if d.val < 26 then 65 + d.val else 24 + d.val)

def unalphabet (b : Byte) : Option Digit :=
  if 65 ≤ b.val ∧ b.val ≤ 90 then some (digit (b.val - 65))
  else if 50 ≤ b.val ∧ b.val ≤ 55 then some (digit (b.val - 24))
  else none

/-- The eight five-bit slices of a zero-extended five-byte chunk. -/
def encodeBlock : Bytes → List Digit
  | [] => []
  | [a] => [digit (a.val / 8), digit (a.val % 8 * 4)]
  | [a,b] => [digit (a.val / 8), digit (a.val % 8 * 4 + b.val / 64),
      digit (b.val / 2), digit (b.val % 2 * 16)]
  | [a,b,c] => [digit (a.val / 8), digit (a.val % 8 * 4 + b.val / 64),
      digit (b.val / 2), digit (b.val % 2 * 16 + c.val / 16),
      digit (c.val % 16 * 2)]
  | [a,b,c,d] => [digit (a.val / 8), digit (a.val % 8 * 4 + b.val / 64),
      digit (b.val / 2), digit (b.val % 2 * 16 + c.val / 16),
      digit (c.val % 16 * 2 + d.val / 128), digit (d.val / 4),
      digit (d.val % 4 * 8)]
  | a::b::c::d::e::_ => [digit (a.val / 8), digit (a.val % 8 * 4 + b.val / 64),
      digit (b.val / 2), digit (b.val % 2 * 16 + c.val / 16),
      digit (c.val % 16 * 2 + d.val / 128), digit (d.val / 4),
      digit (d.val % 4 * 8 + e.val / 32), digit e.val]

def encodeDigits : Bytes → List Digit
  | [] => []
  | [a] => encodeBlock [a]
  | [a,b] => encodeBlock [a,b]
  | [a,b,c] => encodeBlock [a,b,c]
  | [a,b,c,d] => encodeBlock [a,b,c,d]
  | a::b::c::d::e::rest => encodeBlock [a,b,c,d,e] ++ encodeDigits rest

def padding (n : Nat) : Nat :=
  match n % 5 with
  | 1 => 6 | 2 => 4 | 3 => 3 | 4 => 1 | _ => 0

def b32encode (xs : Bytes) : Bytes :=
  (encodeDigits xs).map alphabet ++ List.replicate (padding xs.length) pad

/-- Reassemble full bytes; leftover low bits are intentionally ignored. -/
def decodeDigits : List Digit → Bytes
  | [] => []
  | [_] => []
  | [a,b] => [byte (a.val * 8 + b.val / 4)]
  | [a,b,_] => [byte (a.val * 8 + b.val / 4)]
  | [a,b,c,d] => [byte (a.val * 8 + b.val / 4),
      byte (b.val % 4 * 64 + c.val * 2 + d.val / 16)]
  | [a,b,c,d,e] => [byte (a.val * 8 + b.val / 4),
      byte (b.val % 4 * 64 + c.val * 2 + d.val / 16),
      byte (d.val % 16 * 16 + e.val / 2)]
  | [a,b,c,d,e,_] => [byte (a.val * 8 + b.val / 4),
      byte (b.val % 4 * 64 + c.val * 2 + d.val / 16),
      byte (d.val % 16 * 16 + e.val / 2)]
  | [a,b,c,d,e,f,g] => [byte (a.val * 8 + b.val / 4),
      byte (b.val % 4 * 64 + c.val * 2 + d.val / 16),
      byte (d.val % 16 * 16 + e.val / 2),
      byte (e.val % 2 * 128 + f.val * 4 + g.val / 8)]
  | a::b::c::d::e::f::g::h::rest =>
      byte (a.val * 8 + b.val / 4) ::
      byte (b.val % 4 * 64 + c.val * 2 + d.val / 16) ::
      byte (d.val % 16 * 16 + e.val / 2) ::
      byte (e.val % 2 * 128 + f.val * 4 + g.val / 8) ::
      byte (g.val % 8 * 32 + h.val) :: decodeDigits rest

/-- Equivalent to `rstrip(b'=')`, not to removing internal padding. -/
def stripPad : Bytes → Bytes
  | [] => []
  | b::bs => let tail := stripPad bs
             if tail = [] ∧ b = pad then [] else b::tail

def upper (b : Byte) : Byte :=
  if 97 ≤ b.val ∧ b.val ≤ 122 then byte (b.val - 32) else b

def mapAmbiguous (xs : Bytes) (map01 : Option Bytes) : Bytes :=
  match map01 with
  | none => xs
  | some [] => xs
  | some replacement => xs.flatMap (fun b =>
      if b = byte 48 then [byte 79]
      else if b = byte 49 then replacement else [b])

def prepare (xs : Bytes) (casefold : Bool) (map01 : Option Bytes) : Bytes :=
  stripPad (if casefold then (mapAmbiguous xs map01).map upper
            else mapAmbiguous xs map01)

def readDigits : Bytes → Option (List Digit)
  | [] => some []
  | b::bs => do
      let d ← unalphabet b
      let ds ← readDigits bs
      return d::ds

inductive Error where
  | expectedBytes | nonAscii | nonBase32
  deriving DecidableEq, Repr

def b32decode (xs : Bytes) (casefold : Bool := false)
    (map01 : Option Bytes := none) : Except Error Bytes :=
  match readDigits (prepare xs casefold map01) with
  | none => .error .nonBase32
  | some ds => .ok (decodeDigits ds)

inductive Input where
  | bytes (data : Bytes) | bytearray (data : Bytes) | memoryview (data : Bytes)
  | text (data : String) | other
  deriving Repr

def pre_encode : Input → Bool
  | .bytes _ | .bytearray _ | .memoryview _ => true
  | _ => false

def pre_decode : Input → Bool
  | .text s => s.toList.all (fun c => c.toNat < 128)
  | x => pre_encode x

def benchmark_b32encode : Input → Except Error Bytes
  | .bytes xs | .bytearray xs | .memoryview xs => .ok (b32encode xs)
  | _ => .error .expectedBytes

def benchmark_b32decode (s : Input) (casefold : Bool := false)
    (map01 : Option Bytes := none) : Except Error Bytes :=
  match s with
  | .bytes xs | .bytearray xs | .memoryview xs => b32decode xs casefold map01
  | .text t => if pre_decode (.text t) then b32decode (ascii t) casefold map01
               else .error .nonAscii
  | .other => .error .expectedBytes

-- Unit tests from Python, followed by permissive-decoding and error edge cases.
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
example : b32decode (ascii "A") = .ok [] := by native_decide
example : b32decode (ascii "M=Y") = .error .nonBase32 := by native_decide
example : b32decode (ascii "mzxw6ytb") = .error .nonBase32 := by native_decide
example : b32decode (ascii "01======") false (some (ascii "I")) =
    b32decode (ascii "OI======") := by native_decide
example : b32decode (ascii "1") false (some (ascii "MY")) = .ok (ascii "f") := by native_decide
example : benchmark_b32decode (.text "é") = .error .nonAscii := by native_decide
#eval b32encode (ascii "foobar")
#eval b32decode (ascii "mzxw6ytb") true

/-- The typed core has bytes by construction; these are the dynamic Python
preconditions on the two public inputs, not a restriction to valid Base32. -/
def Pre (encInput decInput : Input) : Prop :=
  pre_encode encInput = true ∧ pre_decode decInput = true


@[simp] theorem unalphabet_alphabet (d : Digit) : unalphabet (alphabet d) = some d := by
  fin_cases d <;> decide

@[simp] theorem alphabet_ne_pad (d : Digit) : alphabet d ≠ pad := by
  fin_cases d <;> decide

@[simp] theorem readDigits_alphabet (ds : List Digit) :
    readDigits (ds.map alphabet) = some ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [readDigits, ih]

@[simp] theorem stripPad_replicate (n : Nat) : stripPad (List.replicate n pad) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, stripPad, ih]

@[simp] theorem stripPad_encoded (ds : List Digit) (n : Nat) :
    stripPad (ds.map alphabet ++ List.replicate n pad) = ds.map alphabet := by
  induction ds with
  | nil => simp
  | cons d ds ih => simp [stripPad, ih]

-- Five local arithmetic identities, with no finite enumeration of byte strings.
theorem rebuild_a (a b : Byte) :
    byte ((digit (a.val / 8)).val * 8 +
      (digit (a.val % 8 * 4 + b.val / 64)).val / 4) = a := by
  apply Fin.ext
  have ha := a.isLt
  have hb := b.isLt
  simp only [byte, digit, Fin.val_mk]
  omega

theorem rebuild_b (a b c : Byte) :
    byte ((digit (a.val % 8 * 4 + b.val / 64)).val % 4 * 64 +
      (digit (b.val / 2)).val * 2 +
      (digit (b.val % 2 * 16 + c.val / 16)).val / 16) = b := by
  apply Fin.ext
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  simp only [byte, digit, Fin.val_mk]
  omega

theorem rebuild_c (b c d : Byte) :
    byte ((digit (b.val % 2 * 16 + c.val / 16)).val % 16 * 16 +
      (digit (c.val % 16 * 2 + d.val / 128)).val / 2) = c := by
  apply Fin.ext
  have hb := b.isLt
  have hc := c.isLt
  have hd := d.isLt
  simp only [byte, digit, Fin.val_mk]
  omega

theorem rebuild_d (c d e : Byte) :
    byte ((digit (c.val % 16 * 2 + d.val / 128)).val % 2 * 128 +
      (digit (d.val / 4)).val * 4 +
      (digit (d.val % 4 * 8 + e.val / 32)).val / 8) = d := by
  apply Fin.ext
  have hc := c.isLt
  have hd := d.isLt
  have he := e.isLt
  simp only [byte, digit, Fin.val_mk]
  omega

theorem rebuild_e (d e : Byte) :
    byte ((digit (d.val % 4 * 8 + e.val / 32)).val % 8 * 32 +
      (digit e.val).val) = e := by
  apply Fin.ext
  have hd := d.isLt
  have he := e.isLt
  simp only [byte, digit, Fin.val_mk]
  omega


theorem decode_encode_digits (xs : Bytes) : decodeDigits (encodeDigits xs) = xs := by
  have ra (a : Byte) := rebuild_a a (byte 0)
  have rb (a b : Byte) := rebuild_b a b (byte 0)
  have rc (b c : Byte) := rebuild_c b c (byte 0)
  have rd (c d : Byte) := rebuild_d c d (byte 0)
  simp only [show (byte 0).val = 0 from rfl, Nat.zero_div, Nat.add_zero] at ra rb rc rd
  induction xs using encodeDigits.induct <;>
    simp only [encodeDigits, encodeBlock, List.cons_append, List.nil_append,
      decodeDigits, rebuild_a, rebuild_b, rebuild_c, rebuild_d, rebuild_e,
      *]

theorem encodeDigits_length (xs : Bytes) :
    (encodeDigits xs).length = (xs.length * 8 + 4) / 5 := by
  induction xs using encodeDigits.induct <;>
    simp_all [encodeDigits, encodeBlock]
  omega

theorem decodeDigits_length (ds : List Digit) :
    (decodeDigits ds).length = ds.length * 5 / 8 := by
  induction ds using decodeDigits.induct <;>
    simp_all [decodeDigits]
  omega

theorem readDigits_length (bs : Bytes) (ds : List Digit)
    (h : readDigits bs = some ds) : ds.length = bs.length := by
  induction bs generalizing ds with
  | nil => simpa [readDigits] using h.symm
  | cons b bs ih =>
    cases hb : unalphabet b <;> cases hs : readDigits bs <;>
      simp [readDigits, hb, hs] at h
    subst ds
    simp [ih _ hs]

theorem readDigits_invalid (bs : Bytes) :
    readDigits bs = none ↔ bs.any (fun b => (unalphabet b).isNone) = true := by
  induction bs with
  | nil => simp [readDigits]
  | cons b bs ih =>
    cases hb : unalphabet b <;> cases hs : readDigits bs <;>
      simp_all [readDigits]

/-- Lossless decoding on the entire bytes domain. -/
def roundtrip_prop (xs : Bytes) : Prop := b32decode (b32encode xs) = .ok xs

theorem roundtrip_thm (xs : Bytes) : roundtrip_prop xs := by
  simp [roundtrip_prop, b32decode, prepare, mapAmbiguous, b32encode, decode_encode_digits]

/-- Exactly eight output characters for each nonempty, possibly partial chunk. -/
def length_prop (xs : Bytes) : Prop := (b32encode xs).length = 8 * ((xs.length + 4) / 5)

theorem length_thm (xs : Bytes) : length_prop xs := by
  unfold length_prop b32encode
  simp only [List.length_append, List.length_map, List.length_replicate, encodeDigits_length]
  have hm : xs.length % 5 < 5 := Nat.mod_lt _ (by decide)
  interval_cases h : xs.length % 5 <;> simp [padding, h] <;> omega

/-- Only the RFC 4648 alphabet and terminal padding can be emitted. -/
def alphabet_prop (xs : Bytes) : Prop :=
  (b32encode xs).all (fun b => (unalphabet b).isSome || b == pad) = true

theorem alphabet_thm (xs : Bytes) : alphabet_prop xs := by
  simp [alphabet_prop, b32encode, List.all_eq_true]

/-- The exact remainder-dependent padding suffix, with no padding in the payload. -/
def padding_prop (xs : Bytes) : Prop :=
  b32encode xs = stripPad (b32encode xs) ++ List.replicate (padding xs.length) pad

theorem padding_thm (xs : Bytes) : padding_prop xs := by
  simp [padding_prop, b32encode]

/-- The decoder rejects exactly the non-alphabet bytes remaining after preprocessing. -/
def validation_prop (xs : Bytes) (cf : Bool) (m : Option Bytes) : Prop :=
  (b32decode xs cf m = .error .nonBase32) ↔
    (prepare xs cf m).any (fun b => (unalphabet b).isNone) = true

theorem validation_thm (xs : Bytes) (cf : Bool) (m : Option Bytes) :
    validation_prop xs cf m := by
  unfold validation_prop b32decode
  rw [← readDigits_invalid]
  cases readDigits (prepare xs cf m) <;> simp

/-- No strict padding check: every full eight bits produces a byte. -/
def decodedLength_prop (xs : Bytes) (cf : Bool) (m : Option Bytes) : Prop :=
  match b32decode xs cf m with
  | .error _ => True
  | .ok out => out.length = (prepare xs cf m).length * 5 / 8

theorem decodedLength_thm (xs : Bytes) (cf : Bool) (m : Option Bytes) :
    decodedLength_prop xs cf m := by
  unfold decodedLength_prop b32decode
  cases h : readDigits (prepare xs cf m) with
  | none => trivial
  | some ds => simp [decodeDigits_length, readDigits_length _ _ h]

/-- Lowercasing for the case-folding specification, not an extra encoder mode. -/
def lower (b : Byte) : Byte :=
  if 65 ≤ b.val ∧ b.val ≤ 90 then byte (b.val + 32) else b

@[simp] theorem upper_lower_alphabet (d : Digit) : upper (lower (alphabet d)) = alphabet d := by
  fin_cases d <;> decide

@[simp] theorem upper_lower_pad : upper (lower pad) = pad := by decide

theorem upper_lower_encode (xs : Bytes) :
    ((b32encode xs).map lower).map upper = b32encode xs := by
  simp [b32encode, List.map_map, Function.comp_def]

def casefold_prop (xs : Bytes) : Prop :=
  b32decode ((b32encode xs).map lower) true = .ok xs

theorem casefold_thm (xs : Bytes) : casefold_prop xs := by
  unfold casefold_prop
  change b32decode (((b32encode xs).map lower).map upper) = .ok xs
  rw [upper_lower_encode]
  exact roundtrip_thm xs


/-- Common byte payload, also used for admissible ASCII text. -/
def payload : Input → Bytes
  | .bytes xs | .bytearray xs | .memoryview xs => xs
  | .text t => ascii t
  | .other => []

def encodeInput_prop (i : Input) : Prop :=
  benchmark_b32encode i = .ok (b32encode (payload i))

theorem encodeInput_thm (i : Input) (h : pre_encode i = true) : encodeInput_prop i := by
  cases i <;> simp_all [pre_encode, encodeInput_prop, benchmark_b32encode, payload]

def decodeInput_prop (i : Input) (cf : Bool) (m : Option Bytes) : Prop :=
  benchmark_b32decode i cf m = b32decode (payload i) cf m

theorem decodeInput_thm (i : Input) (cf : Bool) (m : Option Bytes)
    (h : pre_decode i = true) : decodeInput_prop i cf m := by
  cases i <;> simp_all [pre_decode, pre_encode, decodeInput_prop, benchmark_b32decode, payload]

/-- All byte values and lengths are admissible. No Base32-validity assumption is
made on decoding: invalid digits must produce the modeled Python error. -/
def Post_prop (encInput decInput : Input) (cf : Bool) (m : Option Bytes) : Prop :=
  roundtrip_prop (payload encInput) ∧
  length_prop (payload encInput) ∧
  alphabet_prop (payload encInput) ∧
  padding_prop (payload encInput) ∧
  casefold_prop (payload encInput) ∧
  validation_prop (payload decInput) cf m ∧
  decodedLength_prop (payload decInput) cf m ∧
  encodeInput_prop encInput ∧ decodeInput_prop decInput cf m

/-! ## Bounded property-based tests
These are executable checks, independent of the proofs above. The corpus covers
every single byte, all chunk remainders, multiple chunks, zeros, high bytes, and
structured nonconstant messages. Decoder tests include invalid bytes and both
flags, empty replacements, lowercase replacements and multi-byte replacements.
-/
def samples : List Bytes :=
  [[]] ++ (List.range 256).map (fun n => [byte n]) ++
  (List.range 40).flatMap (fun n => (List.range 32).map (fun seed =>
    (List.range n).map (fun j => byte (seed * 79 + j * 137))))

def decodeSamples : List Bytes :=
  samples.take 257 ++ (samples.drop 257).flatMap (fun xs =>
    [b32encode xs, (b32encode xs).map lower, stripPad (b32encode xs)]) ++
  [ascii "01======", ascii "1", ascii "=A=", ascii "=====", ascii "M=Y", ascii "MY!"]

def mapSamples : List (Option Bytes) :=
  [none, some [], some (ascii "I"), some (ascii "L"), some (ascii "i"),
   some (ascii "MY"), some (ascii "=0")]

-- PBT: roundtrip_prop
example : samples.all (fun xs => decide (b32decode (b32encode xs) = .ok xs)) = true := by
  native_decide
-- PBT: length_prop
example : samples.all (fun xs => decide ((b32encode xs).length = 8 * ((xs.length + 4) / 5))) = true := by
  native_decide
-- PBT: alphabet_prop
example : samples.all (fun xs =>
    (b32encode xs).all (fun b => (unalphabet b).isSome || b == pad)) = true := by native_decide
-- PBT: padding_prop
example : samples.all (fun xs => decide
    (b32encode xs = stripPad (b32encode xs) ++ List.replicate (padding xs.length) pad)) = true := by
  native_decide
-- PBT: casefold_prop
example : samples.all (fun xs => decide
    (b32decode ((b32encode xs).map lower) true = .ok xs)) = true := by native_decide
-- PBT: validation_prop and decodedLength_prop, including unsuccessful decoding.
example : decodeSamples.all (fun xs => [false, true].all (fun cf => mapSamples.all (fun m =>
    decide ((b32decode xs cf m = .error .nonBase32) ↔
      (prepare xs cf m).any (fun b => (unalphabet b).isNone) = true)))) = true := by native_decide
example : decodeSamples.all (fun xs => [false, true].all (fun cf => mapSamples.all (fun m =>
    match b32decode xs cf m with
    | .error _ => true
    | .ok out => decide (out.length = (prepare xs cf m).length * 5 / 8)))) = true := by native_decide

def inputSamples : List Input :=
  (samples.take 300).flatMap (fun xs => [.bytes xs, .bytearray xs, .memoryview xs]) ++
  [.text "", .text "MY======", .text "mzxw6ytb", .text "01======", .text "é", .other]

-- PBT: encodeInput_prop on exactly its precondition.
example : inputSamples.all (fun i => !pre_encode i ||
    decide (benchmark_b32encode i = .ok (b32encode (payload i)))) = true := by native_decide
-- PBT: decodeInput_prop on exactly its precondition, including ASCII non-digits.
example : inputSamples.all (fun i => [false, true].all (fun cf => mapSamples.all (fun m =>
    !pre_decode i || decide (benchmark_b32decode i cf m = b32decode (payload i) cf m)))) = true := by
  native_decide

/-- Executable counterpart of every conjunct of Post_prop. -/
def postCheck (ei di : Input) (cf : Bool) (m : Option Bytes) : Bool :=
  let xs := payload ei
  let ys := payload di
  decide (b32decode (b32encode xs) = .ok xs) &&
  decide ((b32encode xs).length = 8 * ((xs.length + 4) / 5)) &&
  (b32encode xs).all (fun b => (unalphabet b).isSome || b == pad) &&
  decide (b32encode xs = stripPad (b32encode xs) ++ List.replicate (padding xs.length) pad) &&
  decide (b32decode ((b32encode xs).map lower) true = .ok xs) &&
  decide ((b32decode ys cf m = .error .nonBase32) ↔
    (prepare ys cf m).any (fun b => (unalphabet b).isNone) = true) &&
  (match b32decode ys cf m with
   | .error _ => true
   | .ok out => decide (out.length = (prepare ys cf m).length * 5 / 8)) &&
  decide (benchmark_b32encode ei = .ok (b32encode xs)) &&
  decide (benchmark_b32decode di cf m = b32decode ys cf m)

-- PBT: Post_prop; vary both container representations and decoding options.
example : samples.all (fun xs => [false, true].all (fun cf => mapSamples.all (fun m =>
    postCheck (.memoryview xs) (.bytearray (b32encode xs)) cf m))) = true := by native_decide
example : inputSamples.all (fun di => !pre_decode di ||
    postCheck (.bytes (ascii "VeriBench")) di true (some (ascii "I"))) = true := by native_decide
#eval (samples.length, decodeSamples.length,
  samples.all (fun xs => postCheck (.bytes xs) (.bytes (b32encode xs)) false none))

/-- Kernel-checked correctness under the two original input-type preconditions. -/
theorem correctness_thm (ei di : Input) (cf : Bool) (m : Option Bytes) :
    Pre ei di → Post_prop ei di cf m := by
  rintro ⟨he, hd⟩
  exact ⟨roundtrip_thm _, length_thm _, alphabet_thm _, padding_thm _, casefold_thm _,
    validation_thm _ _ _, decodedLength_thm _ _ _, encodeInput_thm _ he,
    decodeInput_thm _ _ _ hd⟩


/-! ## Imperative implementation
The mutable implementations append to an output buffer in loops. The byte
slicing arithmetic is shared, but traversal, accumulation, and digit validation
are independently implemented. Neither whole-input `b32encode` nor `b32decode` is called by the
imperative public entry points.
-/
def chunks5 : List Byte → List (List Byte)
  | [] => []
  | [a] => [[a]]
  | [a,b] => [[a,b]]
  | [a,b,c] => [[a,b,c]]
  | [a,b,c,d] => [[a,b,c,d]]
  | a::b::c::d::e::rest => [a,b,c,d,e] :: chunks5 rest

def chunks8 : List Digit → List (List Digit)
  | [] => []
  | [a] => [[a]]
  | [a,b] => [[a,b]]
  | [a,b,c] => [[a,b,c]]
  | [a,b,c,d] => [[a,b,c,d]]
  | [a,b,c,d,e] => [[a,b,c,d,e]]
  | [a,b,c,d,e,f] => [[a,b,c,d,e,f]]
  | [a,b,c,d,e,f,g] => [[a,b,c,d,e,f,g]]
  | a::b::c::d::e::f::g::h::rest => [a,b,c,d,e,f,g,h] :: chunks8 rest


/-- A reusable mutable output buffer; the invariant allows any initial prefix. -/
def collectImp {α β : Type} (f : α → List β) (xs : List α) (initial : List β) : List β := Id.run do
  let mut out := initial
  for x in xs do
    out := out ++ f x
  return out

def pushDigit (state : Option (List Digit)) (b : Byte) : Option (List Digit) := do
  let ds ← state
  let d ← unalphabet b
  return ds ++ [d]

def scanDigitsImp (bs : Bytes) (initial : Option (List Digit)) : Option (List Digit) := Id.run do
  let mut state := initial
  for b in bs do
    state := pushDigit state b
  return state

def b32encodeImp (xs : Bytes) : Bytes := Id.run do
  let mut out : Bytes := []
  for block in chunks5 xs do
    out := out ++ (encodeBlock block).map alphabet
  out := out ++ List.replicate (padding xs.length) pad
  return out

def b32decodeImp (xs : Bytes) (cf : Bool := false) (m : Option Bytes := none) : Except Error Bytes := Id.run do
  let digits := scanDigitsImp (prepare xs cf m) (some [])
  match digits with
  | none => return .error .nonBase32
  | some ds =>
    let mut out : Bytes := []
    for block in chunks8 ds do
      out := out ++ decodeDigits block
    return .ok out

def benchmark_b32encodeImp : Input → Except Error Bytes
  | .bytes xs | .bytearray xs | .memoryview xs => .ok (b32encodeImp xs)
  | _ => .error .expectedBytes

def benchmark_b32decodeImp (s : Input) (cf : Bool := false)
    (m : Option Bytes := none) : Except Error Bytes :=
  match s with
  | .bytes xs | .bytearray xs | .memoryview xs => b32decodeImp xs cf m
  | .text t => if pre_decode (.text t) then b32decodeImp (ascii t) cf m
               else .error .nonAscii
  | .other => .error .expectedBytes

-- Imperative unit tests and bounded equivalence tests.
example : b32encodeImp (ascii "") = ascii "" := by native_decide
example : b32encodeImp (ascii "f") = ascii "MY======" := by native_decide
example : b32encodeImp (ascii "fo") = ascii "MZXQ====" := by native_decide
example : b32encodeImp (ascii "foo") = ascii "MZXW6===" := by native_decide
example : b32encodeImp (ascii "foob") = ascii "MZXW6YQ=" := by native_decide
example : b32encodeImp (ascii "fooba") = ascii "MZXW6YTB" := by native_decide
example : b32encodeImp (ascii "foobar") = ascii "MZXW6YTBOI======" := by native_decide
example : b32decodeImp (b32encodeImp (ascii "VeriBench")) = .ok (ascii "VeriBench") := by native_decide
example : b32decodeImp (ascii "mzxw6ytb") true = .ok (ascii "fooba") := by native_decide
example : b32decodeImp (ascii "M=Y") = .error .nonBase32 := by native_decide
example : samples.all (fun xs => decide (b32encode xs = b32encodeImp xs)) = true := by native_decide
example : decodeSamples.all (fun xs => [false, true].all (fun cf => mapSamples.all (fun m =>
    decide (b32decode xs cf m = b32decodeImp xs cf m)))) = true := by native_decide
#eval b32encodeImp (ascii "foobar")
#eval b32decodeImp (ascii "mzxw6ytb") true

theorem collectImp_eq {α β : Type} (f : α → List β) (xs : List α) (initial : List β) :
    collectImp f xs initial = initial ++ xs.flatMap f := by
  induction xs generalizing initial with
  | nil => simp [collectImp]
  | cons x xs ih =>
    have step : collectImp f (x::xs) initial = collectImp f xs (initial ++ f x) := by
      simp [collectImp]
    rw [step, ih]
    simp [List.append_assoc]

theorem scanDigitsImp_eq (bs : Bytes) (initial : Option (List Digit)) :
    scanDigitsImp bs initial = (do
      let before ← initial
      let suffix ← readDigits bs
      return before ++ suffix) := by
  induction bs generalizing initial with
  | nil => cases initial <;> simp [scanDigitsImp, readDigits]
  | cons b bs ih =>
    have step : scanDigitsImp (b::bs) initial = scanDigitsImp bs (pushDigit initial b) := by
      simp [scanDigitsImp]
    rw [step, ih]
    cases initial <;> cases hb : unalphabet b <;> cases hs : readDigits bs <;>
      simp [pushDigit, readDigits, hb, hs, List.append_assoc]

theorem chunks5_encode (xs : Bytes) :
    (chunks5 xs).flatMap encodeBlock = encodeDigits xs := by
  induction xs using encodeDigits.induct <;> simp_all [chunks5, encodeDigits]

theorem chunks8_decode (ds : List Digit) :
    (chunks8 ds).flatMap decodeDigits = decodeDigits ds := by
  induction ds using decodeDigits.induct <;> simp_all [chunks8, decodeDigits]

/-- Unconditional equivalence on all byte sequences. -/
theorem encode_equivalence_thm (xs : Bytes) : b32encode xs = b32encodeImp xs := by
  change b32encode xs =
    collectImp (fun block => (encodeBlock block).map alphabet) (chunks5 xs) [] ++
      List.replicate (padding xs.length) pad
  rw [collectImp_eq]
  simp [b32encode, ← List.map_flatMap, chunks5_encode]

theorem decode_equivalence_thm (xs : Bytes) (cf : Bool) (m : Option Bytes) :
    b32decode xs cf m = b32decodeImp xs cf m := by
  change b32decode xs cf m =
    match scanDigitsImp (prepare xs cf m) (some []) with
    | none => .error .nonBase32
    | some ds => .ok (collectImp decodeDigits (chunks8 ds) [])
  rw [scanDigitsImp_eq]
  cases h : readDigits (prepare xs cf m) <;>
    simp [b32decode, h, collectImp_eq, chunks8_decode]

/-- The public functions agree even on modeled type/ASCII errors; equivalence
requires no valid-digit, padding, or input-type assumptions. -/
theorem equivalence_thm (ei di : Input) (cf : Bool) (m : Option Bytes) :
    benchmark_b32encode ei = benchmark_b32encodeImp ei ∧
    benchmark_b32decode di cf m = benchmark_b32decodeImp di cf m := by
  constructor
  · cases ei <;> simp [benchmark_b32encode, benchmark_b32encodeImp, encode_equivalence_thm]
  · cases di <;> simp [benchmark_b32decode, benchmark_b32decodeImp, decode_equivalence_thm]

end Base32
