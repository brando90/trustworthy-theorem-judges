import Mathlib

/-!
# Base32 encoding and decoding (VeriBench task `23_base32`)

A Lean 4 formalization of Python's `base64.b32encode` / `base64.b32decode`
(RFC 3548 Base32), as sourced from CPython's standard `base64` library.

* Bytes are modelled as `List Nat` of octets (values `< 256`); the encoded
  output is the list of ASCII codes of the Base32 text.
* Python raises `binascii.Error` when decoding meets a non-alphabet digit;
  our `revAlphabet` maps such digits to `0` instead, and every theorem is
  stated on the valid domain (encoded output only contains valid digits).
* Bit arithmetic is stated with `/` and `%` (equal to Python's `>>` and `&`
  on non-negative integers) so that the proofs go through `omega`.
-/

namespace Base32

/-- Bytes: a list of octets. -/
abbrev Bytes := List Nat

/-- The ASCII codes of a string. -/
def s2b (s : String) : Bytes := s.toList.map Char.toNat

/-- The Base32 alphabet `ABCDEFGHIJKLMNOPQRSTUVWXYZ234567` as ASCII codes,
indexed by a 5-bit value. -/
def alphabetChar (i : Nat) : Nat := if i < 26 then 65 + i else 50 + (i - 26)

/-- Inverse alphabet: ASCII code to 5-bit value.  Invalid digits map to `0`
(Python raises `binascii.Error` on those instead). -/
def revAlphabet (c : Nat) : Nat :=
  if 65 ≤ c ∧ c ≤ 90 then c - 65
  else if 50 ≤ c ∧ c ≤ 55 then c - 50 + 26
  else 0

/-- Number of `=` padding characters for a final chunk of size `rem`. -/
def padCount : Nat → Nat
  | 1 => 6
  | 2 => 4
  | 3 => 3
  | 4 => 1
  | _ => 0

/-- Encode one full 5-byte chunk into 8 Base32 characters (Python computes
`(val >> 35) & 0x1F` etc. from the 40-bit big-endian value `val`). -/
def encodeChunk (a b c d e : Nat) : Bytes :=
  let val := a * 4294967296 + b * 16777216 + c * 65536 + d * 256 + e
  [ alphabetChar (val / 34359738368 % 32), alphabetChar (val / 1073741824 % 32),
    alphabetChar (val / 33554432 % 32),    alphabetChar (val / 1048576 % 32),
    alphabetChar (val / 32768 % 32),       alphabetChar (val / 1024 % 32),
    alphabetChar (val / 32 % 32),          alphabetChar (val % 32) ]

/-- Encode a chunk (given as a list) into 8 Base32 characters. -/
def encodeChunkL : Bytes → Bytes
  | [a, b, c, d, e] => encodeChunk a b c d e
  | _ => []

/-- Split a byte string into chunks of 5 bytes (the last one may be short). -/
def chunks5 : Bytes → List Bytes
  | [] => []
  | a :: b :: c :: d :: e :: rest => [a, b, c, d, e] :: chunks5 rest
  | l => [l]

/-- Encode all chunks of a (zero-padded) byte string, without `=` padding. -/
def encodeAll (s : Bytes) : Bytes :=
  (chunks5 s).foldl (fun acc c => acc ++ encodeChunkL c) []

/-- The raw encoding stage: pad with zero bytes to a multiple of 5 and encode
every chunk (before the final `=`-padding fix). -/
def b32encodeRaw (s : Bytes) : Bytes :=
  encodeAll (s ++ List.replicate ((5 - s.length % 5) % 5) 0)

/-- Base32 encode: port of Python's `base64.b32encode`.  `61` is `'='`. -/
def b32encode (s : Bytes) : Bytes :=
  (b32encodeRaw s).take ((b32encodeRaw s).length - padCount (s.length % 5)) ++
    List.replicate (padCount (s.length % 5)) 61

/-- One step of Python's streaming decode loop, over the state
`(val, bits, output-so-far-in-reverse)`; `acc * 32 + v` is `(val << 5) | v`
and `acc / 2^(bits-8) % 256` is `(val >> bits) & 0xFF`. -/
def decodeStep (st : Nat × Nat × Bytes) (c : Nat) : Nat × Nat × Bytes :=
  let (acc, bits, out) := st
  let v := revAlphabet c
  let acc := acc * 32 + v
  let bits := bits + 5
  if 8 ≤ bits then
    (acc, bits - 8, (acc / 2^(bits - 8) % 256) :: out)
  else
    (acc, bits, out)

/-- `s.rstrip(b'=')`: strip trailing `=` (ASCII 61). -/
def rstripEq (s : Bytes) : Bytes :=
  (s.reverse.dropWhile (· == 61)).reverse

/-- ASCII upper-casing (Python's `s.upper()`), used for `casefold=True`. -/
def uppercase (s : Bytes) : Bytes :=
  s.map fun c => if 97 ≤ c ∧ c ≤ 122 then c - 32 else c

/-- The `map01` substitution: `'0'` (48) ↦ `'O'` (79), `'1'` (49) ↦ `map01`. -/
def applyMap01 (m : Nat) (s : Bytes) : Bytes :=
  s.map fun c => if c = 48 then 79 else if c = 49 then m else c

/-- Base32 decode: port of Python's `base64.b32decode`. -/
def b32decode (s : Bytes) (casefold : Bool := false) (map01 : Option Nat := none) : Bytes :=
  let s := match map01 with
    | some m => applyMap01 m s
    | none => s
  let s := if casefold then uppercase s else s
  ((rstripEq s).foldl decodeStep (0, 0, [])).2.2.reverse

-- ## Basic lemmas about the alphabet

theorem revAlphabet_alphabetChar {i : Nat} (h : i < 32) :
    revAlphabet (alphabetChar i) = i := by
  interval_cases i <;> rfl

theorem revAlphabet_alphabetChar_mod (x : Nat) :
    revAlphabet (alphabetChar (x % 32)) = x % 32 :=
  revAlphabet_alphabetChar (i := x % 32) (Nat.mod_lt x (y := 32) (by norm_num))

theorem alphabetChar_ne_61 {i : Nat} (h : i < 32) : alphabetChar i ≠ 61 := by
  interval_cases i <;> decide

theorem alphabetChar_mod_ne_61 (x : Nat) : alphabetChar (x % 32) ≠ 61 :=
  alphabetChar_ne_61 (Nat.mod_lt x (y := 32) (by norm_num))

theorem encodeChunk_length (a b c d e : Nat) : (encodeChunk a b c d e).length = 8 := rfl

theorem encodeChunk_reverse_head? (a b c d e : Nat) :
    (encodeChunk a b c d e).reverse.head? =
      some (alphabetChar ((a * 4294967296 + b * 16777216 + c * 65536 + d * 256 + e) % 32)) := rfl

-- ## Lemmas about stripping `=`

theorem dropWhile_beq61_self (t : Bytes) (h : t.head? ≠ some 61) :
    t.dropWhile (· == 61) = t := by
  cases t with
  | nil => rfl
  | cons c u =>
      rw [List.dropWhile_cons]
      have hc : c ≠ 61 := by simpa using h
      have hb : (c == 61) = false := by simp [hc]
      simp [hb]

theorem dropWhile_beq61_append (t u : Bytes) (h : u.head? ≠ some 61) :
    (t ++ u).dropWhile (· == 61) = t.dropWhile (· == 61) ++ u := by
  induction t with
  | nil => simp [dropWhile_beq61_self _ h]
  | cons c t ih =>
      rw [List.cons_append, List.dropWhile_cons, List.dropWhile_cons]
      by_cases hc : (c == 61) = true
      · simp [hc, ih]
      · simp [hc]

theorem rstripEq_append_replicate (l : Bytes) (h : l.reverse.head? ≠ some 61) (k : Nat) :
    rstripEq (l ++ List.replicate k 61) = l := by
  unfold rstripEq
  rw [List.reverse_append, List.reverse_replicate]
  have h1 : (List.replicate k 61 ++ l.reverse).dropWhile (· == 61) = l.reverse := by
    induction k with
    | zero => simp [dropWhile_beq61_self _ h]
    | succ k ih =>
        rw [List.replicate_succ, List.cons_append, List.dropWhile_cons]
        simp [ih]
  rw [h1, List.reverse_reverse]

theorem rstripEq_self (l : Bytes) (h : l.reverse.head? ≠ some 61) : rstripEq l = l := by
  unfold rstripEq
  rw [dropWhile_beq61_self _ h, List.reverse_reverse]

theorem rstripEq_append (l1 l2 : Bytes) (h : l1.reverse.head? ≠ some 61) :
    rstripEq (l1 ++ l2) = l1 ++ rstripEq l2 := by
  unfold rstripEq
  rw [List.reverse_append, dropWhile_beq61_append _ _ h, List.reverse_append, List.reverse_reverse]

-- ## Decode of one encoded chunk (the heart of the round-trip proof)

/-- Single-step decode reductions, one per possible value of `bits`
(the bit counter cycles through 0,5,2,7,4,1,6,3). -/
theorem step_bits0 (acc : Nat) (out : Bytes) (c : Nat) :
    decodeStep (acc, 0, out) c = (acc * 32 + revAlphabet c, 5, out) := rfl
theorem step_bits5 (acc : Nat) (out : Bytes) (c : Nat) :
    decodeStep (acc, 5, out) c =
      (acc * 32 + revAlphabet c, 2, ((acc * 32 + revAlphabet c) / 4 % 256) :: out) := rfl
theorem step_bits2 (acc : Nat) (out : Bytes) (c : Nat) :
    decodeStep (acc, 2, out) c = (acc * 32 + revAlphabet c, 7, out) := rfl
theorem step_bits7 (acc : Nat) (out : Bytes) (c : Nat) :
    decodeStep (acc, 7, out) c =
      (acc * 32 + revAlphabet c, 4, ((acc * 32 + revAlphabet c) / 16 % 256) :: out) := rfl
theorem step_bits4 (acc : Nat) (out : Bytes) (c : Nat) :
    decodeStep (acc, 4, out) c =
      (acc * 32 + revAlphabet c, 1, ((acc * 32 + revAlphabet c) / 2 % 256) :: out) := rfl
theorem step_bits1 (acc : Nat) (out : Bytes) (c : Nat) :
    decodeStep (acc, 1, out) c = (acc * 32 + revAlphabet c, 6, out) := rfl
theorem step_bits6 (acc : Nat) (out : Bytes) (c : Nat) :
    decodeStep (acc, 6, out) c =
      (acc * 32 + revAlphabet c, 3, ((acc * 32 + revAlphabet c) / 8 % 256) :: out) := rfl
theorem step_bits3 (acc : Nat) (out : Bytes) (c : Nat) :
    decodeStep (acc, 3, out) c =
      (acc * 32 + revAlphabet c, 0, ((acc * 32 + revAlphabet c) / 1 % 256) :: out) := rfl

/-- A full 5-byte chunk encodes to 8 characters that the streaming decoder
maps back to the same 5 bytes (for any incoming bit accumulator). -/
theorem decodeStep_encodeChunk (a b c d e acc : Nat) (out : Bytes)
    (ha : a < 256) (hb : b < 256) (hc : c < 256) (hd : d < 256) (he : e < 256) :
    List.foldl decodeStep (acc, 0, out) (encodeChunk a b c d e) =
      (acc * 1099511627776 + (a * 4294967296 + b * 16777216 + c * 65536 + d * 256 + e),
        0, e :: d :: c :: b :: a :: out) := by
  rw [encodeChunk]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [step_bits0, step_bits5, step_bits2, step_bits7, step_bits4, step_bits1, step_bits6, step_bits3]
  simp only [revAlphabet_alphabetChar_mod, Prod.mk.injEq, List.cons.injEq]
  refine ⟨?_, trivial, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> omega

theorem decodeStep_take2 (a acc : Nat) (out : Bytes) (ha : a < 256) :
    List.foldl decodeStep (acc, 0, out) ((encodeChunk a 0 0 0 0).take 2) =
      ((acc * 32 + a * 4294967296 / 34359738368 % 32) * 32 +
        a * 4294967296 / 1073741824 % 32, 2, a :: out) := by
  rw [encodeChunk]
  simp only [List.take_succ_cons, List.take_zero, List.foldl_cons, List.foldl_nil]
  rw [step_bits0, step_bits5]
  simp only [revAlphabet_alphabetChar_mod, Prod.mk.injEq, List.cons.injEq]
  refine ⟨?_, trivial, ?_, trivial⟩ <;> omega

theorem decodeStep_take4 (a b acc : Nat) (out : Bytes) (ha : a < 256) (hb : b < 256) :
    List.foldl decodeStep (acc, 0, out) ((encodeChunk a b 0 0 0).take 4) =
      ((((acc * 32 + (a * 4294967296 + b * 16777216) / 34359738368 % 32) * 32 +
        (a * 4294967296 + b * 16777216) / 1073741824 % 32) * 32 +
        (a * 4294967296 + b * 16777216) / 33554432 % 32) * 32 +
        (a * 4294967296 + b * 16777216) / 1048576 % 32, 4, b :: a :: out) := by
  rw [encodeChunk]
  simp only [List.take_succ_cons, List.take_zero, List.foldl_cons, List.foldl_nil]
  rw [step_bits0, step_bits5, step_bits2, step_bits7]
  simp only [revAlphabet_alphabetChar_mod, Prod.mk.injEq, List.cons.injEq]
  refine ⟨?_, trivial, ?_, ?_, trivial⟩ <;> omega

theorem decodeStep_take5 (a b c acc : Nat) (out : Bytes)
    (ha : a < 256) (hb : b < 256) (hc : c < 256) :
    List.foldl decodeStep (acc, 0, out) ((encodeChunk a b c 0 0).take 5) =
      (((((acc * 32 + (a * 4294967296 + b * 16777216 + c * 65536) / 34359738368 % 32) * 32 +
        (a * 4294967296 + b * 16777216 + c * 65536) / 1073741824 % 32) * 32 +
        (a * 4294967296 + b * 16777216 + c * 65536) / 33554432 % 32) * 32 +
        (a * 4294967296 + b * 16777216 + c * 65536) / 1048576 % 32) * 32 +
        (a * 4294967296 + b * 16777216 + c * 65536) / 32768 % 32, 1, c :: b :: a :: out) := by
  rw [encodeChunk]
  simp only [List.take_succ_cons, List.take_zero, List.foldl_cons, List.foldl_nil]
  rw [step_bits0, step_bits5, step_bits2, step_bits7, step_bits4]
  simp only [revAlphabet_alphabetChar_mod, Prod.mk.injEq, List.cons.injEq]
  refine ⟨?_, trivial, ?_, ?_, ?_, trivial⟩ <;> omega

theorem decodeStep_take7 (a b c d acc : Nat) (out : Bytes)
    (ha : a < 256) (hb : b < 256) (hc : c < 256) (hd : d < 256) :
    List.foldl decodeStep (acc, 0, out) ((encodeChunk a b c d 0).take 7) =
      (((((((acc * 32 + (a * 4294967296 + b * 16777216 + c * 65536 + d * 256) / 34359738368 % 32) * 32 +
        (a * 4294967296 + b * 16777216 + c * 65536 + d * 256) / 1073741824 % 32) * 32 +
        (a * 4294967296 + b * 16777216 + c * 65536 + d * 256) / 33554432 % 32) * 32 +
        (a * 4294967296 + b * 16777216 + c * 65536 + d * 256) / 1048576 % 32) * 32 +
        (a * 4294967296 + b * 16777216 + c * 65536 + d * 256) / 32768 % 32) * 32 +
        (a * 4294967296 + b * 16777216 + c * 65536 + d * 256) / 1024 % 32) * 32 +
        (a * 4294967296 + b * 16777216 + c * 65536 + d * 256) / 32 % 32, 3,
        d :: c :: b :: a :: out) := by
  rw [encodeChunk]
  simp only [List.take_succ_cons, List.take_zero, List.foldl_cons, List.foldl_nil]
  rw [step_bits0, step_bits5, step_bits2, step_bits7, step_bits4, step_bits1, step_bits6]
  simp only [revAlphabet_alphabetChar_mod, Prod.mk.injEq, List.cons.injEq, Nat.add_zero]
  repeat' constructor
  all_goals omega
-- ## Encode-side structural lemmas

theorem foldl_encodeChunkL_append (x : Bytes) (cs : List Bytes) :
    (cs.foldl (fun acc c => acc ++ encodeChunkL c) x) =
    x ++ cs.foldl (fun acc c => acc ++ encodeChunkL c) [] := by
  induction cs generalizing x with
  | nil => simp
  | cons c cs ih =>
      simp only [List.foldl_cons]
      rw [ih, ih (x := [] ++ encodeChunkL c)]
      simp [List.append_assoc]

theorem encodeAll_foldl_length (init : Bytes) (cs : List Bytes) :
    (cs.foldl (fun acc c => acc ++ encodeChunkL c) init).length =
    init.length + (cs.map (fun c => (encodeChunkL c).length)).sum := by
  induction cs generalizing init with
  | nil => simp
  | cons c cs ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih, List.length_append]
      omega

theorem length_eq_five {l : Bytes} (h : l.length = 5) :
    ∃ a b c d e, l = [a, b, c, d, e] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, l'⟩⟩⟩⟩⟩
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · rcases l' with _ | ⟨f, l''⟩
    · exact ⟨a, b, c, d, e, rfl⟩
    · simp only [List.length_cons] at h; omega

theorem chunks5_mem_length {l c : Bytes} (h : l.length % 5 = 0) (hc : c ∈ chunks5 l) :
    c.length = 5 := by
  induction l using chunks5.induct with
  | case1 =>
      have e : chunks5 [] = [] := rfl
      rw [e] at hc
      cases hc
  | case2 a b c d e rest ih =>
      rw [show chunks5 (a :: b :: c :: d :: e :: rest) = [a, b, c, d, e] :: chunks5 rest from rfl] at hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · rfl
      · have hrest : rest.length % 5 = 0 := by
          have h2 : (a :: b :: c :: d :: e :: rest).length = rest.length + 5 := rfl
          rw [h2] at h; omega
        exact ih hrest hc
  | case3 l hnil hcons =>
      rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, rest⟩⟩⟩⟩⟩
      · exact (hnil rfl).elim
      · simp at h
      · simp at h
      · simp at h
      · simp at h
      · exact (hcons a b c d e rest rfl).elim

theorem chunks5_length {l : Bytes} (h : l.length % 5 = 0) :
    (chunks5 l).length = l.length / 5 := by
  induction l using chunks5.induct with
  | case1 => rfl
  | case2 a b c d e rest ih =>
      have hrest : rest.length % 5 = 0 := by
        have h2 : (a :: b :: c :: d :: e :: rest).length = rest.length + 5 := rfl
        rw [h2] at h; omega
      rw [show chunks5 (a :: b :: c :: d :: e :: rest) = [a, b, c, d, e] :: chunks5 rest from rfl,
          List.length_cons, ih hrest]
      have h2 : (a :: b :: c :: d :: e :: rest).length = rest.length + 5 := rfl
      rw [h2]; omega
  | case3 l hnil hcons =>
      rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, rest⟩⟩⟩⟩⟩
      · exact (hnil rfl).elim
      · simp at h
      · simp at h
      · simp at h
      · simp at h
      · exact (hcons a b c d e rest rfl).elim

theorem sum_map_encodeChunkL_length (cs : List Bytes)
    (h : ∀ c ∈ cs, (encodeChunkL c).length = 8) :
    (cs.map (fun c => (encodeChunkL c).length)).sum = 8 * cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ih (fun x hx => h x (List.mem_cons_of_mem _ hx)), h c List.mem_cons_self]
      omega

theorem encodeAll_length {l : Bytes} (h : l.length % 5 = 0) :
    (encodeAll l).length = 8 * (l.length / 5) := by
  unfold encodeAll
  rw [encodeAll_foldl_length]
  simp only [List.length_nil, Nat.zero_add]
  rw [sum_map_encodeChunkL_length _ (fun c hc => by
    have hlen := chunks5_mem_length h hc
    obtain ⟨a, b, c, d, e, rfl⟩ := length_eq_five hlen
    rfl)]
  rw [chunks5_length h]

theorem padCount_le (n : Nat) : padCount n ≤ 6 := by
  unfold padCount
  split <;> omega

theorem b32encodeRaw_length_ge (t : Bytes) (ht : t ≠ []) :
    8 ≤ (b32encodeRaw t).length := by
  unfold b32encodeRaw
  have h0 : (t ++ List.replicate ((5 - t.length % 5) % 5) 0).length % 5 = 0 := by
    rw [List.length_append, List.length_replicate]; omega
  rw [encodeAll_length h0]
  have h1 : t.length ≥ 1 := Nat.pos_of_ne_zero (fun hz => ht (List.length_eq_zero_iff.mp hz))
  have h2 : (t ++ List.replicate ((5 - t.length % 5) % 5) 0).length =
      t.length + (5 - t.length % 5) % 5 := by
    rw [List.length_append, List.length_replicate]
  rw [h2]
  have h3 : (t.length + (5 - t.length % 5) % 5) / 5 ≥ 1 := by omega
  omega

theorem take_append_length_add (l1 l2 : Bytes) (k : Nat) :
    (l1 ++ l2).take (l1.length + k) = l1 ++ l2.take k := by
  induction l1 generalizing k with
  | nil => simp
  | cons x l1 ih =>
      simp [List.cons_append, List.length_cons, Nat.add_right_comm, List.take_succ_cons, ih]

theorem take_append_encodeChunk (a b c d e : Nat) (l2 : Bytes) (k : Nat) :
    (encodeChunk a b c d e ++ l2).take (8 + k) = encodeChunk a b c d e ++ l2.take k := by
  have h := take_append_length_add (encodeChunk a b c d e) l2 k
  rw [encodeChunk_length] at h
  exact h

/-- Encoding distributes over a leading full chunk (as long as more bytes
follow, so that no `=`-padding is inserted in between). -/
theorem b32encode_cons5 (a b c d e : Nat) (t : Bytes) (ht : t ≠ []) :
    b32encode (a :: b :: c :: d :: e :: t) = encodeChunk a b c d e ++ b32encode t := by
  have hrem : (a :: b :: c :: d :: e :: t).length % 5 = t.length % 5 := by
    have h2 : (a :: b :: c :: d :: e :: t).length = t.length + 5 := rfl
    rw [h2]; omega
  have hpad : a :: b :: c :: d :: e :: t ++ List.replicate ((5 - (a :: b :: c :: d :: e :: t).length % 5) % 5) 0
      = [a, b, c, d, e] ++ (t ++ List.replicate ((5 - t.length % 5) % 5) 0) := by
    rw [hrem]
    rfl
  have hraw : b32encodeRaw (a :: b :: c :: d :: e :: t) =
      encodeChunk a b c d e ++ b32encodeRaw t := by
    simp only [b32encodeRaw, encodeAll]
    rw [hpad]
    rw [show chunks5 ([a, b, c, d, e] ++ (t ++ List.replicate ((5 - t.length % 5) % 5) 0))
        = [a, b, c, d, e] :: chunks5 (t ++ List.replicate ((5 - t.length % 5) % 5) 0) from rfl]
    rw [List.foldl_cons]
    show List.foldl (fun acc c => acc ++ encodeChunkL c) (encodeChunk a b c d e) _ = _
    exact foldl_encodeChunkL_append _ _
  simp only [b32encode]
  rw [hraw, hrem]
  have hlen1 : (encodeChunk a b c d e ++ b32encodeRaw t).length = 8 + (b32encodeRaw t).length := by
    rw [List.length_append, encodeChunk_length]
  have hpads : padCount (t.length % 5) ≤ (b32encodeRaw t).length := by
    have g1 := padCount_le (t.length % 5)
    have g2 := b32encodeRaw_length_ge t ht
    omega
  have hsplit : 8 + (b32encodeRaw t).length - padCount (t.length % 5) =
      8 + ((b32encodeRaw t).length - padCount (t.length % 5)) := by omega
  rw [hlen1, hsplit, take_append_encodeChunk, List.append_assoc]

theorem b32encode_five (a b c d e : Nat) :
    b32encode [a, b, c, d, e] = encodeChunk a b c d e := by
  simp [b32encode, b32encodeRaw, encodeAll, chunks5, encodeChunkL, padCount]

-- ## Unit tests (fixed vectors, as in Python's test suite)

example : b32encode (s2b "") = s2b "" := by native_decide
example : b32encode (s2b "f") = s2b "MY======" := by native_decide
example : b32encode (s2b "fo") = s2b "MZXQ====" := by native_decide
example : b32encode (s2b "foo") = s2b "MZXW6===" := by native_decide
example : b32encode (s2b "foob") = s2b "MZXW6YQ=" := by native_decide
example : b32encode (s2b "fooba") = s2b "MZXW6YTB" := by native_decide
example : b32encode (s2b "foobar") = s2b "MZXW6YTBOI======" := by native_decide
example : b32decode (b32encode (s2b "VeriBench")) = s2b "VeriBench" := by native_decide
example : b32decode (s2b "mzxw6ytb") true = s2b "fooba" := by native_decide

/-- Kernel-checked test vector: encoding of `foobar`. -/
theorem b32encode_foobar_test : b32encode (s2b "foobar") = s2b "MZXW6YTBOI======" := by decide

/-- Kernel-checked test vector: round-trip on `VeriBench`. -/
theorem roundtrip_veribench_test :
    b32decode (b32encode (s2b "VeriBench")) = s2b "VeriBench" := by decide

/-- Kernel-checked test vector: `casefold=True` decoding. -/
theorem b32decode_casefold_test : b32decode (s2b "mzxw6ytb") true = s2b "fooba" := by decide

#eval b32encode (s2b "foobar")
#eval b32decode (b32encode (s2b "VeriBench"))

-- ## Pre-condition

/-- Precondition of `benchmark_b32encode`: the input is a bytes-like object,
modelled here as a list of octets (every element `< 256`). -/
def Pre (s : Bytes) : Prop := ∀ b ∈ s, b < 256

/-- Python's `pre_decode`: bytes-like object or ASCII string
(every element `< 128`). -/
def PreDecode (s : Bytes) : Prop := ∀ b ∈ s, b < 128


-- ## The round-trip property and its proof

/-- Generalized round-trip: decoding the encoding of `s` from any
bit-accumulator state with `bits = 0` yields the bytes of `s`
(pushed in reverse), with some leftover accumulator state. -/
theorem roundtrip_gen : ∀ (s : Bytes), Pre s → ∀ (acc : Nat) (out : Bytes),
    ∃ A B, List.foldl decodeStep (acc, 0, out) (rstripEq (b32encode s)) =
      (A, B, s.reverse ++ out)
  | [], _, acc, out => ⟨acc, 0, rfl⟩
  | [a], h, acc, out => by
      have ha : a < 256 := h a (by simp)
      have henc : b32encode [a] = (encodeChunk a 0 0 0 0).take 2 ++ List.replicate 6 61 := rfl
      have h61 : (List.take 2 (encodeChunk a 0 0 0 0)).reverse.head? ≠ some 61 := by
        simp only [encodeChunk, List.take_succ_cons, List.take_zero, List.reverse_cons,
          List.reverse_nil, List.nil_append, List.cons_append, List.head?_cons]
        exact fun hc => alphabetChar_mod_ne_61 _ (Option.some.inj hc)
      rw [henc, rstripEq_append_replicate _ h61 _, decodeStep_take2 a acc out ha]
      exact ⟨_, _, rfl⟩
  | [a, b], h, acc, out => by
      have ha : a < 256 := h a (by simp)
      have hb : b < 256 := h b (by simp)
      have henc : b32encode [a, b] = (encodeChunk a b 0 0 0).take 4 ++ List.replicate 4 61 := rfl
      have h61 : (List.take 4 (encodeChunk a b 0 0 0)).reverse.head? ≠ some 61 := by
        simp only [encodeChunk, List.take_succ_cons, List.take_zero, List.reverse_cons,
          List.reverse_nil, List.nil_append, List.cons_append, List.head?_cons]
        exact fun hc => alphabetChar_mod_ne_61 _ (Option.some.inj hc)
      rw [henc, rstripEq_append_replicate _ h61 _, decodeStep_take4 a b acc out ha hb]
      exact ⟨_, _, rfl⟩
  | [a, b, c], h, acc, out => by
      have ha : a < 256 := h a (by simp)
      have hb : b < 256 := h b (by simp)
      have hc : c < 256 := h c (by simp)
      have henc : b32encode [a, b, c] = (encodeChunk a b c 0 0).take 5 ++ List.replicate 3 61 := rfl
      have h61 : (List.take 5 (encodeChunk a b c 0 0)).reverse.head? ≠ some 61 := by
        simp only [encodeChunk, List.take_succ_cons, List.take_zero, List.reverse_cons,
          List.reverse_nil, List.nil_append, List.cons_append, List.head?_cons]
        exact fun hcc => alphabetChar_mod_ne_61 _ (Option.some.inj hcc)
      rw [henc, rstripEq_append_replicate _ h61 _, decodeStep_take5 a b c acc out ha hb hc]
      exact ⟨_, _, rfl⟩
  | [a, b, c, d], h, acc, out => by
      have ha : a < 256 := h a (by simp)
      have hb : b < 256 := h b (by simp)
      have hc : c < 256 := h c (by simp)
      have hd : d < 256 := h d (by simp)
      have henc : b32encode [a, b, c, d] = (encodeChunk a b c d 0).take 7 ++ List.replicate 1 61 := rfl
      have h61 : (List.take 7 (encodeChunk a b c d 0)).reverse.head? ≠ some 61 := by
        simp only [encodeChunk, List.take_succ_cons, List.take_zero, List.reverse_cons,
          List.reverse_nil, List.nil_append, List.cons_append, List.head?_cons]
        exact fun hcc => alphabetChar_mod_ne_61 _ (Option.some.inj hcc)
      rw [henc, rstripEq_append_replicate _ h61 _, decodeStep_take7 a b c d acc out ha hb hc hd]
      exact ⟨_, _, rfl⟩
  | a :: b :: c :: d :: e :: t, h, acc, out => by
      have ha : a < 256 := h a (by simp)
      have hb : b < 256 := h b (by simp)
      have hc : c < 256 := h c (by simp)
      have hd : d < 256 := h d (by simp)
      have he : e < 256 := h e (by simp)
      by_cases ht : t = []
      · subst ht
        rw [b32encode_five,
            rstripEq_self _ (by
              rw [encodeChunk_reverse_head?]
              exact fun hcc => alphabetChar_mod_ne_61 _ (Option.some.inj hcc)),
            decodeStep_encodeChunk a b c d e acc out ha hb hc hd he]
        exact ⟨_, _, rfl⟩
      · rw [b32encode_cons5 a b c d e t ht,
            rstripEq_append _ _ (by
              rw [encodeChunk_reverse_head?]
              exact fun hcc => alphabetChar_mod_ne_61 _ (Option.some.inj hcc)),
            List.foldl_append,
            decodeStep_encodeChunk a b c d e acc out ha hb hc hd he]
        obtain ⟨A, B, ih⟩ := roundtrip_gen t (fun x hx => h x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))))))
          (acc * 1099511627776 + (a * 4294967296 + b * 16777216 + c * 65536 + d * 256 + e))
          (e :: d :: c :: b :: a :: out)
        rw [ih]
        exact ⟨A, B, by simp [List.reverse_cons, List.append_assoc]⟩

/-- Round-trip property: decoding undoes encoding for every valid input. -/
def roundtrip_prop : Prop := ∀ s : Bytes, Pre s → b32decode (b32encode s) = s

/-- The encoded output length is always a multiple of 8. -/
def encode_length_prop : Prop := ∀ s : Bytes, (b32encode s).length % 8 = 0

theorem roundtrip_thm : roundtrip_prop := fun s h => by
  obtain ⟨A, B, hgen⟩ := roundtrip_gen s h 0 []
  simp only [b32decode, Bool.false_eq_true, if_false]
  rw [hgen]
  simp

theorem encode_length_thm : encode_length_prop := fun s => by
  by_cases hs : s = []
  · subst hs
    show (b32encode []).length % 8 = 0
    rfl
  · have hge := b32encodeRaw_length_ge s hs
    have hle := padCount_le (s.length % 5)
    unfold b32encode
    rw [List.length_append, List.length_take, List.length_replicate]
    have h1 : min ((b32encodeRaw s).length - padCount (s.length % 5)) (b32encodeRaw s).length =
        (b32encodeRaw s).length - padCount (s.length % 5) := by omega
    rw [h1]
    have h2 : (b32encodeRaw s).length - padCount (s.length % 5) + padCount (s.length % 5) =
        (b32encodeRaw s).length := by omega
    rw [h2]
    have h0 : (s ++ List.replicate ((5 - s.length % 5) % 5) 0).length % 5 = 0 := by
      rw [List.length_append, List.length_replicate]; omega
    unfold b32encodeRaw
    rw [encodeAll_length h0]
    omega

-- ## Post-condition

/-- Postcondition: conjunction of the verified properties on input `s`. -/
def Post_prop (s : Bytes) : Prop :=
  b32decode (b32encode s) = s ∧ (b32encode s).length % 8 = 0

-- ## Property-based tests

-- PBT (randomized, via Plausible): the round-trip property holds on random
-- byte strings (restricted to admissible inputs by a decidable implication).
#eval Plausible.Testable.check (∀ s : List Nat, s.all (· < 256) → b32decode (b32encode s) = s)

-- PBT (randomized): the encoded length is a multiple of 8.
#eval Plausible.Testable.check (∀ s : List Nat, (b32encode s).length % 8 = 0)

-- PBT (bounded, exhaustive): round-trip on every single byte.
example : (List.range 256).all (fun b => b32decode (b32encode [b]) = [b]) = true := by native_decide

-- PBT (bounded, exhaustive): encoded length property on every single byte.
example : (List.range 256).all (fun b => (b32encode [b]).length % 8 = 0) = true := by native_decide

-- PBT (bounded): round-trip on repeated-byte strings of all lengths up to 50.
example : (List.range 50).all (fun n =>
    b32decode (b32encode (List.replicate n 111)) = List.replicate n 111) = true := by native_decide

-- PBT (bounded): the postcondition conjunction on repeated-byte strings.
example : (List.range 50).all (fun n =>
    b32decode (b32encode (List.replicate n 65)) = List.replicate n 65 ∧
    (b32encode (List.replicate n 65)).length % 8 = 0) = true := by native_decide

-- ## Correctness theorem: `Pre` implies `Post`

theorem correctness (s : Bytes) (h : Pre s) : Post_prop s :=
  ⟨roundtrip_thm s h, encode_length_thm s⟩

-- ## Imperative implementation (`Id.run` with mutable state)

/-- A mutable accumulating `for`-loop over a list, phrased with `Id.run`
and a `let mut` variable. -/
def loopMut (f : β → α → β) (init : β) (xs : List α) : β := Id.run do
  let mut acc := init
  for x in xs do
    acc := f acc x
  return acc

/-- Imperative Base32 encode: mutable accumulation over the chunks,
then the padding fix-up. -/
def b32encodeImp (s : Bytes) : Bytes := Id.run do
  let rem := s.length % 5
  let padded := s ++ List.replicate ((5 - rem) % 5) 0
  let enc := loopMut (fun acc c => acc ++ encodeChunkL c) [] (chunks5 padded)
  let pads := padCount rem
  return enc.take (enc.length - pads) ++ List.replicate pads 61

/-- Imperative Base32 decode: mutable streaming decode over the
`=`-stripped input. -/
def b32decodeImp (s : Bytes) (casefold : Bool := false) (map01 : Option Nat := none) : Bytes := Id.run do
  let t := match map01 with
    | some m => applyMap01 m s
    | none => s
  let t := if casefold then uppercase t else t
  let st := loopMut decodeStep (0, 0, []) (rstripEq t)
  return st.2.2.reverse

-- ## Imperative tests

example : b32encodeImp (s2b "") = s2b "" := by native_decide
example : b32encodeImp (s2b "f") = s2b "MY======" := by native_decide
example : b32encodeImp (s2b "fooba") = s2b "MZXW6YTB" := by native_decide
example : b32encodeImp (s2b "foobar") = s2b "MZXW6YTBOI======" := by native_decide
example : b32decodeImp (b32encodeImp (s2b "VeriBench")) = s2b "VeriBench" := by native_decide
example : b32decodeImp (s2b "mzxw6ytb") true = s2b "fooba" := by native_decide

#eval b32encodeImp (s2b "foobar")
#eval b32decodeImp (s2b "mzxw6ytb") true

-- ## Equivalence of functional and imperative implementations

theorem loopMut_eq_foldl (f : β → α → β) (init : β) (xs : List α) :
    loopMut f init xs = xs.foldl f init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
      rw [List.foldl_cons, ← ih (f init x)]
      simp only [loopMut]
      rw [List.forIn_cons]
      simp

theorem idRun_pure (x : α) : (pure x : Id α).run = x := rfl

theorem b32encode_imp_eq (s : Bytes) : b32encodeImp s = b32encode s := by
  simp only [b32encodeImp, b32encode, b32encodeRaw, encodeAll, loopMut_eq_foldl, idRun_pure]

theorem b32decode_imp_eq (s : Bytes) (casefold : Bool) (map01 : Option Nat) :
    b32decodeImp s casefold map01 = b32decode s casefold map01 := by
  simp only [b32decodeImp, b32decode, loopMut_eq_foldl, idRun_pure]

end Base32
