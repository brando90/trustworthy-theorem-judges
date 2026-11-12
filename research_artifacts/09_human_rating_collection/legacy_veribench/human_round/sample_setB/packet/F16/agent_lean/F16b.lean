import Mathlib

/-!
# Base32 encoding and decoding (VeriBench task `23_base32`)

A Lean 4 formalization of the Python program providing Base32 encoding and decoding
(sourced from Python's standard `base64` library).

* Python `bytes` are modelled as `List Nat` whose elements are `< 256`.
* Python Base32 output (`bytes` of ASCII characters) is modelled as `List Char`.
* `b32encode` processes the input in 5-byte chunks, turns every chunk into a 40-bit big endian
  integer, extracts eight 5-bit groups, maps them through the alphabet
  `ABCDEFGHIJKLMNOPQRSTUVWXYZ234567` and finally overwrites the trailing characters of the last
  (partial) group with `=`.
* `b32decode` optionally applies the `map01` substitution and the `casefold` upper-casing, strips
  the trailing `=` padding, looks every character up in the reverse alphabet (raising
  `Non-base32 digit found` otherwise) and consumes the resulting 5-bit groups eight bits at a time.

The file contains a functional implementation, unit tests, pre/post-conditions, proved properties,
property-based tests, a correctness theorem, an imperative implementation (`Id.run do` with mutable
state), imperative tests and a proved functional/imperative equivalence theorem.
-/

namespace «23_base32»

/-- `Except` has no `DecidableEq` instance in core; we provide one so that the unit tests about
`b32decode` can be discharged with `native_decide`. -/
instance decidableEqExcept {α β : Type} [DecidableEq α] [DecidableEq β] : DecidableEq (Except α β)
  | .ok x, .ok y =>
      if h : x = y then .isTrue (by rw [h]) else .isFalse (fun hc => h (by cases hc; rfl))
  | .error x, .error y =>
      if h : x = y then .isTrue (by rw [h]) else .isFalse (fun hc => h (by cases hc; rfl))
  | .ok _, .error _ => .isFalse (fun hc => by cases hc)
  | .error _, .ok _ => .isFalse (fun hc => by cases hc)

/-! ## Implementation (functional) -/

/-- Python's `_b32alphabet = b'ABCDEFGHIJKLMNOPQRSTUVWXYZ234567'`. -/
def alphabet : List Char :=
  ['A','B','C','D','E','F','G','H','I','J','K','L','M','N','O','P','Q','R','S','T','U','V','W',
   'X','Y','Z','2','3','4','5','6','7']

theorem alphabet_length : alphabet.length = 32 := rfl

/-- `_b32alphabet[i]`: the `i`-th Base32 digit (default `'A'` when out of range). -/
def b32Char (i : Nat) : Char := alphabet.getD i 'A'

/-- The reverse alphabet `rev_alphabet`: index of a Base32 digit, `none` if `c` is not one. -/
def b32Index (c : Char) : Option Nat :=
  let n := c.toNat
  if 65 ≤ n ∧ n < 91 then some (n - 65)
  else if 50 ≤ n ∧ n < 56 then some (n - 50 + 26)
  else none

/-- Total variant of `b32Index`, only used where validity has been established. -/
def b32Idx (c : Char) : Nat := (b32Index c).getD 0

/-- `true` iff every character of `cs` is a Base32 digit. -/
def allDigits (cs : List Char) : Bool := cs.all (fun c => (b32Index c).isSome)

/-- `true` iff `n` is a byte. -/
def isByte (n : Nat) : Bool := n < 256

/-- `true` iff every element is a byte (the content of a `bytes-like object`). -/
def allBytes (bs : List Nat) : Bool := bs.all (fun b => b < 256)

/-- Split into consecutive chunks of at most five bytes: `s[i:i+5]` for `i` in `range(0,len s,5)`. -/
def chunksOf5 : List Nat → List (List Nat)
  | [] => []
  | [a] => [[a]]
  | [a, b] => [[a, b]]
  | [a, b, c] => [[a, b, c]]
  | [a, b, c, d] => [[a, b, c, d]]
  | [a, b, c, d, e] => [[a, b, c, d, e]]
  | (a :: b :: c :: d :: e :: rest) => [a, b, c, d, e] :: chunksOf5 rest

/-- `int.from_bytes(chunk, 'big')`. -/
def bytesToNat : List Nat → Nat
  | [] => 0
  | (b :: bs) => b * 256 ^ bs.length + bytesToNat bs

/-- `chunk + b'\0' * (5 - len chunk)`: zero padding of a chunk to five bytes. -/
def pad5 (c : List Nat) : List Nat := c ++ List.replicate (5 - c.length) 0

/-- The `j`-th extracted 5-bit group: `(val >> (35 - 5*j)) & 0x1F`. -/
def idxAt (v : Nat) (j : Nat) : Nat := v / 2 ^ (35 - 5 * j) % 32

/-- The eight 5-bit groups of a 40-bit value, most significant first. -/
def indices (v : Nat) : List Nat := (List.range 8).map (idxAt v)

/-- Encode one (at most five byte) chunk into eight Base32 characters. -/
def encodeChunk (c : List Nat) : List Char := (indices (bytesToNat (pad5 c))).map b32Char

/-- `encoded.append(...)` for every chunk. -/
def encodeChunks : List (List Nat) → List Char
  | [] => []
  | (c :: cs) => encodeChunk c ++ encodeChunks cs

/-- Number of `=` characters written for a given `len s % 5` (`# Fix padding`). -/
def padCount (rem : Nat) : Nat :=
  match rem with
  | 1 => 6
  | 2 => 4
  | 3 => 3
  | 4 => 1
  | _ => 0

/-- Number of significant (non `=`) characters produced by a chunk of `L ≤ 5` bytes. -/
def keepCount (L : Nat) : Nat :=
  match L with
  | 0 => 0
  | 1 => 2
  | 2 => 4
  | 3 => 5
  | 4 => 7
  | _ => 8

/-- The `# Fix padding` block of the Python source. -/
def fixPadding (enc : List Char) (rem : Nat) : List Char :=
  enc.take (enc.length - padCount rem) ++ List.replicate (padCount rem) '='

/-- `b32encode`. -/
def b32encode (bs : List Nat) : List Char :=
  fixPadding (encodeChunks (chunksOf5 bs)) (bs.length % 5)

/-- `s.rstrip(b'=')`. -/
def rstripEq : List Char → List Char
  | [] => []
  | (c :: cs) =>
      if rstripEq cs = [] then (if c = '=' then [] else [c]) else c :: rstripEq cs

/-- `s.upper()`, used by `casefold`. -/
def toUpper (c : Char) : Char := c.toUpper

/-- The `map01` / `casefold` / `rstrip` preprocessing of `b32decode`. -/
def preprocess (s : List Char) (casefold : Bool) (map01 : Option Char) : List Char :=
  let s1 := match map01 with
    | none => s
    | some m => s.map (fun c => if c = '0' then 'O' else if c = '1' then m else c)
  let s2 := if casefold then s1.map toUpper else s1
  rstripEq s2

/-- The accumulation loop of `b32decode`. `val`/`bits` mirror the Python variables of the same
name; `val` is kept reduced modulo `2^bits`, which is equivalent because Python masks with
`0xFF` when it appends a byte. -/
def decodeLoop (val bits : Nat) (acc : List Nat) : List Char → Except String (List Nat)
  | [] => .ok acc.reverse
  | (c :: cs) =>
      match b32Index c with
      | none => .error "Non-base32 digit found"
      | some k =>
          if bits + 5 ≥ 8 then
            decodeLoop ((val * 32 + k) % 2 ^ (bits + 5 - 8)) (bits + 5 - 8)
              (((val * 32 + k) / 2 ^ (bits + 5 - 8)) % 256 :: acc) cs
          else
            decodeLoop (val * 32 + k) (bits + 5) acc cs

/-- `b32decode`. -/
def b32decode (s : List Char) (casefold : Bool) (map01 : Option Char) : Except String (List Nat) :=
  decodeLoop 0 0 [] (preprocess s casefold map01)

/-! ## Test helpers -/

/-- ASCII text as a list of bytes. -/
def bytesOf (s : String) : List Nat := s.toList.map Char.toNat

/-! ## Unit tests -/

example : b32encode [] = [] := by native_decide
example : b32encode (bytesOf "f") = "MY======".toList := by native_decide
example : b32encode (bytesOf "fo") = "MZXQ====".toList := by native_decide
example : b32encode (bytesOf "foo") = "MZXW6===".toList := by native_decide
example : b32encode (bytesOf "foob") = "MZXW6YQ=".toList := by native_decide
example : b32encode (bytesOf "fooba") = "MZXW6YTB".toList := by native_decide
example : b32encode (bytesOf "foobar") = "MZXW6YTBOI======".toList := by native_decide
example : b32encode (bytesOf "VeriBench") = "KZSXE2KCMVXGG2A=".toList := by native_decide

example : b32decode [] false none = .ok [] := by native_decide
example : b32decode "MZXW6YTB".toList false none = .ok (bytesOf "fooba") := by native_decide
example : b32decode "mzxw6ytb".toList true none = .ok (bytesOf "fooba") := by native_decide
example : b32decode "MZXW6YTBOI======".toList false none = .ok (bytesOf "foobar") := by native_decide
example : b32decode "MZXW6===".toList false none = .ok (bytesOf "foo") := by native_decide
example : b32decode "MY======".toList false none = .ok (bytesOf "f") := by native_decide
example : b32decode "MZXQ====".toList false none = .ok (bytesOf "fo") := by native_decide
example : b32decode "MZXW6YQ=".toList false none = .ok (bytesOf "foob") := by native_decide
example : b32decode (b32encode (bytesOf "VeriBench")) false none = .ok (bytesOf "VeriBench") :=
  by native_decide
-- `map01`: every `1` is replaced by the given character, every `0` by `O`.
example : b32encode [0, 0, 0, 0, 27] = "AAAAAAA3".toList := by native_decide
example : b32decode "AAAAAAA3".toList false none = .ok [0, 0, 0, 0, 27] := by native_decide
example : b32decode "AAAAA0A1".toList false (some 'L') =
    b32decode "AAAAAOAL".toList false none := by native_decide
example : b32decode "AAAAA0A1".toList false none = .error "Non-base32 digit found" :=
  by native_decide
example : b32decode "M1XW6YTB".toList false (some 'L') =
    b32decode "MLXW6YTB".toList false none := by native_decide
example : b32decode "MZXW60TB".toList false (some 'L') =
    b32decode "MZXW6OTB".toList false none := by native_decide
-- a non Base32 digit raises `binascii.Error('Non-base32 digit found')`
example : b32decode "MZXW6YTB!".toList false none = .error "Non-base32 digit found" :=
  by native_decide
example : b32decode "mzxw6ytb".toList false none = .error "Non-base32 digit found" :=
  by native_decide

#eval b32encode (bytesOf "foobar")
#eval b32encode (bytesOf "VeriBench")
#eval b32decode (b32encode (bytesOf "VeriBench")) false none
#eval b32decode "mzxw6ytb".toList true none

/-! ## Specification helpers -/

/-- `IsBytes bs` says that `bs` is the content of a Python `bytes` object. -/
def IsBytes (bs : List Nat) : Prop := ∀ b ∈ bs, b < 256

theorem IsBytes_nil : IsBytes [] := by simp [IsBytes]

theorem IsBytes_cons {b : Nat} {bs : List Nat} : IsBytes (b :: bs) ↔ b < 256 ∧ IsBytes bs := by
  simp [IsBytes]

theorem IsBytes_append {xs ys : List Nat} : IsBytes (xs ++ ys) ↔ IsBytes xs ∧ IsBytes ys := by
  simp only [IsBytes, List.mem_append]
  constructor
  · intro h
    exact ⟨fun b hb => h b (Or.inl hb), fun b hb => h b (Or.inr hb)⟩
  · rintro ⟨h1, h2⟩ b (hb | hb)
    · exact h1 b hb
    · exact h2 b hb

theorem allBytes_iff (bs : List Nat) : allBytes bs = true ↔ IsBytes bs := by
  simp [allBytes, IsBytes, List.all_eq_true]

/-- `IsDigits cs` says that every character of `cs` is a Base32 digit. -/
def IsDigits (cs : List Char) : Prop := ∀ c ∈ cs, (b32Index c).isSome = true

theorem IsDigits_nil : IsDigits [] := by simp [IsDigits]

theorem IsDigits_cons {c : Char} {cs : List Char} :
    IsDigits (c :: cs) ↔ (b32Index c).isSome = true ∧ IsDigits cs := by
  simp [IsDigits]

theorem allDigits_iff (cs : List Char) : allDigits cs = true ↔ IsDigits cs := by
  simp [allDigits, IsDigits, List.all_eq_true]

/-- Value of a list of 5-bit indices, most significant first. -/
def bitVal : List Nat → Nat
  | [] => 0
  | (i :: is) => i * 32 ^ is.length + bitVal is

/-- The 5-bit indices of a list of characters. -/
def idxs (cs : List Char) : List Nat := cs.map b32Idx

/-- `bytesOfBits V T` extracts the `T / 8` most significant bytes of the `T`-bit value `V`. -/
def bytesOfBits (V T : Nat) : List Nat :=
  (List.range (T / 8)).map (fun j => V / 2 ^ (T - 8 * (j + 1)) % 256)

/-- `bytesOfBE B L` is the big endian byte decomposition of `B` into `L` bytes. -/
def bytesOfBE (B L : Nat) : List Nat :=
  (List.range L).map (fun j => B / 2 ^ (8 * (L - 1 - j)) % 256)

/-! ## Small helpers -/

theorem map_congr_mem {α β : Type} {l : List α} {f g : α → β} (h : ∀ x ∈ l, f x = g x) :
    l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      simp only [List.map_cons]
      rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

theorem pow256 (n : Nat) : 256 ^ n = 2 ^ (8 * n) := by
  rw [show (256 : Nat) = 2 ^ 8 by decide, Nat.pow_mul]

theorem pow32 (n : Nat) : 32 ^ n = 2 ^ (5 * n) := by
  rw [show (32 : Nat) = 2 ^ 5 by decide, Nat.pow_mul]

theorem pow_two_pos (n : Nat) : 0 < 2 ^ n := Nat.pow_pos (by decide)

/-! ## The alphabet -/

theorem b32Index_b32Char_fin : ∀ i : Fin 32, b32Index (b32Char i.val) = some i.val := by decide

theorem b32Index_b32Char (i : Nat) (h : i < 32) : b32Index (b32Char i) = some i :=
  b32Index_b32Char_fin ⟨i, h⟩

theorem b32Char_ne_eq_fin : ∀ i : Fin 32, b32Char i.val ≠ '=' := by decide

theorem b32Char_ne_eq (i : Nat) (h : i < 32) : b32Char i ≠ '=' := b32Char_ne_eq_fin ⟨i, h⟩

theorem b32Char_isDigit_fin : ∀ i : Fin 32, (b32Index (b32Char i.val)).isSome = true := by decide

theorem b32Char_isDigit (i : Nat) (h : i < 32) : (b32Index (b32Char i)).isSome = true :=
  b32Char_isDigit_fin ⟨i, h⟩

theorem b32Idx_b32Char (i : Nat) (h : i < 32) : b32Idx (b32Char i) = i := by
  simp [b32Idx, b32Index_b32Char i h]

theorem b32Index_lt (c : Char) : ∀ k, b32Index c = some k → k < 32 := by
  intro k hk
  dsimp only [b32Index] at hk
  split at hk
  · injection hk with hk'
    subst hk'
    omega
  · split at hk
    · injection hk with hk'
      subst hk'
      omega
    · cases hk

theorem b32Idx_lt (c : Char) (h : (b32Index c).isSome = true) : b32Idx c < 32 := by
  cases hbc : b32Index c with
  | none => simp [hbc] at h
  | some k =>
      simp only [b32Idx, hbc, Option.getD_some]
      exact b32Index_lt c k hbc

theorem IsDigits_map_b32Char {l : List Nat} (h : ∀ i ∈ l, i < 32) : IsDigits (l.map b32Char) := by
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  simp [b32Char_isDigit i (h i hi)]

theorem idxs_map_b32Char {l : List Nat} (h : ∀ i ∈ l, i < 32) : idxs (l.map b32Char) = l := by
  have h1 : ∀ i ∈ l, (b32Idx ∘ b32Char) i = i := fun i hi => b32Idx_b32Char i (h i hi)
  simp only [idxs, List.map_map]
  rw [map_congr_mem h1]
  simp

theorem idxAt_lt (v j : Nat) : idxAt v j < 32 := Nat.mod_lt _ (by decide)

theorem indices_length (v : Nat) : (indices v).length = 8 := by simp [indices]

theorem indices_take (v m : Nat) (hm : m ≤ 8) :
    (indices v).take m = (List.range m).map (idxAt v) := by
  simp only [indices]
  rw [← List.map_take, List.take_range, Nat.min_eq_left hm]

theorem idxs_cons (c : Char) (cs : List Char) : idxs (c :: cs) = b32Idx c :: idxs cs := rfl

theorem idxs_length (cs : List Char) : (idxs cs).length = cs.length := by simp [idxs]

theorem idxs_nil : idxs [] = [] := rfl

theorem IsDigits_head {c : Char} {cs : List Char} (h : IsDigits (c :: cs)) :
    (b32Index c).isSome = true := h c (by simp)

theorem IsDigits_tail {c : Char} {cs : List Char} (h : IsDigits (c :: cs)) : IsDigits cs :=
  fun x hx => h x (by simp [hx])

theorem IsDigits_idxs_lt {c : Char} {cs : List Char} (h : IsDigits (c :: cs)) : b32Idx c < 32 :=
  b32Idx_lt c (IsDigits_head h)


/-! ## Arithmetic toolkit (powers of two, division and remainder) -/

theorem decomp (x y p q : Nat) :
    x * 2 ^ p + y = ((x % 2 ^ q) * 2 ^ p + y) + 2 ^ (p + q) * (x / 2 ^ q) := by
  have h3 : 2 ^ (p + q) = 2 ^ p * 2 ^ q := Nat.pow_add 2 p q
  have h2 : x % 2 ^ q + 2 ^ q * (x / 2 ^ q) = x := Nat.mod_add_div x (2 ^ q)
  have h6 : ((x % 2 ^ q) * 2 ^ p + y) + 2 ^ (p + q) * (x / 2 ^ q)
      = (x % 2 ^ q) * 2 ^ p + y + (2 ^ p * 2 ^ q) * (x / 2 ^ q) := by rw [h3]
  have h7 : (x % 2 ^ q) * 2 ^ p + y + (2 ^ p * 2 ^ q) * (x / 2 ^ q)
      = (x % 2 ^ q + 2 ^ q * (x / 2 ^ q)) * 2 ^ p + y := by ring
  rw [h6, h7, h2]

theorem decomp_lt (x y p q : Nat) (hy : y < 2 ^ p) : (x % 2 ^ q) * 2 ^ p + y < 2 ^ (p + q) := by
  have h5 : x % 2 ^ q < 2 ^ q := Nat.mod_lt _ (pow_two_pos q)
  calc (x % 2 ^ q) * 2 ^ p + y < (x % 2 ^ q) * 2 ^ p + 2 ^ p := Nat.add_lt_add_left hy _
    _ = (x % 2 ^ q + 1) * 2 ^ p := by ring
    _ ≤ 2 ^ q * 2 ^ p := by nlinarith [pow_two_pos p]
    _ = 2 ^ (p + q) := by rw [Nat.pow_add, Nat.mul_comm]

theorem div_pow_add_of_lt (x y p q : Nat) (hy : y < 2 ^ p) :
    (x * 2 ^ p + y) / 2 ^ (p + q) = x / 2 ^ q := by
  rw [decomp x y p q, Nat.add_mul_div_left _ _ (pow_two_pos _),
    Nat.div_eq_of_lt (decomp_lt x y p q hy), Nat.zero_add]

theorem mod_pow_add_of_lt (x y p q : Nat) (hy : y < 2 ^ p) :
    (x * 2 ^ p + y) % 2 ^ (p + q) = (x % 2 ^ q) * 2 ^ p + y := by
  rw [decomp x y p q, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (decomp_lt x y p q hy)]

theorem div_pow_self (B p q : Nat) : (B * 2 ^ p) / 2 ^ (p + q) = B / 2 ^ q :=
  div_pow_add_of_lt B 0 p q (pow_two_pos p)

theorem add_mul_pow_div_mod (x y q r : Nat) (hr : 8 ≤ r) :
    ((x * 2 ^ (q + r) + y) / 2 ^ q) % 256 = (y / 2 ^ q) % 256 := by
  have h1 : x * 2 ^ (q + r) + y = y % 2 ^ q + 2 ^ q * (y / 2 ^ q + x * 2 ^ r) := by
    have h2 : y % 2 ^ q + 2 ^ q * (y / 2 ^ q) = y := Nat.mod_add_div y (2 ^ q)
    have h3 : 2 ^ (q + r) = 2 ^ q * 2 ^ r := Nat.pow_add 2 q r
    have h4 : y % 2 ^ q + 2 ^ q * (y / 2 ^ q + x * 2 ^ r)
        = (y % 2 ^ q + 2 ^ q * (y / 2 ^ q)) + 2 ^ q * (x * 2 ^ r) := by ring
    have h5 : (y % 2 ^ q + 2 ^ q * (y / 2 ^ q)) + 2 ^ q * (x * 2 ^ r)
        = y + 2 ^ q * (2 ^ r * x) := by rw [h2]; ring
    have h6 : y + 2 ^ q * (2 ^ r * x) = x * 2 ^ (q + r) + y := by rw [h3]; ring
    rw [h4, h5, h6]
  have h4 : x * 2 ^ r = 256 * (x * 2 ^ (r - 8)) := by
    have h5 : 2 ^ r = 2 ^ (r - 8) * 2 ^ 8 := by
      have h6 : r - 8 + 8 = r := by omega
      rw [← Nat.pow_add, h6]
    rw [h5, show (2 : Nat) ^ 8 = 256 by decide]
    ring
  rw [h1, Nat.add_mul_div_left _ _ (pow_two_pos q),
    Nat.div_eq_of_lt (Nat.mod_lt _ (pow_two_pos q)), Nat.zero_add, h4,
    Nat.add_mul_mod_self_left]

theorem div_mod_pow_mod (V d e : Nat) (h : e + 8 ≤ d) :
    (V % 2 ^ d) / 2 ^ e % 256 = V / 2 ^ e % 256 := by
  have he : e ≤ d := by omega
  have h1 : 2 ^ d = 2 ^ e * 2 ^ (d - e) := by
    have h2 : e + (d - e) = d := by omega
    rw [← Nat.pow_add, h2]
  have hV : (V % 2 ^ d) / 2 ^ e + 2 ^ (d - e) * (V / 2 ^ d) = V / 2 ^ e := by
    have h6 : V % 2 ^ d + 2 ^ e * (2 ^ (d - e) * (V / 2 ^ d)) = V := by
      rw [← Nat.mul_assoc, ← h1, Nat.mod_add_div]
    have h7 : (V % 2 ^ d) / 2 ^ e + 2 ^ (d - e) * (V / 2 ^ d)
        = (V % 2 ^ d + 2 ^ e * (2 ^ (d - e) * (V / 2 ^ d))) / 2 ^ e :=
      (Nat.add_mul_div_left _ _ (pow_two_pos e)).symm
    rw [h7, h6]
  have h4 : 2 ^ (d - e) * (V / 2 ^ d) = 256 * (2 ^ (d - e - 8) * (V / 2 ^ d)) := by
    have h5 : 2 ^ (d - e) = 2 ^ (d - e - 8) * 2 ^ 8 := by
      have h6 : d - e - 8 + 8 = d - e := by omega
      rw [← Nat.pow_add, h6]
    rw [h5, show (2 : Nat) ^ 8 = 256 by decide]
    ring
  rw [← hV, h4, ← Nat.add_mul_mod_self_left]

/-! ## `bytesToNat` -/

theorem bytesToNat_lt : ∀ (c : List Nat), IsBytes c → bytesToNat c < 256 ^ c.length := by
  intro c
  induction c with
  | nil => intro _; simp [bytesToNat]
  | cons b cs ih =>
      intro h
      obtain ⟨hb, hcs⟩ := IsBytes_cons.mp h
      have h1 : bytesToNat cs < 256 ^ cs.length := ih hcs
      have hP : 0 < 256 ^ cs.length := Nat.pow_pos (by decide)
      simp only [bytesToNat, List.length_cons]
      calc b * 256 ^ cs.length + bytesToNat cs
          < b * 256 ^ cs.length + 256 ^ cs.length := Nat.add_lt_add_left h1 _
        _ = (b + 1) * 256 ^ cs.length := by ring
        _ ≤ 256 * 256 ^ cs.length := by nlinarith
        _ = 256 ^ (cs.length + 1) := by rw [Nat.pow_add, Nat.pow_one, Nat.mul_comm]

theorem bytesToNat_lt_pow (c : List Nat) (h : IsBytes c) : bytesToNat c < 2 ^ (8 * c.length) := by
  have h1 := bytesToNat_lt c h
  rwa [pow256] at h1

theorem bytesToNat_replicate_zero : ∀ k : Nat, bytesToNat (List.replicate k 0) = 0 := by
  intro k
  induction k with
  | zero => simp [bytesToNat]
  | succ k ih => simp [List.replicate_succ, bytesToNat, ih]

theorem bytesToNat_append_zeros : ∀ (c : List Nat) (k : Nat),
    bytesToNat (c ++ List.replicate k 0) = bytesToNat c * 256 ^ k := by
  intro c
  induction c with
  | nil => intro k; simp [bytesToNat, bytesToNat_replicate_zero]
  | cons b cs ih =>
      intro k
      simp only [List.cons_append, bytesToNat, List.length_append, List.length_replicate,
        ih k, Nat.pow_add]
      ring

theorem bytesToNat_pad5 (c : List Nat) :
    bytesToNat (pad5 c) = bytesToNat c * 2 ^ (8 * (5 - c.length)) := by
  simp only [pad5, bytesToNat_append_zeros, pow256]

theorem bytesToNat_pad5_lt (c : List Nat) (h : c.length ≤ 5) (hb : IsBytes c) :
    bytesToNat (pad5 c) < 2 ^ 40 := by
  rw [bytesToNat_pad5]
  have h1 : bytesToNat c < 2 ^ (8 * c.length) := bytesToNat_lt_pow c hb
  have h2 : 8 * c.length + 8 * (5 - c.length) = 40 := by omega
  calc bytesToNat c * 2 ^ (8 * (5 - c.length))
      < 2 ^ (8 * c.length) * 2 ^ (8 * (5 - c.length)) :=
        Nat.mul_lt_mul_of_pos_right h1 (pow_two_pos _)
    _ = 2 ^ 40 := by rw [← Nat.pow_add, h2]

/-! ## `bitVal` -/

theorem bitVal_nil : bitVal [] = 0 := rfl

theorem bitVal_cons (i : Nat) (is : List Nat) :
    bitVal (i :: is) = i * 32 ^ is.length + bitVal is := rfl

theorem bitVal_append_single : ∀ (xs : List Nat) (x : Nat),
    bitVal (xs ++ [x]) = bitVal xs * 32 + x := by
  intro xs
  induction xs with
  | nil => intro x; simp [bitVal]
  | cons y ys ih =>
      intro x
      simp only [List.cons_append, bitVal, List.length_append, List.length_singleton,
        List.length_nil, ih x, Nat.pow_add, Nat.pow_one]
      ring

theorem bitVal_lt : ∀ (is : List Nat), (∀ i ∈ is, i < 32) → bitVal is < 2 ^ (5 * is.length) := by
  intro is
  induction is with
  | nil => intro _; simp [bitVal, pow_two_pos]
  | cons i is ih =>
      intro h
      have hi : i < 32 := h i (by simp)
      have his : ∀ j ∈ is, j < 32 := fun j hj => h j (by simp [hj])
      have h1 : bitVal is < 2 ^ (5 * is.length) := ih his
      have h3 : 2 ^ (5 * is.length) = 32 ^ is.length := (pow32 _).symm
      have hP : 0 < 32 ^ is.length := Nat.pow_pos (by decide)
      have h4 : 2 ^ (5 * (is.length + 1)) = 32 * 32 ^ is.length := by
        have h5 : 5 * (is.length + 1) = 5 * is.length + 5 := by ring
        rw [h5, Nat.pow_add, show (2 : Nat) ^ 5 = 32 by decide, h3, Nat.mul_comm]
      simp only [bitVal, List.length_cons, h4]
      calc i * 32 ^ is.length + bitVal is
          < i * 32 ^ is.length + 32 ^ is.length := by
            rw [← h3]; exact Nat.add_lt_add_left h1 _
        _ = (i + 1) * 32 ^ is.length := by ring
        _ ≤ 32 * 32 ^ is.length := by nlinarith

theorem bitVal_idxs_lt {cs : List Char} (h : IsDigits cs) :
    bitVal (idxs cs) < 2 ^ (5 * cs.length) := by
  have h1 : ∀ i ∈ idxs cs, i < 32 := by
    intro i hi
    rw [idxs, List.mem_map] at hi
    obtain ⟨c, hc, rfl⟩ := hi
    exact b32Idx_lt c (h c hc)
  have h2 := bitVal_lt (idxs cs) h1
  rwa [idxs_length] at h2

theorem bitVal_range_idxAt (v : Nat) (hv : v < 2 ^ 40) :
    ∀ m : Nat, m ≤ 8 → bitVal ((List.range m).map (idxAt v)) = v / 2 ^ (40 - 5 * m) := by
  intro m
  induction m with
  | zero =>
      intro _
      have h : 40 - 5 * 0 = 40 := by decide
      rw [h, List.range_zero, List.map_nil, bitVal_nil]
      exact (Nat.div_eq_of_lt hv).symm
  | succ m ih =>
      intro hm
      have hml : m ≤ 8 := by omega
      have e1 : 40 - 5 * (m + 1) = 35 - 5 * m := by omega
      have e2 : 40 - 5 * m = (35 - 5 * m) + 5 := by omega
      have h3 : 2 ^ (35 - 5 * m) * 32 = 2 ^ ((35 - 5 * m) + 5) := by
        rw [show (32 : Nat) = 2 ^ 5 by decide, ← Nat.pow_add]
      rw [List.range_succ, List.map_append, List.map_singleton, bitVal_append_single,
        ih hml, e1, e2, idxAt, ← h3, ← Nat.div_div_eq_div_mul]
      have h4 := Nat.mod_add_div (v / 2 ^ (35 - 5 * m)) 32
      omega


/-! ## `bytesOfBits` -/

theorem bytesOfBits_zero (V : Nat) : bytesOfBits V 0 = [] := by simp [bytesOfBits]

theorem bytesOfBits_cons (V T : Nat) (hT : 8 ≤ T) :
    bytesOfBits V T = (V / 2 ^ (T - 8) % 256) :: bytesOfBits (V % 2 ^ (T - 8)) (T - 8) := by
  have hdiv : T / 8 = (T - 8) / 8 + 1 := by
    have h2 := Nat.add_div_right (T - 8) (by decide : 0 < (8 : Nat))
    omega
  have hcong : ∀ j ∈ List.range ((T - 8) / 8),
      V / 2 ^ (T - 8 * (Nat.succ j + 1)) % 256 =
        (V % 2 ^ (T - 8)) / 2 ^ ((T - 8) - 8 * (j + 1)) % 256 := by
    intro j hj
    have hjb : j < (T - 8) / 8 := List.mem_range.mp hj
    have hmul := Nat.mul_div_le (T - 8) 8
    have h2 : (T - 8) - 8 * (j + 1) = T - 8 * (Nat.succ j + 1) := by omega
    rw [h2]
    exact (div_mod_pow_mod V (T - 8) (T - 8 * (Nat.succ j + 1)) (by omega)).symm
  have ehead : T - 8 * (0 + 1) = T - 8 := by omega
  have ecomp : ((fun j => V / 2 ^ (T - 8 * (j + 1)) % 256) ∘ Nat.succ)
      = (fun j => V / 2 ^ (T - 8 * (Nat.succ j + 1)) % 256) := by funext j; rfl
  simp only [bytesOfBits, hdiv, List.range_succ_eq_map, List.map_cons, List.map_map, ecomp, ehead]
  congr 1
  exact map_congr_mem hcong

theorem bytesOfBits_append (V1 T1 V2 T2 : Nat) (hV2 : V2 < 2 ^ T2) (h8 : 8 ∣ T1) :
    bytesOfBits (V1 * 2 ^ T2 + V2) (T1 + T2) = bytesOfBits V1 T1 ++ bytesOfBits V2 T2 := by
  obtain ⟨k, hk⟩ := h8
  subst hk
  have hk8 : 8 * k / 8 = k := by omega
  have hdiv : (8 * k + T2) / 8 = k + T2 / 8 := by
    have h1 : 8 * k + T2 = T2 + 8 * k := by ring
    rw [h1, Nat.add_mul_div_left _ _ (by decide : 0 < (8 : Nat))]
    ring
  have ecomp : ((fun j => (V1 * 2 ^ T2 + V2) / 2 ^ (8 * k + T2 - 8 * (j + 1)) % 256)
      ∘ (fun x => k + x))
      = (fun j => (V1 * 2 ^ T2 + V2) / 2 ^ (8 * k + T2 - 8 * (k + j + 1)) % 256) := by
    funext j; rfl
  simp only [bytesOfBits, hdiv, List.range_add, List.map_append, List.map_map, ecomp, hk8]
  congr 1
  · apply map_congr_mem
    intro j hj
    have hjk : j < k := List.mem_range.mp hj
    have he : 8 * k + T2 - 8 * (j + 1) = T2 + (8 * k - 8 * (j + 1)) := by omega
    rw [he, div_pow_add_of_lt V1 V2 T2 (8 * k - 8 * (j + 1)) hV2]
  · apply map_congr_mem
    intro j hj
    have hj2 : j < T2 / 8 := List.mem_range.mp hj
    have hmul := Nat.mul_div_le T2 8
    have he : 8 * k + T2 - 8 * (k + j + 1) = T2 - 8 * (j + 1) := by omega
    rw [he]
    have hqr : (T2 - 8 * (j + 1)) + 8 * (j + 1) = T2 := by omega
    have hr : 8 ≤ 8 * (j + 1) := by omega
    have hgoal := add_mul_pow_div_mod V1 V2 (T2 - 8 * (j + 1)) (8 * (j + 1)) hr
    rwa [hqr] at hgoal

theorem bytesOfBits_shift (B T L : Nat) (h1 : 8 * L ≤ T) (h2 : T < 8 * L + 8) :
    bytesOfBits (B * 2 ^ (T - 8 * L)) T = bytesOfBE B L := by
  have hdiv : T / 8 = L := by omega
  simp only [bytesOfBits, bytesOfBE, hdiv]
  apply map_congr_mem
  intro j hj
  have hjl : j < L := List.mem_range.mp hj
  have he : T - 8 * (j + 1) = (T - 8 * L) + 8 * (L - 1 - j) := by omega
  rw [he, div_pow_self]

theorem bytesOfBE_bytesToNat : ∀ (c : List Nat), IsBytes c →
    bytesOfBE (bytesToNat c) c.length = c := by
  intro c
  induction c with
  | nil => intro _; simp [bytesOfBE, bytesToNat]
  | cons b cs ih =>
      intro h
      obtain ⟨hb, hcs⟩ := IsBytes_cons.mp h
      have hIH := ih hcs
      have hB : bytesToNat cs < 2 ^ (8 * cs.length) := bytesToNat_lt_pow cs hcs
      have hhead : (b * 2 ^ (8 * cs.length) + bytesToNat cs) / 2 ^ (8 * cs.length) % 256 = b := by
        have h4 : b * 2 ^ (8 * cs.length) + bytesToNat cs
            = bytesToNat cs + 2 ^ (8 * cs.length) * b := by ring
        rw [h4, Nat.add_mul_div_left _ _ (pow_two_pos _), Nat.div_eq_of_lt hB, Nat.zero_add,
          Nat.mod_eq_of_lt hb]
      have htail : (List.range cs.length).map
            (fun j => (b * 2 ^ (8 * cs.length) + bytesToNat cs) /
                2 ^ (8 * (cs.length - Nat.succ j)) % 256)
          = (List.range cs.length).map
              (fun j => bytesToNat cs / 2 ^ (8 * (cs.length - 1 - j)) % 256) := by
        apply map_congr_mem
        intro j hj
        have hjc : j < cs.length := List.mem_range.mp hj
        have e2 : cs.length - Nat.succ j = cs.length - 1 - j := by omega
        rw [e2]
        have hqr : 8 * (cs.length - 1 - j) + 8 * (j + 1) = 8 * cs.length := by omega
        have hr : 8 ≤ 8 * (j + 1) := by omega
        have hgoal :=
          add_mul_pow_div_mod b (bytesToNat cs) (8 * (cs.length - 1 - j)) (8 * (j + 1)) hr
        rwa [hqr] at hgoal
      have ecomp : ((fun j => (b * 2 ^ (8 * cs.length) + bytesToNat cs) /
              2 ^ (8 * (cs.length - j)) % 256) ∘ Nat.succ)
          = (fun j => (b * 2 ^ (8 * cs.length) + bytesToNat cs) /
              2 ^ (8 * (cs.length - Nat.succ j)) % 256) := by funext j; rfl
      have hcons :
          (List.range (cs.length + 1)).map
              (fun j => (b * 2 ^ (8 * cs.length) + bytesToNat cs) /
                  2 ^ (8 * (cs.length - j)) % 256)
            = b :: (List.range cs.length).map
                (fun j => bytesToNat cs / 2 ^ (8 * (cs.length - 1 - j)) % 256) := by
        rw [List.range_succ_eq_map, List.map_cons, List.map_map, ecomp]
        rw [show cs.length - 0 = cs.length by omega, hhead, htail]
      have hgoal : bytesOfBE (bytesToNat (b :: cs)) (b :: cs).length =
          (List.range (cs.length + 1)).map
            (fun j => (b * 2 ^ (8 * cs.length) + bytesToNat cs) /
                2 ^ (8 * (cs.length - j)) % 256) := by
        simp [bytesOfBE, bytesToNat, List.length_cons, pow256]
      rw [hgoal, hcons, ← bytesOfBE, hIH]

/-! ## Specification of the decoding loop -/

theorem decodeLoop_error (val bits : Nat) (acc : List Nat) :
    ∀ cs : List Char, (∃ c ∈ cs, b32Index c = none) →
      decodeLoop val bits acc cs = .error "Non-base32 digit found" := by
  intro cs
  induction cs generalizing val bits acc with
  | nil => intro h; exact absurd h (by simp)
  | cons c rest ih =>
      intro h
      cases hbc : b32Index c with
      | none => simp [decodeLoop, hbc]
      | some k =>
          obtain ⟨x, hx, hxnone⟩ := h
          have hxc : x ≠ c := by
            intro hxc
            rw [hxc, hbc] at hxnone
            cases hxnone
          have hxr : x ∈ rest := by
            simp only [List.mem_cons] at hx
            cases hx with
            | inl h1 => exact absurd h1 hxc
            | inr h2 => exact h2
          simp only [decodeLoop, hbc]
          split
          · exact ih _ _ _ ⟨x, hxr, hxnone⟩
          · exact ih _ _ _ ⟨x, hxr, hxnone⟩

theorem decodeLoop_spec (val bits : Nat) (acc : List Nat) :
    ∀ cs : List Char, bits < 8 → val < 2 ^ bits → IsDigits cs →
      decodeLoop val bits acc cs =
        .ok (acc.reverse ++
          bytesOfBits (val * 32 ^ cs.length + bitVal (idxs cs)) (bits + 5 * cs.length)) := by
  intro cs
  induction cs generalizing val bits acc with
  | nil =>
      intro hb hv hd
      have h : bits / 8 = 0 := Nat.div_eq_of_lt hb
      simp [decodeLoop, bytesOfBits, idxs, bitVal, h]
  | cons c rest ih =>
      intro hb hv hd
      have hdc : (b32Index c).isSome = true := IsDigits_head hd
      have hdr : IsDigits rest := IsDigits_tail hd
      cases hbc : b32Index c with
      | none =>
          have h' : (b32Index c).isSome = true := hdc
          rw [hbc] at h'
          simp at h'
      | some k =>
          have hkb : k < 32 := b32Index_lt c k hbc
          have hidx : idxs (c :: rest) = k :: idxs rest := by simp [idxs, b32Idx, hbc]
          have hbit : bitVal (idxs (c :: rest)) = k * 32 ^ rest.length + bitVal (idxs rest) := by
            rw [hidx, bitVal_cons]
            simp only [idxs, List.length_map]
          have hR : bitVal (idxs rest) < 2 ^ (5 * rest.length) := bitVal_idxs_lt hdr
          have hV : val * 32 ^ (rest.length + 1) + bitVal (idxs (c :: rest))
              = (val * 32 + k) * 32 ^ rest.length + bitVal (idxs rest) := by
            rw [hbit, show 32 ^ (rest.length + 1) = 32 ^ rest.length * 32 by
                rw [Nat.pow_add, Nat.pow_one]]
            ring
          by_cases he : bits + 5 ≥ 8
          · have hnewbits : bits + 5 - 8 < 8 := by omega
            have hnewval : (val * 32 + k) % 2 ^ (bits + 5 - 8) < 2 ^ (bits + 5 - 8) :=
              Nat.mod_lt _ (pow_two_pos _)
            have hT : bits + 5 * (rest.length + 1) = (bits + 5 - 8) + 5 * rest.length + 8 :=
              by omega
            have e8 : ((bits + 5 - 8) + 5 * rest.length + 8) - 8
                = (bits + 5 - 8) + 5 * rest.length := by omega
            have hmod : ((val * 32 + k) % 2 ^ (bits + 5 - 8)) * 32 ^ rest.length
                  + bitVal (idxs rest)
                = ((val * 32 + k) * 32 ^ rest.length + bitVal (idxs rest)) %
                    2 ^ ((bits + 5 - 8) + 5 * rest.length) := by
              have hsh : bits + 5 - 8 = bits - 3 := by omega
              rw [hsh]
              have heq : (bits - 3) + 5 * rest.length = 5 * rest.length + (bits - 3) := by ring
              rw [pow32, heq, mod_pow_add_of_lt _ _ _ _ hR]
            have hdiv : ((val * 32 + k) * 32 ^ rest.length + bitVal (idxs rest)) /
                    2 ^ ((bits + 5 - 8) + 5 * rest.length) =
                  (val * 32 + k) / 2 ^ (bits + 5 - 8) := by
              have hsh : bits + 5 - 8 = bits - 3 := by omega
              rw [hsh]
              have heq : (bits - 3) + 5 * rest.length = 5 * rest.length + (bits - 3) := by ring
              rw [pow32, heq, div_pow_add_of_lt _ _ _ _ hR]
            have key : bytesOfBits (val * 32 ^ (rest.length + 1) + bitVal (idxs (c :: rest)))
                    (bits + 5 * (rest.length + 1))
                = [((val * 32 + k) / 2 ^ (bits + 5 - 8)) % 256] ++
                  bytesOfBits (((val * 32 + k) % 2 ^ (bits + 5 - 8)) * 32 ^ rest.length
                    + bitVal (idxs rest)) ((bits + 5 - 8) + 5 * rest.length) := by
              rw [hV, hT, bytesOfBits_cons _ _ (by omega), e8, hdiv, hmod,
                ← List.singleton_append]
            simp only [decodeLoop, hbc, if_pos he, List.length_cons]
            rw [ih ((val * 32 + k) % 2 ^ (bits + 5 - 8)) (bits + 5 - 8)
              (((val * 32 + k) / 2 ^ (bits + 5 - 8)) % 256 :: acc) hnewbits hnewval hdr]
            rw [List.reverse_cons, List.append_assoc, ← key]
          · have hnewbits : bits + 5 < 8 := by omega
            have hnewval : val * 32 + k < 2 ^ (bits + 5) := by
              have h1 : val * 32 + k < 2 ^ bits * 32 :=
                calc val * 32 + k < val * 32 + 32 := Nat.add_lt_add_left hkb _
                  _ = (val + 1) * 32 := by ring
                  _ ≤ 2 ^ bits * 32 := by nlinarith
              have h2 : 2 ^ bits * 32 = 2 ^ (bits + 5) := by
                rw [show (32 : Nat) = 2 ^ 5 by decide, ← Nat.pow_add]
              rwa [h2] at h1
            have hT : bits + 5 * (rest.length + 1) = (bits + 5) + 5 * rest.length := by omega
            simp only [decodeLoop, hbc, if_neg he, List.length_cons]
            rw [ih (val * 32 + k) (bits + 5) acc hnewbits hnewval hdr, hV, hT]


/-! ## Padding counters -/

theorem keepCount_le (L : Nat) (h : L ≤ 5) : keepCount L ≤ 8 := by
  have : L = 0 ∨ L = 1 ∨ L = 2 ∨ L = 3 ∨ L = 4 ∨ L = 5 := by omega
  rcases this with (rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

theorem keepCount_bounds (L : Nat) (h1 : 1 ≤ L) (h5 : L ≤ 5) :
    8 * L ≤ 5 * keepCount L ∧ 5 * keepCount L < 8 * L + 8 := by
  have : L = 1 ∨ L = 2 ∨ L = 3 ∨ L = 4 ∨ L = 5 := by omega
  rcases this with (rfl | rfl | rfl | rfl | rfl) <;> simp [keepCount]

theorem padCount_keepCount (r : Nat) (h1 : 1 ≤ r) (h4 : r ≤ 4) :
    padCount r + keepCount r = 8 := by
  have : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
  rcases this with (rfl | rfl | rfl | rfl) <;> simp [padCount, keepCount]

theorem padCount_zero : padCount 0 = 0 := rfl

theorem mul_pow_div_pow (x p q : Nat) : (x * 2 ^ (p + q)) / 2 ^ p = x * 2 ^ q := by
  have h1 : x * 2 ^ (p + q) = 2 ^ p * (x * 2 ^ q) := by rw [Nat.pow_add]; ring
  rw [h1, Nat.mul_div_cancel_left _ (pow_two_pos p)]

/-! ## `bitVal` on appends -/

theorem bitVal_append : ∀ (xs ys : List Nat),
    bitVal (xs ++ ys) = bitVal xs * 32 ^ ys.length + bitVal ys := by
  intro xs
  induction xs with
  | nil => intro ys; simp [bitVal]
  | cons x xs ih =>
      intro ys
      simp only [List.cons_append, bitVal, List.length_append, ih ys, Nat.pow_add]
      ring

/-! ## `encodeChunk` / `encodeChunks` -/

theorem encodeChunk_length (c : List Nat) : (encodeChunk c).length = 8 := by
  simp [encodeChunk, indices]

theorem IsDigits_encodeChunk (c : List Nat) : IsDigits (encodeChunk c) := by
  apply IsDigits_map_b32Char
  intro i hi
  rw [indices, List.mem_map] at hi
  obtain ⟨j, _, hj⟩ := hi
  rw [← hj]
  exact idxAt_lt _ _

theorem encodeChunk_ne_eq (c : List Nat) : ∀ x ∈ encodeChunk c, x ≠ '=' := by
  intro x hx
  rw [encodeChunk, List.mem_map] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [indices, List.mem_map] at hi
  obtain ⟨j, _, hj⟩ := hi
  rw [← hj]
  exact b32Char_ne_eq _ (idxAt_lt _ _)

theorem idxs_encodeChunk_take (c : List Nat) (m : Nat) (hm : m ≤ 8) :
    idxs ((encodeChunk c).take m) = (List.range m).map (idxAt (bytesToNat (pad5 c))) := by
  have h1 : (encodeChunk c).take m
      = ((List.range m).map (idxAt (bytesToNat (pad5 c)))).map b32Char := by
    simp only [encodeChunk, ← List.map_take, indices_take _ _ hm]
  have h2 : ∀ i ∈ (List.range m).map (idxAt (bytesToNat (pad5 c))), i < 32 := by
    intro i hi
    rw [List.mem_map] at hi
    obtain ⟨j, _, rfl⟩ := hi
    exact idxAt_lt _ _
  rw [h1, idxs_map_b32Char h2]

theorem encodeChunks_nil : encodeChunks [] = [] := rfl

theorem encodeChunks_cons (c : List Nat) (cs : List (List Nat)) :
    encodeChunks (c :: cs) = encodeChunk c ++ encodeChunks cs := rfl

theorem encodeChunks_append : ∀ (xs ys : List (List Nat)),
    encodeChunks (xs ++ ys) = encodeChunks xs ++ encodeChunks ys
  | [], ys => by simp [encodeChunks]
  | (x :: xs), ys => by simp [encodeChunks, encodeChunks_append xs ys]

theorem encodeChunks_length : ∀ (cs : List (List Nat)), (encodeChunks cs).length = 8 * cs.length
  | [] => by simp [encodeChunks]
  | (c :: cs) => by
      simp only [encodeChunks, List.length_append, encodeChunk_length, List.length_cons,
        encodeChunks_length cs]
      omega

theorem IsDigits_encodeChunks : ∀ (cs : List (List Nat)), IsDigits (encodeChunks cs)
  | [] => IsDigits_nil
  | (c :: cs) => by
      intro x hx
      simp only [encodeChunks, List.mem_append] at hx
      cases hx with
      | inl h => exact IsDigits_encodeChunk c x h
      | inr h => exact IsDigits_encodeChunks cs x h

theorem encodeChunks_ne_eq : ∀ (cs : List (List Nat)), ∀ x ∈ encodeChunks cs, x ≠ '='
  | [] => by simp [encodeChunks]
  | (c :: cs) => by
      intro x hx
      simp only [encodeChunks, List.mem_append] at hx
      cases hx with
      | inl h => exact encodeChunk_ne_eq c x h
      | inr h => exact encodeChunks_ne_eq cs x h

theorem flatten_length_five : ∀ (full : List (List Nat)), (∀ c ∈ full, c.length = 5) →
    full.flatten.length = 5 * full.length
  | [] => by intro _; simp
  | (c :: cs) => by
      intro h
      have hc : c.length = 5 := h c (by simp)
      have hcs : ∀ x ∈ cs, x.length = 5 := fun x hx => h x (by simp [hx])
      simp only [List.flatten_cons, List.length_append, List.length_cons,
        flatten_length_five cs hcs, hc]
      omega

/-! ## `fixPadding` -/

theorem fixPadding_zero (enc : List Char) : fixPadding enc 0 = enc := by
  simp [fixPadding, padCount, List.take_length]

theorem take_le_self {α : Type} (X : List α) (n : Nat) (h : X.length ≤ n) : X.take n = X := by
  have h4 := List.take_append_drop n X
  have h5 : X.drop n = [] := List.drop_eq_nil_of_le h
  rw [h5, List.append_nil] at h4
  exact h4

theorem fixPadding_append (X Y : List Char) (r : Nat) (h : padCount r ≤ Y.length) :
    fixPadding (X ++ Y) r = X ++ fixPadding Y r := by
  have h1 : (X ++ Y).length - padCount r = X.length + (Y.length - padCount r) := by
    simp only [List.length_append]
    omega
  have h2 : X.length + (Y.length - padCount r) - X.length = Y.length - padCount r := by omega
  have h3 : X.take (X.length + (Y.length - padCount r)) = X :=
    take_le_self X _ (by omega)
  simp only [fixPadding, h1, List.take_append, h2, h3]
  rw [← List.append_assoc]

/-! ## `rstripEq` -/

theorem rstripEq_nil : rstripEq [] = [] := rfl

theorem rstripEq_cons (c : Char) (cs : List Char) :
    rstripEq (c :: cs)
      = if rstripEq cs = [] then (if c = '=' then [] else [c]) else c :: rstripEq cs := rfl

theorem rstripEq_eq_self : ∀ (cs : List Char), (∀ x ∈ cs, x ≠ '=') → rstripEq cs = cs := by
  intro cs
  induction cs with
  | nil => intro _; rfl
  | cons c cs ih =>
      intro h
      have hc : c ≠ '=' := h c (by simp)
      have hcs : ∀ x ∈ cs, x ≠ '=' := fun x hx => h x (by simp [hx])
      have hIH := ih hcs
      by_cases h0 : rstripEq cs = []
      · have h1 : cs = [] := by rw [hIH] at h0; exact h0
        subst h1
        simp [rstripEq, hc]
      · simp [rstripEq, h0, hIH]

theorem rstripEq_append_eq (ys : List Char) : rstripEq (ys ++ ['=']) = rstripEq ys := by
  induction ys with
  | nil => simp [rstripEq]
  | cons c cs ih =>
      show rstripEq (c :: (cs ++ ['='])) = rstripEq (c :: cs)
      by_cases h0 : rstripEq (cs ++ ['=']) = []
      · have h1 : rstripEq cs = [] := by rw [ih] at h0; exact h0
        simp [rstripEq, h0, h1]
      · have h1 : rstripEq cs ≠ [] := by rw [ih] at h0; exact h0
        simp [rstripEq, h0, h1, ih]

theorem rstripEq_append_replicate (xs : List Char) (k : Nat) :
    rstripEq (xs ++ List.replicate k '=') = rstripEq xs := by
  induction k generalizing xs with
  | zero => simp
  | succ k ih =>
      have e : xs ++ List.replicate (k + 1) '=' = (xs ++ ['=']) ++ List.replicate k '=' := by
        rw [List.replicate_succ, ← List.singleton_append, ← List.append_assoc]
      rw [e, ih (xs ++ ['=']), rstripEq_append_eq]

theorem rstripEq_append_of_ne (xs ys : List Char) (h : ∀ x ∈ xs, x ≠ '=') :
    rstripEq (xs ++ ys) = xs ++ rstripEq ys := by
  induction xs generalizing ys with
  | nil => simp
  | cons c cs ih =>
      have hc : c ≠ '=' := h c (by simp)
      have hcs : ∀ x ∈ cs, x ≠ '=' := fun x hx => h x (by simp [hx])
      have hIH := ih hcs
      rw [List.cons_append]
      by_cases h0 : rstripEq (cs ++ ys) = []
      · have h1 : cs ++ rstripEq ys = [] := by rw [← hIH, h0]
        simp [rstripEq, h0, h1, hc]
      · have h1 : cs ++ rstripEq ys ≠ [] := by rw [← hIH]; exact h0
        simp [rstripEq, h0, h1, hIH]

/-! ## `preprocess` -/

theorem preprocess_false_none (s : List Char) : preprocess s false none = rstripEq s := by
  simp [preprocess]

theorem preprocess_casefold_none (s : List Char) :
    preprocess s true none = rstripEq (s.map toUpper) := by
  simp [preprocess]

theorem preprocess_map01 (s : List Char) (casefold : Bool) (m : Char) :
    preprocess s casefold (some m)
      = preprocess (s.map (fun c => if c = '0' then 'O' else if c = '1' then m else c))
          casefold none := rfl

/-! ## `chunksOf5` -/

theorem chunksOf5_cons5 (a b c d e : Nat) (rest : List Nat) :
    chunksOf5 (a :: b :: c :: d :: e :: rest) = [a, b, c, d, e] :: chunksOf5 rest := by
  simp [chunksOf5]

theorem chunksOf5_eq (bs : List Nat) :
    ∃ (full : List (List Nat)) (last : List Nat),
      chunksOf5 bs = full ++ (if last = [] then [] else [last]) ∧
      (∀ c ∈ full, c.length = 5) ∧
      last.length < 5 ∧
      bs = full.flatten ++ last := by
  have key : ∀ n : Nat, ∀ l : List Nat, l.length = n →
      ∃ (full : List (List Nat)) (last : List Nat),
        chunksOf5 l = full ++ (if last = [] then [] else [last]) ∧
        (∀ c ∈ full, c.length = 5) ∧ last.length < 5 ∧ l = full.flatten ++ last := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih l hlen
    cases l with
    | nil => refine ⟨[], [], ?_, ?_, ?_, ?_⟩ <;> simp [chunksOf5]
    | cons a t =>
        cases t with
        | nil => refine ⟨[], [a], ?_, ?_, ?_, ?_⟩ <;> simp [chunksOf5]
        | cons b t2 =>
            cases t2 with
            | nil => refine ⟨[], [a, b], ?_, ?_, ?_, ?_⟩ <;> simp [chunksOf5]
            | cons c t3 =>
                cases t3 with
                | nil => refine ⟨[], [a, b, c], ?_, ?_, ?_, ?_⟩ <;> simp [chunksOf5]
                | cons d t4 =>
                    cases t4 with
                    | nil => refine ⟨[], [a, b, c, d], ?_, ?_, ?_, ?_⟩ <;> simp [chunksOf5]
                    | cons e t5 =>
                        cases t5 with
                        | nil =>
                            refine ⟨[[a, b, c, d, e]], [], ?_, ?_, ?_, ?_⟩ <;>
                              simp [chunksOf5]
                        | cons f rest =>
                            have hlt : (f :: rest).length < n := by
                              simp only [List.length_cons] at hlen
                              omega
                            obtain ⟨full, last, h1, h2, h3, h4⟩ :=
                              ih (f :: rest).length hlt (f :: rest) rfl
                            refine ⟨[a, b, c, d, e] :: full, last, ?_, ?_, h3, ?_⟩
                            · simp [chunksOf5, h1]
                            · simp [h2]
                            · simp [h4, List.flatten_cons]
  exact key bs.length bs rfl
end «23_base32»
