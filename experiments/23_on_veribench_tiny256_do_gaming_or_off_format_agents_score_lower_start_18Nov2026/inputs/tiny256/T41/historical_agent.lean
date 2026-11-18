import Mathlib
namespace Agent

/-!
# HumanEval/50 — `encode_shift` / `decode_shift`

Lean 4 formalization of the Python program `humaneval_50_encode_shift.py`.

* `encode_shift s` shifts every character of `s` forward by 5 positions in the
  26-letter alphabet: `chr(((ord(ch) + 5 - ord('a')) % 26) + ord('a'))`.
* `decode_shift s` shifts every character backward by 5 positions:
  `chr(((ord(ch) - 5 - ord('a')) % 26) + ord('a'))`.

Python's `%` with a positive modulus always returns a non-negative result, which
coincides with Lean's `Int.emod` (`%` on `Int`); the arithmetic is therefore
translated on `Int` and converted back to a code point with `Int.toNat` and
`Char.ofNat` (the result always lies in `[97, 122]`, so it is a valid code point
and `Char.ofNat` is exact, just like Python's `chr`).

The Python `check` harness asserts that `decode_shift` inverts `encode_shift` on
random strings of lowercase ASCII letters; this is the main correctness theorem.
-/

namespace humaneval_50_encode_shift

/-! ## Functional implementation -/

/-- Python `((n + k - ord('a')) % 26) + ord('a')` on the code point `n`
(`ord('a') = 97`), computed on `Int` so that `%` is non-negative exactly like
Python's `%` with a positive modulus. The result is always in `[97, 122]`. -/
def shiftCode (k : Int) (n : Nat) : Nat :=
  ((((n : Int) + k - 97) % 26) + 97).toNat

/-- Python `chr(((ord(ch) + k - ord('a')) % 26) + ord('a'))`. -/
def shiftChar (k : Int) (ch : Char) : Char :=
  Char.ofNat (shiftCode k ch.toNat)

/-- Python `encode_shift`: shift every character forward by 5. -/
def encode_shift (s : String) : String :=
  String.mk (s.toList.map (shiftChar 5))

/-- Python `decode_shift`: shift every character backward by 5. -/
def decode_shift (s : String) : String :=
  String.mk (s.toList.map (shiftChar (-5)))

/-! ## Unit tests -/

example : encode_shift "abc" = "fgh" := by native_decide
example : encode_shift "xyz" = "cde" := by native_decide
example : encode_shift "" = "" := by native_decide
example : encode_shift "hello" = "mjqqt" := by native_decide
example : decode_shift "fgh" = "abc" := by native_decide
example : decode_shift "cde" = "xyz" := by native_decide
example : decode_shift "mjqqt" = "hello" := by native_decide
example : decode_shift (encode_shift "hello") = "hello" := by native_decide
example : decode_shift (encode_shift "veribench") = "veribench" := by native_decide
example : encode_shift (decode_shift "zzzz") = "zzzz" := by native_decide
example : decode_shift (encode_shift "abcdefghijklmnopqrstuvwxyz") = "abcdefghijklmnopqrstuvwxyz" := by
  native_decide
-- Non-letter input is still mapped into `'a'..'z'` (Python `%` is non-negative).
example : encode_shift "A!" = "zt" := by native_decide

#eval encode_shift "hello"
#eval decode_shift (encode_shift "hello")
#eval decode_shift (encode_shift "abcdefghijklmnopqrstuvwxyz")

/-! ## Pre-condition -/

/-- `c` is a lowercase ASCII letter `'a'..'z'` (code point in `[97, 122]`). -/
def isLowerAscii (c : Char) : Bool := 97 ≤ c.toNat && c.toNat ≤ 122

/-- Pre-condition: the input consists of lowercase ASCII letters only (the
domain on which the Python test harness exercises `decode_shift ∘ encode_shift`). -/
def Pre (s : String) : Prop := ∀ c ∈ s.toList, isLowerAscii c = true

/-! ## Properties -/

/-- Decoding an encoded lowercase string gives the string back (the assertion
of the Python `check` harness). -/
def decode_encode_prop (s : String) : Prop := decode_shift (encode_shift s) = s

/-- Encoding a decoded lowercase string gives the string back. -/
def encode_decode_prop (s : String) : Prop := encode_shift (decode_shift s) = s

/-- Encoding preserves the length (for every string). -/
def encode_length_prop (s : String) : Prop := (encode_shift s).length = s.length

/-- Decoding preserves the length (for every string). -/
def decode_length_prop (s : String) : Prop := (decode_shift s).length = s.length

/-- Every character of an encoded string is a lowercase ASCII letter (for every
string, since Python's `%` is non-negative). -/
def encode_lower_prop (s : String) : Prop :=
  ∀ c ∈ (encode_shift s).toList, isLowerAscii c = true

/-- Every character of a decoded string is a lowercase ASCII letter. -/
def decode_lower_prop (s : String) : Prop :=
  ∀ c ∈ (decode_shift s).toList, isLowerAscii c = true

/-- Character-wise code-point specification on lowercase letters: the encoded
code point of `ch` is `(ord(ch) - 97 + 5) % 26 + 97` and the decoded one is
`(ord(ch) - 97 + 21) % 26 + 97` (shifting back by 5 is shifting forward by 21). -/
def code_spec_prop (s : String) : Prop :=
  (encode_shift s).toList.map Char.toNat =
      s.toList.map (fun c => (c.toNat - 97 + 5) % 26 + 97) ∧
  (decode_shift s).toList.map Char.toNat =
      s.toList.map (fun c => (c.toNat - 97 + 21) % 26 + 97)

/-! ### Helper lemmas about one character -/

theorem shiftCode_ge (k : Int) (n : Nat) : 97 ≤ shiftCode k n := by
  unfold shiftCode; omega

theorem shiftCode_le (k : Int) (n : Nat) : shiftCode k n ≤ 122 := by
  unfold shiftCode; omega

theorem shiftCode_isValidChar (k : Int) (n : Nat) : (shiftCode k n).isValidChar := by
  unfold Nat.isValidChar
  left
  have := shiftCode_le k n
  omega

/-- `Char.ofNat` is exact on the result of `shiftCode` (it is a valid code point). -/
theorem toNat_shiftChar (k : Int) (c : Char) : (shiftChar k c).toNat = shiftCode k c.toNat := by
  unfold shiftChar
  rw [Char.toNat_ofNat, if_pos (shiftCode_isValidChar _ _)]

theorem isLowerAscii_shiftChar (k : Int) (c : Char) : isLowerAscii (shiftChar k c) = true := by
  simp [isLowerAscii, toNat_shiftChar, shiftCode_ge, shiftCode_le]

theorem isLowerAscii_iff (c : Char) : isLowerAscii c = true ↔ 97 ≤ c.toNat ∧ c.toNat ≤ 122 := by
  simp [isLowerAscii]

theorem shiftCode_neg5_shiftCode_5 (n : Nat) (h1 : 97 ≤ n) (h2 : n ≤ 122) :
    shiftCode (-5) (shiftCode 5 n) = n := by
  unfold shiftCode; omega

theorem shiftCode_5_shiftCode_neg5 (n : Nat) (h1 : 97 ≤ n) (h2 : n ≤ 122) :
    shiftCode 5 (shiftCode (-5) n) = n := by
  unfold shiftCode; omega

theorem shiftChar_neg5_shiftChar_5 (c : Char) (h : isLowerAscii c = true) :
    shiftChar (-5) (shiftChar 5 c) = c := by
  have hc := (isLowerAscii_iff c).mp h
  show Char.ofNat (shiftCode (-5) (shiftChar 5 c).toNat) = c
  rw [toNat_shiftChar, shiftCode_neg5_shiftCode_5 _ hc.1 hc.2, Char.ofNat_toNat]

theorem shiftChar_5_shiftChar_neg5 (c : Char) (h : isLowerAscii c = true) :
    shiftChar 5 (shiftChar (-5) c) = c := by
  have hc := (isLowerAscii_iff c).mp h
  show Char.ofNat (shiftCode 5 (shiftChar (-5) c).toNat) = c
  rw [toNat_shiftChar, shiftCode_5_shiftCode_neg5 _ hc.1 hc.2, Char.ofNat_toNat]

/-! ### Property theorems -/

theorem decode_encode_thm (s : String) (h : Pre s) : decode_encode_prop s := by
  unfold decode_encode_prop decode_shift encode_shift
  obtain ⟨l⟩ := s
  show String.mk (List.map (shiftChar (-5)) (List.map (shiftChar 5) l)) = String.mk l
  have hl : ∀ c ∈ l, (shiftChar (-5) ∘ shiftChar 5) c = id c :=
    fun c hc => shiftChar_neg5_shiftChar_5 c (h c hc)
  rw [List.map_map, List.map_congr_left hl, List.map_id]

theorem encode_decode_thm (s : String) (h : Pre s) : encode_decode_prop s := by
  unfold encode_decode_prop decode_shift encode_shift
  obtain ⟨l⟩ := s
  show String.mk (List.map (shiftChar 5) (List.map (shiftChar (-5)) l)) = String.mk l
  have hl : ∀ c ∈ l, (shiftChar 5 ∘ shiftChar (-5)) c = id c :=
    fun c hc => shiftChar_5_shiftChar_neg5 c (h c hc)
  rw [List.map_map, List.map_congr_left hl, List.map_id]

theorem encode_length_thm (s : String) : encode_length_prop s := by
  unfold encode_length_prop encode_shift
  obtain ⟨l⟩ := s
  simp [String.length, String.toList]

theorem decode_length_thm (s : String) : decode_length_prop s := by
  unfold decode_length_prop decode_shift
  obtain ⟨l⟩ := s
  simp [String.length, String.toList]

theorem encode_lower_thm (s : String) : encode_lower_prop s := by
  unfold encode_lower_prop encode_shift
  obtain ⟨l⟩ := s
  intro c hc
  simp only [String.toList, List.mem_map] at hc
  obtain ⟨a, _, rfl⟩ := hc
  exact isLowerAscii_shiftChar 5 a

theorem decode_lower_thm (s : String) : decode_lower_prop s := by
  unfold decode_lower_prop decode_shift
  obtain ⟨l⟩ := s
  intro c hc
  simp only [String.toList, List.mem_map] at hc
  obtain ⟨a, _, rfl⟩ := hc
  exact isLowerAscii_shiftChar (-5) a

theorem code_spec_thm (s : String) (h : Pre s) : code_spec_prop s := by
  unfold code_spec_prop encode_shift decode_shift
  obtain ⟨l⟩ := s
  simp only [String.toList, List.map_map]
  constructor
  · apply List.map_congr_left
    intro c hc
    have hc' := (isLowerAscii_iff c).mp (h c hc)
    simp only [Function.comp, toNat_shiftChar, shiftCode]
    omega
  · apply List.map_congr_left
    intro c hc
    have hc' := (isLowerAscii_iff c).mp (h c hc)
    simp only [Function.comp, toNat_shiftChar, shiftCode]
    omega

/-! ## Post-condition -/

/-- Post-condition: conjunction of all properties above. -/
def Post_prop (s : String) : Prop :=
  decode_encode_prop s ∧ encode_decode_prop s ∧
  encode_length_prop s ∧ decode_length_prop s ∧
  encode_lower_prop s ∧ decode_lower_prop s ∧
  code_spec_prop s

/-! ## Property-based tests -/

/-- Executable form of `Pre`. -/
def preB (s : String) : Bool := s.toList.all isLowerAscii

/-- Executable form of `Post_prop`. -/
def postB (s : String) : Bool :=
  (decode_shift (encode_shift s) == s) &&
  (encode_shift (decode_shift s) == s) &&
  ((encode_shift s).length == s.length) &&
  ((decode_shift s).length == s.length) &&
  (encode_shift s).toList.all isLowerAscii &&
  (decode_shift s).toList.all isLowerAscii &&
  ((encode_shift s).toList.map Char.toNat ==
      s.toList.map (fun c => (c.toNat - 97 + 5) % 26 + 97)) &&
  ((decode_shift s).toList.map Char.toNat ==
      s.toList.map (fun c => (c.toNat - 97 + 21) % 26 + 97))

/-- Deterministic pseudo-random lowercase string (like the Python harness, which
uses lengths in `[10, 20]`). -/
def lowerString (seed : Nat) : String :=
  let len := 10 + (seed * 7 + 3) % 11
  String.mk ((List.range len).map (fun i => Char.ofNat (97 + (seed * 31 + i * 17 + i * i * 5) % 26)))

-- Randomized PBTs (properties that hold for every string).
#eval Plausible.Testable.check (∀ s : String, (encode_shift s).length = s.length)
#eval Plausible.Testable.check (∀ s : String, (decode_shift s).length = s.length)
#eval Plausible.Testable.check (∀ s : String, (encode_shift s).toList.all isLowerAscii = true)
#eval Plausible.Testable.check (∀ s : String, (decode_shift s).toList.all isLowerAscii = true)
-- Randomized PBTs restricted to the pre-condition (random strings rarely satisfy it,
-- so the bounded tests below are the main evidence).
#eval Plausible.Testable.check
  (∀ s : String, preB s = true → decode_shift (encode_shift s) = s)
#eval Plausible.Testable.check
  (∀ s : String, preB s = true → encode_shift (decode_shift s) = s)
#eval Plausible.Testable.check (∀ s : String, preB s = true → postB s = true)
-- Randomized PBTs over lists of lowercase letters (sampled as offsets in `[0, 26)`).
#eval Plausible.Testable.check (∀ l : List (Fin 26),
  let s := String.mk (l.map (fun i => Char.ofNat (97 + i.val)))
  decode_shift (encode_shift s) = s)
#eval Plausible.Testable.check (∀ l : List (Fin 26),
  let s := String.mk (l.map (fun i => Char.ofNat (97 + i.val)))
  postB s = true)

-- Bounded PBTs: 200 pseudo-random lowercase strings satisfy the pre-condition and
-- every property of the post-condition.
example : (List.range 200).all (fun seed => preB (lowerString seed)) = true := by native_decide
example : (List.range 200).all (fun seed =>
    decode_shift (encode_shift (lowerString seed)) == lowerString seed) = true := by native_decide
example : (List.range 200).all (fun seed =>
    encode_shift (decode_shift (lowerString seed)) == lowerString seed) = true := by native_decide
example : (List.range 200).all (fun seed =>
    (encode_shift (lowerString seed)).length == (lowerString seed).length) = true := by native_decide
example : (List.range 200).all (fun seed =>
    (decode_shift (lowerString seed)).length == (lowerString seed).length) = true := by native_decide
example : (List.range 200).all (fun seed =>
    (encode_shift (lowerString seed)).toList.all isLowerAscii) = true := by native_decide
example : (List.range 200).all (fun seed =>
    (decode_shift (lowerString seed)).toList.all isLowerAscii) = true := by native_decide
example : (List.range 200).all (fun seed => postB (lowerString seed)) = true := by native_decide
-- Every single lowercase letter round-trips, and all 256 one-byte characters encode
-- to a lowercase letter of the right length.
example : (List.range 26).all (fun i =>
    let s := String.mk [Char.ofNat (97 + i)]
    postB s) = true := by native_decide
example : (List.range 256).all (fun i =>
    let s := String.mk [Char.ofNat i]
    (encode_shift s).toList.all isLowerAscii && (encode_shift s).length == 1) = true := by
  native_decide

/-! ## Correctness theorem -/

theorem correctness (s : String) (h : Pre s) : Post_prop s :=
  ⟨decode_encode_thm s h, encode_decode_thm s h, encode_length_thm s, decode_length_thm s,
   encode_lower_thm s, decode_lower_thm s, code_spec_thm s h⟩

/-! ## Imperative implementation -/

/-- Imperative `encode_shift`: build the output string character by character
(Python's `"".join([... for ch in s])`). -/
def encode_shift_imp (s : String) : String := Id.run do
  let mut out : String := ""
  for ch in s.toList do
    out := out.push (shiftChar 5 ch)
  return out

/-- Imperative `decode_shift`. -/
def decode_shift_imp (s : String) : String := Id.run do
  let mut out : String := ""
  for ch in s.toList do
    out := out.push (shiftChar (-5) ch)
  return out

/-! ## Imperative tests -/

example : encode_shift_imp "abc" = "fgh" := by native_decide
example : encode_shift_imp "xyz" = "cde" := by native_decide
example : encode_shift_imp "" = "" := by native_decide
example : decode_shift_imp "fgh" = "abc" := by native_decide
example : decode_shift_imp "mjqqt" = "hello" := by native_decide
example : decode_shift_imp (encode_shift_imp "hello") = "hello" := by native_decide
example : (List.range 200).all (fun seed =>
    encode_shift_imp (lowerString seed) == encode_shift (lowerString seed) &&
    decode_shift_imp (lowerString seed) == decode_shift (lowerString seed)) = true := by
  native_decide
#eval encode_shift_imp "hello"
#eval decode_shift_imp (encode_shift_imp "hello")
#eval Plausible.Testable.check (∀ s : String, encode_shift_imp s = encode_shift s)
#eval Plausible.Testable.check (∀ s : String, decode_shift_imp s = decode_shift s)

/-! ## Equivalence theorems -/

/-- The push-loop appends the mapped characters to the accumulator. -/
theorem push_loop (f : Char → Char) (l : List Char) (acc : String) :
    (forIn (m := Id) l acc (fun ch r => pure (ForInStep.yield (r.push (f ch))))) =
      String.mk (acc.toList ++ l.map f) := by
  induction l generalizing acc with
  | nil =>
    obtain ⟨a⟩ := acc
    show ({ data := a } : String) = _
    simp [String.toList]
  | cons c cs ih =>
    rw [List.forIn_cons]
    show forIn (m := Id) cs (acc.push (f c)) (fun ch r => pure (ForInStep.yield (r.push (f ch)))) = _
    rw [ih]
    obtain ⟨a⟩ := acc
    simp [String.toList, String.push]

theorem encode_shift_imp_eq (s : String) : encode_shift_imp s = encode_shift s := by
  unfold encode_shift_imp encode_shift
  show (forIn (m := Id) s.toList "" (fun ch r => pure (ForInStep.yield (r.push (shiftChar 5 ch))))) = _
  rw [push_loop]
  rfl

theorem decode_shift_imp_eq (s : String) : decode_shift_imp s = decode_shift s := by
  unfold decode_shift_imp decode_shift
  show (forIn (m := Id) s.toList "" (fun ch r => pure (ForInStep.yield (r.push (shiftChar (-5) ch))))) = _
  rw [push_loop]
  rfl

/-- Decoding the imperative encoding of a lowercase string returns it. -/
theorem imp_roundtrip (s : String) (h : Pre s) : decode_shift_imp (encode_shift_imp s) = s := by
  rw [decode_shift_imp_eq, encode_shift_imp_eq]
  exact decode_encode_thm s h

end humaneval_50_encode_shift
end Agent
