import Mathlib
namespace Agent

/-!
# Secure token generation and comparison

An executable translation of the supplied deterministic Python module. `Value`
models Python's relevant dynamic types; `other` stands for any unsupported object.
Booleans are accepted as integers, as in Python. Explicit validation errors retain
their Python class and message; implicit operator errors retain their class and
identify the failing operation. Strings use Lean Unicode characters; bytes use `UInt8`.
The token stub is deterministic, not a source of cryptographic randomness.

Comparison performs a length check followed by every XOR/OR iteration, never a
content-dependent early exit. The extra iteration counter is ghost instrumentation
for a functional full-scan theorem, not a claim about Lean/native machine timing.
-/
namespace SecretsToken

inductive Value where
  | none
  | int (n : Int)
  | bool (b : Bool)
  | str (s : String)
  | bytes (bs : List UInt8)
  | other (tag : Nat)
  deriving DecidableEq, Repr

inductive PyError where
  | typeError (message : String)
  | valueError (message : String)
  deriving DecidableEq, Repr

deriving instance DecidableEq for Except

abbrev Result := Except PyError

def DEFAULT_ENTROPY : Nat := 32

def validateNBytes : Value → Result Nat
  | .none => .ok DEFAULT_ENTROPY
  | .int n => if n < 0 then .error (.valueError "nbytes must be non-negative")
              else .ok n.toNat
  | .bool b => .ok (if b then 1 else 0)
  | _ => .error (.typeError "nbytes must be an integer")

def tokenBytesNat (n : Nat) : List UInt8 := List.replicate n 0xab

def hexDigit (n : Nat) : Char := Char.ofNat (if n < 10 then 48 + n else 87 + n)

def byteHex (b : UInt8) : List Char :=
  [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

def bytesHex (bs : List UInt8) : String :=
  String.mk ((bs.map byteHex).flatten)

def tokenHexNat (n : Nat) : String := bytesHex (tokenBytesNat n)

/-- Unlike the validated wrapper, Python repetition truncates negative counts to zero. -/
def tokenBytes (arg : Value := .none) : Result (List UInt8) :=
  match arg with
  | .none => .ok (tokenBytesNat DEFAULT_ENTROPY)
  | .int n => .ok (tokenBytesNat n.toNat)
  | .bool b => .ok (tokenBytesNat (if b then 1 else 0))
  | _ => .error (.typeError "can't multiply sequence by non-int")

def tokenHex (arg : Value := .none) : Result String := do
  let bs ← tokenBytes arg
  pure (bytesHex bs)

def benchmarkTokenHex (arg : Value := .none) : Result String := do
  let n ← validateNBytes arg
  tokenHex (.int n)

def codes : Value → List Nat
  | .str s => s.toList.map Char.toNat
  | .bytes bs => bs.map UInt8.toNat
  | _ => []

def sameKind : Value → Value → Bool
  | .str _, .str _ => true
  | .bytes _, .bytes _ => true
  | _, _ => false

def supported : Value → Bool
  | .str _ | .bytes _ => true
  | _ => false

def validateCompareArgs (a b : Value) : Result Unit :=
  if sameKind a b then .ok ()
  else .error (.typeError "compare_digest requires both args to be same type")

/-- (bitwise accumulator, number of loop iterations). -/
def scanStep (state : Nat × Nat) (xy : Nat × Nat) : Nat × Nat :=
  (state.1 ||| (xy.1 ^^^ xy.2), state.2 + 1)

def scan (pairs : List (Nat × Nat)) (state : Nat × Nat := (0, 0)) : Nat × Nat :=
  pairs.foldl scanStep state

def compareCodes (xs ys : List Nat) : Bool :=
  if xs.length != ys.length then false
  else (scan (xs.zip ys)).1 == 0

/-- Exposes the length leak but no content-dependent iteration count. -/
def comparisonWork (xs ys : List Nat) : Nat :=
  if xs.length != ys.length then 0 else (scan (xs.zip ys)).2

/-- Lower-level Python behavior includes the empty mixed-type corner case. -/
def compareDigest (a b : Value) : Result Bool :=
  if !(supported a && supported b) then
    .error (.typeError "unsupported operand types")
  else if (codes a).length != (codes b).length then .ok false
  else if sameKind a b then .ok (compareCodes (codes a) (codes b))
  else if (codes a).isEmpty then .ok true
  else .error (.typeError "unsupported operand types for ^")

def benchmarkCompareDigest (a b : Value) : Result Bool := do
  validateCompareArgs a b
  compareDigest a b

def isHexDigit (c : Char) : Bool := "0123456789abcdefABCDEF".toList.contains c

def asciiBytes (s : String) : Value := .bytes (s.toList.map (fun c => UInt8.ofNat c.toNat))

/-- Boolean form of every assertion in the supplied Python `check`. -/
def check (hexCand : Value → Result String) (cmpCand : Value → Value → Result Bool) : Bool :=
  ([1, 8, 16, 32] : List Nat).all (fun n =>
    match hexCand (.int n) with
    | .ok s => s.length == 2 * n && s.toList.all isHexDigit
    | .error _ => false) &&
  (match hexCand .none with
    | .ok s => s.length == 2 * DEFAULT_ENTROPY
    | .error _ => false) &&
  decide (cmpCand (.str "abc") (.str "abc") = .ok true) &&
  decide (cmpCand (asciiBytes "xyz") (asciiBytes "xyz") = .ok true) &&
  decide (cmpCand (.str "abc") (.str "abcd") = .ok false) &&
  decide (cmpCand (asciiBytes "abc") (asciiBytes "xyz") = .ok false) &&
  decide (cmpCand (.str "aaaaa") (.str "aaaab") = .ok false)

-- Unit tests: the public Python checks, default, zero, Unicode and errors.
example : check (fun n => benchmarkTokenHex n) benchmarkCompareDigest = true := by native_decide
#eval check (fun n => benchmarkTokenHex n) benchmarkCompareDigest

example : ([1, 8, 16, 32] : List Nat).all (fun n =>
    (tokenHexNat n).length == 2 * n && (tokenHexNat n).toList.all isHexDigit) = true := by
  native_decide
example : benchmarkTokenHex (arg := .none) = .ok (tokenHexNat 32) := by native_decide
example : benchmarkTokenHex (.int 0) = .ok "" := by native_decide
example : benchmarkTokenHex (.int 1) = .ok "ab" := by native_decide
example : benchmarkTokenHex (.int (-1)) =
    .error (.valueError "nbytes must be non-negative") := by native_decide
example : benchmarkTokenHex (.str "1") =
    .error (.typeError "nbytes must be an integer") := by native_decide
example : benchmarkTokenHex (.bool true) = .ok "ab" := by native_decide
example : benchmarkCompareDigest (.str "abc") (.str "abc") = .ok true := by native_decide
example : benchmarkCompareDigest (asciiBytes "xyz") (asciiBytes "xyz") = .ok true := by native_decide
example : benchmarkCompareDigest (.str "abc") (.str "abcd") = .ok false := by native_decide
example : benchmarkCompareDigest (asciiBytes "abc") (asciiBytes "xyz") = .ok false := by native_decide
example : benchmarkCompareDigest (.str "aaaaa") (.str "aaaab") = .ok false := by native_decide
example : benchmarkCompareDigest (.str "λ😀") (.str "λ😀") = .ok true := by native_decide
example : benchmarkCompareDigest (.str "") (.bytes []) =
    .error (.typeError "compare_digest requires both args to be same type") := by native_decide
example : compareDigest (.str "") (.bytes []) = .ok true := by native_decide
example : tokenBytes (.int (-2)) = .ok [] := by native_decide
#eval benchmarkTokenHex (.int 8)
#eval benchmarkCompareDigest (.str "aaaaa") (.str "aaaab")
#eval comparisonWork [97, 97, 97, 97, 97] [97, 97, 97, 97, 98]

/-- Admissible successful calls; invalid inputs are also modeled and specified below. -/
def Pre (arg a b : Value) : Prop :=
  (∃ n, validateNBytes arg = .ok n) ∧ sameKind a b = true


-- Kernel-checked supporting invariants.
@[simp] lemma result_bind_ok {α β : Type} (a : α) (f : α → Result β) :
    ((Except.ok a : Result α) >>= f) = f a := rfl

@[simp] lemma result_bind_error {α β : Type} (e : PyError) (f : α → Result β) :
    ((Except.error e : Result α) >>= f) = .error e := rfl

lemma byteHex_ab : byteHex 0xab = ['a', 'b'] := by decide

lemma token_chars (n : Nat) :
    (tokenHexNat n).toList = (List.replicate n ['a', 'b']).flatten := by
  simp [tokenHexNat, bytesHex, tokenBytesNat, byteHex_ab]

lemma or_zero_iff (a b : Nat) : a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have ha : a ≤ a ||| b := Nat.left_le_or
    have hb : b ≤ a ||| b := Nat.right_le_or
    omega
  · rintro ⟨rfl, rfl⟩
    rfl

lemma scan_zero (pairs : List (Nat × Nat)) (acc count : Nat) :
    (scan pairs (acc, count)).1 = 0 ↔
      acc = 0 ∧ ∀ p ∈ pairs, p.1 = p.2 := by
  induction pairs generalizing acc count with
  | nil => simp [scan]
  | cons p ps ih =>
    change (scan ps (acc ||| (p.1 ^^^ p.2), count + 1)).1 = 0 ↔ _
    rw [ih, or_zero_iff, Nat.xor_eq_zero]
    simp [and_assoc]

lemma scan_count (pairs : List (Nat × Nat)) (acc count : Nat) :
    (scan pairs (acc, count)).2 = count + pairs.length := by
  induction pairs generalizing acc count with
  | nil => simp [scan]
  | cons p ps ih =>
    change (scan ps (acc ||| (p.1 ^^^ p.2), count + 1)).2 = _
    rw [ih]
    simp [Nat.add_comm, Nat.add_left_comm]

lemma zip_equal_iff (xs ys : List Nat) (h : xs.length = ys.length) :
    (∀ p ∈ xs.zip ys, p.1 = p.2) ↔ xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp_all
    | cons y ys =>
      have ht : xs.length = ys.length := by simpa using h
      simp only [List.zip_cons_cons, List.forall_mem_cons, List.cons.injEq]
      exact and_congr Iff.rfl (ih ys ht)

lemma compareCodes_correct (xs ys : List Nat) :
    compareCodes xs ys = decide (xs = ys) := by
  by_cases h : xs.length = ys.length
  · have hz : (scan (xs.zip ys)).1 = 0 ↔ xs = ys := by
      rw [scan_zero]
      simpa using (zip_equal_iff xs ys h)
    apply Bool.eq_iff_iff.mpr
    simp [compareCodes, h, hz]
  · have hn : xs ≠ ys := fun e => h (congrArg List.length e)
    simp [compareCodes, h, hn]

-- Properties of the deterministic token stub, including arbitrary sizes.
def tokenExact_prop (n : Nat) : Prop :=
  tokenHexNat n = String.mk ((List.replicate n ['a', 'b']).flatten)

theorem tokenExact_thm (n : Nat) : tokenExact_prop n := by
  apply String.ext
  exact token_chars n

def tokenLength_prop (n : Nat) : Prop := (tokenHexNat n).length = 2 * n

theorem tokenLength_thm (n : Nat) : tokenLength_prop n := by
  change (tokenHexNat n).toList.length = 2 * n
  rw [token_chars]
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, List.flatten_cons, List.length_append,
      List.length_cons, List.length_nil] at *
    omega

def tokenAlphabet_prop (n : Nat) : Prop :=
  ∀ c ∈ (tokenHexNat n).toList, isHexDigit c = true

theorem tokenAlphabet_thm (n : Nat) : tokenAlphabet_prop n := by
  intro c hc
  rw [token_chars] at hc
  obtain ⟨cs, hcs, hc⟩ := List.mem_flatten.mp hc
  have he : cs = ['a', 'b'] := List.eq_of_mem_replicate hcs
  subst cs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> decide

def fullScan_prop (xs ys : List Nat) : Prop :=
  comparisonWork xs ys = if xs.length = ys.length then xs.length else 0

theorem fullScan_thm (xs ys : List Nat) : fullScan_prop xs ys := by
  by_cases h : xs.length = ys.length
  · simp [fullScan_prop, comparisonWork, h, scan_count]
  · simp [fullScan_prop, comparisonWork, h]


lemma char_code_injective : Function.Injective Char.toNat := by
  intro a b h
  apply Char.ext
  exact UInt32.toNat_inj.mp h

lemma codes_eq_iff (a b : Value) (h : sameKind a b = true) :
    codes a = codes b ↔ a = b := by
  cases a <;> cases b <;> simp only [sameKind, Bool.false_eq_true] at h
  · simp [codes, List.map_inj_right (fun _ _ h => char_code_injective h),
      ← String.ext_iff]
  · simp [codes, List.map_inj_right (fun _ _ h => UInt8.toNat_inj.mp h)]

lemma sameKind_supported (a b : Value) (h : sameKind a b = true) :
    supported a = true ∧ supported b = true := by
  cases a <;> cases b <;> simp_all [sameKind, supported]

lemma compareDigest_same (a b : Value) (h : sameKind a b = true) :
    compareDigest a b = .ok (compareCodes (codes a) (codes b)) := by
  obtain ⟨ha, hb⟩ := sameKind_supported a b h
  by_cases hl : (codes a).length = (codes b).length <;>
    simp [compareDigest, compareCodes, h, ha, hb, hl]

lemma benchmarkTokenHex_of_valid (arg : Value) (n : Nat)
    (h : validateNBytes arg = .ok n) : benchmarkTokenHex arg = .ok (tokenHexNat n) := by
  simp [benchmarkTokenHex, h, tokenHex, tokenBytes, tokenHexNat]

/-- Total specification: no invalid input is hidden by `Pre`. -/
def tokenSpec : Value → Result String
  | .none => .ok (tokenHexNat DEFAULT_ENTROPY)
  | .int n => if n < 0 then .error (.valueError "nbytes must be non-negative")
              else .ok (tokenHexNat n.toNat)
  | .bool b => .ok (tokenHexNat (if b then 1 else 0))
  | _ => .error (.typeError "nbytes must be an integer")

def validation_prop (arg : Value) : Prop := benchmarkTokenHex arg = tokenSpec arg

theorem validation_thm (arg : Value) : validation_prop arg := by
  cases arg <;> simp [validation_prop, benchmarkTokenHex, validateNBytes,
    tokenSpec, tokenHex, tokenBytes, tokenHexNat]
  split <;> simp_all

def defaultEntropy_prop : Prop :=
  benchmarkTokenHex (arg := .none) = .ok (tokenHexNat DEFAULT_ENTROPY) ∧
  (tokenHexNat DEFAULT_ENTROPY).length = 64

theorem defaultEntropy_thm : defaultEntropy_prop := by
  constructor
  · exact benchmarkTokenHex_of_valid .none DEFAULT_ENTROPY rfl
  · exact tokenLength_thm DEFAULT_ENTROPY

/-- Same-type strings and bytes compare exactly by equality; all other calls error. -/
def compare_prop (a b : Value) : Prop :=
  benchmarkCompareDigest a b =
    if sameKind a b then .ok (decide (a = b))
    else .error (.typeError "compare_digest requires both args to be same type")

theorem compare_thm (a b : Value) : compare_prop a b := by
  unfold compare_prop benchmarkCompareDigest validateCompareArgs
  by_cases h : sameKind a b = true
  · simp [h, compareDigest_same a b h, compareCodes_correct, codes_eq_iff a b h]
  · simp [h]

def symmetry_prop (a b : Value) : Prop :=
  benchmarkCompareDigest a b = benchmarkCompareDigest b a

theorem symmetry_thm (a b : Value) : symmetry_prop a b := by
  have h : sameKind a b = sameKind b a := by cases a <;> cases b <;> rfl
  change benchmarkCompareDigest a b = benchmarkCompareDigest b a
  rw [compare_thm a b, compare_thm b a, h]
  by_cases e : a = b
  · subst b
    rfl
  · simp [e, Ne.symm e]

/-- Successful-call postcondition plus total error, equality, and work specifications. -/
def Post_prop (arg a b : Value) : Prop :=
  (∃ n, validateNBytes arg = .ok n ∧
    benchmarkTokenHex arg = .ok (tokenHexNat n) ∧
    tokenExact_prop n ∧ tokenLength_prop n ∧ tokenAlphabet_prop n) ∧
  benchmarkCompareDigest a b = .ok (decide (a = b)) ∧
  compare_prop a b ∧ fullScan_prop (codes a) (codes b) ∧
  symmetry_prop a b ∧ validation_prop arg ∧ defaultEntropy_prop


-- Property-based tests. Each named executable property above is covered below.
-- Token properties: exhaustive sizes 0 through 128, not just the public examples.
example : (List.range 129).all (fun n =>
    tokenHexNat n == String.mk ((List.replicate n ['a', 'b']).flatten)) = true := by
  native_decide -- tokenExact_prop
example : (List.range 129).all (fun n => (tokenHexNat n).length == 2 * n) = true := by
  native_decide -- tokenLength_prop
example : (List.range 129).all (fun n => (tokenHexNat n).toList.all isHexDigit) = true := by
  native_decide -- tokenAlphabet_prop

def countSamples : List Value :=
  [.none, .bool false, .bool true, .str "32", .bytes [], .other 0] ++
  (List.range 81).map (fun n => .int (Int.ofNat n - 16))

def valueSamples : List Value :=
  [.none, .int 0, .int (-1), .bool false, .bool true, .other 1,
   .str "", .str "a", .str "b", .str "abc", .str "abcd", .str "aaaaa", .str "aaaab",
   .str "λ😀", .str "λ😁", .str "\x00", .bytes [], .bytes [0], .bytes [255],
   asciiBytes "a", asciiBytes "b", asciiBytes "abc", asciiBytes "xyz",
   asciiBytes "aaaaa", asciiBytes "aaaab"]

example : countSamples.all (fun arg => decide (benchmarkTokenHex arg = tokenSpec arg)) = true := by
  native_decide -- validation_prop, including negative, default, Boolean and wrong types

-- defaultEntropy_prop is nullary: its entire domain has one element.
example : decide (benchmarkTokenHex (arg := .none) = .ok (tokenHexNat DEFAULT_ENTROPY) ∧
    (tokenHexNat DEFAULT_ENTROPY).length = 64) = true := by native_decide

example : valueSamples.all (fun a => valueSamples.all (fun b =>
    decide (benchmarkCompareDigest a b =
      if sameKind a b then .ok (decide (a = b))
      else .error (.typeError "compare_digest requires both args to be same type")))) = true := by
  native_decide -- compare_prop
example : valueSamples.all (fun a => valueSamples.all (fun b =>
    decide (benchmarkCompareDigest a b = benchmarkCompareDigest b a))) = true := by
  native_decide -- symmetry_prop
example : valueSamples.all (fun a => valueSamples.all (fun b =>
    comparisonWork (codes a) (codes b) ==
      (if (codes a).length = (codes b).length then (codes a).length else 0))) = true := by
  native_decide -- fullScan_prop
#eval Plausible.Testable.check (∀ xs ys : List Nat,
  compareCodes xs ys = decide (xs = ys))
#eval Plausible.Testable.check (∀ xs ys : List Nat,
  comparisonWork xs ys = if xs.length = ys.length then xs.length else 0)

-- compare_prop: all 256 single-byte values against all 256 others.
example : (List.range 256).all (fun x => (List.range 256).all (fun y =>
    decide (benchmarkCompareDigest (.bytes [UInt8.ofNat x]) (.bytes [UInt8.ofNat y]) =
      .ok (x == y)))) = true := by native_decide
-- Random byte strings, including reflexivity to exercise the true branch frequently.
#eval Plausible.Testable.check (∀ xs : List Nat,
  benchmarkCompareDigest (.bytes (xs.map UInt8.ofNat)) (.bytes (xs.map UInt8.ofNat)) = .ok true)
#eval Plausible.Testable.check (∀ xs ys : List Nat,
  benchmarkCompareDigest (.bytes (xs.map UInt8.ofNat)) (.bytes (ys.map UInt8.ofNat)) =
    .ok (decide (xs.map UInt8.ofNat = ys.map UInt8.ofNat)))

/-- Executable `Pre → Post_prop`: rejected inputs do not satisfy `Pre`. -/
def postCheck (arg a b : Value) : Bool :=
  match validateNBytes arg with
  | .error _ => true
  | .ok n =>
    if sameKind a b then
      decide (benchmarkTokenHex arg = .ok (tokenHexNat n)) &&
      (tokenHexNat n == String.mk ((List.replicate n ['a', 'b']).flatten)) &&
      ((tokenHexNat n).length == 2 * n) &&
      (tokenHexNat n).toList.all isHexDigit &&
      decide (benchmarkCompareDigest a b = .ok (decide (a = b))) &&
      (comparisonWork (codes a) (codes b) ==
        if (codes a).length = (codes b).length then (codes a).length else 0) &&
      decide (benchmarkCompareDigest a b = benchmarkCompareDigest b a) &&
      decide (benchmarkTokenHex arg = tokenSpec arg) &&
      decide (benchmarkTokenHex (arg := .none) = .ok (tokenHexNat DEFAULT_ENTROPY)) &&
      ((tokenHexNat DEFAULT_ENTROPY).length == 64)
    else true

example : countSamples.all (fun arg => valueSamples.all (fun a =>
    valueSamples.all (fun b => postCheck arg a b))) = true := by
  native_decide -- Post_prop on every admissible triple in these finite domains
#eval countSamples.all (fun arg => valueSamples.all (fun a =>
  valueSamples.all (fun b => postCheck arg a b)))

-- Correctness is proved from invariants, not inferred from the tests.
theorem correctness (arg a b : Value) : Pre arg a b → Post_prop arg a b := by
  rintro ⟨⟨n, hn⟩, hab⟩
  have hc : benchmarkCompareDigest a b = .ok (decide (a = b)) := by
    have hs := compare_thm a b
    simpa [compare_prop, hab] using hs
  exact ⟨⟨n, hn, benchmarkTokenHex_of_valid arg n hn,
    tokenExact_thm n, tokenLength_thm n, tokenAlphabet_thm n⟩,
    hc, compare_thm a b, fullScan_thm (codes a) (codes b),
    symmetry_thm a b, validation_thm arg, defaultEntropy_thm⟩

-- Imperative implementation. These are actual mutable, non-short-circuiting loops.
def tokenBytesNatImp (n : Nat) : List UInt8 := Id.run do
  let mut bs : List UInt8 := []
  for _ in List.range n do
    bs := bs ++ [0xab]
  return bs

def bytesHexImp (bs : List UInt8) : String := Id.run do
  let mut chars : List Char := []
  for b in bs do
    chars := chars ++ byteHex b
  return String.mk chars

def tokenHexNatImp (n : Nat) : String := Id.run do
  let bs := tokenBytesNatImp n
  return bytesHexImp bs

def benchmarkTokenHexImp (arg : Value := .none) : Result String := Id.run do
  match validateNBytes arg with
  | .error e => return .error e
  | .ok n => return .ok (tokenHexNatImp n)

def scanImp (pairs : List (Nat × Nat)) (initial : Nat × Nat := (0, 0)) : Nat × Nat := Id.run do
  let mut state := initial
  for xy in pairs do
    state := (state.1 ||| (xy.1 ^^^ xy.2), state.2 + 1)
  return state

def compareCodesImp (xs ys : List Nat) : Bool := Id.run do
  if xs.length != ys.length then return false
  let state := scanImp (xs.zip ys)
  return state.1 == 0

def compareDigestImp (a b : Value) : Result Bool := Id.run do
  if !(supported a && supported b) then
    return .error (.typeError "unsupported operand types")
  if (codes a).length != (codes b).length then return .ok false
  if sameKind a b then return .ok (compareCodesImp (codes a) (codes b))
  if (codes a).isEmpty then return .ok true
  return .error (.typeError "unsupported operand types for ^")

def benchmarkCompareDigestImp (a b : Value) : Result Bool := Id.run do
  match validateCompareArgs a b with
  | .error e => return .error e
  | .ok _ => return compareDigestImp a b

-- Imperative tests (fixed and bounded).
example : check (fun n => benchmarkTokenHexImp n) benchmarkCompareDigestImp = true := by native_decide
#eval check (fun n => benchmarkTokenHexImp n) benchmarkCompareDigestImp
example : benchmarkTokenHexImp (.int 8) = .ok "abababababababab" := by native_decide
example : benchmarkTokenHexImp (arg := .none) = .ok (tokenHexNat 32) := by native_decide
example : benchmarkCompareDigestImp (.str "abc") (.str "abc") = .ok true := by native_decide
example : benchmarkCompareDigestImp (asciiBytes "abc") (asciiBytes "xyz") = .ok false := by native_decide
example : benchmarkCompareDigestImp (.str "aaaaa") (.str "aaaab") = .ok false := by native_decide
example : countSamples.all (fun arg =>
    decide (benchmarkTokenHex arg = benchmarkTokenHexImp arg)) = true := by native_decide
example : valueSamples.all (fun a => valueSamples.all (fun b =>
    decide (benchmarkCompareDigest a b = benchmarkCompareDigestImp a b))) = true := by native_decide
#eval benchmarkTokenHexImp (.int 16)
#eval benchmarkCompareDigestImp (.str "λ😀") (.str "λ😁")

-- Loop invariants and equivalence, for all inputs (including invalid ones).
lemma byte_loop_invariant (indices : List Nat) (acc : List UInt8) :
    indices.foldl (fun bs _ => bs ++ [0xab]) acc =
      acc ++ List.replicate indices.length 0xab := by
  induction indices generalizing acc with
  | nil => simp
  | cons x xs ih => simp [List.foldl_cons, ih, List.replicate_succ, List.append_assoc]

lemma hex_loop_invariant (bs : List UInt8) (acc : List Char) :
    bs.foldl (fun cs b => cs ++ byteHex b) acc = acc ++ (bs.map byteHex).flatten := by
  induction bs generalizing acc with
  | nil => simp
  | cons b bs ih => simp [List.foldl_cons, ih, List.append_assoc]

theorem tokenBytes_equiv (n : Nat) : tokenBytesNat n = tokenBytesNatImp n := by
  simp [tokenBytesNatImp, tokenBytesNat]

theorem bytesHex_equiv (bs : List UInt8) : bytesHex bs = bytesHexImp bs := by
  simp [bytesHexImp, bytesHex]

theorem tokenHex_equiv (n : Nat) : tokenHexNat n = tokenHexNatImp n := by
  simp [tokenHexNatImp, tokenHexNat, ← tokenBytes_equiv, ← bytesHex_equiv]

theorem scan_equiv (pairs : List (Nat × Nat)) (initial : Nat × Nat) :
    scan pairs initial = scanImp pairs initial := by
  simp [scan, scanImp]
  rfl

theorem compareCodes_equiv (xs ys : List Nat) : compareCodes xs ys = compareCodesImp xs ys := by
  unfold compareCodes compareCodesImp
  simp only [← scan_equiv]
  rfl

theorem compareDigest_equiv (a b : Value) : compareDigest a b = compareDigestImp a b := by
  unfold compareDigest compareDigestImp
  simp only [← compareCodes_equiv]
  rfl

theorem token_equivalence (arg : Value) : benchmarkTokenHex arg = benchmarkTokenHexImp arg := by
  cases h : validateNBytes arg with
  | error e => simp [benchmarkTokenHex, benchmarkTokenHexImp, h]
  | ok n =>
    rw [benchmarkTokenHex_of_valid arg n h]
    simp [benchmarkTokenHexImp, h, ← tokenHex_equiv]

theorem compare_equivalence (a b : Value) :
    benchmarkCompareDigest a b = benchmarkCompareDigestImp a b := by
  cases h : validateCompareArgs a b <;>
    simp [benchmarkCompareDigest, benchmarkCompareDigestImp, h, ← compareDigest_equiv]

/-- Pointwise functional = imperative equivalence of both public entry points. -/
theorem equivalence (arg a b : Value) :
    benchmarkTokenHex arg = benchmarkTokenHexImp arg ∧
    benchmarkCompareDigest a b = benchmarkCompareDigestImp a b := by
  exact ⟨token_equivalence arg, compare_equivalence a b⟩

end SecretsToken
end Agent
