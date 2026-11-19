import Mathlib
namespace Agent

/-!
# The supplied Python JSON decoder

This is the *prefix* decoder in the question, not a full JSON validator.  In
particular there is no leading-space skipping or end-of-input check. Arrays use
the supplied stub; a nonempty object enters its infinite `while True: pass` loop.
`Outcome.diverges` records that behavior, rather than imposing a terminating
error on it. Offsets count characters, not UTF-8 bytes. Unicode escapes deliberately
skip four characters and append `?`, just as in the supplied benchmark.

`Input` makes the dynamic string precondition explicit. Non-string Python values
are observationally indistinguishable to this program and are represented by
`Input.other`. Decimal floating literals use the executable `Float` layer; no
algebraic law about opaque IEEE operations is assumed in any proof.
-/
namespace JsonDecoder24

inductive Value where
  | null
  | boolean (b : Bool)
  | integer (n : Int)
  | floating (x : Float)
  | string (s : String)
  | array (xs : List Value)
  | object (xs : List (String × Value))
  deriving Repr, BEq

inductive ErrorKind where
  | unterminated
  | control (c : Char)
  | escape (c : Char)
  deriving Repr, BEq, DecidableEq

/-- The three stored JSONDecodeError fields, with a structured message. -/
structure DecodeError where
  kind : ErrorKind
  doc : String
  pos : Nat
  deriving Repr, BEq, DecidableEq

/-- These are the Python exception's computed line and column numbers. -/
def DecodeError.line (e : DecodeError) : Nat :=
  ((e.doc.toList.take e.pos).filter (· == '\n')).length + 1

def DecodeError.column (e : DecodeError) : Nat :=
  e.pos - (e.doc.toList.take e.pos).length +
    ((e.doc.toList.take e.pos).reverse.takeWhile (· != '\n')).length + 1

inductive Outcome (α : Type) where
  | ok (value : α)
  | jsonError (err : DecodeError)
  | stopIteration (pos : Nat)
  | typeError
  | diverges
  deriving Repr, BEq

def Outcome.map (f : α → β) : Outcome α → Outcome β
  | .ok a => .ok (f a)
  | .jsonError e => .jsonError e
  | .stopIteration p => .stopIteration p
  | .typeError => .typeError
  | .diverges => .diverges

inductive Input where
  | text (s : String)
  | other
  deriving Repr, BEq, DecidableEq

/-- The eight entries of Python's BACKSLASH table. -/
def backslash : Char → Option Char
  | '"' => some '"'
  | '\\' => some '\\'
  | '/' => some '/'
  | 'b' => some '\x08'
  | 'f' => some '\x0c'
  | 'n' => some '\n'
  | 'r' => some '\r'
  | 't' => some '\t'
  | _ => none

structure StringState where
  rest : List Char
  pos : Nat
  acc : List Char := [] -- reverse order, avoiding repeated string concatenation
  deriving Repr

inductive StringStep where
  | done (result : Outcome (String × Nat))
  | more (state : StringState)

/-- One iteration of `scanstring`. A no-terminator suffix ultimately reports the
opening quote, even if ordinary characters have already been accumulated. -/
def stringStep (doc : String) (begin : Nat) (strict : Bool)
    (st : StringState) : StringStep :=
  match st.rest with
  | [] => .done (.jsonError ⟨.unterminated, doc, begin⟩)
  | c :: cs =>
    if c = '"' then
      .done (.ok (String.mk st.acc.reverse, st.pos + 1))
    else if c = '\\' then
      match cs with
      | [] => .done (.jsonError ⟨.unterminated, doc, begin⟩)
      | esc :: tail =>
        if esc = 'u' then
          .more ⟨tail.drop 4, st.pos + 6, '?' :: st.acc⟩
        else match backslash esc with
          | some decoded => .more ⟨tail, st.pos + 2, decoded :: st.acc⟩
          | none => .done (.jsonError ⟨.escape esc, doc, st.pos + 1⟩)
    else if c.toNat < 32 ∧ strict = true then
      .done (.jsonError ⟨.control c, doc, st.pos + 1⟩)
    else .more ⟨cs, st.pos + 1, c :: st.acc⟩

/-- Fuel is input length plus one; each nonterminal step consumes input. -/
def stringLoop (doc : String) (begin : Nat) (strict : Bool) :
    Nat → StringState → Outcome (String × Nat)
  | 0, _ => .jsonError ⟨.unterminated, doc, begin⟩
  | n + 1, st =>
    match stringStep doc begin strict st with
    | .done r => r
    | .more next => stringLoop doc begin strict n next

def scanstring (s : String) (endPos : Nat) (strict : Bool := true) :
    Outcome (String × Nat) :=
  let rest := s.toList.drop endPos
  stringLoop s (endPos - 1) strict (rest.length + 1) ⟨rest, endPos, []⟩

/-- Python regex `\d` includes Unicode decimal digits. Each block below starts
at its zero code point (Unicode 15 decimal digits); the first nonzero digit of
an integer is nevertheless required to be ASCII by `[1-9]`. -/
def decimalZeros : List Nat :=
  [0x30, 0x660, 0x6f0, 0x7c0, 0x966, 0x9e6, 0xa66, 0xae6, 0xb66,
   0xbe6, 0xc66, 0xce6, 0xd66, 0xde6, 0xe50, 0xed0, 0xf20, 0x1040,
   0x1090, 0x17e0, 0x1810, 0x1946, 0x19d0, 0x1a80, 0x1a90, 0x1b50,
   0x1bb0, 0x1c40, 0x1c50, 0xa620, 0xa8d0, 0xa900, 0xa9d0, 0xa9f0,
   0xaa50, 0xabf0, 0xff10, 0x104a0, 0x10d30, 0x11066, 0x110f0,
   0x11136, 0x111d0, 0x112f0, 0x11450, 0x114d0, 0x11650, 0x116c0,
   0x11730, 0x118e0, 0x11950, 0x11c50, 0x11d50, 0x11da0, 0x11f50,
   0x16a60, 0x16ac0, 0x16b50, 0x1d7ce, 0x1d7d8, 0x1d7e2,
   0x1d7ec, 0x1d7f6, 0x1e140, 0x1e2f0, 0x1e4f0, 0x1e950, 0x1fbf0]

def digitValue (c : Char) : Nat :=
  match decimalZeros.find? (fun z => z ≤ c.toNat && c.toNat < z + 10) with
  | some z => c.toNat - z
  | none => 0

def decimalDigit (c : Char) : Bool :=
  decimalZeros.any (fun z => z ≤ c.toNat && c.toNat < z + 10)

def digitsValue (ds : List Char) : Nat :=
  ds.foldl (fun n c => 10 * n + digitValue c) 0

structure NumberToken where
  negative : Bool
  whole : List Char
  fraction : List Char
  exponent : Int
  isFloat : Bool
  width : Nat
  deriving Repr, BEq

/-- Optional fraction and exponent backtrack when their mandatory digits are
absent: `1.e2` parses as 1 and `1e+` also parses as 1. -/
def numberTail (neg : Bool) (whole rest : List Char) (width : Nat) : NumberToken :=
  let (frac, rem, extra, floating) := match rest with
    | '.' :: c :: cs =>
      if decimalDigit c then
        let ds := c :: cs.takeWhile decimalDigit
        (ds, cs.dropWhile decimalDigit, 1 + ds.length, true)
      else ([], rest, 0, false)
    | _ => ([], rest, 0, false)
  let base : NumberToken := ⟨neg, whole, frac, 0, floating, width + extra⟩
  match rem with
  | e :: es =>
    if e = 'e' ∨ e = 'E' then
      let (negativeExp, signWidth, digits) := match es with
        | '+' :: xs => (false, 1, xs)
        | '-' :: xs => (true, 1, xs)
        | xs => (false, 0, xs)
      let ds := digits.takeWhile decimalDigit
      if ds.isEmpty then base
      else
        let magnitude : Int := digitsValue ds
        ⟨neg, whole, frac, (if negativeExp then -magnitude else magnitude),
          true, base.width + 1 + signWidth + ds.length⟩
    else base
  | [] => base

def matchNumber (xs : List Char) : Option NumberToken :=
  let (neg, signWidth, rest) := match xs with
    | '-' :: cs => (true, 1, cs)
    | cs => (false, 0, cs)
  match rest with
  | '0' :: cs => some (numberTail neg ['0'] cs (signWidth + 1))
  | c :: cs =>
    if '1' ≤ c ∧ c ≤ '9' then
      let ds := c :: cs.takeWhile decimalDigit
      some (numberTail neg ds (cs.dropWhile decimalDigit) (signWidth + ds.length))
    else none
  | [] => none

/-- Round a nonnegative rational to an integer, nearest with ties to even. -/
def roundRatio (num den : Nat) : Nat :=
  let q := num / den
  let r := num % den
  if 2 * r > den ∨ (2 * r = den ∧ q % 2 = 1) then q + 1 else q

/-- Exact binary64 magnitude bits for a positive decimal rational. Decimal
order guards avoid constructing enormous powers for certainly overflowing or
underflowing exponents. All rounding is done with unbounded integer arithmetic. -/
def decimalBits (mantissa : Nat) (exponent : Int) : Nat :=
  let infinity := 2047 * 2^52
  if mantissa = 0 then 0
  else
    let order : Int := exponent + (toString mantissa).length - 1
    if order > 308 then infinity
    else if order < -324 then 0
    else
      let (num, den) := if exponent < 0 then
        (mantissa, 10^exponent.natAbs) else (mantissa * 10^exponent.toNat, 1)
      let k₀ : Int := (num.log2 : Int) - (den.log2 : Int)
      let below := if k₀ < 0 then num * 2^k₀.natAbs < den
        else num < den * 2^k₀.toNat
      let k := if below then k₀ - 1 else k₀
      if k < -1022 then
        -- This can round up to the least normal number, whose bits are 2^52.
        roundRatio (num * 2^1074) den
      else
        let shift : Int := 52 - k
        let significand := if shift < 0 then roundRatio num (den * 2^shift.natAbs)
          else roundRatio (num * 2^shift.toNat) den
        let (significand, k) := if significand = 2^53 then
          (significand / 2, k + 1) else (significand, k)
        if k > 1023 then infinity
        else (k + 1023).toNat * 2^52 + (significand - 2^52)

/-- The sign bit is set explicitly, preserving negative zero and infinity. -/
def decimalFloat (negative : Bool) (mantissa : Nat) (exponent : Int) : Float :=
  Float.ofBits (UInt64.ofNat (decimalBits mantissa exponent +
    if negative then 2^63 else 0))

/-- Numeric values preserve Python's integer/float distinction. IEEE exceptional
magnitudes are represented as infinities or signed zero, not rejected. -/
def NumberToken.value (t : NumberToken) : Value :=
  if t.isFloat then
    let mantissa := digitsValue (t.whole ++ t.fraction)
    let e := t.exponent - (t.fraction.length : Int)
    .floating (decimalFloat t.negative mantissa e)
  else
    let n : Int := digitsValue t.whole
    .integer (if t.negative then -n else n)

/-- JSONObject is an infinite loop unless the next character is exactly `}`. -/
def objectResult (rest : List Char) (pos : Nat) : Outcome (Value × Nat) :=
  match rest with
  | '}' :: _ => .ok (.object [], pos + 1)
  | _ => .diverges

/-- JSONArray returns the empty list without consuming a non-`]` character. -/
def arrayResult (rest : List Char) (pos : Nat) : Outcome (Value × Nat) :=
  match rest with
  | ']' :: _ => .ok (.array [], pos + 1)
  | _ => .ok (.array [], pos)

/-- `scan_once`, including StopIteration. The disjoint number branch is tested
first to keep the executable dispatch and its proofs small; no number can begin
with a quote, bracket, brace, or keyword. -/
def scanOnce (s : String) (idx : Nat) : Outcome (Value × Nat) :=
  let xs := s.toList.drop idx
  match matchNumber xs with
  | some t => .ok (t.value, idx + t.width)
  | none =>
    if xs.head? = some '"' then
      (scanstring s (idx + 1)).map (fun (v, p) => (.string v, p))
    else if xs.head? = some '{' then objectResult xs.tail (idx + 1)
    else if xs.head? = some '[' then arrayResult xs.tail (idx + 1)
    else if "null".toList.isPrefixOf xs then .ok (.null, idx + 4)
    else if "true".toList.isPrefixOf xs then .ok (.boolean true, idx + 4)
    else if "false".toList.isPrefixOf xs then .ok (.boolean false, idx + 5)
    else .stopIteration idx

/-- Like `decode`, deliberately discards the final position. -/
def decode (s : String) : Outcome Value := (scanOnce s 0).map Prod.fst

def benchmarkLoads : Input → Outcome Value
  | .text s => decode s
  | .other => .typeError

-- Unit tests from the question.
example : benchmarkLoads (.text "true") == .ok (.boolean true) := by native_decide
example : benchmarkLoads (.text "false") == .ok (.boolean false) := by native_decide
example : benchmarkLoads (.text "null") == .ok .null := by native_decide
example : benchmarkLoads (.text "123") == .ok (.integer 123) := by native_decide
example : benchmarkLoads (.text "-7") == .ok (.integer (-7)) := by native_decide
example : benchmarkLoads (.text "[]") == .ok (.array []) := by native_decide
example : benchmarkLoads (.text "{}") == .ok (.object []) := by native_decide
example : benchmarkLoads (.text "\"hi\"") == .ok (.string "hi") := by native_decide
#eval benchmarkLoads (.text "\"hi\"")
#eval benchmarkLoads (.text "-12.5e2 trailing")

-- Tests distinguishing this program from a conventional JSON decoder.
example : decode "trueXYZ" == .ok (.boolean true) := by native_decide
example : decode "[1,2]" == .ok (.array []) := by native_decide
example : decode "{" == .diverges := by native_decide
example : decode " true" == .stopIteration 0 := by native_decide
example : decode "NaN" == .stopIteration 0 := by native_decide
example : decode "1e+" == .ok (.integer 1) := by native_decide
example : decode "01" == .ok (.integer 0) := by native_decide
example : decode "\"a\\uXXXXb\"" == .ok (.string "a?b") := by native_decide
example : decode "\"\\q\"" == .jsonError ⟨.escape 'q', "\"\\q\"", 2⟩ := by native_decide
example : decode "\"\n\"" == .jsonError ⟨.control '\n', "\"\n\"", 2⟩ := by native_decide
example : decode "1.25" == .ok (.floating 1.25) := by native_decide
example : benchmarkLoads .other == .typeError := by native_decide

-- Binary64 boundary tests check bit patterns, not approximate equality.
example : (decimalFloat false 0 100000).toBits = 0 := by native_decide
example : (decimalFloat true 0 (-100000)).toBits = 0x8000000000000000 := by native_decide
example : (decimalFloat false 1 100000).toBits = 0x7ff0000000000000 := by native_decide
example : (decimalFloat true 1 (-100000)).toBits = 0x8000000000000000 := by native_decide
example : (decimalFloat false 5 (-324)).toBits = 1 := by native_decide
example : (decimalFloat false 9007199254740993 0).toBits = (9007199254740992.0 : Float).toBits := by native_decide
example : (decimalFloat false 17976931348623157 292).toBits = 0x7fefffffffffffff := by native_decide

-- Halfway cases at zero, the normal/subnormal boundary, and one.
example : (decimalFloat false (5^1075) (-1075)).toBits = 0 := by native_decide
example : (decimalFloat false (3 * 5^1075) (-1075)).toBits = 2 := by native_decide
example : (decimalFloat false ((2^53 - 1) * 5^1075) (-1075)).toBits =
    0x0010000000000000 := by native_decide
example : (decimalFloat false ((2^53 + 1) * 5^53) (-53)).toBits =
    0x3ff0000000000000 := by native_decide
example : decode "1e309" == .ok (.floating (Float.ofBits 0x7ff0000000000000)) := by native_decide
example : scanstring "\"\n\"" 1 false == .ok ("\n", 3) := by native_decide

/-- Exactly `isinstance(s, str)`, not an assumption that the string is valid JSON. -/
def Pre : Input → Prop
  | .text _ => True
  | .other => False


/-- A terminating execution of the string scanner, without a fuel parameter. -/
inductive StringExec (doc : String) (begin : Nat) (strict : Bool) :
    StringState → Outcome (String × Nat) → Prop where
  | finish {st r} : stringStep doc begin strict st = .done r →
      StringExec doc begin strict st r
  | advance {st next r} : stringStep doc begin strict st = .more next →
      StringExec doc begin strict next r → StringExec doc begin strict st r

/-- Every continuation really consumes characters, including truncated `\u`. -/
theorem stringStep_progress (doc : String) (begin : Nat) (strict : Bool)
    (st next : StringState) (h : stringStep doc begin strict st = .more next) :
    next.rest.length < st.rest.length := by
  rcases st with ⟨rest, pos, acc⟩
  unfold stringStep at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h
  · split at h <;> try contradiction
    split at h
    · cases h
      simp_all only [List.length_drop, List.length_cons]
      omega
    · split at h
      · cases h
        simp_all
        omega
      · contradiction
  · split at h <;> try contradiction
    cases h
    simp_all

/-- Consequently the executable fuel bound never introduces a spurious error. -/
theorem stringLoop_exec (doc : String) (begin : Nat) (strict : Bool)
    (fuel : Nat) (st : StringState) (h : st.rest.length < fuel) :
    StringExec doc begin strict st (stringLoop doc begin strict fuel st) := by
  induction fuel generalizing st with
  | zero => omega
  | succ n ih =>
    simp only [stringLoop]
    cases hs : stringStep doc begin strict st with
    | done r => exact .finish hs
    | more next =>
      apply StringExec.advance hs
      apply ih
      have hp := stringStep_progress doc begin strict st next hs
      omega

/-- An independently unbounded contract for the top-level dispatch. It records
both successful values and exceptional/nonterminating behavior on *all* strings.
The numeric branch uses the concrete decimal conversion, not a real-number
replacement for Python floats. -/
def DispatchSpec (s : String) (out : Outcome Value) : Prop :=
  let xs := s.toList
  match matchNumber xs with
  | some t => out = .ok t.value
  | none =>
    if xs.head? = some '"' then
      ∃ r, StringExec s 0 true ⟨xs.drop 1, 1, []⟩ r ∧
        out = r.map (fun p => Value.string p.1)
    else if xs.head? = some '{' then out = (objectResult xs.tail 1).map Prod.fst
    else if xs.head? = some '[' then out = .ok (.array [])
    else if "null".toList.isPrefixOf xs then out = .ok .null
    else if "true".toList.isPrefixOf xs then out = .ok (.boolean true)
    else if "false".toList.isPrefixOf xs then out = .ok (.boolean false)
    else out = .stopIteration 0

def dispatch_prop (s : String) : Prop := DispatchSpec s (decode s)

theorem outcome_map_map (r : Outcome α) (f : α → β) (g : β → γ) :
    (r.map f).map g = r.map (g ∘ f) := by
  cases r <;> rfl

theorem dispatch_thm (s : String) : dispatch_prop s := by
  unfold dispatch_prop DispatchSpec decode scanOnce
  dsimp only
  simp only [List.drop_zero]
  cases hn : matchNumber s.toList with
  | some t => rfl
  | none =>
    by_cases hq : s.toList.head? = some '"'
    · simp only [hq, ↓reduceIte]
      refine ⟨scanstring s 1, ?_, ?_⟩
      · exact stringLoop_exec s 0 true _ _ (Nat.lt_succ_self _)
      · exact outcome_map_map _ _ _
    · simp only [hq, ↓reduceIte]
      by_cases ho : s.toList.head? = some '{'
      · simp only [ho, ↓reduceIte]
      · simp only [ho, ↓reduceIte]
        by_cases ha : s.toList.head? = some '['
        · simp only [ha, ↓reduceIte]
          unfold arrayResult
          split <;> rfl
        · simp only [ha, ↓reduceIte]
          by_cases hn : "null".toList.isPrefixOf s.toList = true
          · simp only [hn]; rfl
          · simp only [hn]
            by_cases ht : "true".toList.isPrefixOf s.toList = true
            · simp only [ht]; rfl
            · simp only [ht]
              by_cases hf : "false".toList.isPrefixOf s.toList = true
              · simp only [hf]; rfl
              · simp only [hf]; rfl

/-- No text input raises the dynamic precondition's TypeError. -/
def type_safety_prop (s : String) : Prop := decode s ≠ .typeError

theorem stringStep_safe (doc : String) (begin : Nat) (strict : Bool)
    (st : StringState) (r : Outcome (String × Nat))
    (h : stringStep doc begin strict st = .done r) : r ≠ .typeError := by
  unfold stringStep at h
  split at h
  · cases h; intro hh; cases hh
  · split at h
    · cases h; intro hh; cases hh
    · split at h
      · split at h
        · cases h; intro hh; cases hh
        · split at h
          · contradiction
          · split at h
            · contradiction
            · cases h; intro hh; cases hh
      · split at h
        · cases h; intro hh; cases hh
        · contradiction

theorem stringLoop_safe (doc : String) (begin : Nat) (strict : Bool)
    (fuel : Nat) (st : StringState) :
    stringLoop doc begin strict fuel st ≠ .typeError := by
  induction fuel generalizing st with
  | zero => simp [stringLoop]
  | succ n ih =>
    simp only [stringLoop]
    cases hs : stringStep doc begin strict st with
    | done r => exact stringStep_safe _ _ _ _ _ hs
    | more next => exact ih next

theorem map_type_safety (r : Outcome α) (f : α → β) (h : r ≠ .typeError) :
    r.map f ≠ .typeError := by
  cases r <;> simp_all [Outcome.map]

theorem type_safety_thm (s : String) : type_safety_prop s := by
  unfold type_safety_prop decode
  apply map_type_safety
  unfold scanOnce
  dsimp only
  split
  · simp
  · split
    · apply map_type_safety
      exact stringLoop_safe _ _ _ _ _
    · split
      · unfold objectResult; split <;> simp
      · split
        · unfold arrayResult; split <;> simp
        · split
          · simp
          · split
            · simp
            · split <;> simp

/-- Trailing text is ignored for every primitive keyword. -/
def primitives_prop (tail : List Char) : Prop :=
  decode (String.mk ("true".toList ++ tail)) = .ok (.boolean true) ∧
  decode (String.mk ("false".toList ++ tail)) = .ok (.boolean false) ∧
  decode (String.mk ("null".toList ++ tail)) = .ok .null

theorem primitives_thm (tail : List Char) : primitives_prop tail := by
  unfold primitives_prop
  constructor
  · simp [decode, scanOnce, matchNumber, List.isPrefixOf, String.toList, Outcome.map]
  constructor
  · simp [decode, scanOnce, matchNumber, List.isPrefixOf, String.toList, Outcome.map]
  · simp [decode, scanOnce, matchNumber, List.isPrefixOf, String.toList, Outcome.map]

/-- Includes the surprising nonempty-array stub and nonempty-object divergence. -/
def containers_prop (tail : List Char) : Prop :=
  decode (String.mk ('[' :: tail)) = .ok (.array []) ∧
  decode (String.mk ('{' :: '}' :: tail)) = .ok (.object []) ∧
  (tail.head? ≠ some '}' → decode (String.mk ('{' :: tail)) = .diverges)

theorem containers_thm (tail : List Char) : containers_prop tail := by
  unfold containers_prop
  refine ⟨?_, rfl, ?_⟩
  · change (arrayResult tail 1).map Prod.fst = _
    unfold arrayResult
    split <;> rfl
  · intro h
    change (objectResult tail 1).map Prod.fst = _
    cases tail with
    | nil => rfl
    | cons c cs =>
      have hc : c ≠ '}' := by simpa using h
      simp [objectResult, hc, Outcome.map]

/-- Both integer and floating branches are selected by the actual regex token,
not by an assumption that the entire input is valid JSON. -/
def number_prop (s : String) : Prop :=
  ∀ t, matchNumber s.toList = some t → decode s = .ok t.value

theorem number_thm (s : String) : number_prop s := by
  intro t ht
  unfold decode scanOnce
  simp only [List.drop_zero, ht]
  rfl

/-- An ordinary string character in strict mode. -/
def Plain (c : Char) : Prop := c ≠ '"' ∧ c ≠ '\\' ∧ 32 ≤ c.toNat

def PlainText (cs : List Char) : Prop := ∀ c ∈ cs, Plain c

instance (c : Char) : Decidable (Plain c) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
instance (cs : List Char) : Decidable (PlainText cs) :=
  inferInstanceAs (Decidable (∀ c ∈ cs, Plain c))

theorem stringLoop_plain (content suffix acc : List Char) (doc : String)
    (begin pos fuel : Nat) (plain : PlainText content) (bound : content.length < fuel) :
    stringLoop doc begin true fuel ⟨content ++ '"' :: suffix, pos, acc⟩ =
      .ok (String.mk (acc.reverse ++ content), pos + content.length + 1) := by
  induction content generalizing acc pos fuel with
  | nil =>
    cases fuel with
    | zero => simp at bound
    | succ n => simp [stringLoop, stringStep]
  | cons c cs ih =>
    have hc := plain c (by simp)
    have hp : PlainText cs := fun d hd => plain d (by simp [hd])
    rcases hc with ⟨hq, hb, hn⟩
    cases fuel with
    | zero => simp at bound
    | succ n =>
      have hn' : ¬ c.toNat < 32 := by omega
      simp only [List.cons_append, stringLoop, stringStep, hq, hb,
        hn', false_and, ↓reduceIte]
      rw [ih (c :: acc) (pos + 1) n hp (by simpa using bound)]
      simp [List.reverse_cons, List.append_assoc, Nat.add_comm,
        Nat.add_left_comm]

/-- Strings without escapes round-trip, with arbitrary ignored trailing text. -/
def strings_prop (content suffix : List Char) : Prop :=
  PlainText content →
  decode (String.mk ('"' :: (content ++ '"' :: suffix))) = .ok (.string (String.mk content))

theorem strings_thm (content suffix : List Char) : strings_prop content suffix := by
  intro h
  change ((scanstring (String.mk ('"' :: (content ++ '"' :: suffix))) 1).map
    (fun (v, p) => (Value.string v, p))).map Prod.fst = _
  unfold scanstring
  change ((stringLoop _ 0 true ((content ++ '"' :: suffix).length + 1)
    ⟨content ++ '"' :: suffix, 1, []⟩).map _).map _ = _
  rw [stringLoop_plain content suffix [] _ 0 1 _ h (by simp only [List.length_append, List.length_cons]; omega)]
  rfl

/-- Exact integer conversion at the token layer; no bounded machine integer is used. -/
def integer_value_prop (negative : Bool) (digits : List Char) : Prop :=
  (NumberToken.mk negative digits [] 0 false digits.length).value =
    .integer (if negative then -(digitsValue digits : Int) else (digitsValue digits : Int))

theorem integer_value_thm (negative : Bool) (digits : List Char) :
    integer_value_prop negative digits := by
  rfl

/-- An integer lexeme of any length, with an ASCII nonzero leading digit and
Python-regex decimal continuation digits, decodes to its signed decimal fold. -/
def integer_syntax_prop (negative : Bool) (c : Char) (ds : List Char) : Prop :=
  ('1' ≤ c ∧ c ≤ '9') → (∀ d ∈ ds, decimalDigit d = true) →
  decode (String.mk ((if negative then ['-'] else []) ++ c :: ds)) =
    .ok (.integer (if negative then -(digitsValue (c :: ds) : Int)
      else (digitsValue (c :: ds) : Int)))

theorem integer_syntax_thm (negative : Bool) (c : Char) (ds : List Char) :
    integer_syntax_prop negative c ds := by
  intro hc hd
  have hm : c ≠ '-' := by intro h; subst c; simp at hc
  have hz : c ≠ '0' := by intro h; subst c; simp at hc
  have ht : ds.takeWhile decimalDigit = ds := List.takeWhile_eq_self_iff.mpr hd
  have hr : ds.dropWhile decimalDigit = [] := List.dropWhile_eq_nil_iff.mpr hd
  let t : NumberToken := ⟨negative, c :: ds, [], 0, false,
    (if negative then 1 else 0) + (c :: ds).length⟩
  have hn : matchNumber
      (String.mk ((if negative then ['-'] else []) ++ c :: ds)).toList = some t := by
    cases negative <;>
      simp [matchNumber, String.toList, hm, hz, hc, ht, hr, numberTail, t]
  rw [number_thm _ _ hn]
  rfl

/-- Every supported one-character escape is decoded, with ignored suffixes. -/
def escapes_prop (esc decoded : Char) (suffix : List Char) : Prop :=
  backslash esc = some decoded →
    decode (String.mk ('"' :: '\\' :: esc :: '"' :: suffix)) =
      .ok (.string (String.mk [decoded]))

theorem escapes_thm (esc decoded : Char) (suffix : List Char) :
    escapes_prop esc decoded suffix := by
  intro h
  have hu : esc ≠ 'u' := by intro he; subst esc; simp [backslash] at h
  change ((scanstring _ 1).map (fun (v, p) => (Value.string v, p))).map Prod.fst = _
  simp [scanstring, String.toList, stringLoop, stringStep, hu, h, Outcome.map]

/-- Invalid backslash escapes report the escape character's index, not the quote. -/
def escape_error_prop (esc : Char) (suffix : List Char) : Prop :=
  esc ≠ 'u' → backslash esc = none →
  let doc := String.mk ('"' :: '\\' :: esc :: suffix)
  decode doc = .jsonError ⟨.escape esc, doc, 2⟩

theorem escape_error_thm (esc : Char) (suffix : List Char) :
    escape_error_prop esc suffix := by
  intro hu h
  change ((scanstring _ 1).map (fun (v, p) => (Value.string v, p))).map Prod.fst = _
  simp [scanstring, String.toList, stringLoop, stringStep, hu, h, Outcome.map]

/-- Strict controls use `end` (one after the offending character), as in Python. -/
def control_error_prop (c : Char) (suffix : List Char) : Prop :=
  c.toNat < 32 →
  let doc := String.mk ('"' :: c :: suffix)
  decode doc = .jsonError ⟨.control c, doc, 2⟩

theorem control_error_thm (c : Char) (suffix : List Char) :
    control_error_prop c suffix := by
  intro h
  have hq : c ≠ '"' := by intro he; subst c; contradiction
  have hb : c ≠ '\\' := by intro he; subst c; contradiction
  change ((scanstring _ 1).map (fun (v, p) => (Value.string v, p))).map Prod.fst = _
  simp [scanstring, String.toList, stringLoop, stringStep, hq, hb, h, Outcome.map]

/-- The benchmark deliberately does not validate Unicode hex digits: any four
characters, even quotes or controls, are skipped and replaced by `?`. -/
def unicode_placeholder_prop (a b c d : Char) (suffix : List Char) : Prop :=
  decode (String.mk ('"' :: '\\' :: 'u' :: a :: b :: c :: d :: '"' :: suffix)) =
    .ok (.string "?")

theorem unicode_placeholder_thm (a b c d : Char) (suffix : List Char) :
    unicode_placeholder_prop a b c d suffix := by
  rfl

theorem stringLoop_unterminated (content acc : List Char) (doc : String)
    (begin pos fuel : Nat) (plain : PlainText content) (bound : content.length < fuel) :
    stringLoop doc begin true fuel ⟨content, pos, acc⟩ =
      .jsonError ⟨.unterminated, doc, begin⟩ := by
  induction content generalizing acc pos fuel with
  | nil => cases fuel <;> rfl
  | cons c cs ih =>
    rcases plain c (by simp) with ⟨hq, hb, hn⟩
    have hp : PlainText cs := fun d hd => plain d (by simp [hd])
    cases fuel with
    | zero => rfl
    | succ n =>
      have hn' : ¬ c.toNat < 32 := by omega
      simp only [stringLoop, stringStep, hq, hb, hn', false_and, ↓reduceIte]
      exact ih (c :: acc) (pos + 1) n hp (by simpa using bound)

/-- Unterminated ordinary strings report the opening quote, not the input end. -/
def unterminated_prop (content : List Char) : Prop :=
  PlainText content →
  let doc := String.mk ('"' :: content)
  decode doc = .jsonError ⟨.unterminated, doc, 0⟩

theorem unterminated_thm (content : List Char) : unterminated_prop content := by
  intro h
  change ((scanstring _ 1).map (fun (v, p) => (Value.string v, p))).map Prod.fst = _
  unfold scanstring
  change ((stringLoop _ 0 true (content.length + 1) ⟨content, 1, []⟩).map _).map _ = _
  rw [stringLoop_unterminated content [] _ 0 1 _ h (Nat.lt_succ_self _)]
  rfl

/-- The integer rounding stage has at most half a unit of error and ties are even.
This theorem is about exact integer arithmetic, not opaque Float operations. -/
def rounding_prop (num den : Nat) : Prop :=
  0 < den →
  (-(den : Int) ≤ 2 * ((roundRatio num den : Int) * den - num) ∧
    2 * ((roundRatio num den : Int) * den - num) ≤ den) ∧
  (2 * (num % den) = den → roundRatio num den % 2 = 0)

theorem rounding_thm (num den : Nat) : rounding_prop num den := by
  intro hd
  have hr := Nat.mod_lt num hd
  have hdivision : (num : Int) = (num / den : Nat) * (den : Int) + (num % den : Nat) := by
    exact_mod_cast (by simpa [Nat.mul_comm] using (Nat.div_add_mod num den).symm :
      num = num / den * den + num % den)
  constructor
  · unfold roundRatio
    dsimp only
    split
    · rename_i h
      simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      rcases h with h | ⟨h, _⟩
      · constructor <;> omega
      · constructor <;> omega
    · rename_i h
      constructor <;> omega
  · intro ht
    unfold roundRatio
    dsimp only
    split <;> omega

/-- Every admissible input has the full dispatch behavior and cannot raise the
precondition's TypeError. Invalid JSON is still admissible and may fail or loop. -/
def Post_prop : Input → Prop
  | .text s => dispatch_prop s ∧ type_safety_prop s
  | .other => benchmarkLoads .other = .typeError


/-! ## Property-based tests

All PBTs below are bounded executable checks, not proof tactics. The corpus
combines malformed inputs, numeric lexemes, every short word over a boundary
alphabet, and variable-length strings. For `dispatch_prop`'s unbounded
`StringExec`, `traceCheck` checks the corresponding finite execution trace;
`stringStep_progress` proves that the input-length bound suffices.
-/

def words (alphabet : List Char) : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 => (words alphabet n).flatMap (fun xs => alphabet.map (· :: xs))

def numericSamples : List String :=
  (List.range 80).flatMap fun n =>
    [toString n, "-" ++ toString n, toString n ++ ".25",
      toString n ++ "e-2", toString n ++ "e+", toString n ++ "xyz"]

def samples : List String :=
  ["", "true", "false", "null", "truefalse", "null\n", "[]", "[1,2]", "[", "{}", "{ ",
   "{\"a\":1}", "\"\"", "\"hi\"", "\"a\\nb\"", "\"\\uXXXX\"", "\"\\u12\"", "\"\\q\"",
   "\"\n\"", "\"unterminated", "\"\\", " 1", "Infinity", "-Infinity", "NaN", "01", "-0",
   "1.", "1e", "1e-", ".5", "1E+3", "1٢", "2.٥", "1e309", "-1e-400", "-0.0"] ++
  numericSamples ++
  ((List.range 4).flatMap (words ['0', 'e', '"', '\\', '[', '{', '\n'])).map String.mk

def traceCheck (doc : String) (begin : Nat) (strict : Bool) :
    Nat → StringState → Outcome (String × Nat) → Bool
  | 0, _, _ => false
  | n + 1, st, expected => match stringStep doc begin strict st with
    | .done r => r == expected
    | .more next => traceCheck doc begin strict n next expected

def dispatchCheck (s : String) : Bool :=
  let xs := s.toList
  let out := decode s
  match matchNumber xs with
  | some t => out == .ok t.value
  | none =>
    if xs.head? = some '"' then
      let r := scanstring s 1
      traceCheck s 0 true ((xs.drop 1).length + 1) ⟨xs.drop 1, 1, []⟩ r &&
        out == r.map (fun p => Value.string p.1)
    else if xs.head? = some '{' then out == (objectResult xs.tail 1).map Prod.fst
    else if xs.head? = some '[' then out == .ok (.array [])
    else if "null".toList.isPrefixOf xs then out == .ok .null
    else if "true".toList.isPrefixOf xs then out == .ok (.boolean true)
    else if "false".toList.isPrefixOf xs then out == .ok (.boolean false)
    else out == .stopIteration 0

def typeSafetyCheck (s : String) : Bool := match decode s with
  | .typeError => false
  | _ => true

-- PBT: dispatch_prop and type_safety_prop.
example : samples.all dispatchCheck = true := by native_decide
example : samples.all typeSafetyCheck = true := by native_decide

-- PBT: primitives_prop, over every corpus entry as an arbitrary trailing suffix.
example : samples.all (fun s =>
    decode ("true" ++ s) == .ok (.boolean true) &&
    decode ("false" ++ s) == .ok (.boolean false) &&
    decode ("null" ++ s) == .ok .null) = true := by native_decide

-- PBT: containers_prop, including divergent objects and incomplete arrays.
example : samples.all (fun s =>
    decode ("[" ++ s) == .ok (.array []) &&
    decode ("{}" ++ s) == .ok (.object []) &&
    (s.toList.head? == some '}' || decode ("{" ++ s) == .diverges)) = true := by native_decide

-- PBT: number_prop. Tests both integer and Float branches and regex backtracking.
example : samples.all (fun s => match matchNumber s.toList with
    | some t => decode s == .ok t.value
    | none => true) = true := by native_decide

-- PBT: strings_prop, exhaustively over ordinary short words and arbitrary suffixes.
def plainSamples : List (List Char) :=
  (List.range 4).flatMap (words ['a', ' ', 'é', '𝄞'])
example : plainSamples.all (fun cs => samples.all (fun suffix =>
    decode (String.mk ('"' :: (cs ++ '"' :: suffix.toList))) ==
      .ok (.string (String.mk cs)))) = true := by native_decide

-- PBT: integer_value_prop, including both signs and long digit lists.
example : (List.range 150).all (fun n => [false, true].all (fun neg =>
    let ds := (toString n).toList
    (NumberToken.mk neg ds [] 0 false ds.length).value ==
      .integer (if neg then -(digitsValue ds : Int) else (digitsValue ds : Int)))) = true :=
  by native_decide

-- PBT: integer_syntax_prop, signed leading digits and mixed Unicode continuation digits.
example : ['1', '4', '9'].all (fun c =>
    ((List.range 4).flatMap (words ['0', '3', '٧'])).all (fun ds =>
      [false, true].all (fun neg =>
        decode (String.mk ((if neg then ['-'] else []) ++ c :: ds)) ==
          .ok (.integer (if neg then -(digitsValue (c :: ds) : Int)
            else (digitsValue (c :: ds) : Int)))))) = true := by native_decide

-- PBT: escapes_prop, escape_error_prop and control_error_prop.
example : ['"', '\\', '/', 'b', 'f', 'n', 'r', 't'].all (fun esc =>
    samples.all (fun suffix => match backslash esc with
      | some c => decode (String.mk ('"' :: '\\' :: esc :: '"' :: suffix.toList)) ==
          .ok (.string (String.mk [c]))
      | none => false)) = true := by native_decide
example : ['q', 'x', '0', '\n', 'é'].all (fun esc => samples.all (fun suffix =>
    let doc := String.mk ('"' :: '\\' :: esc :: suffix.toList)
    decode doc == .jsonError ⟨.escape esc, doc, 2⟩)) = true := by native_decide
example : (List.range 32).all (fun n => samples.all (fun suffix =>
    let c := Char.ofNat n
    let doc := String.mk ('"' :: c :: suffix.toList)
    decode doc == .jsonError ⟨.control c, doc, 2⟩)) = true := by native_decide

-- PBT: unicode_placeholder_prop, including characters forbidden in real hex escapes.
example : (words ['q', '"', '\n'] 4).all (fun block => samples.all (fun suffix =>
    decode (String.mk ('"' :: '\\' :: 'u' :: (block ++ '"' :: suffix.toList))) ==
      .ok (.string "?"))) = true := by native_decide

-- PBT: unterminated_prop over the same ordinary text generator as strings_prop.
example : plainSamples.all (fun content =>
    let doc := String.mk ('"' :: content)
    decode doc == .jsonError ⟨.unterminated, doc, 0⟩) = true := by native_decide

-- PBT: rounding_prop, exhaustive rational rounding and tie cases.
example : (List.range 150).all (fun num => (List.range 35).all (fun d =>
    let den := d + 1
    let error : Int := (roundRatio num den : Int) * den - num
    decide (-(den : Int) ≤ 2 * error ∧ 2 * error ≤ den) &&
      (2 * (num % den) != den || roundRatio num den % 2 == 0))) = true := by native_decide

-- PBT: Post_prop (the conjunction), including the non-string branch.
def postCheck : Input → Bool
  | .text s => dispatchCheck s && typeSafetyCheck s
  | .other => benchmarkLoads .other == .typeError
example : (Input.other :: samples.map Input.text).all postCheck = true := by native_decide
#eval (samples.length, samples.all dispatchCheck, samples.all typeSafetyCheck)

/-- End-to-end correctness has exactly the original dynamic precondition. -/
theorem correctness_thm (input : Input) : Pre input → Post_prop input := by
  cases input with
  | text s => intro _; exact ⟨dispatch_thm s, type_safety_thm s⟩
  | other => intro h; exact False.elim h

/-! ## Imperative implementation

The mutable machine retains the first terminal result. It takes at most
`remaining.length + 1` iterations, which is sufficient by the progress theorem.
Unlike the functional recursive evaluator, `runMachine` uses a mutable variable
and an actual `for` loop. The shared transition is the primitive scanner step;
this is not a call to the functional decoder.
-/

abbrev Machine := Sum (Outcome (String × Nat)) StringState

def tick (doc : String) (begin : Nat) (strict : Bool) : Machine → Machine
  | .inl r => .inl r
  | .inr st => match stringStep doc begin strict st with
    | .done r => .inl r
    | .more next => .inr next

def runMachine (doc : String) (begin : Nat) (strict : Bool)
    (n : Nat) (initial : Machine) : Machine := Id.run do
  let mut state := initial
  for _ in List.replicate n () do
    state := tick doc begin strict state
  return state

def finishMachine (doc : String) (begin : Nat) : Machine → Outcome (String × Nat)
  | .inl r => r
  | .inr _ => .jsonError ⟨.unterminated, doc, begin⟩

def stringLoopImp (doc : String) (begin : Nat) (strict : Bool)
    (n : Nat) (st : StringState) : Outcome (String × Nat) :=
  finishMachine doc begin (runMachine doc begin strict n (.inr st))

def scanstringImp (s : String) (endPos : Nat) (strict : Bool := true) :
    Outcome (String × Nat) := Id.run do
  let mut remaining := s.toList
  remaining := remaining.drop endPos
  let mut state : StringState := ⟨remaining, endPos, []⟩
  return stringLoopImp s (endPos - 1) strict (remaining.length + 1) state

def scanOnceImp (s : String) (idx : Nat) : Outcome (Value × Nat) := Id.run do
  let xs := s.toList.drop idx
  let mut result : Outcome (Value × Nat) := .stopIteration idx
  match matchNumber xs with
  | some t => result := .ok (t.value, idx + t.width)
  | none =>
    if xs.head? = some '"' then
      result := (scanstringImp s (idx + 1)).map (fun (v, p) => (.string v, p))
    else if xs.head? = some '{' then result := objectResult xs.tail (idx + 1)
    else if xs.head? = some '[' then result := arrayResult xs.tail (idx + 1)
    else if "null".toList.isPrefixOf xs then result := .ok (.null, idx + 4)
    else if "true".toList.isPrefixOf xs then result := .ok (.boolean true, idx + 4)
    else if "false".toList.isPrefixOf xs then result := .ok (.boolean false, idx + 5)
  return result

def benchmarkLoadsImp (input : Input) : Outcome Value := Id.run do
  let mut result : Outcome Value := .typeError
  match input with
  | .other => pure ()
  | .text s => result := (scanOnceImp s 0).map Prod.fst
  return result

-- Imperative unit tests, including the original eight cases.
example : benchmarkLoadsImp (.text "true") == .ok (.boolean true) := by native_decide
example : benchmarkLoadsImp (.text "false") == .ok (.boolean false) := by native_decide
example : benchmarkLoadsImp (.text "null") == .ok .null := by native_decide
example : benchmarkLoadsImp (.text "123") == .ok (.integer 123) := by native_decide
example : benchmarkLoadsImp (.text "-7") == .ok (.integer (-7)) := by native_decide
example : benchmarkLoadsImp (.text "[]") == .ok (.array []) := by native_decide
example : benchmarkLoadsImp (.text "{}") == .ok (.object []) := by native_decide
example : benchmarkLoadsImp (.text "\"hi\"") == .ok (.string "hi") := by native_decide
example : samples.all (fun s => benchmarkLoads (.text s) == benchmarkLoadsImp (.text s)) = true :=
  by native_decide
#eval benchmarkLoadsImp (.text "\"hello\\nworld\"")

-- Kernel proofs for the actual mutable loop, including arbitrary initial states.
theorem runMachine_zero (doc : String) (begin : Nat) (strict : Bool) (st : Machine) :
    runMachine doc begin strict 0 st = st := by rfl

theorem runMachine_succ (doc : String) (begin : Nat) (strict : Bool) (n : Nat) (st : Machine) :
    runMachine doc begin strict (n + 1) st =
      runMachine doc begin strict n (tick doc begin strict st) := by
  simp only [runMachine, List.replicate_succ, List.forIn_cons]
  rfl

theorem runMachine_terminal (doc : String) (begin : Nat) (strict : Bool)
    (n : Nat) (r : Outcome (String × Nat)) :
    runMachine doc begin strict n (.inl r) = .inl r := by
  induction n with
  | zero => rfl
  | succ n ih => rw [runMachine_succ]; exact ih

theorem stringLoop_equivalence (doc : String) (begin : Nat) (strict : Bool)
    (n : Nat) (st : StringState) :
    stringLoop doc begin strict n st = stringLoopImp doc begin strict n st := by
  induction n generalizing st with
  | zero => rfl
  | succ n ih =>
    unfold stringLoopImp
    rw [runMachine_succ]
    simp only [tick, stringLoop]
    cases h : stringStep doc begin strict st with
    | done r => rw [runMachine_terminal]; rfl
    | more next => exact ih next

theorem scanstring_equivalence (s : String) (endPos : Nat) (strict : Bool) :
    scanstring s endPos strict = scanstringImp s endPos strict := by
  exact stringLoop_equivalence _ _ _ _ _

theorem scanOnce_equivalence (s : String) (idx : Nat) :
    scanOnce s idx = scanOnceImp s idx := by
  unfold scanOnce scanOnceImp
  simp only [← scanstring_equivalence]
  rfl

/-- Equality holds for every input, not only valid JSON or inputs satisfying Pre.
This includes the error position, partial array result, and divergent-object tag. -/
theorem equivalence_thm (input : Input) : benchmarkLoads input = benchmarkLoadsImp input := by
  cases input with
  | other => rfl
  | text s => exact congrArg (Outcome.map Prod.fst) (scanOnce_equivalence s 0)

end JsonDecoder24
end Agent
