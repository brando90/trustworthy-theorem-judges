import Mathlib
namespace Agent

/-!
# Safe SSL/TLS Finished MAC check

Translation of the Python simplified Finished-MAC model. Message identifiers,
MACs, and secrets are unbounded signed integers. `Int.xor` models Python's
bitwise XOR, including negative integers. This is a model of the CCS gating
fix, not a cryptographic security claim about XOR as a real MAC.

The server rejects Finished when ChangeCipherSpec (CCS) has not previously
arrived. With CCS, it accepts exactly the XOR fold seeded by the master secret.
The Boolean input records prior receipt of CCS, as in the source program.
-/

namespace «157_unsafeSSLFinishedMAC_safe»

/-- XOR each message ID into the running MAC, initially the master secret. -/
def compute_finished_mac (messages : List Int) (master_secret : Int) : Int :=
  messages.foldl Int.xor master_secret

/-- Reject without CCS before doing the Finished comparison. -/
def safe_ssl_finished_check (received_messages : List Int)
    (finished_mac master_secret : Int) (change_cipher_spec_received : Bool) : Bool :=
  if change_cipher_spec_received then
    decide (finished_mac = compute_finished_mac received_messages master_secret)
  else false

-- The five tests in the Python source.
example : safe_ssl_finished_check [1, 2, 3, 4, 5]
    (compute_finished_mac [1, 2, 3, 4, 5] 42) 42 true = true := by native_decide
example : safe_ssl_finished_check [1, 2, 3, 4, 5]
    (compute_finished_mac [1, 2, 3, 4, 5] 42) 42 false = false := by native_decide
example : safe_ssl_finished_check [1, 2, 3, 4, 5]
    (compute_finished_mac [1, 2, 3, 4, 5] 42 + 1) 42 true = false := by native_decide
example : safe_ssl_finished_check [] (compute_finished_mac [] 42) 42 true = true := by
  native_decide
example : safe_ssl_finished_check [] (compute_finished_mac [] 42) 42 false = false := by
  native_decide
example : compute_finished_mac [1, 2, 3, 4, 5] 42 = 43 := by native_decide
example : compute_finished_mac [-1, 2] 42 = -41 := by native_decide
example : safe_ssl_finished_check [-1, 2] (-41) 42 true = true := by native_decide
example : safe_ssl_finished_check [] (-42) (-42) true = true := by native_decide

/-- Executable translation of Python's `check` test harness. -/
def check (candidate : List Int → Int → Int → Bool → Bool) : Bool :=
  let msgs := [1, 2, 3, 4, 5]
  let secret := 42
  let mac := compute_finished_mac msgs secret
  let empty_mac := compute_finished_mac [] secret
  candidate msgs mac secret true &&
  !(candidate msgs mac secret false) &&
  !(candidate msgs (mac + 1) secret true) &&
  candidate [] empty_mac secret true &&
  !(candidate [] empty_mac secret false)

example : check safe_ssl_finished_check = true := by native_decide
#eval compute_finished_mac [1, 2, 3, 4, 5] 42
#eval check safe_ssl_finished_check

/-- Python imposes no restrictions on the integer inputs or message list. -/
def Pre (_messages : List Int) (_finished_mac _master_secret : Int)
    (_ccs : Bool) : Prop := True

/-- The empty transcript leaves the initial secret unchanged. -/
def mac_empty_prop (secret : Int) : Prop :=
  compute_finished_mac [] secret = secret

theorem mac_empty_thm (secret : Int) : mac_empty_prop secret := by
  rfl

/-- One iteration XORs the first message and then processes the tail. -/
def mac_step_prop (msg : Int) (messages : List Int) (secret : Int) : Prop :=
  compute_finished_mac (msg :: messages) secret =
    compute_finished_mac messages (Int.xor secret msg)

theorem mac_step_thm (msg : Int) (messages : List Int) (secret : Int) :
    mac_step_prop msg messages secret := by
  rfl

/-- Processing concatenated transcripts is the same as continuing the fold. -/
def mac_append_prop (xs ys : List Int) (secret : Int) : Prop :=
  compute_finished_mac (xs ++ ys) secret =
    compute_finished_mac ys (compute_finished_mac xs secret)

theorem mac_append_thm (xs ys : List Int) (secret : Int) :
    mac_append_prop xs ys secret := by
  simp [mac_append_prop, compute_finished_mac, List.foldl_append]

/-- Exact acceptance characterization: both prior CCS and a matching MAC. -/
def acceptance_prop (messages : List Int) (mac secret : Int) (ccs : Bool) : Prop :=
  safe_ssl_finished_check messages mac secret ccs = true ↔
    ccs = true ∧ mac = compute_finished_mac messages secret

theorem acceptance_thm (messages : List Int) (mac secret : Int) (ccs : Bool) :
    acceptance_prop messages mac secret ccs := by
  cases ccs <;> simp [acceptance_prop, safe_ssl_finished_check]

/-- The attack of dropping CCS fails, even if the supplied MAC is correct. -/
def no_ccs_prop (messages : List Int) (mac secret : Int) : Prop :=
  safe_ssl_finished_check messages mac secret false = false

theorem no_ccs_thm (messages : List Int) (mac secret : Int) :
    no_ccs_prop messages mac secret := by
  rfl

/-- With the correct MAC, the result is exactly the prior-CCS flag. -/
def matching_mac_prop (messages : List Int) (secret : Int) (ccs : Bool) : Prop :=
  safe_ssl_finished_check messages (compute_finished_mac messages secret) secret ccs = ccs

theorem matching_mac_thm (messages : List Int) (secret : Int) (ccs : Bool) :
    matching_mac_prop messages secret ccs := by
  cases ccs <;> simp [matching_mac_prop, safe_ssl_finished_check]

/-- A wrong MAC is rejected regardless of whether CCS arrived. -/
def wrong_mac_prop (messages : List Int) (mac secret : Int) (ccs : Bool) : Prop :=
  mac ≠ compute_finished_mac messages secret →
    safe_ssl_finished_check messages mac secret ccs = false

theorem wrong_mac_thm (messages : List Int) (mac secret : Int) (ccs : Bool) :
    wrong_mac_prop messages mac secret ccs := by
  intro h
  cases ccs <;> simp_all [safe_ssl_finished_check]

/-- Empty transcripts still require CCS and a MAC equal to the secret. -/
def empty_check_prop (mac secret : Int) (ccs : Bool) : Prop :=
  safe_ssl_finished_check [] mac secret ccs = (ccs && decide (mac = secret))

theorem empty_check_thm (mac secret : Int) (ccs : Bool) :
    empty_check_prop mac secret ccs := by
  cases ccs <;> simp [empty_check_prop, safe_ssl_finished_check, compute_finished_mac]

/-- The postcondition combines exact behavior, the mitigation, edge cases,
and the equations specifying the MAC computation. -/
def Post_prop (messages : List Int) (mac secret : Int) (ccs : Bool) : Prop :=
  acceptance_prop messages mac secret ccs ∧
  no_ccs_prop messages mac secret ∧
  matching_mac_prop messages secret ccs ∧
  wrong_mac_prop messages mac secret ccs ∧
  empty_check_prop mac secret ccs ∧
  mac_empty_prop secret ∧
  (∀ msg : Int, mac_step_prop msg messages secret) ∧
  (∀ suffix : List Int, mac_append_prop messages suffix secret)

/-! ## Property-based tests

These are bounded, exhaustive executable checks, separate from the proofs.
They include signed integers, empty transcripts, repeated IDs and both CCS
flags. In particular, rejection properties are tested on matching as well as
nonmatching MACs, rather than only random unequal values.
-/

private def smallInts : List Int := (List.range 9).map (fun n => (n : Int) - 4)
private def smallMessages : List (List Int) :=
  [[]] ++ smallInts.map (fun x => [x]) ++
    smallInts.flatMap (fun x => smallInts.map (fun y => [x, y]))

-- PBT for mac_empty_prop.
example : smallInts.all (fun s => compute_finished_mac [] s == s) = true := by
  native_decide

-- PBT for mac_step_prop.
example : smallInts.all (fun x => smallMessages.all (fun xs => smallInts.all (fun s =>
    compute_finished_mac (x :: xs) s == compute_finished_mac xs (Int.xor s x)))) =
    true := by native_decide

-- PBT for mac_append_prop.
example : smallMessages.all (fun xs => smallMessages.all (fun ys => smallInts.all (fun s =>
    compute_finished_mac (xs ++ ys) s ==
      compute_finished_mac ys (compute_finished_mac xs s)))) = true := by native_decide

-- PBT for acceptance_prop (Boolean equality expresses the iff).
example : smallMessages.all (fun xs => smallInts.all (fun s =>
    (compute_finished_mac xs s :: smallInts).all (fun mac => [false, true].all (fun c =>
      safe_ssl_finished_check xs mac s c ==
        (c && decide (mac = compute_finished_mac xs s)))))) = true := by native_decide

-- PBT for no_ccs_prop, explicitly including the correct MAC.
example : smallMessages.all (fun xs => smallInts.all (fun s =>
    (compute_finished_mac xs s :: smallInts).all (fun mac =>
      !(safe_ssl_finished_check xs mac s false)))) = true := by native_decide

-- PBT for matching_mac_prop.
example : smallMessages.all (fun xs => smallInts.all (fun s => [false, true].all (fun c =>
    safe_ssl_finished_check xs (compute_finished_mac xs s) s c == c))) = true := by
  native_decide

-- PBT for wrong_mac_prop; (!premise || conclusion) is executable implication.
example : smallMessages.all (fun xs => smallInts.all (fun s =>
    (compute_finished_mac xs s :: (compute_finished_mac xs s + 1) :: smallInts).all
      (fun mac => [false, true].all (fun c =>
        decide (mac = compute_finished_mac xs s) ||
          !(safe_ssl_finished_check xs mac s c))))) = true := by native_decide

-- PBT for empty_check_prop.
example : smallInts.all (fun mac => smallInts.all (fun s => [false, true].all (fun c =>
    safe_ssl_finished_check [] mac s c == (c && decide (mac = s))))) = true := by
  native_decide

-- PBT for Post_prop: each conjunct, with the quantified msg/suffix clauses
-- instantiated over the same bounded domains. Pre is True for every input.
private def postTest (xs : List Int) (mac s : Int) (c : Bool) : Bool :=
  (safe_ssl_finished_check xs mac s c == (c && decide (mac = compute_finished_mac xs s))) &&
  !(safe_ssl_finished_check xs mac s false) &&
  (safe_ssl_finished_check xs (compute_finished_mac xs s) s c == c) &&
  (decide (mac = compute_finished_mac xs s) || !(safe_ssl_finished_check xs mac s c)) &&
  (safe_ssl_finished_check [] mac s c == (c && decide (mac = s))) &&
  (compute_finished_mac [] s == s) &&
  smallInts.all (fun x =>
    compute_finished_mac (x :: xs) s == compute_finished_mac xs (Int.xor s x)) &&
  smallMessages.all (fun ys =>
    compute_finished_mac (xs ++ ys) s == compute_finished_mac ys (compute_finished_mac xs s))

example : smallMessages.all (fun xs => smallInts.all (fun s =>
    (compute_finished_mac xs s :: (compute_finished_mac xs s + 1) :: smallInts).all
      (fun mac => [false, true].all (fun c => postTest xs mac s c)))) = true := by
  native_decide
#eval smallMessages.all (fun xs => smallInts.all (fun s =>
  [false, true].all (fun c => postTest xs (compute_finished_mac xs s) s c)))

/-- Full correctness over all Python-admissible inputs, not just test samples. -/
theorem correctness_thm (messages : List Int) (mac secret : Int) (ccs : Bool) :
    Pre messages mac secret ccs → Post_prop messages mac secret ccs := by
  intro _
  exact ⟨acceptance_thm messages mac secret ccs,
    no_ccs_thm messages mac secret,
    matching_mac_thm messages secret ccs,
    wrong_mac_thm messages mac secret ccs,
    empty_check_thm mac secret ccs,
    mac_empty_thm secret,
    fun msg => mac_step_thm msg messages secret,
    fun suffix => mac_append_thm messages suffix secret⟩

/-! ## Imperative translation -/

/-- Literal mutable accumulator and for-loop from `compute_finished_mac`. -/
def compute_finished_mac_imperative (messages : List Int) (master_secret : Int) : Int :=
  Id.run do
    let mut result := master_secret
    for msg in messages do
      result := Int.xor result msg
    return result

/-- Literal early return for missing CCS, followed by the comparison. -/
def safe_ssl_finished_check_imperative (received_messages : List Int)
    (finished_mac master_secret : Int) (change_cipher_spec_received : Bool) : Bool :=
  Id.run do
    if !change_cipher_spec_received then
      return false
    let mut expected_mac := master_secret
    expected_mac := compute_finished_mac_imperative received_messages expected_mac
    return finished_mac == expected_mac

example : check safe_ssl_finished_check_imperative = true := by native_decide
example : compute_finished_mac_imperative [-1, 2] 42 = -41 := by native_decide
example : safe_ssl_finished_check_imperative [] (-42) (-42) true = true := by native_decide
example : safe_ssl_finished_check_imperative [-1, 2] (-41) 42 false = false := by
  native_decide
#eval check safe_ssl_finished_check_imperative
#eval compute_finished_mac_imperative [1, 2, 3, 4, 5] 42

-- Bounded cross-implementation tests, including the correct and an incorrect MAC.
example : smallMessages.all (fun xs => smallInts.all (fun s =>
    compute_finished_mac xs s == compute_finished_mac_imperative xs s)) = true := by
  native_decide
example : smallMessages.all (fun xs => smallInts.all (fun s =>
    (compute_finished_mac xs s :: (compute_finished_mac xs s + 1) :: smallInts).all
      (fun mac => [false, true].all (fun c =>
        safe_ssl_finished_check xs mac s c ==
          safe_ssl_finished_check_imperative xs mac s c)))) = true := by native_decide

/-- A yielding mutable loop is precisely the functional left fold. The
standard-library loop-to-fold theorem is kernel checked, not a test. -/
theorem compute_finished_mac_equiv (messages : List Int) (secret : Int) :
    compute_finished_mac messages secret = compute_finished_mac_imperative messages secret := by
  simp [compute_finished_mac, compute_finished_mac_imperative]

/-- Pointwise equivalence, including the early-return branch for missing CCS. -/
theorem safe_ssl_finished_check_equiv (messages : List Int) (mac secret : Int) (ccs : Bool) :
    safe_ssl_finished_check messages mac secret ccs =
      safe_ssl_finished_check_imperative messages mac secret ccs := by
  cases ccs <;> simp [safe_ssl_finished_check, safe_ssl_finished_check_imperative,
    ← compute_finished_mac_equiv, Bool.beq_eq_decide_eq]

/-- Equality of the complete functional and imperative checker functions. -/
theorem functional_imperative_equiv :
    safe_ssl_finished_check = safe_ssl_finished_check_imperative := by
  funext messages mac secret ccs
  exact safe_ssl_finished_check_equiv messages mac secret ccs

end «157_unsafeSSLFinishedMAC_safe»
end Agent
