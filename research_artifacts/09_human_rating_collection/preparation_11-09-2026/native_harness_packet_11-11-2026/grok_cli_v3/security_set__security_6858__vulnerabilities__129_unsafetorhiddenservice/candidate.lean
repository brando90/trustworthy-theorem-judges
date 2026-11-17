import Mathlib

/-!
# Unsafe Tor hidden-service rendezvous

Formalization of a Tor hidden-service rendezvous check that does not authenticate
the rendezvous point (MIT 6.858 Fall 2012 Quiz 2).

The Python function `unsafe_tor_rendezvous(rendezvous_addr, is_malicious,
hidden_service_connects)` returns `True` for every input. A malicious Tor onion
router can advertise itself as the rendezvous point. When the hidden service
connects, that router records the incoming connection's origin and deanonymizes
the service. The hidden service never vets the rendezvous point.

`Int` models Python `int` (unbounded, signed). `Bool` models Python `bool`.
The four quiz vectors are `0x0A000001` (honest, connects), `0xDEADBEEF`
(malicious, connects), `0x00000000` (malicious, no connect), and `0x7F000001`
(localhost, honest, no connect). All four are accepted.

## Main definitions

* `unsafe_tor_rendezvous` — functional implementation (`return True`)
* `authenticated_rendezvous` — the missing check (`not is_malicious`)
* `Pre`, property predicates, and `Post_prop`
* `unsafe_tor_rendezvous_imp` — imperative implementation (`Id.run do`)
* correctness (`Pre → Post`) and functional/imperative equivalence
-/

namespace «129_unsafeTorHiddenService»

/-! ## Implementation -/

/-- Accept the rendezvous point.

The result is `true` for every address, malice flag, and connection flag.
Vulnerability: the hidden service does not authenticate or vet the rendezvous
point, so an adversary-controlled rendezvous point is accepted. -/
def unsafe_tor_rendezvous (rendezvous_addr : Int) (is_malicious : Bool)
    (hidden_service_connects : Bool) : Bool :=
  -- All three arguments are intentionally discarded.
  let _discardAddr := rendezvous_addr
  let _discardMalicious := is_malicious
  let _discardConnects := hidden_service_connects
  true

/-- Decision a client would make if it authenticated the rendezvous point:
reject an adversary-controlled OR, accept an honest one. The unsafe
implementation does not compute this predicate. -/
def authenticated_rendezvous (is_malicious : Bool) : Bool :=
  !is_malicious

/-- What the rendezvous point learns about the hidden service. -/
inductive OriginObservation where
  /-- The malicious OR records the origin of the hidden service's connection. -/
  | hiddenServiceOrigin
  /-- No deanonymizing observation (honest OR, or the hidden service does not connect). -/
  | nothing
  deriving DecidableEq, Repr

/-- A malicious rendezvous point records the hidden service's origin exactly when
the hidden service connects to it. This is the quiz's deanonymization condition. -/
def originObservation (is_malicious : Bool) (hidden_service_connects : Bool) : OriginObservation :=
  if is_malicious && hidden_service_connects then
    OriginObservation.hiddenServiceOrigin
  else
    OriginObservation.nothing

/-! ## Unit tests -/

-- Python: assert unsafe_tor_rendezvous(0x0A000001, False, True) == True
example : unsafe_tor_rendezvous 0x0A000001 false true = true := by native_decide
#eval unsafe_tor_rendezvous 0x0A000001 false true

-- Python: assert unsafe_tor_rendezvous(0xDEADBEEF, True, True) == True
example : unsafe_tor_rendezvous 0xDEADBEEF true true = true := by native_decide
#eval unsafe_tor_rendezvous 0xDEADBEEF true true

-- Python: assert unsafe_tor_rendezvous(0x00000000, True, False) == True
example : unsafe_tor_rendezvous 0x00000000 true false = true := by native_decide
#eval unsafe_tor_rendezvous 0x00000000 true false

-- Python: assert unsafe_tor_rendezvous(0x7F000001, False, False) == True
example : unsafe_tor_rendezvous 0x7F000001 false false = true := by native_decide
#eval unsafe_tor_rendezvous 0x7F000001 false false

-- The missing authenticator rejects a malicious rendezvous and accepts an honest one.
example : authenticated_rendezvous true = false := by native_decide
example : authenticated_rendezvous false = true := by native_decide
#eval authenticated_rendezvous true
#eval authenticated_rendezvous false

-- Deanonymizing scenario: malicious rendezvous and the hidden service connects.
example : originObservation true true = OriginObservation.hiddenServiceOrigin := by native_decide
example : originObservation true false = OriginObservation.nothing := by native_decide
example : originObservation false true = OriginObservation.nothing := by native_decide
#eval originObservation true true

/-! ## Precondition -/

/-- Every Python `int` / `bool` triple is admissible.

The routine does not range-check the address and does not require the rendezvous
point to be honest or the hidden service to connect. -/
def Pre (_rendezvous_addr : Int) (_is_malicious : Bool) (_hidden_service_connects : Bool) : Prop :=
  True

/-! ## Properties -/

/-- This call accepts the rendezvous point. -/
def returns_true_prop (rendezvous_addr : Int) (is_malicious : Bool)
    (hidden_service_connects : Bool) : Prop :=
  unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects = true

/-- The body `return True`: every input is accepted. -/
def always_accepts_prop : Prop :=
  ∀ (rendezvous_addr : Int) (is_malicious hidden_service_connects : Bool),
    unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects = true

/-- The result does not depend on any argument. -/
def constant_result_prop : Prop :=
  ∀ (a1 a2 : Int) (m1 m2 c1 c2 : Bool),
    unsafe_tor_rendezvous a1 m1 c1 = unsafe_tor_rendezvous a2 m2 c2

/-- An honest rendezvous point is accepted (the Python "honest rendezvous" assert). -/
def honest_rendezvous_accepted_prop (rendezvous_addr : Int) (hidden_service_connects : Bool) : Prop :=
  unsafe_tor_rendezvous rendezvous_addr false hidden_service_connects = true

/-- A malicious rendezvous point is accepted. This is the vulnerability. -/
def malicious_rendezvous_accepted_prop (rendezvous_addr : Int)
    (hidden_service_connects : Bool) : Prop :=
  unsafe_tor_rendezvous rendezvous_addr true hidden_service_connects = true

/-- A malicious rendezvous is accepted even when the hidden service does not connect
(the Python "no-connect malicious accepted" assert). -/
def no_connect_malicious_accepted_prop (rendezvous_addr : Int) : Prop :=
  unsafe_tor_rendezvous rendezvous_addr true false = true

/-- The address is ignored: acceptance does not depend on `rendezvous_addr`. -/
def address_irrelevant_prop (is_malicious : Bool) (hidden_service_connects : Bool) : Prop :=
  ∀ a1 a2 : Int,
    unsafe_tor_rendezvous a1 is_malicious hidden_service_connects =
      unsafe_tor_rendezvous a2 is_malicious hidden_service_connects

/-- The malice flag is ignored: a malicious OR is treated like an honest one.
The hidden service does not vet the rendezvous point. -/
def malice_irrelevant_prop (rendezvous_addr : Int) (hidden_service_connects : Bool) : Prop :=
  ∀ m1 m2 : Bool,
    unsafe_tor_rendezvous rendezvous_addr m1 hidden_service_connects =
      unsafe_tor_rendezvous rendezvous_addr m2 hidden_service_connects

/-- The connect flag is ignored. -/
def connect_irrelevant_prop (rendezvous_addr : Int) (is_malicious : Bool) : Prop :=
  ∀ c1 c2 : Bool,
    unsafe_tor_rendezvous rendezvous_addr is_malicious c1 =
      unsafe_tor_rendezvous rendezvous_addr is_malicious c2

/-- Gap against authentication: the unsafe result agrees with
`authenticated_rendezvous` on an honest OR and disagrees on a malicious OR. -/
def authentication_gap_prop (rendezvous_addr : Int) (hidden_service_connects : Bool) : Prop :=
  unsafe_tor_rendezvous rendezvous_addr false hidden_service_connects =
      authenticated_rendezvous false ∧
    unsafe_tor_rendezvous rendezvous_addr true hidden_service_connects ≠
      authenticated_rendezvous true

/-- The unsafe result matches the authenticated decision if and only if the
rendezvous point is honest. On a malicious OR the two decisions differ. -/
def matches_authenticated_iff_honest_prop (rendezvous_addr : Int) (is_malicious : Bool)
    (hidden_service_connects : Bool) : Prop :=
  (unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects =
      authenticated_rendezvous is_malicious) ↔
    (is_malicious = false)

/-- Connecting to a malicious rendezvous reveals the hidden service's origin,
and the unsafe client still accepts that rendezvous. -/
def deanonymization_permitted_prop (rendezvous_addr : Int) : Prop :=
  originObservation true true = OriginObservation.hiddenServiceOrigin ∧
    unsafe_tor_rendezvous rendezvous_addr true true = true

/-- The quiz attack is possible: some malicious rendezvous address is accepted
while the hidden service connects. -/
def attack_succeeds_prop : Prop :=
  ∃ rendezvous_addr : Int, unsafe_tor_rendezvous rendezvous_addr true true = true

/-- The four asserts in the Python `check` function. -/
def check_prop : Prop :=
  unsafe_tor_rendezvous 0x0A000001 false true = true ∧
    unsafe_tor_rendezvous 0xDEADBEEF true true = true ∧
      unsafe_tor_rendezvous 0x00000000 true false = true ∧
        unsafe_tor_rendezvous 0x7F000001 false false = true

theorem returns_true_thm (rendezvous_addr : Int) (is_malicious : Bool)
    (hidden_service_connects : Bool) :
    returns_true_prop rendezvous_addr is_malicious hidden_service_connects := by
  rfl

theorem always_accepts_thm : always_accepts_prop := by
  intro _rendezvous_addr _is_malicious _hidden_service_connects
  rfl

theorem constant_result_thm : constant_result_prop := by
  intro _a1 _a2 _m1 _m2 _c1 _c2
  rfl

theorem honest_rendezvous_accepted_thm (rendezvous_addr : Int) (hidden_service_connects : Bool) :
    honest_rendezvous_accepted_prop rendezvous_addr hidden_service_connects := by
  rfl

theorem malicious_rendezvous_accepted_thm (rendezvous_addr : Int) (hidden_service_connects : Bool) :
    malicious_rendezvous_accepted_prop rendezvous_addr hidden_service_connects := by
  rfl

theorem no_connect_malicious_accepted_thm (rendezvous_addr : Int) :
    no_connect_malicious_accepted_prop rendezvous_addr := by
  rfl

theorem address_irrelevant_thm (is_malicious : Bool) (hidden_service_connects : Bool) :
    address_irrelevant_prop is_malicious hidden_service_connects := by
  intro _a1 _a2
  rfl

theorem malice_irrelevant_thm (rendezvous_addr : Int) (hidden_service_connects : Bool) :
    malice_irrelevant_prop rendezvous_addr hidden_service_connects := by
  intro _m1 _m2
  rfl

theorem connect_irrelevant_thm (rendezvous_addr : Int) (is_malicious : Bool) :
    connect_irrelevant_prop rendezvous_addr is_malicious := by
  intro _c1 _c2
  rfl

theorem authentication_gap_thm (rendezvous_addr : Int) (hidden_service_connects : Bool) :
    authentication_gap_prop rendezvous_addr hidden_service_connects := by
  unfold authentication_gap_prop authenticated_rendezvous unsafe_tor_rendezvous
  constructor
  · rfl
  · intro h
    cases h

theorem matches_authenticated_iff_honest_thm (rendezvous_addr : Int) (is_malicious : Bool)
    (hidden_service_connects : Bool) :
    matches_authenticated_iff_honest_prop rendezvous_addr is_malicious hidden_service_connects := by
  unfold matches_authenticated_iff_honest_prop authenticated_rendezvous unsafe_tor_rendezvous
  cases is_malicious with
  | false =>
    constructor
    · intro _
      rfl
    · intro _
      rfl
  | true =>
    constructor
    · intro h
      cases h
    · intro h
      cases h

theorem deanonymization_permitted_thm (rendezvous_addr : Int) :
    deanonymization_permitted_prop rendezvous_addr := by
  unfold deanonymization_permitted_prop originObservation unsafe_tor_rendezvous
  constructor <;> rfl

theorem attack_succeeds_thm : attack_succeeds_prop := by
  unfold attack_succeeds_prop
  exact ⟨(0xDEADBEEF : Int), rfl⟩

theorem check_thm : check_prop := by
  unfold check_prop
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Every input satisfies `Pre`. -/
theorem pre_total_thm (rendezvous_addr : Int) (is_malicious : Bool)
    (hidden_service_connects : Bool) :
    Pre rendezvous_addr is_malicious hidden_service_connects := by
  trivial

/-! ## Postcondition -/

/-- Postcondition of one call: the rendezvous is accepted, the decision ignores
the address, the malice flag, and the connect flag, and that acceptance disagrees
with authentication exactly on a malicious rendezvous point (the deanonymization
window included). The Python regression vectors hold as well. -/
def Post_prop (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) : Prop :=
  returns_true_prop rendezvous_addr is_malicious hidden_service_connects ∧
    always_accepts_prop ∧
      constant_result_prop ∧
        honest_rendezvous_accepted_prop rendezvous_addr hidden_service_connects ∧
          malicious_rendezvous_accepted_prop rendezvous_addr hidden_service_connects ∧
            no_connect_malicious_accepted_prop rendezvous_addr ∧
              address_irrelevant_prop is_malicious hidden_service_connects ∧
                malice_irrelevant_prop rendezvous_addr hidden_service_connects ∧
                  connect_irrelevant_prop rendezvous_addr is_malicious ∧
                    authentication_gap_prop rendezvous_addr hidden_service_connects ∧
                      matches_authenticated_iff_honest_prop rendezvous_addr is_malicious
                          hidden_service_connects ∧
                        deanonymization_permitted_prop rendezvous_addr ∧
                          attack_succeeds_prop ∧
                            check_prop

/-! ## Property-based tests -/

/-- Executable pointwise fragment of `Post_prop`.

Universal conjuncts (`always_accepts_prop`, `constant_result_prop`,
`address_irrelevant_prop`, `malice_irrelevant_prop`, `connect_irrelevant_prop`)
are checked by their own PBTs below. `check_prop` and `attack_succeeds_prop`
are included via the four quiz vectors, one of which is the attack witness. -/
def postBool (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) : Bool :=
  (unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects == true) &&
    (unsafe_tor_rendezvous rendezvous_addr false hidden_service_connects == true) &&
      (unsafe_tor_rendezvous rendezvous_addr true hidden_service_connects == true) &&
        (unsafe_tor_rendezvous rendezvous_addr true false == true) &&
          (unsafe_tor_rendezvous rendezvous_addr false hidden_service_connects ==
              authenticated_rendezvous false) &&
            (unsafe_tor_rendezvous rendezvous_addr true hidden_service_connects !=
                authenticated_rendezvous true) &&
              ((unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects ==
                    authenticated_rendezvous is_malicious) ==
                  (is_malicious == false)) &&
                (originObservation true true == OriginObservation.hiddenServiceOrigin) &&
                  (unsafe_tor_rendezvous rendezvous_addr true true == true) &&
                    (unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects ==
                        unsafe_tor_rendezvous (rendezvous_addr + 1) is_malicious
                          hidden_service_connects) &&
                      (unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects ==
                          unsafe_tor_rendezvous rendezvous_addr (!is_malicious)
                            hidden_service_connects) &&
                        (unsafe_tor_rendezvous rendezvous_addr is_malicious
                              hidden_service_connects ==
                            unsafe_tor_rendezvous rendezvous_addr is_malicious
                              (!hidden_service_connects)) &&
                          (unsafe_tor_rendezvous 0x0A000001 false true &&
                            unsafe_tor_rendezvous 0xDEADBEEF true true &&
                              unsafe_tor_rendezvous 0x00000000 true false &&
                                unsafe_tor_rendezvous 0x7F000001 false false)

/-- Addresses used by the bounded checks: a signed window plus the quiz vectors. -/
def addrWindow : List Int :=
  (List.range 16).map Int.ofNat ++
    (List.range 16).map (fun n => -Int.ofNat n) ++
      [0x0A000001, 0xDEADBEEF, 0x00000000, 0x7F000001, 0xFFFFFFFF, (2 : Int) ^ 32, (2 : Int) ^ 64]

/-- Both Boolean values. -/
def boolPairs : List (Bool × Bool) :=
  [(true, true), (true, false), (false, true), (false, false)]

-- PBT (randomized): returns_true_prop
#eval Plausible.Testable.check
  (∀ (rendezvous_addr : Int) (is_malicious hidden_service_connects : Bool),
    unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects = true)

-- PBT (bounded): returns_true_prop
example : addrWindow.all (fun a =>
    boolPairs.all (fun mc =>
      unsafe_tor_rendezvous a mc.fst mc.snd == true)) = true := by
  native_decide

-- PBT (randomized): always_accepts_prop
#eval Plausible.Testable.check
  (∀ (rendezvous_addr : Int) (is_malicious hidden_service_connects : Bool),
    unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects = true)

-- PBT (bounded): always_accepts_prop
example : addrWindow.all (fun a =>
    ([true, false]).all (fun m =>
      ([true, false]).all (fun c =>
        unsafe_tor_rendezvous a m c == true))) = true := by
  native_decide

-- PBT (randomized): constant_result_prop
#eval Plausible.Testable.check
  (∀ (a1 a2 : Int) (m1 m2 c1 c2 : Bool),
    unsafe_tor_rendezvous a1 m1 c1 = unsafe_tor_rendezvous a2 m2 c2)

-- PBT (bounded): constant_result_prop
example : addrWindow.all (fun a1 =>
    addrWindow.all (fun a2 =>
      boolPairs.all (fun p1 =>
        boolPairs.all (fun p2 =>
          unsafe_tor_rendezvous a1 p1.fst p1.snd ==
            unsafe_tor_rendezvous a2 p2.fst p2.snd)))) = true := by
  native_decide

-- PBT (randomized): honest_rendezvous_accepted_prop
#eval Plausible.Testable.check
  (∀ (rendezvous_addr : Int) (hidden_service_connects : Bool),
    unsafe_tor_rendezvous rendezvous_addr false hidden_service_connects = true)

-- PBT (bounded): honest_rendezvous_accepted_prop
example : addrWindow.all (fun a =>
    ([true, false]).all (fun c =>
      unsafe_tor_rendezvous a false c == true)) = true := by
  native_decide

-- PBT (randomized): malicious_rendezvous_accepted_prop
#eval Plausible.Testable.check
  (∀ (rendezvous_addr : Int) (hidden_service_connects : Bool),
    unsafe_tor_rendezvous rendezvous_addr true hidden_service_connects = true)

-- PBT (bounded): malicious_rendezvous_accepted_prop
example : addrWindow.all (fun a =>
    ([true, false]).all (fun c =>
      unsafe_tor_rendezvous a true c == true)) = true := by
  native_decide

-- PBT (randomized): no_connect_malicious_accepted_prop
#eval Plausible.Testable.check
  (∀ rendezvous_addr : Int, unsafe_tor_rendezvous rendezvous_addr true false = true)

-- PBT (bounded): no_connect_malicious_accepted_prop
example : addrWindow.all (fun a =>
    unsafe_tor_rendezvous a true false == true) = true := by
  native_decide

-- PBT (randomized): address_irrelevant_prop
#eval Plausible.Testable.check
  (∀ (a1 a2 : Int) (is_malicious hidden_service_connects : Bool),
    unsafe_tor_rendezvous a1 is_malicious hidden_service_connects =
      unsafe_tor_rendezvous a2 is_malicious hidden_service_connects)

-- PBT (bounded): address_irrelevant_prop
example : addrWindow.all (fun a1 =>
    addrWindow.all (fun a2 =>
      boolPairs.all (fun mc =>
        unsafe_tor_rendezvous a1 mc.fst mc.snd ==
          unsafe_tor_rendezvous a2 mc.fst mc.snd))) = true := by
  native_decide

-- PBT (randomized): malice_irrelevant_prop
#eval Plausible.Testable.check
  (∀ (rendezvous_addr : Int) (hidden_service_connects m1 m2 : Bool),
    unsafe_tor_rendezvous rendezvous_addr m1 hidden_service_connects =
      unsafe_tor_rendezvous rendezvous_addr m2 hidden_service_connects)

-- PBT (bounded): malice_irrelevant_prop
example : addrWindow.all (fun a =>
    ([true, false]).all (fun c =>
      ([true, false]).all (fun m1 =>
        ([true, false]).all (fun m2 =>
          unsafe_tor_rendezvous a m1 c == unsafe_tor_rendezvous a m2 c)))) = true := by
  native_decide

-- PBT (randomized): connect_irrelevant_prop
#eval Plausible.Testable.check
  (∀ (rendezvous_addr : Int) (is_malicious c1 c2 : Bool),
    unsafe_tor_rendezvous rendezvous_addr is_malicious c1 =
      unsafe_tor_rendezvous rendezvous_addr is_malicious c2)

-- PBT (bounded): connect_irrelevant_prop
example : addrWindow.all (fun a =>
    ([true, false]).all (fun m =>
      ([true, false]).all (fun c1 =>
        ([true, false]).all (fun c2 =>
          unsafe_tor_rendezvous a m c1 == unsafe_tor_rendezvous a m c2)))) = true := by
  native_decide

-- PBT (randomized): authentication_gap_prop
#eval Plausible.Testable.check
  (∀ (rendezvous_addr : Int) (hidden_service_connects : Bool),
    unsafe_tor_rendezvous rendezvous_addr false hidden_service_connects =
        authenticated_rendezvous false ∧
      unsafe_tor_rendezvous rendezvous_addr true hidden_service_connects ≠
        authenticated_rendezvous true)

-- PBT (bounded): authentication_gap_prop
example : addrWindow.all (fun a =>
    ([true, false]).all (fun c =>
      (unsafe_tor_rendezvous a false c == authenticated_rendezvous false) &&
        (unsafe_tor_rendezvous a true c != authenticated_rendezvous true))) = true := by
  native_decide

-- PBT (randomized): matches_authenticated_iff_honest_prop
#eval Plausible.Testable.check
  (∀ (rendezvous_addr : Int) (is_malicious hidden_service_connects : Bool),
    (unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects ==
        authenticated_rendezvous is_malicious) =
      (is_malicious == false))

-- PBT (bounded): matches_authenticated_iff_honest_prop
example : addrWindow.all (fun a =>
    boolPairs.all (fun mc =>
      (unsafe_tor_rendezvous a mc.fst mc.snd == authenticated_rendezvous mc.fst) ==
        (mc.fst == false))) = true := by
  native_decide

-- PBT (randomized): deanonymization_permitted_prop
#eval Plausible.Testable.check
  (∀ rendezvous_addr : Int,
    originObservation true true = OriginObservation.hiddenServiceOrigin ∧
      unsafe_tor_rendezvous rendezvous_addr true true = true)

-- PBT (bounded): deanonymization_permitted_prop
example : addrWindow.all (fun a =>
    (originObservation true true == OriginObservation.hiddenServiceOrigin) &&
      (unsafe_tor_rendezvous a true true == true)) = true := by
  native_decide

-- PBT (bounded witness search): attack_succeeds_prop
-- Plausible has no useful sampler obligation here: the property is existential,
-- so the executable check searches `addrWindow` for an accepting malicious rendezvous.
example : addrWindow.any (fun a => unsafe_tor_rendezvous a true true) = true := by
  native_decide

-- PBT (closed): check_prop
example :
    (unsafe_tor_rendezvous 0x0A000001 false true &&
      unsafe_tor_rendezvous 0xDEADBEEF true true &&
        unsafe_tor_rendezvous 0x00000000 true false &&
          unsafe_tor_rendezvous 0x7F000001 false false) = true := by
  native_decide

-- PBT (randomized): Post_prop pointwise fragment (`postBool`)
#eval Plausible.Testable.check
  (∀ (rendezvous_addr : Int) (is_malicious hidden_service_connects : Bool),
    postBool rendezvous_addr is_malicious hidden_service_connects = true)

-- PBT (bounded): Post_prop pointwise fragment (`postBool`)
example : addrWindow.all (fun a =>
    boolPairs.all (fun mc =>
      postBool a mc.fst mc.snd)) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (rendezvous_addr : Int) (is_malicious : Bool)
    (hidden_service_connects : Bool)
    (_h : Pre rendezvous_addr is_malicious hidden_service_connects) :
    Post_prop rendezvous_addr is_malicious hidden_service_connects := by
  unfold Post_prop
  exact
    ⟨returns_true_thm rendezvous_addr is_malicious hidden_service_connects,
      always_accepts_thm, constant_result_thm,
      honest_rendezvous_accepted_thm rendezvous_addr hidden_service_connects,
      malicious_rendezvous_accepted_thm rendezvous_addr hidden_service_connects,
      no_connect_malicious_accepted_thm rendezvous_addr,
      address_irrelevant_thm is_malicious hidden_service_connects,
      malice_irrelevant_thm rendezvous_addr hidden_service_connects,
      connect_irrelevant_thm rendezvous_addr is_malicious,
      authentication_gap_thm rendezvous_addr hidden_service_connects,
      matches_authenticated_iff_honest_thm rendezvous_addr is_malicious hidden_service_connects,
      deanonymization_permitted_thm rendezvous_addr, attack_succeeds_thm, check_thm⟩

/-- `Post_prop` holds for every input, because `Pre` is total. -/
theorem post_holds_thm (rendezvous_addr : Int) (is_malicious : Bool)
    (hidden_service_connects : Bool) :
    Post_prop rendezvous_addr is_malicious hidden_service_connects :=
  correctness_thm rendezvous_addr is_malicious hidden_service_connects
    (pre_total_thm rendezvous_addr is_malicious hidden_service_connects)

/-! ## Imperative implementation -/

/-- Imperative rendering of `unsafe_tor_rendezvous`.

`accepted` starts `true`. Every branch stores the request parameters and then
leaves `accepted` equal to `true`. No branch rejects a malicious rendezvous
point, so the hidden service never authenticates it. -/
def unsafe_tor_rendezvous_imp (rendezvous_addr : Int) (is_malicious : Bool)
    (hidden_service_connects : Bool) : Bool :=
  Id.run do
    let mut accepted : Bool := true
    let mut addr : Int := rendezvous_addr
    let mut malicious : Bool := is_malicious
    let mut connects : Bool := hidden_service_connects
    -- Vulnerable: a malicious rendezvous is accepted whether or not the
    -- hidden service connects. An honest rendezvous is accepted as well.
    if malicious && connects then
      accepted := true
    else if malicious && !connects then
      accepted := true
    else
      accepted := true
    -- The address is retained and then discarded; it does not affect acceptance.
    addr := addr
    return accepted

theorem imp_returns_true_thm (rendezvous_addr : Int) (is_malicious : Bool)
    (hidden_service_connects : Bool) :
    unsafe_tor_rendezvous_imp rendezvous_addr is_malicious hidden_service_connects = true := by
  cases is_malicious <;> cases hidden_service_connects <;> rfl

/-! ## Imperative tests -/

example : unsafe_tor_rendezvous_imp 0x0A000001 false true = true := by native_decide
#eval unsafe_tor_rendezvous_imp 0x0A000001 false true

example : unsafe_tor_rendezvous_imp 0xDEADBEEF true true = true := by native_decide
#eval unsafe_tor_rendezvous_imp 0xDEADBEEF true true

example : unsafe_tor_rendezvous_imp 0x00000000 true false = true := by native_decide
#eval unsafe_tor_rendezvous_imp 0x00000000 true false

example : unsafe_tor_rendezvous_imp 0x7F000001 false false = true := by native_decide
#eval unsafe_tor_rendezvous_imp 0x7F000001 false false

example : unsafe_tor_rendezvous 0x0A000001 false true =
    unsafe_tor_rendezvous_imp 0x0A000001 false true := by native_decide
example : unsafe_tor_rendezvous 0xDEADBEEF true true =
    unsafe_tor_rendezvous_imp 0xDEADBEEF true true := by native_decide
example : unsafe_tor_rendezvous 0x00000000 true false =
    unsafe_tor_rendezvous_imp 0x00000000 true false := by native_decide
example : unsafe_tor_rendezvous 0x7F000001 false false =
    unsafe_tor_rendezvous_imp 0x7F000001 false false := by native_decide

-- Bounded check that the imperative loop matches the functional result on the window.
example : addrWindow.all (fun a =>
    boolPairs.all (fun mc =>
      unsafe_tor_rendezvous a mc.fst mc.snd ==
        unsafe_tor_rendezvous_imp a mc.fst mc.snd)) = true := by
  native_decide

/-! ## Equivalence -/

theorem equiv_thm (rendezvous_addr : Int) (is_malicious : Bool) (hidden_service_connects : Bool) :
    unsafe_tor_rendezvous rendezvous_addr is_malicious hidden_service_connects =
      unsafe_tor_rendezvous_imp rendezvous_addr is_malicious hidden_service_connects := by
  cases is_malicious <;> cases hidden_service_connects <;> rfl

end «129_unsafeTorHiddenService»
