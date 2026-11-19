import Mathlib
namespace Agent

/-!
# Unsafe direct routing

Translation of the Python `unsafe_direct_route` example from MIT 6.858,
Lecture 19. A packet is `(source IP, destination IP, message)`, represented
by the right-associated product `Int × Int × Int`. Python integers are
unbounded and signed, so all fields use `Int`, without an IP-range restriction.

Direct routing exposes both addresses and preserves the message. Reading the
first field recovers the source exactly, so different sources are distinguishable
and the source/destination pair is directly observable. These are statements
about the visible packet, not assumptions about an external network model.

Tests are executable evidence only; every named theorem has a kernel proof.
-/

namespace UnsafeDirectRoute

/-! ## Functional implementation -/

def unsafe_direct_route (src_ip dst_ip msg : Int) : Int × Int × Int :=
  (src_ip, dst_ip, msg)

/-- Executable translation of every assertion in the Python `check` function. -/
def check (candidate : Int → Int → Int → Int × Int × Int) : Bool :=
  let result := candidate 192168001 8080 42
  let r1 := candidate 10 20 99
  let r2 := candidate 11 20 99
  decide (result.1 = 192168001 ∧
    result.2.1 = 8080 ∧
    result.2.2 = 42 ∧
    r1.1 ≠ r2.1 ∧
    candidate 0 0 0 = (0, 0, 0) ∧
    (candidate 1 2 3).1 = 1)

/-! ## Unit tests -/

example : unsafe_direct_route 192168001 8080 42 = (192168001, 8080, 42) := by
  native_decide

example : (unsafe_direct_route 10 20 99).1 ≠ (unsafe_direct_route 11 20 99).1 := by
  native_decide

example : unsafe_direct_route 0 0 0 = (0, 0, 0) := by
  native_decide

example : (unsafe_direct_route 1 2 3).1 = 1 := by
  native_decide

-- Negative values are also valid Python integers, including in address fields.
example : unsafe_direct_route (-10) (-20) (-99) = (-10, -20, -99) := by
  native_decide

example : check unsafe_direct_route = true := by
  native_decide

#eval unsafe_direct_route 192168001 8080 42
#eval check unsafe_direct_route
#eval if check unsafe_direct_route then "All tests passed." else "Tests failed."

/-! ## Precondition -/

/-- The Python function is total on all integer inputs. -/
def Pre (_src_ip _dst_ip _msg : Int) : Prop := True

/-! ## Properties and kernel-checked proofs -/

/-- The returned triple is exactly the supplied triple. -/
def route_exact_prop (src_ip dst_ip msg : Int) : Prop :=
  unsafe_direct_route src_ip dst_ip msg = (src_ip, dst_ip, msg)

theorem route_exact_thm (src_ip dst_ip msg : Int) :
    route_exact_prop src_ip dst_ip msg := by
  rfl

/-- An observer reads the source IP directly from the first field. -/
def source_visible_prop (src_ip dst_ip msg : Int) : Prop :=
  (unsafe_direct_route src_ip dst_ip msg).1 = src_ip

theorem source_visible_thm (src_ip dst_ip msg : Int) :
    source_visible_prop src_ip dst_ip msg := by
  rfl

/-- Direct routing does not change the destination. -/
def destination_preserved_prop (src_ip dst_ip msg : Int) : Prop :=
  (unsafe_direct_route src_ip dst_ip msg).2.1 = dst_ip

theorem destination_preserved_thm (src_ip dst_ip msg : Int) :
    destination_preserved_prop src_ip dst_ip msg := by
  rfl

/-- Direct routing does not change the message. -/
def message_preserved_prop (src_ip dst_ip msg : Int) : Prop :=
  (unsafe_direct_route src_ip dst_ip msg).2.2 = msg

theorem message_preserved_thm (src_ip dst_ip msg : Int) :
    message_preserved_prop src_ip dst_ip msg := by
  rfl

/-- Both endpoints are jointly visible, making their pairing directly linkable. -/
def address_pair_visible_prop (src_ip dst_ip msg : Int) : Prop :=
  ((unsafe_direct_route src_ip dst_ip msg).1,
    (unsafe_direct_route src_ip dst_ip msg).2.1) = (src_ip, dst_ip)

theorem address_pair_visible_thm (src_ip dst_ip msg : Int) :
    address_pair_visible_prop src_ip dst_ip msg := by
  rfl

/-- Even with identical destination and message, different senders have different
visible first fields and different packets. -/
def senders_distinguishable_prop (src1 src2 dst_ip msg : Int) : Prop :=
  src1 ≠ src2 →
    (unsafe_direct_route src1 dst_ip msg).1 ≠
      (unsafe_direct_route src2 dst_ip msg).1 ∧
    unsafe_direct_route src1 dst_ip msg ≠ unsafe_direct_route src2 dst_ip msg

theorem senders_distinguishable_thm (src1 src2 dst_ip msg : Int) :
    senders_distinguishable_prop src1 src2 dst_ip msg := by
  change src1 ≠ src2 → src1 ≠ src2 ∧ (src1, dst_ip, msg) ≠ (src2, dst_ip, msg)
  intro h
  exact ⟨h, fun heq => h (congrArg Prod.fst heq)⟩

/-! ## Postcondition -/

/-- The complete packet specification, including distinguishability from every
other sender (not just the concrete senders in the original unit tests). -/
def Post_prop (src_ip dst_ip msg : Int) : Prop :=
  route_exact_prop src_ip dst_ip msg ∧
  source_visible_prop src_ip dst_ip msg ∧
  destination_preserved_prop src_ip dst_ip msg ∧
  message_preserved_prop src_ip dst_ip msg ∧
  address_pair_visible_prop src_ip dst_ip msg ∧
  ∀ other_src : Int, senders_distinguishable_prop src_ip other_src dst_ip msg

/-! ## Property-based tests

Each randomized test below expands its named property into computable equalities
and inequalities. No `Decidable` instance for the specification definitions is
needed. In the postcondition test, the universally quantified `other_src` is
moved into the outer list of sampled inputs; no obligation is removed.
-/

-- PBT: route_exact_prop.
#eval Plausible.Testable.check (∀ src dst msg : Int,
  unsafe_direct_route src dst msg = (src, dst, msg))

-- PBT: source_visible_prop.
#eval Plausible.Testable.check (∀ src dst msg : Int,
  (unsafe_direct_route src dst msg).1 = src)

-- PBT: destination_preserved_prop.
#eval Plausible.Testable.check (∀ src dst msg : Int,
  (unsafe_direct_route src dst msg).2.1 = dst)

-- PBT: message_preserved_prop.
#eval Plausible.Testable.check (∀ src dst msg : Int,
  (unsafe_direct_route src dst msg).2.2 = msg)

-- PBT: address_pair_visible_prop.
#eval Plausible.Testable.check (∀ src dst msg : Int,
  ((unsafe_direct_route src dst msg).1, (unsafe_direct_route src dst msg).2.1) =
    (src, dst))

-- PBT: senders_distinguishable_prop, including inequality of entire packets.
-- Evaluate the decidable implication as a Boolean rather than discarding samples.
#eval Plausible.Testable.check (∀ src1 src2 dst msg : Int,
  decide (src1 ≠ src2 →
    (unsafe_direct_route src1 dst msg).1 ≠ (unsafe_direct_route src2 dst msg).1 ∧
    unsafe_direct_route src1 dst msg ≠ unsafe_direct_route src2 dst msg) = true)

-- PBT: Post_prop. Pre is True for every sampled integer triple.
#eval Plausible.Testable.check (∀ src dst msg other_src : Int,
  decide (unsafe_direct_route src dst msg = (src, dst, msg) ∧
  (unsafe_direct_route src dst msg).1 = src ∧
  (unsafe_direct_route src dst msg).2.1 = dst ∧
  (unsafe_direct_route src dst msg).2.2 = msg ∧
  ((unsafe_direct_route src dst msg).1, (unsafe_direct_route src dst msg).2.1) =
    (src, dst) ∧
  (src ≠ other_src →
    (unsafe_direct_route src dst msg).1 ≠ (unsafe_direct_route other_src dst msg).1 ∧
    unsafe_direct_route src dst msg ≠ unsafe_direct_route other_src dst msg)) = true)

/-- Exhaustive signed test domain, including negative, zero, and positive values. -/
def smallInputs : List Int :=
  (List.range 9).map (fun n => (n : Int) - 4)

-- Bounded PBT: all six components of Post_prop, including all source comparisons,
-- for all 9^4 combinations in [-4, 4]. The theorem domains remain all of Int.
example :
    smallInputs.all (fun src =>
      smallInputs.all (fun dst =>
        smallInputs.all (fun msg =>
          smallInputs.all (fun other_src => decide (
            unsafe_direct_route src dst msg = (src, dst, msg) ∧
            (unsafe_direct_route src dst msg).1 = src ∧
            (unsafe_direct_route src dst msg).2.1 = dst ∧
            (unsafe_direct_route src dst msg).2.2 = msg ∧
            ((unsafe_direct_route src dst msg).1,
              (unsafe_direct_route src dst msg).2.1) = (src, dst) ∧
            (src ≠ other_src →
              (unsafe_direct_route src dst msg).1 ≠
                (unsafe_direct_route other_src dst msg).1 ∧
              unsafe_direct_route src dst msg ≠
                unsafe_direct_route other_src dst msg)))))) = true := by
  native_decide

/-! ## Correctness -/

theorem correctness_thm (src_ip dst_ip msg : Int) :
    Pre src_ip dst_ip msg → Post_prop src_ip dst_ip msg := by
  intro _
  exact ⟨route_exact_thm src_ip dst_ip msg,
    source_visible_thm src_ip dst_ip msg,
    destination_preserved_thm src_ip dst_ip msg,
    message_preserved_thm src_ip dst_ip msg,
    address_pair_visible_thm src_ip dst_ip msg,
    fun other_src => senders_distinguishable_thm src_ip other_src dst_ip msg⟩

/-! ## Imperative implementation -/

/-- Build the outgoing packet by updating a mutable packet's fields in order. -/
def unsafe_direct_route_imperative (src_ip dst_ip msg : Int) : Int × Int × Int :=
  Id.run do
    let mut packet : Int × Int × Int := (0, 0, 0)
    packet := (src_ip, packet.2.1, packet.2.2)
    packet := (packet.1, dst_ip, packet.2.2)
    packet := (packet.1, packet.2.1, msg)
    return packet

/-! ## Imperative tests -/

example : check unsafe_direct_route_imperative = true := by
  native_decide

example : unsafe_direct_route_imperative 192168001 8080 42 =
    (192168001, 8080, 42) := by
  native_decide

example : unsafe_direct_route_imperative 0 0 0 = (0, 0, 0) := by
  native_decide

example : unsafe_direct_route_imperative (-10) (-20) (-99) = (-10, -20, -99) := by
  native_decide

#eval unsafe_direct_route_imperative 192168001 8080 42
#eval check unsafe_direct_route_imperative

/-! ## Functional/imperative equivalence -/

theorem functional_imperative_equivalence_thm (src_ip dst_ip msg : Int) :
    unsafe_direct_route src_ip dst_ip msg =
      unsafe_direct_route_imperative src_ip dst_ip msg := by
  rfl

end UnsafeDirectRoute
end Agent
