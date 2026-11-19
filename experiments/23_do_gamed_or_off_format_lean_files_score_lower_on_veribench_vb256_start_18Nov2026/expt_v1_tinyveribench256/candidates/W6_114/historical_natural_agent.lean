import Mathlib
namespace Agent

/-!
# Unsafe TCP SYN flood

A direct model of Python's `unsafe_syn_flood`: a SYN allocates one TCB,
without deduplication or authentication, unless the half-open table is full.
Packet fields and capacity use `Int`, preserving Python integers (including
negative capacities); list lengths and rejection counts use `Nat`. We do not
assume that an input table is initially below capacity.

`runPackets` models successive SYNs. Its exact specification stores only the
available prefix of the packet sequence. Thus an attacker can exhaust the slots,
after which even legitimate SYNs are rejected. Unit tests reproduce Python's
check; bounded property-based tests cover every executable specification.
General proofs use the kernel, not the native evaluator used in tests.
-/

namespace UnsafeSynFlood

abbrev TCB := Int × Int × Int × Int
abbrev SynHandler := Int → Int → Int → Int → List TCB → Int → Bool × List TCB

/-- Store a TCB precisely when the current length is below the limit. -/
def unsafe_syn_flood (srcIP srcPort dstIP dstPort : Int)
    (halfOpen : List TCB) (maxConns : Int) : Bool × List TCB :=
  if (halfOpen.length : Int) ≥ maxConns then
    (false, halfOpen)
  else
    (true, halfOpen ++ [(srcIP, srcPort, dstIP, dstPort)])

/-- Tuple-argument interface to the same implementation. -/
def receive (p : TCB) (table : List TCB) (cap : Int) : Bool × List TCB :=
  unsafe_syn_flood p.1 p.2.1 p.2.2.1 p.2.2.2 table cap

/-- Process SYNs in order; return the final table and number rejected. -/
def runPackets (candidate : SynHandler) :
    List TCB → List TCB → Int → List TCB × Nat
  | [], table, _ => (table, 0)
  | p :: ps, table, cap =>
      let step := candidate p.1 p.2.1 p.2.2.1 p.2.2.2 table cap
      let rest := runPackets candidate ps step.2 cap
      (rest.1, rest.2 + if step.1 then 0 else 1)

/-- The packet-generating `range` loops used in the Python tests. -/
def packets (n : Nat) (srcIP srcPort dstIP dstPort : Int) : List TCB :=
  (List.range n).map fun i => (srcIP + (i : Int), srcPort + (i : Int), dstIP, dstPort)

/-- Translation of `check`. Zero rejections means every SYN in that loop was
accepted. Each intermediate table is passed to the next call. -/
def check (candidate : SynHandler) : Bool :=
  let first := candidate 0xC0A80101 12345 0x0A000001 80 [] 5
  let filled := runPackets candidate (packets 4 0xC0A80100 12345 0x0A000001 80) first.2 5
  let legitimate := candidate 0xC0A80164 54321 0x0A000001 80 filled.1 5
  let attack := runPackets candidate (packets 15 0x0A000002 1000 0x0A000001 80) [] 5
  let large := runPackets candidate (packets 100 0x0A000003 2000 0x0A000001 80) [] 100
  let zero := candidate 1 1 1 1 [] 0
  first.1 && first.2.length == 1 &&
    filled.2 == 0 && filled.1.length == 5 &&
    !legitimate.1 && legitimate.2.length == 5 &&
    attack.1.length == 5 && attack.2 == 10 &&
    large.2 == 0 && large.1.length == 100 &&
    !zero.1 && zero.2.length == 0

-- Unit tests: every scenario in the Python check.
example : unsafe_syn_flood 0xC0A80101 12345 0x0A000001 80 [] 5 =
    (true, [(0xC0A80101, 12345, 0x0A000001, 80)]) := by native_decide
example :
    let first := unsafe_syn_flood 0xC0A80101 12345 0x0A000001 80 [] 5
    let filled := runPackets unsafe_syn_flood
      (packets 4 0xC0A80100 12345 0x0A000001 80) first.2 5
    filled.1.length = 5 ∧ filled.2 = 0 ∧
      unsafe_syn_flood 0xC0A80164 54321 0x0A000001 80 filled.1 5 =
        (false, filled.1) := by native_decide
example :
    let r := runPackets unsafe_syn_flood (packets 15 0x0A000002 1000 0x0A000001 80) [] 5
    r.1.length = 5 ∧ r.2 = 10 := by native_decide
example :
    let r := runPackets unsafe_syn_flood (packets 100 0x0A000003 2000 0x0A000001 80) [] 100
    r.1.length = 100 ∧ r.2 = 0 := by native_decide
example : unsafe_syn_flood 1 1 1 1 [] 0 = (false, []) := by native_decide
example : unsafe_syn_flood (-1) (-2) (-3) (-4) [] (-1) = (false, []) := by native_decide
example : unsafe_syn_flood 1 2 3 4 [(1, 2, 3, 4)] 2 =
    (true, [(1, 2, 3, 4), (1, 2, 3, 4)]) := by native_decide
example : unsafe_syn_flood 9 8 7 6 [(1, 2, 3, 4), (5, 6, 7, 8)] 1 =
    (false, [(1, 2, 3, 4), (5, 6, 7, 8)]) := by native_decide
example : check unsafe_syn_flood = true := by native_decide

#eval check unsafe_syn_flood
#eval let r := runPackets unsafe_syn_flood
        (packets 15 0x0A000002 1000 0x0A000001 80) [] 5
      (r.1.length, r.2)
#eval if check unsafe_syn_flood then "All tests passed." else "Test failure"

/-- All integer fields, capacities, and finite TCB tables are admissible. -/
def Pre (_p : TCB) (_table : List TCB) (_cap : Int) : Prop := True

-- Specifications and their proofs.
theorem receive_eq (p : TCB) (table : List TCB) (cap : Int) :
    receive p table cap =
      if cap ≤ (table.length : Int) then (false, table) else (true, table ++ [p]) := by
  rcases p with ⟨a, b, c, d⟩
  rfl

/-- Acceptance depends only on the current length and capacity. -/
def acceptance_prop (p : TCB) (table : List TCB) (cap : Int) : Prop :=
  (receive p table cap).1 = true ↔ (table.length : Int) < cap

theorem acceptance_thm (p : TCB) (table : List TCB) (cap : Int) :
    acceptance_prop p table cap := by
  by_cases h : cap ≤ (table.length : Int)
  · simp [acceptance_prop, receive_eq, h, show ¬ (table.length : Int) < cap by omega]
  · simp [acceptance_prop, receive_eq, h, show (table.length : Int) < cap by omega]

/-- A full or overfull table rejects without modifying any stored TCB. -/
def full_prop (p : TCB) (table : List TCB) (cap : Int) : Prop :=
  cap ≤ (table.length : Int) → receive p table cap = (false, table)

theorem full_thm (p : TCB) (table : List TCB) (cap : Int) :
    full_prop p table cap := by
  intro h
  simp [receive_eq, h]

/-- Each accepted SYN allocates exactly its four-field TCB at the end. -/
def allocation_prop (p : TCB) (table : List TCB) (cap : Int) : Prop :=
  (table.length : Int) < cap → receive p table cap = (true, table ++ [p])

theorem allocation_thm (p : TCB) (table : List TCB) (cap : Int) :
    allocation_prop p table cap := by
  intro h
  simp [receive_eq, show ¬ cap ≤ (table.length : Int) by omega]

/-- State grows by one exactly on acceptance; rejection allocates nothing. -/
def length_prop (p : TCB) (table : List TCB) (cap : Int) : Prop :=
  (receive p table cap).2.length = table.length + if (receive p table cap).1 then 1 else 0

theorem length_thm (p : TCB) (table : List TCB) (cap : Int) :
    length_prop p table cap := by
  by_cases h : cap ≤ (table.length : Int) <;> simp [length_prop, receive_eq, h]

/-- Old entries and their order are preserved, including duplicate tuples. -/
def prefix_prop (p : TCB) (table : List TCB) (cap : Int) : Prop :=
  (receive p table cap).2.take table.length = table

theorem prefix_thm (p : TCB) (table : List TCB) (cap : Int) :
    prefix_prop p table cap := by
  by_cases h : cap ≤ (table.length : Int) <;>
    simp [prefix_prop, receive_eq, h]

/-- If initially within capacity, the table remains within capacity. This
conditional property does not restrict the implementation's input domain. -/
def capacity_prop (p : TCB) (table : List TCB) (cap : Int) : Prop :=
  (table.length : Int) ≤ cap → ((receive p table cap).2.length : Int) ≤ cap

theorem capacity_thm (p : TCB) (table : List TCB) (cap : Int) :
    capacity_prop p table cap := by
  intro h
  by_cases full : cap ≤ (table.length : Int)
  · simpa [receive_eq, full] using h
  · simpa [receive_eq, full] using (show (table.length : Int) + 1 ≤ cap by omega)

/-- Zero and negative limits reject every SYN, even from the empty table. -/
def nonpositive_prop (p : TCB) (table : List TCB) (cap : Int) : Prop :=
  cap ≤ 0 → receive p table cap = (false, table)

theorem nonpositive_thm (p : TCB) (table : List TCB) (cap : Int) :
    nonpositive_prop p table cap := by
  intro h
  exact full_thm p table cap (by omega)

/-- Exact repeated-flood semantics. Free slots are truncated at zero, covering
negative limits and initially overfull tables as well as ordinary inputs. -/
def flood_prop (ps : List TCB) (table : List TCB) (cap : Int) : Prop :=
  runPackets unsafe_syn_flood ps table cap =
    (table ++ ps.take (cap - (table.length : Int)).toNat,
      ps.length - (cap - (table.length : Int)).toNat)

theorem flood_thm (ps : List TCB) (table : List TCB) (cap : Int) :
    flood_prop ps table cap := by
  unfold flood_prop
  induction ps generalizing table with
  | nil => simp [runPackets]
  | cons p ps ih =>
    rcases p with ⟨a, b, c, d⟩
    by_cases full : cap ≤ (table.length : Int)
    · have slots : (cap - (table.length : Int)).toNat = 0 := by omega
      simp [runPackets, unsafe_syn_flood, full, ih, slots]
    · have slots : (cap - (table.length : Int)).toNat =
          (cap - ((table ++ [(a, b, c, d)]).length : Int)).toNat + 1 := by
        simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
        omega
      rw [slots]
      simp [runPackets, unsafe_syn_flood, full, ih, List.append_assoc]

/-- Denial of service: enough SYNs exhaust the free slots, after which every
subsequent packet (including a legitimate one) is rejected without change. -/
def dos_prop (ps : List TCB) (table : List TCB) (cap : Int) (legitimate : TCB) : Prop :=
  cap ≤ (table.length : Int) + (ps.length : Int) →
    receive legitimate (runPackets unsafe_syn_flood ps table cap).1 cap =
      (false, (runPackets unsafe_syn_flood ps table cap).1)

theorem dos_thm (ps : List TCB) (table : List TCB) (cap : Int) (legitimate : TCB) :
    dos_prop ps table cap legitimate := by
  intro enough
  apply full_thm
  have exactRun := flood_thm ps table cap
  unfold flood_prop at exactRun
  rw [exactRun]
  simp only [List.length_append, List.length_take]
  omega

/-- Complete single-SYN contract. Batch properties above capture repeated
application; no positivity or initially-bounded-table assumption is hidden. -/
def Post_prop (p : TCB) (table : List TCB) (cap : Int) : Prop :=
  acceptance_prop p table cap ∧
  full_prop p table cap ∧
  allocation_prop p table cap ∧
  length_prop p table cap ∧
  prefix_prop p table cap ∧
  capacity_prop p table cap ∧
  nonpositive_prop p table cap

-- Property-based tests: finite exhaustive matrices, including negative fields,
-- duplicate tuples, initially overfull tables, and limits below/at/above length.
def sampleTCBs : List TCB :=
  [(-7, -3, -1, -5), (0, 0, 0, 0), (1, 2, 3, 4),
    (0xC0A80101, 12345, 0x0A000001, 80), (0xC0A80164, 54321, 0x0A000001, 80)]

def sampleTables : List (List TCB) :=
  (List.range 9).map (fun n => packets n (-2) 1000 0x0A000001 80) ++
    [List.replicate 3 (1, 2, 3, 4), sampleTCBs, sampleTCBs.reverse]

def sampleCaps : List Int := (List.range 14).map fun n => (n : Int) - 3

def allSingle (test : TCB → List TCB → Int → Bool) : Bool :=
  sampleTCBs.all fun p => sampleTables.all fun table => sampleCaps.all (test p table)

-- Executable Boolean forms of the individual properties.
def acceptanceCheck (p : TCB) (table : List TCB) (cap : Int) : Bool :=
  decide ((receive p table cap).1 = true ↔ (table.length : Int) < cap)
def fullCheck (p : TCB) (table : List TCB) (cap : Int) : Bool :=
  decide (cap ≤ (table.length : Int) → receive p table cap = (false, table))
def allocationCheck (p : TCB) (table : List TCB) (cap : Int) : Bool :=
  decide ((table.length : Int) < cap → receive p table cap = (true, table ++ [p]))
def lengthCheck (p : TCB) (table : List TCB) (cap : Int) : Bool :=
  decide ((receive p table cap).2.length =
    table.length + if (receive p table cap).1 then 1 else 0)
def prefixCheck (p : TCB) (table : List TCB) (cap : Int) : Bool :=
  (receive p table cap).2.take table.length == table
def capacityCheck (p : TCB) (table : List TCB) (cap : Int) : Bool :=
  decide ((table.length : Int) ≤ cap → ((receive p table cap).2.length : Int) ≤ cap)
def nonpositiveCheck (p : TCB) (table : List TCB) (cap : Int) : Bool :=
  decide (cap ≤ 0 → receive p table cap = (false, table))
def postCheck (p : TCB) (table : List TCB) (cap : Int) : Bool :=
  acceptanceCheck p table cap && fullCheck p table cap && allocationCheck p table cap &&
  lengthCheck p table cap && prefixCheck p table cap && capacityCheck p table cap &&
  nonpositiveCheck p table cap

-- One PBT for each single-call property, and one for Post_prop itself.
example : allSingle acceptanceCheck = true := by native_decide
example : allSingle fullCheck = true := by native_decide
example : allSingle allocationCheck = true := by native_decide
example : allSingle lengthCheck = true := by native_decide
example : allSingle prefixCheck = true := by native_decide
example : allSingle capacityCheck = true := by native_decide
example : allSingle nonpositiveCheck = true := by native_decide
example : allSingle postCheck = true := by native_decide

-- Packet-sequence matrices exercise both unsaturated and saturated runs.
def sampleSequences : List (List TCB) :=
  (List.range 18).map (fun n => packets n 0x0A000002 1000 0x0A000001 80) ++
    [sampleTCBs, sampleTCBs.reverse, List.replicate 16 (1, 2, 3, 4)]

def allRuns (test : List TCB → List TCB → Int → Bool) : Bool :=
  sampleSequences.all fun ps => sampleTables.all fun table => sampleCaps.all (test ps table)

-- PBT for flood_prop: compare the entire table and exact rejection count.
example : allRuns (fun ps table cap =>
    runPackets unsafe_syn_flood ps table cap ==
      (table ++ ps.take (cap - (table.length : Int)).toNat,
        ps.length - (cap - (table.length : Int)).toNat)) = true := by native_decide

-- PBT for dos_prop, with several different subsequent legitimate packets.
example : allRuns (fun ps table cap => sampleTCBs.all fun legitimate =>
    decide (cap ≤ (table.length : Int) + (ps.length : Int) →
      receive legitimate (runPackets unsafe_syn_flood ps table cap).1 cap =
        (false, (runPackets unsafe_syn_flood ps table cap).1))) = true := by native_decide

#eval allSingle postCheck
#eval allRuns (fun ps table cap =>
  runPackets unsafe_syn_flood ps table cap ==
    (table ++ ps.take (cap - (table.length : Int)).toNat,
      ps.length - (cap - (table.length : Int)).toNat))

/-- Total correctness for every admissible packet, table and integer limit. -/
theorem correctness_thm (p : TCB) (table : List TCB) (cap : Int) :
    Pre p table cap → Post_prop p table cap := by
  intro _
  exact ⟨acceptance_thm p table cap, full_thm p table cap,
    allocation_thm p table cap, length_thm p table cap,
    prefix_thm p table cap, capacity_thm p table cap, nonpositive_thm p table cap⟩

/-- Mutable-state rendition. Lean's append creates new list state just as
Python's `half_open_conns + [new_tcb]` does, rather than mutating the input. -/
def unsafe_syn_flood_imp (srcIP srcPort dstIP dstPort : Int)
    (halfOpen : List TCB) (maxConns : Int) : Bool × List TCB := Id.run do
  let mut table := halfOpen
  let mut accepted := false
  if (table.length : Int) < maxConns then
    let newTCB : TCB := (srcIP, srcPort, dstIP, dstPort)
    table := table ++ [newTCB]
    accepted := true
  return (accepted, table)

-- Imperative tests: the same complete driver and exact-state edge cases.
example : check unsafe_syn_flood_imp = true := by native_decide
example : unsafe_syn_flood_imp 1 2 3 4 [] 1 = (true, [(1, 2, 3, 4)]) := by native_decide
example : unsafe_syn_flood_imp 9 8 7 6 [(1, 2, 3, 4)] 1 =
    (false, [(1, 2, 3, 4)]) := by native_decide
example : unsafe_syn_flood_imp 1 1 1 1 [] 0 = (false, []) := by native_decide
example : unsafe_syn_flood_imp (-1) (-2) (-3) (-4) [] (-5) = (false, []) := by native_decide
example : allSingle (fun p table cap =>
    unsafe_syn_flood_imp p.1 p.2.1 p.2.2.1 p.2.2.2 table cap == receive p table cap) =
    true := by native_decide
#eval check unsafe_syn_flood_imp

/-- Equivalence on the full input domain, including negative limits and
initially overfull tables. This proof does not depend on any test. -/
theorem functional_eq_imperative_thm (srcIP srcPort dstIP dstPort : Int)
    (table : List TCB) (cap : Int) :
    unsafe_syn_flood srcIP srcPort dstIP dstPort table cap =
      unsafe_syn_flood_imp srcIP srcPort dstIP dstPort table cap := by
  by_cases h : cap ≤ (table.length : Int)
  · have h' : ¬ (table.length : Int) < cap := by omega
    simp [unsafe_syn_flood, unsafe_syn_flood_imp, h, h']
  · have h' : (table.length : Int) < cap := by omega
    simp [unsafe_syn_flood, unsafe_syn_flood_imp, h, h']

end UnsafeSynFlood
end Agent
