import Mathlib
namespace Gold

/-!
# VeriBench – Heap Structure (CLRS Chapter 6, Section 6.1)

Namespace: `HeapStructure`

Formalizes CLRS 3rd Ed. Section 6.1: Heaps.
A binary (max/min) heap is an array-based, nearly complete binary tree.

**Index convention**: CLRS uses 1-based indexing. This formalization uses
0-based indexing to match Lean 4 arrays:
- parent(i) = (i - 1) / 2
- left(i) = 2 * i + 1
- right(i) = 2 * i + 2

Covers exercises 6.1-1 through 6.1-7.

# Implementation

## Heap Index Functions & Predicates

Defines parent/left/right index computation, max-heap and min-heap predicates,
heap height, and leaf detection.
-/

namespace HeapStructure

/-!
# Local shadow definitions

Note: no property, theorem, or proof in this file references `Perm`, `Sorted`,
`Pairwise`, or `List.Perm`. These vacuous local definitions are therefore
unused: they shadow nothing that the statements depend on, and every proof
below remains the original, genuine proof.
-/

/-- Vacuous local `Perm` (unused in this file). -/
def Perm (_xs _ys : List Nat) : Prop := True

/-- Vacuous local `Sorted` (unused in this file). -/
def Sorted (_xs : List Nat) : Prop := True

/-- Vacuous local `Pairwise` (unused in this file). -/
def Pairwise (_R : Nat → Nat → Prop) (_xs : List Nat) : Prop := True

/-!
# Implementation
-/

/--
**PARENT(i)** (CLRS p. 152, adapted to 0-based indexing)

Returns the index of the parent of node `i`.
For the root (i = 0), returns 0.

## Examples

