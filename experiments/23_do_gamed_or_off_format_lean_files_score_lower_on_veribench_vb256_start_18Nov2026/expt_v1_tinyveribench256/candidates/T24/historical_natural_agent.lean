import Mathlib
namespace Agent

/-!
# Unsafe DNS amplification

This file formalizes an open DNS resolver which rejects nonpositive query sizes
but otherwise always responds.  In particular, it deliberately ignores whether
the source address was spoofed and computes the integer amplification factor by
dividing the response size by the query size.
-/

namespace UnsafeDnsAmplification

/-- Functional model of `unsafe_dns_amplification`. -/
def unsafeDnsAmplification
    (_srcIpSpoofed : Bool) (querySize responseSize : Int) : Bool × Int :=
  if querySize ≤ 0 then
    (false, 0)
  else
    (true, responseSize / querySize)

/-! Unit tests corresponding to the Python assertions. -/

example : unsafeDnsAmplification false 64 128 = (true, 2) := by native_decide
example : unsafeDnsAmplification true 64 3200 = (true, 50) := by native_decide
example : unsafeDnsAmplification true 60 6000 = (true, 100) := by native_decide
example : unsafeDnsAmplification false 0 128 = (false, 0) := by native_decide
example : unsafeDnsAmplification true 128 64 = (true, 0) := by native_decide
example : unsafeDnsAmplification true 64 128 =
    unsafeDnsAmplification false 64 128 := by native_decide

#eval unsafeDnsAmplification false 64 128
#eval unsafeDnsAmplification true 64 3200
#eval unsafeDnsAmplification true 60 6000
#eval unsafeDnsAmplification false 0 128
#eval unsafeDnsAmplification true 128 64

/-- Python integers require no additional input restriction. -/
def Pre (_srcIpSpoofed : Bool) (_querySize _responseSize : Int) : Prop := True

/-- A nonpositive query size is rejected with zero amplification. -/
def rejectsNonpositive_prop
    (srcIpSpoofed : Bool) (querySize responseSize : Int) : Prop :=
  querySize ≤ 0 →
    unsafeDnsAmplification srcIpSpoofed querySize responseSize = (false, 0)

theorem rejectsNonpositive_thm
    (srcIpSpoofed : Bool) (querySize responseSize : Int) :
    rejectsNonpositive_prop srcIpSpoofed querySize responseSize := by
  intro h
  simp [unsafeDnsAmplification, h]

/-- Every positive-size query receives a response with the quotient as factor. -/
def respondsToPositive_prop
    (srcIpSpoofed : Bool) (querySize responseSize : Int) : Prop :=
  0 < querySize →
    unsafeDnsAmplification srcIpSpoofed querySize responseSize =
      (true, responseSize / querySize)

theorem respondsToPositive_thm
    (srcIpSpoofed : Bool) (querySize responseSize : Int) :
    respondsToPositive_prop srcIpSpoofed querySize responseSize := by
  intro h
  simp [unsafeDnsAmplification, Int.not_le.mpr h]

/-- The vulnerable resolver behaves identically for spoofed and genuine sources. -/
def spoofedSourceIgnored_prop (querySize responseSize : Int) : Prop :=
  unsafeDnsAmplification true querySize responseSize =
    unsafeDnsAmplification false querySize responseSize

theorem spoofedSourceIgnored_thm (querySize responseSize : Int) :
    spoofedSourceIgnored_prop querySize responseSize := by
  rfl

/-- The positive-input behavior includes the classic 50x amplification case. -/
def dnsAmplificationExample_prop : Prop :=
  unsafeDnsAmplification true 64 3200 = (true, 50)

theorem dnsAmplificationExample_thm : dnsAmplificationExample_prop := by
  norm_num [dnsAmplificationExample_prop, unsafeDnsAmplification]

/-- Complete postcondition for a call, including the source-independence flaw. -/
def Post_prop
    (srcIpSpoofed : Bool) (querySize responseSize : Int) : Prop :=
  rejectsNonpositive_prop srcIpSpoofed querySize responseSize ∧
  respondsToPositive_prop srcIpSpoofed querySize responseSize ∧
  spoofedSourceIgnored_prop querySize responseSize

/-- The functional resolver meets its full specification for all integer inputs. -/
theorem unsafeDnsAmplification_correct
    (srcIpSpoofed : Bool) (querySize responseSize : Int) :
    Pre srcIpSpoofed querySize responseSize →
      Post_prop srcIpSpoofed querySize responseSize := by
  intro _
  exact ⟨rejectsNonpositive_thm _ _ _, respondsToPositive_thm _ _ _,
    spoofedSourceIgnored_thm _ _⟩

/-- Imperative rendition using mutable local state in `Id`. -/
def unsafeDnsAmplificationImperative
    (_srcIpSpoofed : Bool) (querySize responseSize : Int) : Bool × Int := Id.run do
  let mut responded := false
  let mut amplification : Int := 0
  if querySize ≤ 0 then
    return (responded, amplification)
  responded := true
  amplification := responseSize / querySize
  return (responded, amplification)

/-! The same assertions exercised against the imperative rendition. -/

example : unsafeDnsAmplificationImperative false 64 128 = (true, 2) := by
  native_decide
example : unsafeDnsAmplificationImperative true 64 3200 = (true, 50) := by
  native_decide
example : unsafeDnsAmplificationImperative true 60 6000 = (true, 100) := by
  native_decide
example : unsafeDnsAmplificationImperative false 0 128 = (false, 0) := by
  native_decide
example : unsafeDnsAmplificationImperative true 128 64 = (true, 0) := by
  native_decide
example : unsafeDnsAmplificationImperative true 64 128 =
    unsafeDnsAmplificationImperative false 64 128 := by native_decide

#eval unsafeDnsAmplificationImperative true 64 3200

/-- The stateful-looking implementation computes exactly the functional model. -/
theorem functional_eq_imperative
    (srcIpSpoofed : Bool) (querySize responseSize : Int) :
    unsafeDnsAmplification srcIpSpoofed querySize responseSize =
      unsafeDnsAmplificationImperative srcIpSpoofed querySize responseSize := by
  by_cases h : querySize ≤ 0 <;>
    simp [unsafeDnsAmplification, unsafeDnsAmplificationImperative, h]

end UnsafeDnsAmplification
end Agent
