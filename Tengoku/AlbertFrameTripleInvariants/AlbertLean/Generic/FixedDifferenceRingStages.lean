import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.RationalEvenRingAction
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourceVectorCoefficientMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms map_secondCenter` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms targets_field` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms stageOneVector_field` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms secondCenter_field` (it only prints; the queue checks the axioms of every declaration). -/

/-! Ring formulas for the fixed-difference pair stages after adjoining the
orientation root and before adjoining either even-lift root. -/

noncomputable section
namespace AlbertLean.Generic.FixedDifferenceRingStages

open AlbertLean.Triality ExteriorSix CoordinateTensor StructuredCubic
open SourceEvenReflections SourceVectorPairDephase
open SourceVectorPairReflection
open RationalEvenRingAction

universe u v
variable {R : Type u} [CommRing R] [Algebra ℚ R] [Invertible (2 : R)]

def plane (r z : R) : VCoord R := { r := r, z := z, omega := 0 }

def parity : VCoord R := { r := 0, z := 0, omega := wBasis .i12 + wBasis .i34 }

def aCoeff (v1 : VCoord R) : R := ringNV v1
def hCoeff (v1 v2 : VCoord R) : R := ringBV v1 v2
def mCoeff (v2 : VCoord R) : R := ringNV v2
def discriminant (v1 v2 : VCoord R) : R :=
  hCoeff v1 v2 ^ 2 - 4 * aCoeff v1 * mCoeff v2

def targetT (a : R) : VCoord R := plane 1 a

def beta (twoInv aInv h : R) : R := h * twoInv * aInv

def targetZ (twoInv aInv a h sigma : R) : VCoord R :=
  plane ((h - sigma) * twoInv * aInv) ((h + sigma) * twoInv)

def targetQ (twoInv aInv a h sigma : R) : VCoord R :=
  targetZ twoInv aInv a h sigma - beta twoInv aInv h • targetT a

def firstCenter (v1 : VCoord R) (a : R) : VCoord R := v1 - targetT a

/-- The first algorithmic V stage. `n1Inv` is the supplied inverse of the
norm of `firstCenter`; the parity center has norm one.-/
def stageOneVector (v1 v2 : VCoord R) (a n1Inv : R) : VCoord R :=
  ringReflectV parity 1 (ringReflectV (firstCenter v1 a) n1Inv v2)

def secondRemainder (v1 v2 : VCoord R)
    (twoInv aInv a h n1Inv : R) : VCoord R :=
  stageOneVector v1 v2 a n1Inv - beta twoInv aInv h • targetT a

def secondCenter (v1 v2 : VCoord R)
    (twoInv aInv a h sigma n1Inv : R) : VCoord R :=
  secondRemainder v1 v2 twoInv aInv a h n1Inv -
    targetQ twoInv aInv a h sigma

def mapV {S : Type v} [CommRing S] (f : R →+* S) (x : VCoord R) : VCoord S :=
  { r := f x.r, z := f x.z, omega := f ∘ x.omega }

private theorem mapV_sub {S : Type v} [CommRing S] (f : R →+* S)
    (x y : VCoord R) : mapV f (x - y) = mapV f x - mapV f y := by
  apply VCoord.ext
  · exact map_sub f x.r y.r
  · exact map_sub f x.z y.z
  · funext i
    exact map_sub f (x.omega i) (y.omega i)

private theorem mapV_smul {S : Type v} [CommRing S] (f : R →+* S)
    (c : R) (x : VCoord R) : mapV f (c • x) = f c • mapV f x := by
  apply VCoord.ext
  · exact map_mul f c x.r
  · exact map_mul f c x.z
  · funext i
    exact map_mul f c (x.omega i)

private theorem map_ringBV {S : Type v} [CommRing S] (f : R →+* S)
    (x y : VCoord R) : f (ringBV x y) = ringBV (mapV f x) (mapV f y) := by
  simp [ringBV, mapV, BW]

private theorem map_ringReflectV {S : Type v} [CommRing S]
    [Algebra ℚ S] [Invertible (2 : S)] (f : R →+* S)
    (c : VCoord R) (nInv : R) (x : VCoord R) :
    mapV f (ringReflectV c nInv x) =
      ringReflectV (mapV f c) (f nInv) (mapV f x) := by
  rw [ringReflectV, ringReflectV, mapV_sub, mapV_smul, map_mul, map_ringBV]

private theorem map_plane {S : Type v} [CommRing S] (f : R →+* S)
    (r z : R) : mapV f (plane r z) = plane (f r) (f z) := by
  apply VCoord.ext
  · rfl
  · rfl
  · funext i
    simp [mapV, plane]

private theorem map_parity {S : Type v} [CommRing S] (f : R →+* S) :
    mapV f (parity : VCoord R) = (parity : VCoord S) := by
  apply VCoord.ext
  · simp [mapV, parity]
  · simp [mapV, parity]
  · funext i
    fin_cases i <;> simp [mapV, parity, wBasis]

private theorem map_targetT {S : Type v} [CommRing S] (f : R →+* S) (a : R) :
    mapV f (targetT a) = targetT (f a) := by
  rw [targetT, targetT, map_plane, map_one]

private theorem map_beta {S : Type v} [CommRing S] (f : R →+* S)
    (twoInv aInv h : R) :
    f (beta twoInv aInv h) = beta (f twoInv) (f aInv) (f h) := by
  simp [beta]

private theorem map_targetZ {S : Type v} [CommRing S] (f : R →+* S)
    (twoInv aInv a h sigma : R) :
    mapV f (targetZ twoInv aInv a h sigma) =
      targetZ (f twoInv) (f aInv) (f a) (f h) (f sigma) := by
  rw [targetZ, targetZ, map_plane]
  simp

private theorem map_targetQ {S : Type v} [CommRing S] (f : R →+* S)
    (twoInv aInv a h sigma : R) :
    mapV f (targetQ twoInv aInv a h sigma) =
      targetQ (f twoInv) (f aInv) (f a) (f h) (f sigma) := by
  rw [targetQ, targetQ, mapV_sub, mapV_smul, map_targetZ, map_targetT,
    map_beta]

private theorem map_firstCenter {S : Type v} [CommRing S] (f : R →+* S)
    (v : VCoord R) (a : R) :
    mapV f (firstCenter v a) = firstCenter (mapV f v) (f a) := by
  rw [firstCenter, firstCenter, mapV_sub, map_targetT]

private theorem map_stageOneVector {S : Type v} [CommRing S]
    [Algebra ℚ S] [Invertible (2 : S)] (f : R →+* S)
    (v1 v2 : VCoord R) (a n1Inv : R) :
    mapV f (stageOneVector v1 v2 a n1Inv) =
      stageOneVector (mapV f v1) (mapV f v2) (f a) (f n1Inv) := by
  rw [stageOneVector, stageOneVector, map_ringReflectV, map_ringReflectV,
    map_parity, map_firstCenter, map_one]

/-- Exact coefficient naturality of all data constructed before the two lift
roots. The inverse scalars are mapped as displayed ring elements.
@isnad1 id=eq.0h11v.s8.e7f2e78a1a3c from=translated src=- shape=b0da4bd8 vocab=53aea235
-/
theorem map_secondCenter {S : Type v} [CommRing S] [Algebra ℚ S]
    [Invertible (2 : S)] (f : R →+* S)
    (v1 v2 : VCoord R) (twoInv aInv a h sigma n1Inv : R) :
    mapV f (secondCenter v1 v2 twoInv aInv a h sigma n1Inv) =
      secondCenter (mapV f v1) (mapV f v2) (f twoInv) (f aInv)
        (f a) (f h) (f sigma) (f n1Inv) := by
  rw [secondCenter, secondCenter, mapV_sub, secondRemainder, secondRemainder,
    mapV_sub, mapV_smul, map_stageOneVector, map_beta, map_targetT,
    map_targetQ]

section FieldSpecialization

variable {K : Type*} [Field K] [CharZero K]
local instance : Invertible (2 : K) := invertibleOfNonzero (by norm_num)

private theorem targetZ_field (a h sigma : K) (ha : a ≠ 0) :
    targetZ (2 : K)⁻¹ a⁻¹ a h sigma = targetSecond a h sigma := by
  apply VCoord.ext
  · simp [targetZ, targetSecond, targetB, targetC, plane, planeVector]
    field_simp [ha] <;> ring
  · simp [targetZ, targetSecond, targetB, targetC, plane, planeVector]
    field_simp <;> ring
  · funext i
    simp [targetZ, targetSecond, targetB, targetC, plane, planeVector]

/--
@isnad1 id=and.1h4v.s7.a05012ad9cc3 from=translated src=- shape=845e5e0d vocab=741accfe
-/
theorem targets_field (a h sigma : K) (ha : a ≠ 0) :
    targetT a = targetFirst a ∧
    targetZ (2 : K)⁻¹ a⁻¹ a h sigma = targetSecond a h sigma ∧
    targetQ (2 : K)⁻¹ a⁻¹ a h sigma = targetRemainder a h sigma := by
  constructor
  · rfl
  constructor
  · exact targetZ_field a h sigma ha
  · rw [targetQ, targetRemainder, targetZ_field a h sigma ha]
    have hc : beta (2 : K)⁻¹ a⁻¹ h = h / (2 * a) := by
      unfold beta
      field_simp [ha] <;> ring
    rw [hc]
    rfl

/--
@isnad1 id=eq.1h4v.s6.9dbed4075701 from=translated src=- shape=992009d7 vocab=6d205f0f
-/
theorem stageOneVector_field (v1 v2 : VCoord K) (a : K)
    (hB1 : nV (firstCenter v1 a) ≠ 0) :
    stageOneVector v1 v2 a (nV (firstCenter v1 a))⁻¹ =
      evenV parityVector (firstCenter v1 a) v2 := by
  unfold stageOneVector
  have hp : (nV (parityVector : VCoord K))⁻¹ = 1 := by simp
  change ringReflectV parityVector 1
      (ringReflectV (firstCenter v1 a) (nV (firstCenter v1 a))⁻¹ v2) = _
  rw [← hp, ringReflectV_eq, ringReflectV_eq, evenV]

/--
@isnad1 id=eq.3h6v.s8.a95820e64f97 from=translated src=- shape=553f2576 vocab=71ea6846
-/
theorem secondCenter_field (v1 v2 : VCoord K) (a h sigma : K)
    (ha : a ≠ 0) (hB1 : nV (firstCenter v1 a) ≠ 0)
    (hpair : BV (targetFirst a)
      (evenV parityVector (firstCenter v1 a) v2) = h) :
    secondCenter v1 v2 (2 : K)⁻¹ a⁻¹ a h sigma
        (nV (firstCenter v1 a))⁻¹ =
      orthogonalRemainder (targetFirst a)
          (evenV parityVector (firstCenter v1 a) v2) -
        targetRemainder a h sigma := by
  rw [secondCenter, secondRemainder, stageOneVector_field v1 v2 a hB1]
  obtain ⟨ht, _, hq⟩ := targets_field a h sigma ha
  rw [ht, hq, orthogonalRemainder]
  congr 1
  simp [projectionCoeff, beta, targetFirst_norm, hpair]
  field_simp [ha] <;> ring

end FieldSpecialization
end AlbertLean.Generic.FixedDifferenceRingStages
