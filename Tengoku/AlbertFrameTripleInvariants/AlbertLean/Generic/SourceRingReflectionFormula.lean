import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourcePeirceAttachment
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Comparison.GenericProductTransport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms map_ringProduct` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms map_ringReflection` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms ringReflection_eq_source` (it only prints; the queue checks the axioms of every declaration). -/

/-! Polynomial F0 formulas for products and Peirce reflections over
commutative rational algebras. These formulas define the localized schedule;
their agreement with the source operation is proved over fields. -/

noncomputable section
namespace AlbertLean.Generic.SourceRingReflectionFormula

open scoped BigOperators
open AlbertLean Generated
open AlbertLean.Comparison.GenericF0
open AlbertLean.Comparison.GenericProductTransport
open AlbertLean.Triality.GenericCoordinates
open AlbertLean.Triality.StructuredCubic
open AlbertLean.Generic.SourcePeirceAttachment

universe u v
variable {R : Type u} [CommRing R] [Algebra ℚ R]

abbrev F0Ring (A : Type*) := Fin 27 → A

/-- The rational structure tensor extended to a commutative ℚ-algebra.-/
def ringProduct (x y : F0Ring R) : F0Ring R := fun c =>
  ∑ a : Fin 27, ∑ b : Fin 27,
    x a * y b * algebraMap ℚ R (tensorCoeff a b c)

/-- The literal reflection polynomial `x - 8(px) + 8(p(px))`.-/
def ringReflection (p x : F0Ring R) : F0Ring R :=
  x - (8 : R) • ringProduct p x +
    (8 : R) • ringProduct p (ringProduct p x)

def mapF0Ring {S : Type v} [CommRing S] (f : R →+* S) (x : F0Ring R) : F0Ring S :=
  fun i => f (x i)

theorem map_ringProduct {S : Type v} [CommRing S] [Algebra ℚ S]
    (f : R →+* S) (hf : f.comp (algebraMap ℚ R) = algebraMap ℚ S)
    (x y : F0Ring R) :
    mapF0Ring f (ringProduct x y) =
      ringProduct (mapF0Ring f x) (mapF0Ring f y) := by
  funext c
  have hc (q : ℚ) : f (algebraMap ℚ R q) = algebraMap ℚ S q :=
    DFunLike.congr_fun hf q
  simp [mapF0Ring, ringProduct, map_sum, map_mul, hc]

theorem map_ringReflection {S : Type v} [CommRing S] [Algebra ℚ S]
    (f : R →+* S) (hf : f.comp (algebraMap ℚ R) = algebraMap ℚ S)
    (p x : F0Ring R) :
    mapF0Ring f (ringReflection p x) =
      ringReflection (mapF0Ring f p) (mapF0Ring f x) := by
  funext c
  have hpx := congrFun (map_ringProduct f hf p x) c
  have hppx := congrFun (map_ringProduct f hf p (ringProduct p x)) c
  have hpx' := map_ringProduct f hf p x
  rw [hpx'] at hppx
  dsimp only [mapF0Ring] at hpx hppx
  simp only [ringReflection, mapF0Ring, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, map_add, map_sub, map_mul, map_ofNat, hpx, hppx]

theorem ringProduct_eq_f0ProductK {K : Type v} [Field K] [CharZero K]
    (x y : F0Ring K) : ringProduct x y = f0ProductK x y := by
  funext c
  simp [ringProduct, f0ProductK, tensorCoeffK]

/-- Over a characteristic-zero field, the ring formula is exactly the
accepted source Peirce reflection in literal F0 coordinates.-/
theorem ringReflection_eq_source {K : Type v} [Field K] [CharZero K]
    (p x : JCoord K) :
    ringReflection (structuredEquivK K p) (structuredEquivK K x) =
      structuredEquivK K (sourcePeirceReflection p x) := by
  rw [sourcePeirceReflection_formula]
  simp only [map_sub, map_add, map_smul, ringReflection,
    ringProduct_eq_f0ProductK, GenericStructuredProductAgreesWithF0]

end AlbertLean.Generic.SourceRingReflectionFormula
