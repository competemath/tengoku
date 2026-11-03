import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.GenericJordanExtension
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.PeirceJordan
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ResidualAction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms sourcePeirceLinearEquiv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sourcePeirceLinearEquiv_product` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sourcePeirceAut` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Peirce reflections on the actual generic source product

The generic Jordan identity and Peirce reflection theorem are attached to the
accepted source product without another coordinate expansion.
-/

noncomputable section
namespace AlbertLean.Generic.SourcePeirceAttachment

open AlbertLean.Triality
open AlbertLean.Generic.JordanPolarization
open AlbertLean.Generic.PeirceJordan
open AlbertLean.Generic.PeircePolynomial
open AlbertLean.Generic.ResidualAction
open AlbertLean.Comparison.GenericJordanExtension
open AlbertLean.Triality.CoordinateTensor
open AlbertLean.Triality.StructuredCubic
open AlbertLean.Triality.StructuredProduct

variable {K : Type*} [Field K] [CharZero K]

private theorem sourceResidual_zero (x y : JCoord K) :
    residual (sourceProductLinear (K := K)) x y = 0 := by
  apply sub_eq_zero.mpr
  simpa only [sourceProductLinear_apply] using
    AlbertLean.Comparison.GenericJordanExtension.sourceJordanIdentity x y

/-- The literal source reflection attached to an idempotent.-/
def sourcePeirceReflection (p x : JCoord K) : JCoord K :=
  PeircePolynomial.reflection (sourceProductLinear (K := K)) p x

/--
@isnad1 id=eq.0h3v.s8.762a5002bb15 from=translated src=- shape=1c6f9b5c vocab=48ba2e17
-/
theorem sourcePeirceReflection_formula (p x : JCoord K) :
    sourcePeirceReflection p x =
      x - (8 : K) • sourceProduct p x +
        (8 : K) • sourceProduct p (sourceProduct p x) := rfl

/-- An idempotent gives an actual involutive linear equivalence of the source
carrier.-/
def sourcePeirceLinearEquiv (p : JCoord K)
    (hp : sourceProduct p p = p) : JCoord K ≃ₗ[K] JCoord K :=
  reflectionEquiv sourceProductLinear sourceProduct_comm sourceResidual_zero p hp

/--
@isnad1 id=eq.1h3v.s8.b89c14de1847 from=translated src=- shape=75616c00 vocab=3344fe83
-/
@[simp] theorem sourcePeirceLinearEquiv_apply (p : JCoord K)
    (hp : sourceProduct p p = p) (x : JCoord K) :
    sourcePeirceLinearEquiv p hp x = sourcePeirceReflection p x := by
  exact reflectionEquiv_apply sourceProductLinear sourceProduct_comm
    sourceResidual_zero p hp x

/--
@isnad1 id=eq.1h2v.s8.e7a1e65ce0cb from=translated src=- shape=044f4cd3 vocab=d5f056e3
-/
@[simp] theorem sourcePeirceLinearEquiv_one (p : JCoord K)
    (hp : sourceProduct p p = p) :
    sourcePeirceLinearEquiv p hp sourceOne = sourceOne := by
  exact reflectionEquiv_unit sourceProductLinear sourceProduct_comm
    sourceResidual_zero sourceOne p (sourceProduct_one_right p) hp

/--
@isnad1 id=eq.1h4v.s10.6bf10f9cf40f from=translated src=- shape=aa40084e vocab=75e4b733
-/
theorem sourcePeirceLinearEquiv_product (p : JCoord K)
    (hp : sourceProduct p p = p) (x y : JCoord K) :
    sourcePeirceLinearEquiv p hp (sourceProduct x y) =
      sourceProduct (sourcePeirceLinearEquiv p hp x)
        (sourcePeirceLinearEquiv p hp y) := by
  simpa only [sourcePeirceLinearEquiv_apply, sourcePeirceReflection,
    sourceProductLinear_apply] using
    reflection_mul sourceProductLinear sourceProduct_comm
      sourceResidual_zero p hp x y

/-- Package the Peirce reflection in the already accepted minimal source
automorphism structure.  No cubic- or trace-preservation premise is used.-/
def sourcePeirceAut (p : JCoord K) (hp : sourceProduct p p = p) :
    SourceAut (K := K) where
  linear := sourcePeirceLinearEquiv p hp
  map_one := sourcePeirceLinearEquiv_one p hp
  map_product := sourcePeirceLinearEquiv_product p hp

end AlbertLean.Generic.SourcePeirceAttachment
