import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.KrauseLaceyNativePositiveSuffixResolved
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.KrauseLaceyPStoppingPositiveClosure
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.LacunaryEndpointSmoothResolved

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The native positive-suffix route to the lacunary endpoint

This interface records the two conditional entrances to the positive
Krause--Lacey argument.  A one-node good-part estimate yields sparse control
of each concrete localized shifted tail.  Independently, the native unit
positive-suffix sparse estimate feeds the proved annular, dilation, and
principal-value adapters.
-/

open MeasureTheory
open scoped ENNReal

namespace QuadraticCarleson.KrauseLaceyNativePositiveEndpoint

open KrauseLaceyAnnularSparseTransfer KrauseLaceyNativePositiveSuffixClosure
open KrauseLaceyNativePositiveSuffixResolved
open KrauseLaceyPStoppingPositiveClosure
open KrauseLaceyThreeShiftGrid LacunaryEndpointSmoothResolved
open PositivePrincipalValueEndpoints

set_option autoImplicit false

/-- The established stopping recursion turns the one-node good-part input
into sparse domination for a concrete localized shifted tail.
@isnad1 id=hasspars.5h8v.s6.8169ba8981d7 from=translated src=- shape=83cd93d5 vocab=b5a3c8cf
-/
theorem hasSparseOnePBound_localizedTail_of_oneNodeGoodPart
    {A p : ℝ} (hA : HasOneNodeGoodPartPairingBound A)
    (hp : 1 < p) (hp2 : p < 2)
    (ell₀ topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ) (q₀ : ℤ)
    (S : Finset RealInterval) (hS : S ⊆
      completeFiniteShiftGridTree topScale shift maxDepth q₀)
    (hell : 3 ≤ ell₀) :
    HasSparseOnePBound (A * holderConjugate p) p
      (localizedTailMaximalTestOperator ell₀
        (finiteShiftGridScale topScale shift) S) :=
  hasSparseOnePBound_localizedTailMaximalTestOperator_of_tree
    hA hp hp2 ell₀ topScale shift maxDepth q₀ S hS hell

/-- Localized-tail sparse domination through the genuine `p`-mass stopping
recursion.
@isnad1 id=hasspars.5h8v.s6.c685b332326a from=translated src=- shape=83cd93d5 vocab=26078c6e
-/
theorem hasSparseOnePBound_localizedTail_of_oneNodePStoppingGoodPart
    {A p : ℝ} (hA : HasOneNodePStoppingGoodPartPairingBound A)
    (hp : 1 < p) (hp2 : p < 2)
    (ell₀ topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ) (q₀ : ℤ)
    (S : Finset RealInterval) (hS : S ⊆
      completeFiniteShiftGridTree topScale shift maxDepth q₀)
    (hell : 3 ≤ ell₀) :
    HasSparseOnePBound (A * holderConjugate p) p
      (localizedTailMaximalTestOperator ell₀
        (finiteShiftGridScale topScale shift) S) :=
  hasSparseOnePBound_localizedTailMaximalTestOperator_of_pStopping_tree
    hA hp hp2.le ell₀ topScale shift maxDepth q₀ S hS hell

/-- The paper-facing lacunary principal-value endpoint conditional on exactly
the native unit-modulation positive dyadic-suffix sparse estimate.
@isnad1 id=ex.1h1v.s7.50c25561b5a8 from=translated src=- shape=c04912af vocab=1b48052e
-/
theorem lacunary_principalValue_endpoint_of_nativePositiveSuffix
    {C : ℝ} (hC : HasNativeUnitPositiveSuffixSparseBound C) :
    ∃ K : ℝ≥0∞, K < ∞ ∧ ∀ f : L0Infinity,
      (∀ᵐ x, ∀ m : ℤ, HasQuadraticPrincipalValue (dyadicModulation m) f x
        (principalValueRepresentative (dyadicModulation m) f x)) ∧
      ∀ alpha : ℝ, 0 < alpha →
        volume {x | ENNReal.ofReal alpha < lacunaryPrincipalValueMaximal f x} ≤
          K * ∫⁻ x, ENNReal.ofReal
            ((‖f x‖ / alpha) * paperLog 2 (‖f x‖ / alpha) ^ 2 *
              paperLog 4 (‖f x‖ / alpha)) :=
  lacunary_principalValue_endpoint_of_smoothSparse
    (hasUniformFiniteRadiusSmoothSparseBound_of_native hC)

/-- Paper-facing endpoint obtained from the genuine p-stopping one-node
estimate, with the source-external low-starting suffix range isolated as a
separate hypothesis.
@isnad1 id=ex.2h2v.s7.2cd7dc45a4ab from=translated src=- shape=bfba0c0a vocab=c7f8ae9f
-/
theorem lacunary_principalValue_endpoint_of_oneNodePStoppingGoodPart_and_low
    {A D : ℝ} (hlocal : HasOneNodePStoppingGoodPartPairingBound A)
    (hlow : HasNativeUnitLowPositiveSuffixSparseBound D) :
    ∃ K : ℝ≥0∞, K < ∞ ∧ ∀ f : L0Infinity,
      (∀ᵐ x, ∀ m : ℤ, HasQuadraticPrincipalValue (dyadicModulation m) f x
        (principalValueRepresentative (dyadicModulation m) f x)) ∧
      ∀ alpha : ℝ, 0 < alpha →
        volume {x | ENNReal.ofReal alpha < lacunaryPrincipalValueMaximal f x} ≤
          K * ∫⁻ x, ENNReal.ofReal
            ((‖f x‖ / alpha) * paperLog 2 (‖f x‖ / alpha) ^ 2 *
              paperLog 4 (‖f x‖ / alpha)) :=
  lacunary_principalValue_endpoint_of_nativePositiveSuffix
    (hasNativeUnitPositiveSuffixSparseBound_of_oneNodePStoppingGoodPart_and_low
      hlocal hlow)

end QuadraticCarleson.KrauseLaceyNativePositiveEndpoint
