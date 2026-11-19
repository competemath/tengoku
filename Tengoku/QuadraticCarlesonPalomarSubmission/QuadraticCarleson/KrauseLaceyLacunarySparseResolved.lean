/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.FiniteSparseMaximalProof
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.KrauseLaceyLacunaryBlock

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The finite sparse-maximal input in the lacunary endpoint

This module installs the proved finite sparse-maximal lemma into the precise
interface used by the frozen lacunary block.  Consequently, the strongest
paper-facing endpoint below retains only the two genuinely analytic inputs
which are independent of that lemma: the individual Krause--Lacey sparse
bound for finite-radius quadratic Hilbert transforms and the ordinary
Hilbert maximal weak bound.
-/

open MeasureTheory
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyLacunarySparseResolved

open KrauseLaceyBlockHypothesis PositivePrincipalValueEndpoints
open KrauseLaceyLacunaryBlock
open LacunaryMiddleBlockWeak
open LacunaryOscillatoryScaling

set_option autoImplicit false

noncomputable section

/-- The operational finite sparse-maximal hypothesis used by the lacunary
block, with the explicit universal constant proved in
`FiniteSparseMaximalProof`.
@isnad1 id=hasfinit.0h0v.s1.b1d80b3697c4 from=translated src=- shape=49959d42 vocab=d8616561
-/
theorem hasFiniteSparseMaximalWeakBound :
    HasFiniteSparseMaximalWeakBound finiteSparseMaximalUniversalConstant := by
  refine ⟨finiteSparseMaximalUniversalConstant_pos.le, ?_⟩
  intro N T A hT
  exact finiteSparseMaximal_hasWeakOneOneBound T A hT

/-- The individual Krause--Lacey sparse bound now unconditionally supplies
the logarithm-squared frozen-block estimate.
@isnad1 id=hasunifo.1h1v.s5.c64de80395e2 from=translated src=- shape=4cd459c6 vocab=226912fe
-/
theorem hasUniformL0LogSquaredFrozenBlockWeakBounds
    {A : ℝ} (hKL : HasUniformFiniteRadiusQuadraticSparseBound A) :
    HasUniformL0LogSquaredFrozenBlockWeakBounds
      (4 * (finiteSparseMaximalUniversalConstant * A) + 128) :=
  hasUniformL0LogSquaredFrozenBlockWeakBounds_of_sparse
    hasFiniteSparseMaximalWeakBound hKL

/-- Strongest currently unconditional downstream lacunary theorem: after
discharging the finite sparse-maximal lemma, only the genuine individual
Krause--Lacey sparse theorem and the ordinary Hilbert maximal theorem remain
as analytic inputs.
@isnad1 id=ex.2h2v.s7.f2ee9972b463 from=translated src=- shape=959274d3 vocab=ee8ec87f
-/
theorem lacunary_principalValue_endpoint
    {CH : ℝ≥0∞}
    (hH : HilbertPrincipalValueClosure.HasUniformHilbertMaximalWeakBound CH)
    {A : ℝ} (hKL : HasUniformFiniteRadiusQuadraticSparseBound A) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ f : L0Infinity,
      (∀ᵐ x, ∀ m : ℤ, HasQuadraticPrincipalValue (dyadicModulation m) f x
        (principalValueRepresentative (dyadicModulation m) f x)) ∧
      ∀ α : ℝ, 0 < α →
        volume {x | ENNReal.ofReal α < lacunaryPrincipalValueMaximal f x} ≤
          C * ∫⁻ x, ENNReal.ofReal
            ((‖f x‖ / α) * paperLog 2 (‖f x‖ / α) ^ 2 *
              paperLog 4 (‖f x‖ / α)) :=
  lacunary_principalValue_endpoint_of_sparse hH
    hasFiniteSparseMaximalWeakBound hKL

end
end KrauseLaceyLacunarySparseResolved
end QuadraticCarleson
