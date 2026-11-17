/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.HadamardProduct.LogDerivative
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.Xi.Definitions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Xi-specific Hadamard limit data

This module contains the compatibility interface between the generic
genus-one product library and the experimental completed-xi development. It is
kept separate so the paper's generic canonical-product results do not import
or depend on the unfinished Riemann-xi pipeline.
-/

namespace OverflowResidueRH

/-- Analytic legitimacy data for a genus-one product on points where the
project's completed-xi expression is nonzero.-/
structure HadamardLocallyUniformProductData
    {ι : Type*} (zeroLoc : ι → ℂ) : Type where
  product_multipliable :
    ∀ s : ℂ,
      Multipliable fun i : ι => hadamardGenus1Factor (zeroLoc i) s
  product_differentiable_at_xi_nonzero :
    ∀ s : ℂ,
      completedXiFunction s ≠ 0 →
      DifferentiableAt ℂ (infiniteHadamardProduct zeroLoc) s
  regularized_summable_at_xi_nonzero :
    ∀ s : ℂ,
      completedXiFunction s ≠ 0 →
      Summable fun i : ι => 1 / (s - zeroLoc i) + 1 / zeroLoc i
  logDeriv_eq_tsum_at_xi_nonzero :
    ∀ s : ℂ,
      completedXiFunction s ≠ 0 →
      logDerivativeResponse (infiniteHadamardProduct zeroLoc) s =
        hadamardRegularizedLogDerivSeries zeroLoc s

/-- Restrict generic log-derivative limit data to the nonzero completed-xi
region.-/
noncomputable def HadamardLocallyUniformProductData.of_logDerivLimitData
    {ι : Type*} {zeroLoc : ι → ℂ}
    (Hprod :
      ∀ s : ℂ,
        Multipliable fun i : ι => hadamardGenus1Factor (zeroLoc i) s)
    (Hlim : HadamardLogDerivLimitData zeroLoc)
    (h_region :
      ∀ s : ℂ, completedXiFunction s ≠ 0 → s ∈ Hlim.region) :
    HadamardLocallyUniformProductData zeroLoc :=
  { product_multipliable := Hprod
    product_differentiable_at_xi_nonzero := fun s hs =>
      Hlim.product_differentiable_at s (h_region s hs)
    regularized_summable_at_xi_nonzero := fun s hs =>
      Hlim.regularized_summable_at s (h_region s hs)
    logDeriv_eq_tsum_at_xi_nonzero := fun s hs =>
      Hlim.logDeriv_eq_tsum_at s (h_region s hs) }

end OverflowResidueRH
