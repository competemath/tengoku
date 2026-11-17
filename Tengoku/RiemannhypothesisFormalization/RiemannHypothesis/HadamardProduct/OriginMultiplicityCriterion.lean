/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Tengoku.Seed.Analysis.Analytic.Order
import Tengoku.Seed.Analysis.Complex.Cardinality
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.HadamardProduct.StrictRealZeroCriterion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Affine genus-one products with a zero at the origin

This module extends the affine genus-one product by a factor `z ^ m`.  It
allows a canonical-product interface to record a zero of arbitrary finite
multiplicity at the origin instead of silently forcing the represented entire
function to be nonzero there.
-/

namespace OverflowResidueRH

open Filter Topology

/-- An affine-exponential genus-one product with an additional origin factor
`z ^ m`.-/
noncomputable def expAffineGenusOneProductWithOriginMultiplicity
    (m : ℕ) (C a b : ℂ) (zeroLoc : ℕ → ℂ) : ℂ → ℂ :=
  fun z => z ^ m * expAffineGenusOneProduct C a b zeroLoc z

/-- With a nonzero affine prefactor, the explicit origin exponent is exactly
the analytic order of the product at the origin.
@isnad1 id=eq.2h5v.s5.2e37e4851900 from=translated src=- shape=0c8d1c48 vocab=c3302c69
-/
theorem expAffineGenusOneProductWithOriginMultiplicity_analyticOrderAt_zero
    (m : ℕ) {C a b : ℂ} (hC : C ≠ 0)
    (zeroLoc : ℕ → ℂ) (H : NatHadamardZeroInvSqData zeroLoc) :
    analyticOrderAt
      (expAffineGenusOneProductWithOriginMultiplicity m C a b zeroLoc) 0 =
        (m : ℕ∞) := by
  let Hgen : HadamardZeroInvSqSummability zeroLoc :=
    H.toHadamardZeroInvSqSummability
  let Hluc : HadamardProductLocallyUniformLimitData zeroLoc
      (natHadamardFiniteExhaustion Hgen) :=
    natHadamardProductLocallyUniformLimitData Hgen
  have hbase_differentiable :
      Differentiable ℂ (expAffineGenusOneProduct C a b zeroLoc) := by
    intro z
    unfold expAffineGenusOneProduct
    exact ((by fun_prop :
      DifferentiableAt ℂ
        (fun w : ℂ => C * Complex.exp (a + b * w)) z).mul
          (Hluc.infinite_differentiableAt (Set.mem_univ z)))
  have hbase_analytic :
      AnalyticAt ℂ (expAffineGenusOneProduct C a b zeroLoc) 0 :=
    hbase_differentiable.analyticAt 0
  have hbase_ne :
      expAffineGenusOneProduct C a b zeroLoc 0 ≠ 0 := by
    unfold expAffineGenusOneProduct
    exact mul_ne_zero
      (mul_ne_zero hC (Complex.exp_ne_zero _))
      (Hgen.infiniteProduct_ne_zero (fun i => (H.zero_ne i).symm))
  have hfull_differentiable :
      Differentiable ℂ
        (expAffineGenusOneProductWithOriginMultiplicity
          m C a b zeroLoc) := by
    intro z
    unfold expAffineGenusOneProductWithOriginMultiplicity
    exact (by fun_prop :
      DifferentiableAt ℂ (fun w : ℂ => w ^ m) z).mul
        (hbase_differentiable z)
  have hfull_analytic :
      AnalyticAt ℂ
        (expAffineGenusOneProductWithOriginMultiplicity
          m C a b zeroLoc) 0 :=
    hfull_differentiable.analyticAt 0
  rw [hfull_analytic.analyticOrderAt_eq_natCast]
  refine ⟨expAffineGenusOneProduct C a b zeroLoc,
    hbase_analytic, hbase_ne, ?_⟩
  filter_upwards with z
  simp [expAffineGenusOneProductWithOriginMultiplicity]

/-- The origin contribution `m / z` has nonpositive imaginary part in the
open upper half-plane.-/
private theorem originMultiplicityResponse_im_nonpos
    (m : ℕ) (z : ℂ) (hz : 0 < z.im) :
    (((m : ℂ) / z).im) ≤ 0 := by
  rw [Complex.div_im]
  have hm_im : ((m : ℂ).im) = 0 := by simp
  have hm_re : ((m : ℂ).re) = (m : ℝ) := by simp
  rw [hm_im, hm_re]
  simp only [zero_mul, zero_div, zero_sub]
  exact neg_nonpos.mpr <| div_nonneg
    (mul_nonneg (Nat.cast_nonneg m) (le_of_lt hz))
    (Complex.normSq_nonneg z)

end OverflowResidueRH
