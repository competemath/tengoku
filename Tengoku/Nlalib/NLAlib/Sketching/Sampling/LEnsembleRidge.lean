import Tengoku.Nlalib.NLAlib.Sketching.Sampling.LEnsembleMoments
import Tengoku.Nlalib.NLAlib.Matrix.Functions.RidgeKernel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ridge leverage scores as determinantal marginals

The L-ensemble with kernel `A Aᵀ / ρ` has marginal kernel equal to the
native ridge kernel. Thus its singleton probabilities are the native row
ridge scores and its expected cardinality is the native effective dimension.
Source: Dereziński–Mahoney 2020, §4.1 and §4.3.
Atlas: `l-ensemble-marginals`.
-/

noncomputable section

open MeasureTheory
open scoped Matrix

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The L-ensemble marginal kernel of a scaled row Gram matrix is exactly
the inverse-Gram ridge kernel. No rank assumption on `A` is used.
Dereziński–Mahoney 2020, §4.1.
atlas: l-ensemble-marginals (partial)
@isnad1 id=eq.1h4v.s6.d0632fda8d64 from=translated src=- shape=4b31f14b vocab=9a4c2a90
-/
theorem lEnsembleKernel_scaled_rowGram (A : Matrix m n ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    lEnsembleKernel (ρ⁻¹ • (A * Aᵀ)) = ridgeKernel A ρ := by
  have hL : (ρ⁻¹ • (A * Aᵀ)).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] using
      (Matrix.posSemidef_conjTranspose_mul_self Aᵀ).smul (inv_nonneg.mpr hρ.le)
  have hm : 1 + ρ⁻¹ • (A * Aᵀ) = ρ⁻¹ • ridgeGram Aᵀ ρ := by
    simp only [ridgeGram, Matrix.transpose_transpose, smul_add, smul_smul,
      inv_mul_cancel₀ hρ.ne', one_smul, add_comm]
  have hi : (1 + ρ⁻¹ • (A * Aᵀ))⁻¹ = ρ • (ridgeGram Aᵀ ρ)⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [hm, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp
        (posDef_ridgeGram Aᵀ hρ).isUnit), smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]
  rw [lEnsembleKernel_eq_one_sub_inv hL, hi, ridgeKernel_eq_one_sub_smul_inv A hρ]

/-- The actual variable-size determinantal law with kernel `A Aᵀ / ρ` for
positive regularization. Its singleton masses are ridge leverage scores;
it is not a fixed-cardinality volume-sampling law.
Dereziński–Mahoney 2020, §4.1.-/
def lEnsembleRidgeLaw (A : Matrix m n ℝ) (ρ : ℝ) (hρ : 0 < ρ) : Measure (Finset m) :=
  lEnsembleLaw (ρ⁻¹ • (A * Aᵀ)) (by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] using
      (Matrix.posSemidef_conjTranspose_mul_self Aᵀ).smul (inv_nonneg.mpr hρ.le))

/-- A row's ridge leverage score is its singleton inclusion probability in
the corresponding variable-size DPP. Dereziński–Mahoney 2020, §4.1.
atlas: l-ensemble-marginals (partial)
@isnad1 id=eq.1h5v.s6.c8e809ab99dd from=translated src=- shape=3acfdfea vocab=5ced9d0b
-/
theorem measureReal_mem_lEnsembleRidgeLaw (A : Matrix m n ℝ) (ρ : ℝ)
    (hρ : 0 < ρ) (i : m) :
    (lEnsembleRidgeLaw A ρ hρ).real {S | i ∈ S} = ridgeLeverageScore A ρ i := by
  unfold lEnsembleRidgeLaw
  rw [measureReal_mem_lEnsembleLaw, lEnsembleKernel_scaled_rowGram A hρ]
  exact (ridgeLeverageScore_eq_ridgeKernel_apply A ρ i).symm

/-- The expected size of the ridge L-ensemble is the native effective
dimension, defined as the sum of the actual row scores.
Dereziński–Mahoney 2020, §4.3.
atlas: l-ensemble-marginals (partial)
@isnad1 id=eq.1h4v.s6.c084dfc81a2d from=translated src=- shape=cf783745 vocab=b8379b7b
-/
theorem integral_card_lEnsembleRidgeLaw (A : Matrix m n ℝ) (ρ : ℝ) (hρ : 0 < ρ) :
    ∫ S, (S.card : ℝ) ∂lEnsembleRidgeLaw A ρ hρ = ridgeEffectiveDimension A ρ := by
  unfold lEnsembleRidgeLaw
  rw [integral_card_lEnsembleLaw, lEnsembleKernel_scaled_rowGram A hρ,
    ridgeEffectiveDimension_eq_trace]

end NLAlib
