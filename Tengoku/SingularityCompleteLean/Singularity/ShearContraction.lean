import Tengoku.SingularityCompleteLean.Singularity.HyperbolicTraceNormalization
import Tengoku.Seed.Topology.Algebra.Group.Matrix

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Contraction of the two unipotent subgroups

Explicit matrix multiplication proves exponential contraction of the upper
and lower shears under opposite diagonal conjugations. These are the concrete
inputs to the Mautner fixed-vector argument for SL(2,ℝ).
-/

noncomputable section
open Filter
open scoped Classical Topology MatrixGroups

namespace Singularity

/-- The upper triangular unipotent one-parameter subgroup.-/
def upperShearMatrix (u : ℝ) : SL(2, ℝ) := ⟨!![1, u; 0, 1], by simp⟩

/--
@isnad1 id=eq.0h0v.s6.25936e6a666e from=translated src=- shape=98680116 vocab=2caf9444
-/
theorem upperShearMatrix_zero : upperShearMatrix 0 = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [upperShearMatrix]

/--
@isnad1 id=eq.0h0v.s6.783eb6088caf from=translated src=- shape=98680116 vocab=79a144dd
-/
theorem lowerShearMatrix_zero : lowerShearMatrix 0 = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [lowerShearMatrix]

/--
@isnad1 id=continuo.0h0v.s5.6f30a93c45c8 from=translated src=- shape=8c4e1e81 vocab=f9190600
-/
theorem continuous_upperShearMatrix : Continuous upperShearMatrix := by
  apply Continuous.subtype_mk
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> first | exact continuous_id | exact continuous_const

/--
@isnad1 id=continuo.0h0v.s5.64377eb32112 from=translated src=- shape=8c4e1e81 vocab=cd5869f5
-/
theorem continuous_lowerShearMatrix : Continuous lowerShearMatrix := by
  apply Continuous.subtype_mk
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> first | exact continuous_id | exact continuous_const

/-- Inversion of the diagonal subgroup negates its parameter.
@isnad1 id=eq.0h1v.s6.00bfcfc4bb56 from=translated src=- shape=0aeb49a7 vocab=0be4b9c4
-/
theorem dilationMatrix_inv (t : ℝ) : (dilationMatrix t)⁻¹ = dilationMatrix (-t) := by
  have h := dilationMatrixHom.map_inv (Multiplicative.ofAdd t)
  exact h.symm

/-- Upper shears contract under backward diagonal conjugation.
@isnad1 id=eq.0h2v.s8.534555e8bf8f from=translated src=- shape=9235232a vocab=7bba7288
-/
theorem dilationMatrix_conjugate_upper (t u : ℝ) :
    (dilationMatrix t)⁻¹ * upperShearMatrix u * dilationMatrix t =
      upperShearMatrix (Real.exp (-t) * u) := by
  have he : Real.exp (t / 2) * Real.exp (t / 2) = Real.exp t := by
    rw [← Real.exp_add]; congr 1; ring
  rw [dilationMatrix_inv]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [upperShearMatrix, dilationMatrix, neg_div, Real.exp_neg, mul_assoc]
  rw [← he, mul_inv_rev]
  ring

/-- Lower shears contract under forward diagonal conjugation.
@isnad1 id=eq.0h2v.s8.002205c242c6 from=translated src=- shape=5e06daf8 vocab=5027e811
-/
theorem dilationMatrix_conjugate_lower (t u : ℝ) :
    dilationMatrix t * lowerShearMatrix u * (dilationMatrix t)⁻¹ =
      lowerShearMatrix (Real.exp (-t) * u) := by
  have he : Real.exp (t / 2) * Real.exp (t / 2) = Real.exp t := by
    rw [← Real.exp_add]; congr 1; ring
  rw [dilationMatrix_inv]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [lowerShearMatrix, dilationMatrix, neg_div, Real.exp_neg, mul_assoc]
  rw [← he, mul_inv_rev]
  ring

/-- The contraction coefficient tends to zero along positive multiples of a fixed time.
@isnad1 id=tendsto.1h2v.s5.5e696dbc1cc4 from=translated src=- shape=d354f14f vocab=54f5e8dc
-/
theorem shearParameter_tendsto_zero (τ u : ℝ) (hτ : 0 < τ) :
    Tendsto (fun n : ℕ => Real.exp (-((n : ℝ) * τ)) * u) atTop (nhds 0) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) * τ) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hτ
  have he := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ht)
  simpa using he.mul_const u

/-- The actual conjugated upper matrices converge to the identity.
@isnad1 id=tendsto.1h2v.s8.c98d9cdc71b5 from=translated src=- shape=caaef800 vocab=ac1d35b3
-/
theorem upperShear_conjugates_tendsto_one (τ u : ℝ) (hτ : 0 < τ) :
    Tendsto (fun n : ℕ => (dilationMatrix ((n : ℝ) * τ))⁻¹ * upperShearMatrix u *
      dilationMatrix ((n : ℝ) * τ)) atTop (nhds 1) := by
  simp only [dilationMatrix_conjugate_upper]
  simpa only [upperShearMatrix_zero, Function.comp_def] using
    continuous_upperShearMatrix.continuousAt.tendsto.comp (shearParameter_tendsto_zero τ u hτ)

/-- The actual conjugated lower matrices converge to the identity.
@isnad1 id=tendsto.1h2v.s8.ea4f0bf6d5d5 from=translated src=- shape=01ef2ab9 vocab=82dea331
-/
theorem lowerShear_conjugates_tendsto_one (τ u : ℝ) (hτ : 0 < τ) :
    Tendsto (fun n : ℕ => dilationMatrix ((n : ℝ) * τ) * lowerShearMatrix u *
      (dilationMatrix ((n : ℝ) * τ))⁻¹) atTop (nhds 1) := by
  simp only [dilationMatrix_conjugate_lower]
  simpa only [lowerShearMatrix_zero, Function.comp_def] using
    continuous_lowerShearMatrix.continuousAt.tendsto.comp (shearParameter_tendsto_zero τ u hτ)

end Singularity
