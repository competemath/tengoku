/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Tengoku.BrownianMotion.BrownianMotion.Auxiliary.ContinuousBilinForm
public import Tengoku.BrownianMotion.BrownianMotion.Auxiliary.MeasureTheory
public import Tengoku

/-!
# Covariance matrix

-/

@[expose] public section

open MeasureTheory InnerProductSpace NormedSpace WithLp
open scoped ENNReal NNReal Matrix

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

/--
@isnad1 id=eq.0h4v.s9.e592986ad857 from=translated src=- shape=9f2977e1 vocab=88974eda
-/
nonrec
lemma IsGaussian.covarianceBilin_apply [IsGaussian μ] [SecondCountableTopology E] [CompleteSpace E]
    (x y : E) :
    covarianceBilin μ x y = ∫ z, ⟪x, z - μ[id]⟫_ℝ * ⟪y, z - μ[id]⟫_ℝ ∂μ :=
  covarianceBilin_apply IsGaussian.memLp_two_id x y

/--
@isnad1 id=eq.2h7v.s12.04f8be3f2d12 from=translated src=- shape=b25f82a7 vocab=82165f43
-/
lemma covarianceBilin_apply_prod {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (x y : WithLp 2 (ℝ × ℝ)) :
    covarianceBilin (μ.map (fun ω ↦ toLp 2 (X ω, Y ω))) x y =
      x.fst * y.fst * Var[X; μ] + (x.fst * y.snd + x.snd * y.fst) * cov[X, Y; μ] +
      x.snd * y.snd * Var[Y; μ] := by
  have := hX.aemeasurable
  have := hY.aemeasurable
  nth_rw 1 [covarianceBilin_apply_eq_cov, covariance_map_fun]
  · simp only [prod_inner_apply, ofLp_fst, RCLike.inner_apply', conj_trivial, ofLp_snd]
    rw [covariance_fun_add_left, covariance_fun_add_right, covariance_fun_add_right]
    · simp_rw [covariance_const_mul_left, covariance_const_mul_right]
      rw [covariance_comm X Y, covariance_self, covariance_self]
      · ring
      · exact hY.aemeasurable
      · exact hX.aemeasurable
    any_goals exact MemLp.const_mul (by assumption) _
    exact hX.const_mul _ |>.add <| hY.const_mul _
  any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop
  · exact (memLp_map_measure_iff aestronglyMeasurable_id (by fun_prop)).2
      (MemLp.of_fst_of_snd_prodLp ⟨hX, hY⟩)

/--
@isnad1 id=issymm.0h2v.s6.d9dc73e15d2d from=translated src=- shape=d719cca0 vocab=7745cff9
-/
lemma isSymm_covarianceBilin :
    LinearMap.BilinForm.IsSymm (covarianceBilin μ).toBilinForm :=
 isPosSemidef_covarianceBilin.1

variable [FiniteDimensional ℝ E]

/-- Covariance matrix of a measure on a finite dimensional inner product space. -/
noncomputable
def covMatrix (μ : Measure E) : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  LinearMap.BilinForm.toMatrix (stdOrthonormalBasis ℝ E).toBasis (covarianceBilin μ).toBilinForm

/--
@isnad1 id=eq.0h4v.s10.5507ed7ca330 from=translated src=- shape=5d256d14 vocab=112c251c
-/
lemma covMatrix_apply (μ : Measure E) (i j : Fin (Module.finrank ℝ E)) :
    covMatrix μ i j =
      covarianceBilin μ (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j) := by
  simp [covMatrix]

/--
@isnad1 id=eq.0h3v.s10.17fdd535ac07 from=translated src=- shape=b6b858b4 vocab=40fecad5
-/
lemma covMatrix_mulVec (x : Fin (Module.finrank ℝ E) → ℝ) :
    (covMatrix μ).mulVec x = fun i ↦
      covarianceBilin μ (stdOrthonormalBasis ℝ E i) (∑ j, x j • stdOrthonormalBasis ℝ E j) := by
  ext
  simp [covMatrix, Matrix.mulVec_eq_sum]

/--
@isnad1 id=eq.0h4v.s10.2761394349ad from=translated src=- shape=8b050962 vocab=e4e03f55
-/
lemma dotProduct_covMatrix_mulVec (x y : Fin (Module.finrank ℝ E) → ℝ) :
    x ⬝ᵥ (covMatrix μ).mulVec y =
      covarianceBilin μ (∑ j, x j • stdOrthonormalBasis ℝ E j)
        (∑ j, y j • stdOrthonormalBasis ℝ E j) := by
  simp_rw [covMatrix, LinearMap.BilinForm.dotProduct_toMatrix_mulVec,
    Module.Basis.equivFun_symm_apply, OrthonormalBasis.coe_toBasis]
  simp

/--
@isnad1 id=eq.0h4v.s12.29e7e790d549 from=translated src=- shape=4a7144c9 vocab=c89a381f
-/
lemma covarianceBilin_eq_dotProduct_covMatrix_mulVec (x y : E) :
    covarianceBilin μ x y =
      ((stdOrthonormalBasis ℝ E).repr x) ⬝ᵥ
        ((covMatrix μ).mulVec ((stdOrthonormalBasis ℝ E).repr y)) := by
  rw [ContinuousBilinForm.apply_eq_dotProduct_toMatrix_mulVec _ (stdOrthonormalBasis ℝ E).toBasis]
  rfl

/--
@isnad1 id=eq.1h6v.s13.a0f86944dd05 from=translated src=- shape=548348ec vocab=2cf07d86
-/
lemma covMatrix_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    [IsFiniteMeasure μ] (h : MemLp id 2 μ) (L : E →L[ℝ] F) (i j : Fin (Module.finrank ℝ F)) :
    covMatrix (μ.map L) i j =
      (stdOrthonormalBasis ℝ E).repr (L.adjoint (stdOrthonormalBasis ℝ F i)) ⬝ᵥ ((covMatrix μ) *ᵥ
        (stdOrthonormalBasis ℝ E).repr (L.adjoint (stdOrthonormalBasis ℝ F j))) := by
  rw [covMatrix_apply, covarianceBilin_map h, covarianceBilin_eq_dotProduct_covMatrix_mulVec]

/--
@isnad1 id=possemid.0h2v.s6.10a8e32c8cc7 from=translated src=- shape=904965ca vocab=60ec5e83
-/
lemma posSemidef_covMatrix : (covMatrix μ).PosSemidef := by
  rw [covMatrix, ← LinearMap.BilinForm.isPosSemidef_iff_posSemidef_toMatrix]
  exact isPosSemidef_covarianceBilin

end ProbabilityTheory
