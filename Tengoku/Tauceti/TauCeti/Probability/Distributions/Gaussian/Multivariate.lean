/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.Probability.Moments.Covariance

/-!
# The covariance matrix of a multivariate Gaussian

This file identifies the generic covariance matrix from
`TauCeti.Probability.Moments.Covariance` with the covariance parameter of Mathlib's multivariate
Gaussian, and records the centred multivariate Gaussian as the image of the standard Gaussian
under the square root of its matrix parameter. It also records covariance under matrix-valued
linear maps and characterizes independence of complementary coordinate blocks.

## Main results

* `TauCeti.Probability.covMatrix_multivariateGaussian` recovers the covariance parameter of a
  multivariate
  Gaussian law.
* `TauCeti.Probability.integral_of_hasLaw_multivariateGaussian` gives the Bochner mean of a
  random variable with a multivariate Gaussian law.
* `TauCeti.Probability.multivariateGaussian_zero_eq_map_stdGaussian_sqrt` writes the centred law as
  an image
  of the standard Gaussian.
* `TauCeti.Probability.covariance_inner_matrix_multivariateGaussian` computes covariance after two
  matrix
  maps.
* `TauCeti.Probability.indepFun_sumEquivProd_multivariateGaussian_iff` characterizes independence of
  two
  complementary coordinate blocks.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 5, item 1,
  **Covariance matrices**.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace

namespace TauCeti.Probability

variable {ι : Type*}

/-- The covariance matrix of a positive-semidefinite multivariate Gaussian is its covariance
parameter. -/
@[simp]
theorem covMatrix_multivariateGaussian [Fintype ι] [DecidableEq ι] (m : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) :
    covMatrix (multivariateGaussian m S) = S := by
  classical
  ext i j
  simpa only [covMatrix_apply] using covariance_eval_multivariateGaussian hS i j

/-- The Bochner mean of a random variable with a multivariate Gaussian law is its Gaussian mean. -/
theorem integral_of_hasLaw_multivariateGaussian [Fintype ι] [DecidableEq ι]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → EuclideanSpace ℝ ι} {m : EuclideanSpace ℝ ι}
    {S : Matrix ι ι ℝ} (hX : HasLaw X (multivariateGaussian m S) P) :
    ∫ ω, X ω ∂P = m := by
  rw [hX.integral_eq, integral_id_multivariateGaussian]

/-- A centred multivariate Gaussian law is the image of the standard Gaussian under the square
root of its matrix parameter. No hypothesis on that parameter is needed. -/
theorem multivariateGaussian_zero_eq_map_stdGaussian_sqrt [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) :
    multivariateGaussian 0 S =
      (stdGaussian (EuclideanSpace ℝ ι)).map
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)) := by
  simp [multivariateGaussian]

/-- The covariance of scalar inner-product projections after two matrix-valued linear maps of a
multivariate Gaussian. -/
theorem covariance_inner_matrix_multivariateGaussian
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq γ]
    (m : EuclideanSpace ℝ γ) {S : Matrix γ γ ℝ} (hS : S.PosSemidef)
    (L : Matrix α γ ℝ) (K : Matrix β γ ℝ) (x : EuclideanSpace ℝ α)
    (y : EuclideanSpace ℝ β) :
    cov[fun z => ⟪x, L.toEuclideanLin z⟫, fun z => ⟪y, K.toEuclideanLin z⟫;
      multivariateGaussian m S] =
      x.ofLp ⬝ᵥ (L * S * K.transpose).mulVec y.ofLp := by
  classical
  have hL : (fun z => ⟪x, L.toEuclideanLin z⟫) =
      fun z => ⟪L.transpose.toEuclideanLin x, z⟫ := by
    funext z
    symm
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial L,
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]
  have hK : (fun z => ⟪y, K.toEuclideanLin z⟫) =
      fun z => ⟪K.transpose.toEuclideanLin y, z⟫ := by
    funext z
    symm
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial K,
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]
  rw [hL, hK, ← covarianceBilin_apply_eq_cov,
    covarianceBilin_multivariateGaussian hS]
  · have hLapply : (L.transpose.toEuclideanLin x).ofLp = L.transpose.mulVec x.ofLp := by
      simpa only [Matrix.toLin'_apply] using
        Matrix.ofLp_toLpLin (p := 2) (q := 2) L.transpose x
    have hKapply : (K.transpose.toEuclideanLin y).ofLp = K.transpose.mulVec y.ofLp := by
      simpa only [Matrix.toLin'_apply] using
        Matrix.ofLp_toLpLin (p := 2) (q := 2) K.transpose y
    rw [hLapply, hKapply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    calc
      L.transpose.mulVec x.ofLp ⬝ᵥ S.mulVec (K.transpose.mulVec y.ofLp) =
          Matrix.vecMul x.ofLp L ⬝ᵥ S.mulVec (K.transpose.mulVec y.ofLp) := by
        rw [Matrix.mulVec_transpose]
      _ = x.ofLp ⬝ᵥ L.mulVec (S.mulVec (K.transpose.mulVec y.ofLp)) :=
        (Matrix.dotProduct_mulVec x.ofLp L
          (S.mulVec (K.transpose.mulVec y.ofLp))).symm
  · exact IsGaussian.memLp_two_id

end TauCeti.Probability
