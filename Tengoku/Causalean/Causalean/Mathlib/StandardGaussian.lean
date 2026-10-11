/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Tengoku

/-! # Standard Gaussian Measures

This file retains compatibility names for Mathlib's standard Gaussian measure on a
finite-dimensional real inner-product space. It also identifies the law of the squared norm with
the sum of squared independent one-dimensional standard Gaussians.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InnerProductSpace WithLp
open scoped RealInnerProductSpace

namespace Causalean.Mathlib

attribute [local instance] Fintype.ofFinite

section CompatibilityCoordinateModels

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The chosen orthonormal basis of `E`. -/
@[deprecated stdOrthonormalBasis (since := "2026-09-15")]
noncomputable def onb : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E :=
  stdOrthonormalBasis ℝ E

/-- For every [real normed inner-product space](hyp:E), the [coordinate product Gaussian
measure](goal) is the product of independent standard normal laws, with one real-valued coordinate
for every element of the finite index set whose size is the space's real rank.

The product measure of independent standard normal laws, with one real-valued coordinate
for each dimension of a finite-dimensional real inner-product space. -/
noncomputable def piGaussian : Measure (Fin (Module.finrank ℝ E) → ℝ) :=
  Measure.pi (fun _ : Fin (Module.finrank ℝ E) => gaussianReal 0 1)

/-- The product standard Gaussian transported to `EuclideanSpace ℝ (Fin n)`. -/
@[deprecated ProbabilityTheory.stdGaussian (since := "2026-09-15")]
noncomputable def euclideanStdGaussian :
    Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
  ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))

end CompatibilityCoordinateModels

/-- The standard Gaussian measure on a finite-dimensional real inner-product space.

This compatibility definition is retained because banked statements use its qualified name; its
value is Mathlib's `ProbabilityTheory.stdGaussian`. -/
noncomputable def stdGaussian (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : Measure E :=
  ProbabilityTheory.stdGaussian E

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Each coordinate is `MemLp` of order 2 under the product measure.
@isnad1 id=memlp.0h2v.s7.e287eec93852 from=translated src=- shape=42549778 vocab=34a5c01f
-/
lemma memLp_eval (i : Fin (Module.finrank ℝ E)) :
    MemLp (fun ω : Fin (Module.finrank ℝ E) → ℝ => ω i) 2 (piGaussian E) := by
  have h : MemLp id 2 (gaussianReal (0 : ℝ) 1) := memLp_id_gaussianReal' 2 (by simp)
  exact h.comp_measurePreserving (measurePreserving_eval _ i)

/-- Transporting a measure through a continuous linear equivalence transports its vector integral
through the same equivalence.
@isnad1 id=eq.0h4v.s9.a406cef37334 from=translated src=- shape=adb4a66c vocab=0d365711
-/
lemma integral_id_map_equiv {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G]
    {μ : Measure F} (L : F ≃L[ℝ] G) :
    ∫ x, x ∂(μ.map L) = L (∫ x, x ∂μ) := by
  rw [integral_map (φ := L) (f := fun x => x) (by fun_prop)
    (aestronglyMeasurable_id.congr (by rfl))]
  exact L.integral_comp_comm (fun x => x)

/-- The standard Gaussian measure is a probability measure.
@isnad1 id=isprobab.0h1v.s5.ccf9c6566b5d from=translated src=- shape=4b4c0ce2 vocab=c72a4ba9
-/
@[deprecated ProbabilityTheory.isProbabilityMeasure_stdGaussian (since := "2026-09-15")]
instance isProbabilityMeasure_stdGaussian : IsProbabilityMeasure (stdGaussian E) := by
  change IsProbabilityMeasure (ProbabilityTheory.stdGaussian E)
  infer_instance

/-- The standard Gaussian measure on a finite-dimensional real inner-product space has mean
zero.
@isnad1 id=eq.0h1v.s6.2a1a3645dac8 from=translated src=- shape=73194ccd vocab=b0c33115
-/
@[deprecated ProbabilityTheory.integral_id_stdGaussian (since := "2026-09-15")]
theorem stdGaussian_mean : ∫ x, x ∂(stdGaussian E) = 0 := by
  simpa only [stdGaussian] using (ProbabilityTheory.integral_id_stdGaussian (E := E))

/-- The covariance bilinear form of the standard Gaussian measure is the ambient inner
product.
@isnad1 id=eq.0h3v.s9.52049df18d83 from=translated src=- shape=002b3425 vocab=c276f7a3
-/
@[deprecated ProbabilityTheory.covarianceBilin_stdGaussian (since := "2026-09-15")]
theorem covarianceBilin_stdGaussian (u v : E) :
    covarianceBilin (stdGaussian E) u v = (inner ℝ u v : ℝ) := by
  rw [stdGaussian, ProbabilityTheory.covarianceBilin_stdGaussian]
  rfl

/-- **Product-of-1-D-Gaussians model for the squared norm.** [The law of the squared norm
under the standard Gaussian measure on `E` equals the law of the sum of squared
coordinates under a product of `finrank ℝ E` independent standard real Gaussians](goal).

This exposes the explicit product structure needed to prove atomlessness of the χ² law.
@isnad1 id=eq.0h1v.s8.021e2615516b from=translated src=- shape=7c17a6f5 vocab=5570fbf6
-/
theorem stdGaussian_map_normSq_eq_pi :
    (stdGaussian E).map (fun x => ‖x‖ ^ 2)
      = (Measure.pi (fun _ : Fin (Module.finrank ℝ E) => gaussianReal 0 1)).map
          (fun w => ∑ i, (w i) ^ 2) := by
  rw [stdGaussian,
    ProbabilityTheory.stdGaussian_eq_map_pi_orthonormalBasis (stdOrthonormalBasis ℝ E),
    Measure.map_map (by fun_prop) (by fun_prop)]
  refine Measure.map_congr (ae_of_all _ fun w => ?_)
  simp only [Function.comp_apply]
  rw [← (stdOrthonormalBasis ℝ E).equiv_apply_euclideanSpace (toLp 2 w),
    LinearIsometryEquiv.norm_map, EuclideanSpace.norm_eq,
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, sq_abs]

end Causalean.Mathlib
