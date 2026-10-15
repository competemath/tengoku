/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/
module

public import Tengoku.LeanPool.LeanPool.LocalComplexGeometry.ClassicalComplexWPT.AnalyticSeries
public import Tengoku

/-!
# Analytic maps into a weighted coefficient space

An ambient formal multilinear series with positive radius determines, after
choosing a smaller distinguished-variable radius `r`, an analytic map from the
base variables into `ℓ¹(ℕ, ℂ)`.  Its `k`-th coordinate is
`r ^ k * lastTaylorCoefficient p k z`.

The proof is entirely Archimedean.  It uses Mathlib's explicit
`changeOriginSeries_summable_aux₁` binomial majorant, absolute summability, and
the ordinary triangle inequality.  In particular, it does not use the
ultrametric multiplication estimates for restricted or Gauss-norm power
series.
-/

@[expose] public section

open scoped NNReal ENNReal Topology

namespace ClassicalComplexWPT

/-- The Banach space of absolutely summable complex sequences. -/
noncomputable abbrev WeightedSeq := lp (fun _ : ℕ ↦ ℂ) 1

/-- Include the base variables into the ambient space at last coordinate zero. -/
noncomputable def baseInclusion (n : ℕ) : Base n →L[ℂ] Ambient n :=
  ContinuousLinearMap.inl ℂ (Base n) ℂ

/-- Evaluate a multilinear form on copies of the last coordinate direction. -/
noncomputable def evalLast (n k : ℕ) :
    ((Ambient n)[×k]→L[ℂ] ℂ) →L[ℂ] ℂ :=
  ContinuousMultilinearMap.apply ℂ (fun _ : Fin k ↦ Ambient n) ℂ
    (fun _ ↦ lastDirection n)

/--
@isnad1 id=eq.0h1v.s5.532f3e0d7693 from=translated src=- shape=7aab2fa7 vocab=1d7e139f
-/
@[simp] theorem norm_lastDirection (n : ℕ) : ‖lastDirection n‖ = 1 := by
  simp [lastDirection]

/--
@isnad1 id=eq.0h2v.s8.98929c36b225 from=translated src=- shape=9fb0948b vocab=150c72ee
-/
@[simp] theorem baseInclusion_apply (n : ℕ) (z : Base n) :
    baseInclusion n z = (z, 0) := rfl

/--
@isnad1 id=le.0h1v.s8.de2dd6f6c0c8 from=translated src=- shape=94243882 vocab=41d6e9e6
-/
theorem norm_baseInclusion_le (n : ℕ) : ‖baseInclusion n‖ ≤ 1 := by
  exact ContinuousLinearMap.opNorm_le_bound (baseInclusion n) (by norm_num) (fun z ↦ by
    simp [baseInclusion])

/--
@isnad1 id=le.0h2v.s9.a835773bcebd from=translated src=- shape=56a25f30 vocab=d8798acf
-/
theorem norm_evalLast_le (n k : ℕ) : ‖evalLast n k‖ ≤ 1 := by
  exact ContinuousLinearMap.opNorm_le_bound (evalLast n k) (by norm_num) (fun q ↦ by
    simpa [evalLast, norm_lastDirection] using
      q.le_opNorm (fun _ ↦ lastDirection n))

/-- The base-variable series for the `k`th last-coordinate coefficient. -/
noncomputable def lastCoefficientSeries {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (k : ℕ) :
    FormalMultilinearSeries ℂ (Base n) ℂ :=
  (evalLast n k).compFormalMultilinearSeries
    ((p.changeOriginSeries k).compContinuousLinearMap (baseInclusion n))

/-- Place a scalar in sequence coordinate `k`, weighted by `r ^ k`. -/
noncomputable def weightedSingleCLM (r : ℝ≥0) (k : ℕ) :
    ℂ →L[ℂ] WeightedSeq :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ℕ ↦ ℂ) 1 k).comp
    ((r : ℂ) ^ k • ContinuousLinearMap.id ℂ ℂ)

/--
@isnad1 id=eq.0h3v.s10.90dcc3b5fcdc from=translated src=- shape=59aae671 vocab=34ffe877
-/
@[simp] theorem weightedSingleCLM_apply (r : ℝ≥0) (k : ℕ) (z : ℂ) :
    weightedSingleCLM r k z = lp.single 1 k ((r : ℂ) ^ k * z) := by
  rfl

/-- The weighted sequence-valued series supported in coordinate `k`. -/
noncomputable def weightedCoordinateSeries {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0) (k : ℕ) :
    FormalMultilinearSeries ℂ (Base n) WeightedSeq :=
  (weightedSingleCLM r k).compFormalMultilinearSeries (lastCoefficientSeries p k)

/-- Assemble all weighted last-coordinate coefficient series. -/
noncomputable def weightedCoefficientSeries {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0) :
    FormalMultilinearSeries ℂ (Base n) WeightedSeq :=
  fun l ↦ ∑' k : ℕ, weightedCoordinateSeries p r k l

/--
@isnad1 id=le.0h4v.s10.b513c9016742 from=translated src=- shape=b82a7c72 vocab=71d1d5d3
-/
theorem norm_lastCoefficientSeries_le {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (k l : ℕ) :
    ‖lastCoefficientSeries p k l‖ ≤ ‖p.changeOriginSeries k l‖ := by
  unfold lastCoefficientSeries
  rw [ContinuousLinearMap.compFormalMultilinearSeries_apply]
  have hpre :
      ‖((p.changeOriginSeries k).compContinuousLinearMap (baseInclusion n)) l‖ ≤
        ‖p.changeOriginSeries k l‖ := by
    calc
      _ ≤ ‖p.changeOriginSeries k l‖ * ‖baseInclusion n‖ ^ l :=
        (p.changeOriginSeries k).norm_compContinuousLinearMap_le (baseInclusion n) l
      _ ≤ ‖p.changeOriginSeries k l‖ * 1 ^ l := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg (baseInclusion n)) (norm_baseInclusion_le n) l)
          (norm_nonneg (p.changeOriginSeries k l))
      _ = ‖p.changeOriginSeries k l‖ := by simp
  calc
    ‖(evalLast n k).compContinuousMultilinearMap
        (((p.changeOriginSeries k).compContinuousLinearMap (baseInclusion n)) l)‖ ≤
        ‖evalLast n k‖ *
          ‖((p.changeOriginSeries k).compContinuousLinearMap (baseInclusion n)) l‖ :=
      ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ 1 * ‖p.changeOriginSeries k l‖ :=
      mul_le_mul (norm_evalLast_le n k) hpre
        (norm_nonneg (((p.changeOriginSeries k).compContinuousLinearMap
          (baseInclusion n)) l)) (by norm_num)
    _ = ‖p.changeOriginSeries k l‖ := one_mul _

/--
@isnad1 id=eq.0h6v.s12.28b42ee6d92d from=translated src=- shape=45666607 vocab=7cfb2ed5
-/
@[simp] theorem weightedCoordinateSeries_apply {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0) (k l : ℕ)
    (v : Fin l → Base n) :
    weightedCoordinateSeries p r k l v =
      lp.single 1 k ((r : ℂ) ^ k *
        (p.changeOriginSeries k l) (fun i ↦ baseInclusion n (v i))
          (fun _ ↦ lastDirection n)) := by
  rfl

/-- The weighted last-direction Taylor coefficients at an ambient point. -/
noncomputable def weightedLastCoeffs {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0) (x : Ambient n)
    (hr : (r : ℝ≥0∞) < (p.changeOrigin x).radius) : WeightedSeq :=
  ⟨fun k ↦ (r : ℂ) ^ k * p.changeOrigin x k (fun _ ↦ lastDirection n), by
    apply memℓp_gen
    have hs : Summable (fun k : ℕ ↦ ‖p.changeOrigin x k‖ * (r : ℝ) ^ k) :=
      (p.changeOrigin x).summable_norm_mul_pow hr
    simpa only [ENNReal.toReal_one, Real.rpow_one] using
      hs.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ by
        change ‖(r : ℂ) ^ k * ((p.changeOrigin x) k) (fun _ ↦ lastDirection n)‖ ≤
          ‖(p.changeOrigin x) k‖ * (r : ℝ) ^ k
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg r.coe_nonneg]
        have hv : ‖((p.changeOrigin x) k) (fun _ ↦ lastDirection n)‖ ≤
            ‖(p.changeOrigin x) k‖ := by
          simpa [norm_lastDirection] using
            ((p.changeOrigin x) k).le_opNorm (fun _ ↦ lastDirection n)
        calc
          (r : ℝ) ^ k * ‖((p.changeOrigin x) k) (fun _ ↦ lastDirection n)‖ ≤
              (r : ℝ) ^ k * ‖(p.changeOrigin x) k‖ :=
            mul_le_mul_of_nonneg_left hv (pow_nonneg r.coe_nonneg k)
          _ = ‖(p.changeOrigin x) k‖ * (r : ℝ) ^ k := mul_comm _ _)⟩

/--
@isnad1 id=eq.1h5v.s9.5726b1555027 from=translated src=- shape=0fd3f7b0 vocab=96db6e7e
-/
@[simp] theorem weightedLastCoeffs_apply {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0) (x : Ambient n)
    (hr : (r : ℝ≥0∞) < (p.changeOrigin x).radius) (k : ℕ) :
    weightedLastCoeffs p r x hr k =
      (r : ℂ) ^ k * p.changeOrigin x k (fun _ ↦ lastDirection n) := rfl

end ClassicalComplexWPT
