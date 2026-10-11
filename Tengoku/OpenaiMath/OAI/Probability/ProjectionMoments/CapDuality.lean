import Tengoku.OpenaiMath.OAI.Probability.ProjectionMoments.CapTests

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace Matrix
open MeasureTheory
open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rowMap_mixRows [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (X : Fin k → E) (s : E) :
    rowMap (mixRows M X) s = WithLp.toLp 2 (M *ᵥ (rowMap X s).ofLp) := by
  ext i
  simp [rowMap, mixRows, Matrix.mulVec, dotProduct]

lemma polar_label_identity {k : ℕ} {X : Fin k → E} (hX : LinearIndependent ℝ X)
    (u : Fin k → E) (c s : E) (r : ℝ) :
    rowMap X (dilate c r s) = rowMap X c + r • radialLabel X (rowMap (polarRows u X) s) := by
  have he : radialLabel X (rowMap (polarRows u X) s) = rowMap X s := by
    rw [radialLabel, ← rowMap_mixRows]
    simp only [polarRows, ite_eq_left hX, polar_reconstruction hX]
  rw [he, dilate, map_add, map_smul]
  exact add_comm _ _

lemma normalizedDensity_unitBall (ν : Measure E) [IsFiniteMeasure ν] {k : ℕ}
    {u : Fin k → E} (hu : Orthonormal ℝ u) (hs : ν.support ⊆ Metric.closedBall 0 1)
    (X : Fin k → E) (hac : ν.map (rowMap (polarRows u X)) ≪ (volume : Measure (Label k))) :
    (unitBallLaw k).withDensity (fun y => normalizedDensity ν k u (X,y)) =
      ν.map (rowMap (polarRows u X)) := by
  have he : (Metric.closedBall (0:Label k) 1).indicator
      (fun y => normalizedDensity ν k u (X,y)) = fun y => normalizedDensity ν k u (X,y) := by
    funext y
    by_cases hy : y ∈ Metric.closedBall (0:Label k) 1
    · simp [hy]
    · rw [Set.indicator_of_notMem hy]
      have hh : 1 < ‖y‖ := by simpa using hy
      exact (normalizedDensity_support ν hu hs X y hh).symm
  rw [unitBallLaw, withDensity_smul_measure, ← withDensity_indicator Metric.isClosed_closedBall.measurableSet, he,
    ← withDensity_smul_measure]
  exact normalizedDensity_is_density ν X hac

@[fun_prop] lemma measurable_capKernelValue {k : ℕ} {K : (Fin k → E) × Label k → ℝ≥0∞}
    (hK : Measurable K) : Measurable (capKernelValue K) := by
  apply Measurable.lintegral_prod_right
  exact hK.comp (measurable_snd.prodMk (by simp only [rowMap_apply]; fun_prop))

omit [BorelSpace E] in
lemma capReference_le_one [BorelSpace E] {k : ℕ} {K : (Fin k → E) × Label k → ℝ≥0∞}
    (hK1 : ∀ z, K z ≤ 1) (c : E) (r : ℝ) : capReference K c r ≤ 1 := by
  calc
    _ ≤ ∫⁻ X, ∫⁻ z : Label k, (1:ℝ≥0∞) ∂unitBallLaw k ∂Measure.pi (fun _ : Fin k => stdGaussian E) :=
      lintegral_mono (fun X => lintegral_mono (fun z => hK1 _))
    _ = 1 := by simp

omit [BorelSpace E] in
lemma capKernelValue_le_one [BorelSpace E] {k : ℕ} {K : (Fin k → E) × Label k → ℝ≥0∞}
    (hK1 : ∀ z, K z ≤ 1) (s : E) : capKernelValue K s ≤ 1 := by
  calc
    _ ≤ ∫⁻ X : Fin k → E, (1:ℝ≥0∞) ∂Measure.pi (fun _ => stdGaussian E) :=
      lintegral_mono (fun X => hK1 _)
    _ = 1 := by simp

end

lemma holder_bounded_kernel {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {g f : Ω → ℝ≥0∞} (hg : Measurable g) (hf : Measurable f) (hf1 : ∀ x, f x ≤ 1)
    {p : ℝ} (hp : 1 < p) {D : ℝ≥0∞} (hD : (∫⁻ x, g x^p ∂μ) ≤ D) :
    (∫⁻ x, g x*f x ∂μ) ≤ D^(1/p) * (∫⁻ x, f x ∂μ)^(1-1/p) := by
  have hpq := Real.HolderConjugate.conjExponent hp
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hg.aemeasurable hf.aemeasurable
  have he : 1 / Real.conjExponent p = 1-1/p := by
    simpa only [one_div] using hpq.one_sub_inv.symm
  have hpow : ∀ x, f x ^ Real.conjExponent p ≤ f x := by
    intro x
    simpa only [ENNReal.rpow_one] using ENNReal.rpow_le_rpow_of_exponent_ge (hf1 x) hpq.symm.lt.le
  simp only [Pi.mul_apply, he] at hh
  exact hh.trans (mul_le_mul' (ENNReal.rpow_le_rpow hD (by positivity))
    (ENNReal.rpow_le_rpow (lintegral_mono hpow) (by rw [← he]; exact one_div_nonneg.mpr hpq.symm.pos.le)))

lemma cap_exp_root (C d : ℝ) {p : ℝ} (hp : 0 < p) :
    (ENNReal.ofReal (Real.exp (C*d*p))) ^ (1/p) = ENNReal.ofReal (Real.exp (C*d)) := by
  rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
  congr 2
  field_simp

end ProjectionMoments

end

end OAI
