import Tengoku.OpenaiMath.OAI.Probability.GaussianPropeller.Polar

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric

namespace GaussianPropeller.Cap
open OneCell ProbabilityBounds Polar
open scoped Topology

lemma p_eq_integral_indicator (a : ℝ) :
    p a = ∫ x : ℝ, (Ioi a).indicator (fun _ => (1:ℝ)) x ∂gaussianReal 0 1 := by
  rw [integral_gaussianReal_std]
  have he : (fun x : ℝ => (Ioi a).indicator (fun _ => (1:ℝ)) x*density x) =
      (Ioi a).indicator density := by
    funext x
    by_cases hx : x∈Ioi a <;> simp [hx]
  rw [he,integral_indicator measurableSet_Ioi]
  rfl

lemma p_le_one (a : ℝ) : p a ≤ 1 := by
  rw [p_eq_integral_indicator, integral_indicator measurableSet_Ioi, setIntegral_const,
    smul_eq_mul, mul_one]
  exact measureReal_le_one

lemma density_le_one (a : ℝ) : density a ≤ 1 := by
  unfold density
  rw [Real.exp_le_one_iff]
  linarith [sq_nonneg a]

variable {n : ℕ}
abbrev CE (n : ℕ) := EuclideanSpace ℝ (Fin n)

noncomputable def capP (n : ℕ) (a : ℝ) : ℝ := ∫ y : CE n, p (a*‖y‖) ∂stdGaussian (CE n)
noncomputable def capM (n : ℕ) (a : ℝ) : ℝ := gaussianConst * ∫ y : CE n, density (a*‖y‖) ∂stdGaussian (CE n)

lemma capP_zero (n : ℕ) : capP n 0 = 1/2 := by
  simp [capP,p,tail_zero]

lemma capM_eq (hn : 0<n) (a : ℝ) :
    capM n a = gaussianConst * (Real.sqrt (1+a^2))⁻¹^n := by
  let : NeZero n := ⟨by omega⟩
  have hh := integral_norm_pow_exp (ι:=Fin n) 0 (a:=a^2/2) (by positivity)
  have hs := radial_scale (n-1) (b:=a^2/2+1/2) (by positivity)
  simp only [Fintype.card_fin, add_zero, pow_zero, one_mul] at hh
  unfold capM
  have he : (fun y : CE n => density (a*‖y‖)) = fun y => Real.exp (-(a^2/2)*‖y‖^2) := by
    funext y; unfold density; congr 1; ring
  rw [he,hh,hs,show 2*(a^2/2+1/2)=1+a^2 by ring,
    show n-1+1=n by omega, mul_div_cancel_right₀ _ (radial_pos _ (by norm_num)).ne']

end GaussianPropeller.Cap

end OAI
