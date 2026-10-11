import Tengoku.OpenaiMath.OAI.Combinatorics.SparsestCut.DirectionFamily

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.PivotFamily
open UniformSparsestCut.GaussianTools UniformSparsestCut.Directions
open UniformSparsestCut.DirectionFamily UniformSparsestCut.DirectionAsymptotics
open UniformSparsestCut.DirectionInterpolation
open scoped NNReal

lemma standard_density_le_one (x : ℝ) : gaussianPDFReal 0 1 x ≤ 1 := by
  rw [gaussianPDFReal]
  simp only [NNReal.coe_one,mul_one,sub_zero]
  have hs : 1 ≤ Real.sqrt (2*Real.pi) := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [Real.pi_gt_three])
  have hex : Real.exp (-x^2/2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  have hi : (√(2*Real.pi))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs
  simpa using mul_le_mul hi hex (Real.exp_nonneg _) (by norm_num : (0:ℝ) ≤ 1)

lemma standard_small_ball {a : ℝ} (ha : 0 ≤ a) :
    (gaussianReal 0 1).real {x | |x| ≤ a} ≤ 2*a := by
  have hs : {x : ℝ | |x| ≤ a} = Icc (-a) a := by ext (x : ℝ); exact (abs_le : |x| ≤ a ↔ -a ≤ x ∧ x ≤ a)
  rw [hs,measureReal_def,gaussianReal_apply_eq_integral 0 (by norm_num)]
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x))]
  calc
    _ ≤ ∫ x in Icc (-a) a, (1:ℝ) := by
      apply integral_mono (integrable_gaussianPDFReal 0 1).integrableOn (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
      exact standard_density_le_one
    _ = 2*a := by
      rw [integral_const,measureReal_def,Measure.restrict_apply MeasurableSet.univ,Set.univ_inter,Real.volume_Icc,ENNReal.toReal_ofReal (by linarith : 0 ≤ a-(-a))]
      simp only [smul_eq_mul,mul_one]; ring

lemma coordinate_small_ball {m : ℕ} (j : Fin m) {a : ℝ} (ha : 0 ≤ a) :
    (stdGaussian (EuclideanSpace ℝ (Fin m))).real {x | |x j| ≤ a} ≤ 2*a := by
  have hmap : (stdGaussian (EuclideanSpace ℝ (Fin m))).map (fun x => x j) = gaussianReal 0 1 := by
    have h := gaussian_inner_law (EuclideanSpace.single j 1 : EuclideanSpace ℝ (Fin m))
    have he : (⟨‖(EuclideanSpace.single j 1 : EuclideanSpace ℝ (Fin m))‖^2, sq_nonneg _⟩ : NNReal) = 1 := by
      apply Subtype.ext
      simp
    rw [he] at h
    simp only [EuclideanSpace.inner_single_left, map_one, one_mul] at h
    exact h
  have h := congrArg (fun μ : Measure ℝ => μ.real {x | |x| ≤ a}) hmap
  simp only [measureReal_def] at h
  rw [Measure.map_apply_of_aemeasurable (by fun_prop) (by measurability)] at h
  exact h.le.trans (standard_small_ball ha)

lemma all_coordinate_small_ball {m N S : ℕ} {a : ℝ} (ha : 0 ≤ a) :
    (Measure.pi (fun _ : Fin S => Measure.pi (fun _ : Fin N => stdGaussian (EuclideanSpace ℝ (Fin m))))).real
      {g | ∃ s i j, |g s i j| ≤ a} ≤ (S:ℝ)*((N:ℝ)*((m:ℝ)*(2*a))) := by
  have hcol : (stdGaussian (EuclideanSpace ℝ (Fin m))).real {x | ∃ j, |x j| ≤ a} ≤ (m:ℝ)*(2*a) := by
    simpa only [Fintype.card_fin,Set.mem_ofPred_eq] using finite_union_bound (fun j : Fin m => {x : EuclideanSpace ℝ (Fin m) | |x j| ≤ a}) (fun j => coordinate_small_ball j ha)
  have hchart := real_measure_exists_le (μ := stdGaussian (EuclideanSpace ℝ (Fin m)))
    (fun _ : Fin N => {x : EuclideanSpace ℝ (Fin m) | ∃ j, |x j| ≤ a}) (fun _ => by measurability) (fun _ => hcol)
  exact real_measure_exists_le
    (fun _ : Fin S => {g : Fin N → EuclideanSpace ℝ (Fin m) | ∃ i j, |g i j| ≤ a})
    (fun _ => by measurability) (fun _ => hchart)

section ExtraSelection
variable {m N S : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "μ" => stdGaussian E
local notation "ν" => Measure.pi (fun _ : Fin N => μ)
local notation "π" => Measure.pi (fun _ : Fin S => ν)

end ExtraSelection

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

structure PFamily (m : ℕ) extends Family m where
  pivot : ∀ s i j, 1/(m:ℝ)^30 < |g s i j|

lemma pivot_majorant_tendsto :
    Tendsto (fun m : ℕ => 2*(m : ℝ)^9*Real.exp (-(m : ℝ)/8) +
      6*(m : ℝ)^3*Real.exp (-(m : ℝ)) + 2/(m:ℝ)^20) atTop (𝓝 0) := by
  have hi : Tendsto (fun m : ℕ => (m:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hh := (hi.pow 20).const_mul 2
  have h := selection_majorant_tendsto.add hh
  simpa [div_eq_mul_inv,inv_pow] using h

end UniformSparsestCut.PivotFamily

end

end OAI
