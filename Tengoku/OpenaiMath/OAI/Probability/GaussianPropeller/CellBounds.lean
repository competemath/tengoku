import Tengoku.OpenaiMath.OAI.Probability.GaussianPropeller.Attainment

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

namespace GaussianPropeller.Reduction
open Set GaussianPropeller.Quantile GaussianPropeller.OneCell GaussianPropeller.ProbabilityBounds
open scoped RealInnerProductSpace
variable {d k : ℕ} [NeZero k]

lemma winning_inner_nonneg (z : Fin k → Space d) (hz : ∑ j,z j=0)
    (i : Fin k) {x : Space d} (hx : x ∈ closedCell z i) : 0 ≤ ⟪z i,x⟫ := by
  have hh : (0:ℝ) ≤ ∑ j : Fin k, (⟪z i,x⟫-⟪z j,x⟫) :=
    Finset.sum_nonneg (fun j _ => sub_nonneg.mpr (hx j))
  have hz' : (∑ j,⟪z j,x⟫)=0 := by rw [← sum_inner,hz,inner_zero_left]
  rw [Finset.sum_sub_distrib, hz', sub_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  exact nonneg_of_mul_nonneg_right hh (by exact_mod_cast (NeZero.pos k))

lemma active_probability_mem (_hk : 2 ≤ k) {A : Fin k → Set (Space d)}
    (hA : MinimalOptimal A) (hpos : 0 < value A) {i : Fin k}
    (hi : gaussian d (A i) ≠ 0) : 0 < (gaussian d).real (A i) ∧ (gaussian d).real (A i) ≤ 1/2 := by
  let : IsProbabilityMeasure (gaussian d) := inferInstanceAs (IsProbabilityMeasure (stdGaussian (Space d)))
  have hP : 0 < (gaussian d).real (A i) := ENNReal.toReal_pos hi (measure_ne_top _ _)
  have hzn : centroid (A i) ≠ 0 := active_centroid_ne_zero hA hpos hi
  let e : Space d := - (‖centroid (A i)‖⁻¹ • centroid (A i))
  have he : ‖e‖=1 := by simp [e, norm_smul, norm_ne_zero_iff.mpr hzn]
  have hmap := OneCell.map_unit_inner_gaussian e he
  have hs : closedCell (fun j => centroid (A j)) i ⊆ {x | ⟪e,x⟫ ≤ 0} := by
    intro x hx
    have hn := winning_inner_nonneg (fun j => centroid (A j)) (sum_centroid_eq_zero hA.1.1) i hx
    simp only [Set.mem_ofPred_eq,e,inner_neg_left,real_inner_smul_left]
    exact neg_nonpos.mpr (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) hn)
  have heq : (gaussian d) {x | ⟪e,x⟫ ≤ 0} = (gaussianReal 0 1) (Iic 0) := by
    rw [← hmap, Measure.map_apply (by fun_prop) measurableSet_Iic]
    rfl
  refine ⟨hP, ?_⟩
  have hh := measure_mono (μ:=gaussian d) hs
  rw [← measure_congr (active_eq_closedCell_ae hA hpos hi), heq] at hh
  have hh' := ENNReal.toReal_mono (measure_ne_top _ _) hh
  change (gaussian d).real (A i) ≤ (gaussianReal 0 1).real (Iic 0) at hh'
  rw [← Φ_eq_gaussianReal, Φ_zero] at hh'
  exact hh'

lemma p_eq_Φ_neg (x : ℝ) : p x=Φ (-x) := by
  rw [Φ_neg, Φ_eq_one_sub_tail]
  simp only [φ, OneCell.gaussianConst, p, OneCell.tail, OneCell.density]
  rw [integral_const_mul]
  ring

lemma loss_rationalize {C α r L : ℝ} (_hC : 0 < C) (hα : 0 < α)
    (_hr : 0 ≤ r) (hs : 0 ≤ 1-α*r^2)
    (hl : C*(1-Real.sqrt (1-α*r^2)) ≤ α*L) :
    C*r^2/(1+Real.sqrt (1-α*r^2)) ≤ L := by
  have hq := Real.sqrt_nonneg (1-α*r^2)
  have hq2 := Real.sq_sqrt hs
  rw [div_le_iff₀ (by positivity)]
  have hm := mul_le_mul_of_nonneg_right hl (show 0 ≤ 1+Real.sqrt (1-α*r^2) by positivity)
  have heq : C*(1-Real.sqrt (1-α*r^2))*(1+Real.sqrt (1-α*r^2)) = α*(C*r^2) := by
    calc
      _ = C*(1-Real.sqrt (1-α*r^2)^2) := by ring
      _ = _ := by rw [hq2]; ring
  rw [heq] at hm
  exact (mul_le_mul_iff_right₀ hα).mp (by simpa only [mul_assoc] using hm)

end GaussianPropeller.Reduction

end OAI
