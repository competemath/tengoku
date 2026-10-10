import Tengoku.OpenaiMath.OAI.Analysis.DirectCrouzeix.Convexity

namespace OAI

universe u_143

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set

open scoped ComplexConjugate Matrix

namespace DirectCrouzeix.Geometry

theorem positive_parallel_of_complex_inner {G q : ℂ} (hG : G ≠ 0) (hq : q ≠ 0)
    (horth : inner ℝ G (Complex.I*q) = 0) (hpos : 0 ≤ inner ℝ G q) :
    ∃ t : ℝ, 0 < t ∧ q = t • G := by
  have him : (conj G*q).im = 0 := by
    rw [real_inner_eq_re_inner ℂ,RCLike.inner_apply] at horth
    change ((Complex.I*q)*conj G).re = 0 at horth
    simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.conj_re,Complex.conj_im] at horth ⊢
    nlinarith
  have hre : (conj G*q).re = inner ℝ G q := by
    simp [real_inner_eq_re_inner ℂ,RCLike.inner_apply,mul_comm]
  have hnon : inner ℝ G q ≠ 0 := by
    intro hh
    have he : conj G*q = 0 := Complex.ext (by simpa [hre] using hh) (by simpa using him)
    exact mul_ne_zero ((map_ne_zero (starRingEnd ℂ)).mpr hG) hq he
  have hp : 0 < inner ℝ G q := lt_of_le_of_ne hpos (Ne.symm hnon)
  let t := inner ℝ G q/‖G‖^2
  refine ⟨t,div_pos hp (sq_pos_of_pos (norm_pos_iff.mpr hG)),?_⟩
  have hprod : conj G*q = (inner ℝ G q:ℂ) := by
    apply Complex.ext <;> simp [hre,him]
  have hGG : conj G*G = ((‖G‖^2:ℝ):ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
  apply mul_left_cancel₀ ((map_ne_zero (starRingEnd ℂ)).mpr hG : conj G ≠ 0)
  rw [hprod,Complex.real_smul,mul_left_comm,hGG]
  dsimp only [t]
  rw [Complex.ofReal_div,Complex.ofReal_pow,div_mul_cancel₀ _ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hG)))]

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

end

end

end

end

end

end

end

end

end

end OAI
