import Tengoku.OpenaiMath.OAI.Combinatorics.SparsestCut.CubePoincare

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.CubeGeometry
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal
noncomputable section
variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "μ" => CubePoincare.cube (m := m)

lemma uniform_mem : ∀ᵐ t ∂GaussianCDF.uniform, t∈Ioo (-1:ℝ) 1 := by
  have h : GaussianCDF.uniform ≪ volume.restrict (Ioo (-1:ℝ) 1) :=
    (Measure.AbsolutelyContinuous.refl _).smul_left _
  exact h.ae_le (ae_restrict_mem measurableSet_Ioo)

lemma uniform_pow (k : ℕ) : (∫ t, t^k ∂GaussianCDF.uniform)=
    (1-(-1:ℝ)^(k+1))/(2*(k+1)) := by
  rw [GaussianCDF.uniform,integral_smul_measure,restrict_Ioo_eq_restrict_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ)≤1),integral_pow]
  simp only [ENNReal.toReal_inv,ENNReal.toReal_ofNat,smul_eq_mul,one_pow]
  field_simp

end
end UniformSparsestCut.CubeGeometry

end

end OAI
