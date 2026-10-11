import Tengoku.OpenaiMath.OAI.Combinatorics.SparsestCut.GaussianCDF

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.CubePoincare
open MeasureTheory ProbabilityTheory Set
open scoped Topology ContDiff ENNReal BigOperators
variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

def Ψ (x : E) : E := WithLp.toLp 2 (fun i => GaussianCDF.ψ (x i))
def cube : Measure E := (Measure.pi (fun _ : Fin m => GaussianCDF.uniform)).map (WithLp.toLp 2)

def coordinate (i : Fin m) : E →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (EuclideanSpace.equiv (Fin m) ℝ).toContinuousLinearMap

@[simp] lemma coordinate_apply (i : Fin m) (x : E) : coordinate i x = x i := rfl

def derivative (x : E) : E →L[ℝ] E :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => (2*GaussianCDF.φ (x i)) • coordinate i))

@[simp] lemma derivative_apply (x v : E) (i : Fin m) : derivative x v i = 2*GaussianCDF.φ (x i)*v i := rfl

lemma derivative_norm (x : E) : ‖derivative x‖ ≤ 1 := by
  apply (derivative x).opNorm_le_bound (by norm_num)
  intro v
  simp only [one_mul]
  have h : ‖derivative x v‖^2 ≤ ‖v‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    change ‖2*GaussianCDF.φ (x i)*v i‖^2 ≤ ‖v i‖^2
    rw [norm_mul, mul_pow]
    have hi := GaussianCDF.ψ_deriv_bound (x i)
    have hh : ‖2*GaussianCDF.φ (x i)‖^2 ≤ 1 := by
      rw [Real.norm_eq_abs]
      nlinarith [abs_nonneg (2*GaussianCDF.φ (x i))]
    nlinarith [sq_nonneg ‖v i‖]
  nlinarith [norm_nonneg (derivative x v), norm_nonneg v]

end UniformSparsestCut.CubePoincare

end

end OAI
