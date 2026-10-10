import Tengoku.OpenaiMath.OAI.Analysis.TracialSplitting.StateExtension

namespace OAI

universe uA uB uE uF uH uK uι

section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

noncomputable section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

noncomputable section

open scoped TensorProduct InnerProductSpace

open UniformSpace.Completion

namespace UnitalTomsWinter

variable {H : Type uH} {K : Type uK} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

abbrev SpatialHilbert (H : Type uH) (K : Type uK) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] :=
  UniformSpace.Completion (H ⊗[ℂ] K)

def spatialTensorOp (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    SpatialHilbert H K →L[ℂ] SpatialHilbert H K :=
  (TensorProduct.mapL S T).completion

@[simp] lemma spatialTensorOp_coe (S : H →L[ℂ] H) (T : K →L[ℂ] K) (x : H ⊗[ℂ] K) :
    spatialTensorOp S T x = (TensorProduct.mapL S T x : SpatialHilbert H K) := by
  exact (TensorProduct.mapL S T).completion_apply_coe x

private lemma completion_opNorm_le {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (f : E →L[ℂ] F) : ‖f.completion‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
  intro z
  induction z using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_le <;> fun_prop
  | ih z => simpa using f.le_opNorm z

lemma spatialTensorOp_norm_le (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    ‖spatialTensorOp S T‖ ≤ ‖S‖ * ‖T‖ :=
  (completion_opNorm_le (TensorProduct.mapL S T)).trans (TensorProduct.norm_mapL_le S T)

variable [CompleteSpace H] [CompleteSpace K]

end UnitalTomsWinter

noncomputable section

namespace Pureness

open UnitalTomsWinter

open scoped TensorProduct InnerProductSpace

variable {A : Type uA} {B : Type uB} {H : Type uH} {K : Type uK} [CStarAlgebra A] [CStarAlgebra B]

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (β : B →⋆ₐ[ℂ] (K →L[ℂ] K))

end Pureness

noncomputable section

namespace Pureness

open UnitalTomsWinter

open scoped TensorProduct InnerProductSpace

variable {A : Type uA} {B : Type uB} {H : Type uH} {K : Type uK} [CStarAlgebra A] [CStarAlgebra B]

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (β : B →⋆ₐ[ℂ] (K →L[ℂ] K))

end Pureness

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
