import Tengoku.OpenaiMath.OAI.Analysis.TracialSplitting.TensorExtension

namespace OAI

universe uA uB uE uH uN

section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

namespace NuclearTrace

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (f : A →ₚ[ℂ] ℂ) (ht : ∀ a b, f (a*b) = f (b*a))

include ht in
lemma norm_preGNS_star (a : A) : ‖f.toPreGNS (star a)‖ = ‖f.toPreGNS a‖ := by
  rw [PositiveLinearMap.preGNS_norm_def, PositiveLinearMap.preGNS_norm_def]
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS,star_star]
  rw [ht]

include ht in
lemma right_preGNS_norm (a : A) (x : f.PreGNS) :
    ‖f.toPreGNS (f.ofPreGNS x*a)‖ ≤ ‖a‖*‖x‖ := by
  rw [← norm_preGNS_star f ht]
  simp only [star_mul]
  have h := (f.leftMulMapPreGNS (star a)).le_opNorm
    (f.toPreGNS (star (f.ofPreGNS x)))
  have hb : ‖f.leftMulMapPreGNS (star a)‖ ≤ ‖star a‖ :=
    LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
  apply h.trans
  rw [norm_star] at hb
  rw [norm_preGNS_star f ht, PositiveLinearMap.toPreGNS_ofPreGNS]
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

def rightPreGNS (a : A) : f.PreGNS →L[ℂ] f.PreGNS :=
  (f.toPreGNS.toLinearMap.comp ((LinearMap.mulRight ℂ a).comp f.ofPreGNS.toLinearMap)).mkContinuous
    ‖a‖ (right_preGNS_norm f ht a)

@[simp] lemma rightPreGNS_apply (a : A) (x : f.PreGNS) :
    rightPreGNS f ht a x = f.toPreGNS (f.ofPreGNS x*a) := rfl

def rightGNSMap (a : A) : f.GNS →L[ℂ] f.GNS := (rightPreGNS f ht a).completion

@[simp] lemma rightGNSMap_coe (a : A) (x : f.PreGNS) :
    rightGNSMap f ht a (x : f.GNS) = (rightPreGNS f ht a x : f.GNS) :=
  ContinuousLinearMap.completion_apply_coe (rightPreGNS f ht a) x

lemma rightGNSMap_mul (a b : A) :
    rightGNSMap f ht (a*b) = rightGNSMap f ht b * rightGNSMap f ht a := by
  apply ContinuousLinearMap.ext
  intro x
  induction x using induction_on with
  | hp => exact isClosed_eq (map_continuous _) (map_continuous _)
  | ih x => simp [rightPreGNS_apply,mul_assoc]

lemma rightGNSMap_star (a : A) : rightGNSMap f ht (star a) = star (rightGNSMap f ht a) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  induction x, y using induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
    simp only [rightGNSMap_coe,UniformSpace.Completion.inner_coe,
      PositiveLinearMap.preGNS_inner_def,rightPreGNS_apply,
      PositiveLinearMap.ofPreGNS_toPreGNS,star_mul,star_star]
    simpa only [mul_assoc] using ht a (star (f.ofPreGNS x) * f.ofPreGNS y)

def rightGNS : Aᵐᵒᵖ →⋆ₐ[ℂ] (f.GNS →L[ℂ] f.GNS) where
  toFun a := rightGNSMap f ht a.unop
  map_one' := by
    ext x
    induction x using induction_on with
    | hp => exact isClosed_eq (map_continuous _) continuous_id
    | ih x => simp
  map_mul' a b := rightGNSMap_mul f ht b.unop a.unop
  map_zero' := by
    ext x
    induction x using induction_on with
    | hp => exact isClosed_eq (map_continuous _) continuous_const
    | ih x => simp [UniformSpace.Completion.coe_zero]
  map_add' a b := by
    ext x
    induction x using induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x => simp [mul_add,map_add,UniformSpace.Completion.coe_add]
  commutes' c := by
    ext x
    induction x using induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x =>
      simp [Algebra.algebraMap_eq_smul_one,UniformSpace.Completion.coe_smul]
  map_star' a := rightGNSMap_star f ht a.unop

@[simp] lemma rightGNS_coe (a : Aᵐᵒᵖ) (x : f.PreGNS) :
    rightGNS f ht a (x : f.GNS) = (f.toPreGNS (f.ofPreGNS x*a.unop) : f.GNS) :=
  rightGNSMap_coe f ht a.unop x

lemma left_right_commute (a : A) (b : Aᵐᵒᵖ) :
    Commute (f.gnsStarAlgHom a) (rightGNS f ht b) := by
  change f.gnsStarAlgHom a * rightGNS f ht b = rightGNS f ht b * f.gnsStarAlgHom a
  ext x
  induction x using induction_on with
  | hp => exact isClosed_eq (map_continuous _) (map_continuous _)
  | ih x =>
    simp [PositiveLinearMap.gnsStarAlgHom,PositiveLinearMap.leftMulMapPreGNS,mul_assoc]

end NuclearTrace

noncomputable section

namespace Pureness

open scoped TensorProduct

variable {A : Type uA} {B : Type uB} {N : Type uN} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra N]

end Pureness

namespace NuclearTrace

open scoped TensorProduct ComplexOrder InnerProductSpace

section VectorFunctional

variable {E : Type uE} {H : Type uH} [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def vectorFunctional (π : E →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) : E →ₚ[ℂ] ℂ where
  toFun x := ⟪ξ, π x ξ⟫_ℂ
  map_add' x y := by simp
  map_smul' c x := by simp
  monotone' := by
    intro a b hab
    have h := (ContinuousLinearMap.nonneg_iff_isPositive.mp
      (map_nonneg π (sub_nonneg.mpr hab))).inner_nonneg_right ξ
    simpa only [map_sub,sub_apply,inner_sub_right,sub_nonneg] using h

@[simp] lemma vectorFunctional_apply (π : E →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (a : E) :
    vectorFunctional π ξ a = ⟪ξ, π a ξ⟫_ℂ := rfl

end VectorFunctional

section DiagonalState

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (f : A →ₚ[ℂ] ℂ) (ht : ∀ a b, f (a*b) = f (b*a))

end DiagonalState

end NuclearTrace

end

end

end

end

end OAI
