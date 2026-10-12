import Tengoku
import Tengoku.OpenaiMath.OAI.Probability.Subsphere.Regression.Spheres

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def act (u : Orthogonal E) (x : E) : E := (u.val : E →L[ℝ] E) x

lemma continuous_act : Continuous (fun z : Orthogonal E × E => act z.1 z.2) := by
  unfold act
  fun_prop

lemma act_mul (u v : Orthogonal E) (x : E) : act (u*v) x = act u (act v x) := rfl

lemma act_one (x : E) : act (1 : Orthogonal E) x = x := rfl

lemma act_norm (u : Orthogonal E) (x : E) : ‖act u x‖ = ‖x‖ := Unitary.norm_map u x

lemma exists_act {x y : E} (h : ‖x‖ = ‖y‖) : ∃ u : Orthogonal E, act u x = y := by
  let e := (ℝ ∙ (x-y))ᗮ.reflection
  refine ⟨Unitary.linearIsometryEquiv.symm e,?_⟩
  change Unitary.linearIsometryEquiv (Unitary.linearIsometryEquiv.symm e) x = y
  rw [MulEquiv.apply_symm_apply]
  exact Submodule.reflection_sub h

variable [MeasurableSpace E] [BorelSpace E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma blockIso_apply (V : Submodule ℝ E) (u : Orthogonal V) (w : Orthogonal Vᗮ) (x : E) :
    blockIso V u w x = (act (E := V) u (V.orthogonalProjectionOnto x) : E) +
      (act (E := Vᗮ) w (Vᗮ.orthogonalProjectionOnto x) : E) := by
  simp only [blockIso,LinearIsometryEquiv.trans_apply,Submodule.orthogonalDecomposition_symm_apply,
    Submodule.orthogonalDecomposition_apply,LinearIsometryEquiv.withLpProdCongr_apply]
  rfl

lemma continuous_blockIso (V : Submodule ℝ E) :
    Continuous (fun z : (Orthogonal V × Orthogonal Vᗮ) × E => blockIso V z.1.1 z.1.2 z.2) := by
  simp only [blockIso_apply]
  exact ((continuous_subtype_val.comp (continuous_act.comp
      ((continuous_fst.comp continuous_fst).prodMk (V.orthogonalProjectionOnto.continuous.comp continuous_snd)))).add
    (continuous_subtype_val.comp (continuous_act.comp
      ((continuous_snd.comp continuous_fst).prodMk (Vᗮ.orthogonalProjectionOnto.continuous.comp continuous_snd)))))

@[simp] lemma blockIso_one (V : Submodule ℝ E) (x : E) : blockIso V 1 1 x = x := by
  rw [blockIso_apply,act_one,act_one]
  exact V.starProjection_add_starProjection_orthogonal x

@[simp] lemma blockIso_on_left (V : Submodule ℝ E) (u : Orthogonal V) (w : Orthogonal Vᗮ) (x : V) :
    blockIso V u w (x : E) = ((act (E := V) u x : V) : E) := by
  rw [blockIso_apply,Vᗮ.orthogonalProjectionOnto_apply_of_mem_orthogonal (by simp)]
  simp [act]

@[simp] lemma blockIso_on_right (V : Submodule ℝ E) (u : Orthogonal V) (w : Orthogonal Vᗮ) (x : Vᗮ) :
    blockIso V u w (x : E) = ((act (E := Vᗮ) w x : Vᗮ) : E) := by
  rw [blockIso_apply,V.orthogonalProjectionOnto_apply_of_mem_orthogonal x.prop]
  simp [act]

lemma blockIso_mul (V : Submodule ℝ E) (u u' : Orthogonal V) (w w' : Orthogonal Vᗮ) (x : E) :
    blockIso V (u*u') (w*w') x = blockIso V u w (blockIso V u' w' x) := by
  rw [blockIso_apply V u' w',map_add,blockIso_on_left,blockIso_on_right]
  rw [blockIso_apply,act_mul,act_mul]

lemma blockIso_comp (V : Submodule ℝ E) (u : Orthogonal V) (w : Orthogonal Vᗮ) :
    blockIso V u w = (blockIso V u 1).trans (blockIso V 1 w) := by
  ext x
  simpa using (blockIso_mul V 1 u w 1 x)

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end SubsphereCurrent.Mixture
end
end
section
noncomputable section
universe u v w
namespace SubsphereCurrent

end SubsphereCurrent
end
end

end OAI
