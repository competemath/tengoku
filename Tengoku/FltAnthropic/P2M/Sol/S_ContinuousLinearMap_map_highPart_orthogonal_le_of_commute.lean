import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ContinuousLinearMap_map_highPart_orthogonal_le_of_commute.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ContinuousLinearMap_map_highPart_orthogonal_le_of_commute

set_option autoImplicit false

open Module.End

namespace ContinuousLinearMap
export _root_.ContinuousLinearMap (apply comp eq_zero_of_forall_hasEigenvalue_eq_zero finite_dimensional_eigenspace coe_coe restrict adjoint_comp adjoint comp_apply ext coe_comp' adjoint_inner_left inl inr)
open _root_.ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

def highPart (T : E →L[𝕜] E) (r : ℝ) : Submodule 𝕜 E :=
  ⨆ (μ : 𝕜) (_ : r ≤ ‖μ‖), eigenspace (T : Module.End 𝕜 E) μ

theorem map_highPart_le_of_commute_pf {T S : E →L[𝕜] E}
    (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) (hST : S.comp T = T.comp S) (r : ℝ) :
    Submodule.map (S : E →ₗ[𝕜] E) (highPart T r) ≤ highPart T r := by
  unfold highPart
  rw [Submodule.map_iSup]
  refine iSup_mono fun μ => ?_
  rw [Submodule.map_iSup]
  refine iSup_mono fun hμ => ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, mem_eigenspace_iff] at hx
  rw [mem_eigenspace_iff]
  have h := congrArg (fun A : E →L[𝕜] E => A x) hST
  simp only [coe_comp, Function.comp_apply] at h
  show (T : E →ₗ[𝕜] E) (S x) = μ • S x
  have : T (S x) = S (T x) := h.symm
  rw [ContinuousLinearMap.coe_coe, this, show (T x) = μ • x from hx, map_smul]

theorem adjoint_comp_eq_of_isSymmetric {T S : E →L[𝕜] E}
    (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) (hST : S.comp T = T.comp S) :
    (adjoint S).comp T = T.comp (adjoint S) := by
  have hT : adjoint T = T := hT'.isSelfAdjoint.adjoint_eq
  have := congrArg adjoint hST
  rw [adjoint_comp, adjoint_comp, hT] at this
  exact this.symm

theorem map_highPart_orthogonal_le_of_commute_pf {T S : E →L[𝕜] E}
    (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) (hST : S.comp T = T.comp S) (r : ℝ) :
    Submodule.map (S : E →ₗ[𝕜] E) (highPart T r)ᗮ ≤ (highPart T r)ᗮ := by
  rintro _ ⟨y, hy, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_orthogonal] at hy
  rw [Submodule.mem_orthogonal]
  intro x hx
  have hx' : adjoint S x ∈ highPart T r :=
    map_highPart_le_of_commute_pf hT' (adjoint_comp_eq_of_isSymmetric hT' hST) r ⟨x, hx, rfl⟩
  rw [ContinuousLinearMap.coe_coe, ← adjoint_inner_left]
  exact hy _ hx'

end ContinuousLinearMap

open Module.End in
theorem solution {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] {T S : E →L[𝕜] E}
    (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) (hST : S.comp T = T.comp S) (r : ℝ) :
    Submodule.map (S : E →ₗ[𝕜] E) (⨆ (μ : 𝕜) (_ : r ≤ ‖μ‖), Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ ≤ (⨆ (μ : 𝕜) (_ : r ≤ ‖μ‖), Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ :=
  ContinuousLinearMap.map_highPart_orthogonal_le_of_commute_pf hT' hST r
