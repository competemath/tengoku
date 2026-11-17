import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ContinuousLinearMap_orthogonal_iSup_eigenspace_ne_zero_eq_ker.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ContinuousLinearMap_orthogonal_iSup_eigenspace_ne_zero_eq_ker

set_option autoImplicit false

open Module.End

namespace ContinuousLinearMap
export _root_.ContinuousLinearMap (apply comp eq_zero_of_forall_hasEigenvalue_eq_zero finite_dimensional_eigenspace coe_coe restrict adjoint_comp adjoint comp_apply ext coe_comp' adjoint_inner_left inl inr)
open _root_.ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

def highPart (T : E →L[𝕜] E) (r : ℝ) : Submodule 𝕜 E :=
  ⨆ (μ : 𝕜) (_ : r ≤ ‖μ‖), eigenspace (T : Module.End 𝕜 E) μ

theorem apply_mem_iSup_eigenspace_ne_zero {T : E →L[𝕜] E} {u : E}
    (hu : u ∈ ⨆ (μ : 𝕜) (_ : μ ≠ 0), eigenspace (T : Module.End 𝕜 E) μ) :
    T u ∈ ⨆ (μ : 𝕜) (_ : μ ≠ 0), eigenspace (T : Module.End 𝕜 E) μ := by
  refine Submodule.iSup_induction _
    (motive := fun u => T u ∈ ⨆ (μ : 𝕜) (_ : μ ≠ 0), eigenspace (T : Module.End 𝕜 E) μ) hu
    (fun μ x hx => ?_) (by simp) (fun x y hx hy => ?_)
  · by_cases hμ : μ = 0
    · simp [hμ] at hx; simp [hx]
    · rw [iSup_pos hμ, mem_eigenspace_iff] at hx
      have hx' : T x = μ • x := hx
      rw [hx']
      refine Submodule.smul_mem _ μ (Submodule.mem_iSup_of_mem μ ?_)
      rw [iSup_pos hμ, mem_eigenspace_iff]
      show T x = μ • x
      exact hx'
  · rw [map_add]; exact Submodule.add_mem _ hx hy

theorem orthogonal_iSup_eigenspace_ne_zero_eq_ker {T : E →L[𝕜] E}
    (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) :
    (⨆ (μ : 𝕜) (_ : μ ≠ 0), eigenspace (T : Module.End 𝕜 E) μ)ᗮ = LinearMap.ker (T : E →ₗ[𝕜] E) := by
  set K : Submodule 𝕜 E := ⨆ (μ : 𝕜) (_ : μ ≠ 0), eigenspace (T : Module.End 𝕜 E) μ with hK
  apply le_antisymm
  · intro v hv
    have hinv : ∀ w ∈ Kᗮ, T w ∈ Kᗮ := by
      intro w hw
      rw [Submodule.mem_orthogonal] at hw ⊢
      intro u hu
      have e : inner 𝕜 u (T w) = inner 𝕜 ((T : E →ₗ[𝕜] E) u) w := (hT' u w).symm
      rw [e]
      exact hw _ (apply_mem_iSup_eigenspace_ne_zero hu)
    let S : ↥Kᗮ →L[𝕜] ↥Kᗮ := T.restrict hinv
    have hS_compact : IsCompactOperator S := hT.restrict' hinv
    have hS_symm : (S : ↥Kᗮ →ₗ[𝕜] ↥Kᗮ).IsSymmetric := hT'.restrict_invariant hinv
    have hS0 : S = 0 := by
      rw [← eq_zero_of_forall_hasEigenvalue_eq_zero hS_compact hS_symm]
      intro μ hμ
      by_contra hμ0
      rw [hasEigenvalue_iff] at hμ
      apply hμ
      rw [eq_bot_iff]
      intro w hw
      rw [mem_eigenspace_iff] at hw
      have hw' : ((S w : Kᗮ) : E) = ((μ • w : Kᗮ) : E) := congrArg Subtype.val hw
      have hwE : (w : E) ∈ eigenspace (T : Module.End 𝕜 E) μ := by
        rw [mem_eigenspace_iff]
        exact hw'
      have hwK : (w : E) ∈ K := by
        refine Submodule.mem_iSup_of_mem μ ?_
        rw [iSup_pos hμ0]; exact hwE
      have hw0 : (w : E) ∈ K ⊓ Kᗮ := ⟨hwK, w.2⟩
      rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hw0
      rw [Submodule.mem_bot]
      exact Subtype.ext hw0
    have h1 : ((S ⟨v, hv⟩ : Kᗮ) : E) = 0 := by rw [hS0]; rfl
    exact h1
  ·
    intro v hv
    have hv0 : v ∈ eigenspace (T : Module.End 𝕜 E) 0 := by
      rw [mem_eigenspace_iff, zero_smul]; exact hv
    rw [Submodule.mem_orthogonal]
    intro u hu
    refine Submodule.iSup_induction _ (motive := fun u => inner 𝕜 u v = 0) hu
      (fun μ x hx => ?_) (by simp) (fun x y hx hy => ?_)
    · by_cases hμ : μ = 0
      · simp [hμ] at hx; simp [hx]
      · rw [iSup_pos hμ] at hx
        exact hT'.orthogonalFamily_eigenspaces hμ ⟨x, hx⟩ ⟨v, hv0⟩
    · rw [inner_add_left, hx, hy, add_zero]

end ContinuousLinearMap

open Module.End in
theorem solution {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] {T : E →L[𝕜] E}
    (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) :
    (⨆ (μ : 𝕜) (_ : μ ≠ 0), eigenspace (T : Module.End 𝕜 E) μ)ᗮ = LinearMap.ker (T : E →ₗ[𝕜] E) :=
  ContinuousLinearMap.orthogonal_iSup_eigenspace_ne_zero_eq_ker hT hT'
