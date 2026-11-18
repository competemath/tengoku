import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LinearMap_exact_dualMap_of_exact.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LinearMap_exact_dualMap_of_exact

set_option autoImplicit false
set_option maxHeartbeats 1600000

/--
@isnad1 id=exact.1h6v.s10.7ef257390224 from=translated src=- shape=ae012a9d vocab=a72e2d8b
-/
theorem solution {K V₁ V₂ V₃ : Type*} [Field K]
    [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂] [AddCommGroup V₃] [Module K V₃]
    (f : V₁ →ₗ[K] V₂) (g : V₂ →ₗ[K] V₃) (h : Function.Exact f g) :
    Function.Exact g.dualMap f.dualMap := by
  rw [LinearMap.exact_iff] at h ⊢
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, h]
  ext ψ
  simp only [LinearMap.mem_ker, Submodule.mem_dualAnnihilator, LinearMap.mem_range]
  constructor
  · rintro hψ _ ⟨y, rfl⟩
    exact congrArg (fun χ : Module.Dual K V₁ => χ y) hψ
  · intro hψ
    ext y
    exact hψ _ ⟨y, rfl⟩
