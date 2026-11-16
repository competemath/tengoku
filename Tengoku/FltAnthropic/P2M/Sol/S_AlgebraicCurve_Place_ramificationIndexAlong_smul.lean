import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_Correspondence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_Place_ramificationIndexAlong_smul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_Place_ramificationIndexAlong_smul

noncomputable section

open AlgebraicCurve

namespace FibreSolG

section Generic

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

variable (α β : F →ₐ[K] F') (hα : α.toRingHom.IsIntegral) (hβ : β.toRingHom.IsIntegral)
  (σ : F' ≃ₐ[K] F') (τ : F ≃ₐ[K] F) (h : ∀ x, α (τ x) = σ (β x))
include h

theorem sq_symm (x : F) : σ.symm (α x) = β (τ.symm x) := by
  apply σ.injective
  rw [AlgEquiv.apply_symm_apply, ← h, AlgEquiv.apply_symm_apply]

theorem ramificationIndexAlong_smul (W : Place K F') :
    (σ • W).ramificationIndexAlong α = W.ramificationIndexAlong β := by
  show sInf {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ (σ • W).ord (α f) = n}
    = sInf {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ W.ord (β f) = n}
  congr 1
  ext n
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨f, hf, hn⟩
    refine ⟨τ.symm f, by simpa using hf, ?_⟩
    rw [← hn, ← sq_symm α β σ τ h f, ← Place.ord_smul σ W (σ.symm (α f)), AlgEquiv.apply_symm_apply]
  · rintro ⟨g, hg, hn⟩
    refine ⟨τ g, by simpa using hg, ?_⟩
    rw [← hn, h g, Place.ord_smul]

end Generic

end FibreSolG

end

open AlgebraicCurve in
theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] (α β : F →ₐ[K] F') (σ : F' ≃ₐ[K] F') (τ : F ≃ₐ[K] F) (h : ∀ x, α (τ x) = σ (β x)) (W : Place K F') : (σ • W).ramificationIndexAlong α = W.ramificationIndexAlong β :=
  FibreSolG.ramificationIndexAlong_smul α β σ τ h W
