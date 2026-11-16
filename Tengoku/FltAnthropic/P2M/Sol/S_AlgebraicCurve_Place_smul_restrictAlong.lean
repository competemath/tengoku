import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_Correspondence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_Place_smul_restrictAlong.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_Place_smul_restrictAlong

noncomputable section

open AlgebraicCurve

namespace FibreSolG

section Generic

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem mem_restrictAlong_iff (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') (f : F) :
    f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w.toValuationSubring := Iff.rfl

theorem mem_smul_iff (σ : F' ≃ₐ[K] F') (w : Place K F') (x : F') :
    x ∈ (σ • w).toValuationSubring ↔ σ.symm x ∈ w.toValuationSubring := by
  rw [Place.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

variable (α β : F →ₐ[K] F') (hα : α.toRingHom.IsIntegral) (hβ : β.toRingHom.IsIntegral)
  (σ : F' ≃ₐ[K] F') (τ : F ≃ₐ[K] F) (h : ∀ x, α (τ x) = σ (β x))
include h

theorem sq_symm (x : F) : σ.symm (α x) = β (τ.symm x) := by
  apply σ.injective
  rw [AlgEquiv.apply_symm_apply, ← h, AlgEquiv.apply_symm_apply]

theorem smul_restrictAlong (W : Place K F') :
    (σ • W).restrictAlong α hα = τ • (W.restrictAlong β hβ) := by
  ext f
  rw [mem_restrictAlong_iff, mem_smul_iff, sq_symm α β σ τ h,
    show f ∈ (τ • W.restrictAlong β hβ).toValuationSubring ↔ τ.symm f ∈ (W.restrictAlong β hβ).toValuationSubring from by
      rw [Place.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]; rfl,
    mem_restrictAlong_iff]

end Generic

end FibreSolG

end

open AlgebraicCurve in
theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] (α β : F →ₐ[K] F') (hα : α.toRingHom.IsIntegral) (hβ : β.toRingHom.IsIntegral) (σ : F' ≃ₐ[K] F') (τ : F ≃ₐ[K] F) (h : ∀ x, α (τ x) = σ (β x)) (W : Place K F') : (σ • W).restrictAlong α hα = τ • W.restrictAlong β hβ :=
  FibreSolG.smul_restrictAlong α β hα hβ σ τ h W
