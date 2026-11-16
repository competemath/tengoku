import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_GluedPic0

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_Place_hasValue_smul_iff.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_Place_hasValue_smul_iff

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F]
    (σ : F ≃ₐ[K] F) (v : Place K F) (g : F) (a : K) :
    (σ • v).HasValue (σ g) a ↔ v.HasValue g a := by

  have one : ∀ (τ : F ≃ₐ[K] F) (w : Place K F) (x : F), w.HasValue x a → (τ • w).HasValue (τ x) a := by
    intro τ w x ⟨hx, hres⟩
    let e := Place.smulRingEquiv τ w.toValuationSubring
    have hmem : τ x ∈ (τ • w).toValuationSubring := (e ⟨x, hx⟩).2
    refine ⟨hmem, ?_⟩
    have hex : (⟨τ x, hmem⟩ : (τ • w).toValuationSubring) = e ⟨x, hx⟩ := Subtype.ext rfl
    have key : (Place.smulResidueAlgEquiv τ w) (residue w.toValuationSubring ⟨x, hx⟩)
        = residue (τ • w).toValuationSubring (e ⟨x, hx⟩) := by
      show IsLocalRing.ResidueField.mapEquiv _ (residue _ _) = residue _ _
      rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
      rfl
    rw [hex, ← key, hres, AlgEquiv.commutes]
  refine ⟨fun h => ?_, one σ v g⟩
  have := one σ⁻¹ (σ • v) (σ g) h
  rwa [inv_smul_smul, show σ⁻¹ (σ g) = g from σ.symm_apply_apply g] at this
