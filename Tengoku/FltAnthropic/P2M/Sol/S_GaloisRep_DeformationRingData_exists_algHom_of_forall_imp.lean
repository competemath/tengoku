import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_DeformationRingData

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRep_DeformationRingData_exists_algHom_of_forall_imp.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRep_DeformationRingData_exists_algHom_of_forall_imp

/--
@isnad1 id=ex.0h7v.s10.9e13c7dd6834 from=translated src=- shape=01db0664 vocab=00eaa24c
-/
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A],
      GaloisRepAdic A → Prop}
    (h : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
      (ρ : GaloisRepAdic A), 𝒟₀ ρ → 𝒟' ρ)
    (D₀ : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟₀)
    (D' : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟') :
    ∃ θ : D'.R →ₐ[𝒪] D₀.R, ∃ hθ : IsLocalHom (θ : D'.R →+* D₀.R),
      (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ := by
  obtain ⟨θ, hθ, -⟩ :=
    D'.universal D₀.R D₀.residue_surjective D₀.ρ (h D₀.ρ D₀.isOfType) D₀.residual_isEquiv
  exact ⟨θ, hθ⟩

-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
