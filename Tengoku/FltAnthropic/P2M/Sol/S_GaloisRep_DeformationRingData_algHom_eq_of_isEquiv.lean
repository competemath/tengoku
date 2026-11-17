import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_DeformationRingData

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRep_DeformationRingData_algHom_eq_of_isEquiv.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRep_DeformationRingData_algHom_eq_of_isEquiv

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟)
    (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [Algebra 𝒪 A] [IsLocalHom (algebraMap 𝒪 A)]
    (hA : Function.Surjective (IsLocalRing.residue A ∘ algebraMap 𝒪 A))
    (ρA : GaloisRepAdic A) (hρA : 𝒟 ρA)
    (hres : ρA.residual.IsEquiv (ρbar.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 A))))
    (φ₁ φ₂ : D.R →ₐ[𝒪] A) (h₁ : IsLocalHom (φ₁ : D.R →+* A)) (h₂ : IsLocalHom (φ₂ : D.R →+* A))
    (e₁ : (D.ρ.baseChangeAlong (φ₁ : D.R →+* A) h₁).IsEquiv ρA)
    (e₂ : (D.ρ.baseChangeAlong (φ₂ : D.R →+* A) h₂).IsEquiv ρA) :
    φ₁ = φ₂ :=
  (D.universal A hA ρA hρA hres).unique ⟨h₁, e₁⟩ ⟨h₂, e₂⟩

-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
