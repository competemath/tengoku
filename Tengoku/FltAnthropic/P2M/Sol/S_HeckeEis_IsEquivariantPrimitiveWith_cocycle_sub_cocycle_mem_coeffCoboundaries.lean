import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomology
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_EichlerIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeEis_IsEquivariantPrimitiveWith_cocycle_sub_cocycle_mem_coeffCoboundaries.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeEis_IsEquivariantPrimitiveWith_cocycle_sub_cocycle_mem_coeffCoboundaries

set_option autoImplicit false

noncomputable section

namespace HeckeEis
export _root_.HeckeEis (coeffCoboundaries mem_coeffCoboundaries_iff IsEquivariantPrimitiveWith)
open _root_.HeckeEis

open UpperHalfPlane MvPolynomial ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm

theorem SolMain.cob
    {K : Type*} [CommRing K] {Γ : Subgroup SL(2, ℤ)} {V : Type*} [AddCommGroup V] [Module K V]
    {ρ : Representation K Γ V} {F G : ℍ → V}
    (hF : IsEquivariantPrimitiveWith ρ F) (hG : IsEquivariantPrimitiveWith ρ G)
    {v : V} (h : ∀ τ : ℍ, F τ - G τ = v) :
    hF.cocycle - hG.cocycle ∈ coeffCoboundaries ρ := by
  rw [mem_coeffCoboundaries_iff]
  refine ⟨-v, funext fun γ => ?_⟩
  change ρ γ (-v) - -v = (F ((γ : SL(2, ℤ)) • I) - ρ γ (F I)) - (G ((γ : SL(2, ℤ)) • I) - ρ γ (G I))
  rw [map_neg, sub_eq_iff_eq_add.mp (h ((γ : SL(2, ℤ)) • I)), sub_eq_iff_eq_add.mp (h I), map_add]
  abel

end HeckeEis

end

open scoped MatrixGroups ModularForm in
theorem solution
    {K : Type*} [CommRing K] {Γ : Subgroup SL(2, ℤ)} {V : Type*} [AddCommGroup V] [Module K V]
    {ρ : Representation K Γ V} {F G : UpperHalfPlane → V}
    (hF : HeckeEis.IsEquivariantPrimitiveWith ρ F) (hG : HeckeEis.IsEquivariantPrimitiveWith ρ G)
    {v : V} (h : ∀ τ : UpperHalfPlane, F τ - G τ = v) :
    hF.cocycle - hG.cocycle ∈ HeckeEis.coeffCoboundaries ρ :=
  HeckeEis.SolMain.cob hF hG h

