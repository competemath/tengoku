import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_CerednikDrinfeld_Onr_isDiscreteValuationRing_equalizer_and_irreducible

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CerednikDrinfeld_Onr_isDiscreteValuationRing_equalizer_and_irreducible.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
theorem CerednikDrinfeld.Onr.isDiscreteValuationRing_equalizer_and_irreducible
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [Algebra 𝒪 Onr]
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hπ0 : algebraMap 𝒪 Onr π ≠ 0)
    (F : Onr ≃ₐ[𝒪] Onr) :
    IsDiscreteValuationRing ↥(AlgHom.equalizer (F : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ∧ Irreducible (algebraMap 𝒪 ↥(AlgHom.equalizer (F : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) := by exact @_root_.P2MW.S_CerednikDrinfeld_Onr_isDiscreteValuationRing_equalizer_and_irreducible.solution 𝒪 _ π Onr _ _ _ hOnr_complete hOnr_max hπ0 F
