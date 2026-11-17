import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_CerednikDrinfeld_Onr_faithfullyFlat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CerednikDrinfeld_Onr_faithfullyFlat.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem CerednikDrinfeld.Onr.faithfullyFlat
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪) (π : 𝒪) (hπ : Irreducible π)
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [Algebra 𝒪 Onr]
    (hinj : Function.Injective (algebraMap 𝒪 Onr)) (hproper : Ideal.span {algebraMap 𝒪 Onr π} ≠ ⊤) :
    Module.FaithfullyFlat 𝒪 Onr := by exact @_root_.P2MW.S_CerednikDrinfeld_Onr_faithfullyFlat.solution 𝒪 _ _ hdvr π hπ Onr _ _ _ hinj hproper
