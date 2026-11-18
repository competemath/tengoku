import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import Tengoku.FltAnthropic.P2M.Sol.S_CerednikDrinfeld_Omega_crossRatio_pmoebius_eq_div_symp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CerednikDrinfeld_Omega_crossRatio_pmoebius_eq_div_symp.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

/--
@isnad1 id=other.4h10v.s11.fd69a4881cd1 from=translated src=- shape=d0083f54 vocab=230edb3f
-/
theorem CerednikDrinfeld.Omega.crossRatio_pmoebius_eq_div_symp
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    (g₁ g₂ g₃ g₄ : GL (Fin 2) K₀) {w₁ w₂ w₃ w₄ : K}
    (hw₁ : w₁ ∈ upperHalfPlane K₀ K) (hw₂ : w₂ ∈ upperHalfPlane K₀ K)
    (hw₃ : w₃ ∈ upperHalfPlane K₀ K) (hw₄ : w₄ ∈ upperHalfPlane K₀ K) :
    let P : GL (Fin 2) K₀ → K → Fin 2 → K := fun g w =>
      ![algebraMap K₀ K (g 0 0) * w + algebraMap K₀ K (g 0 1), algebraMap K₀ K (g 1 0) * w + algebraMap K₀ K (g 1 1)]
    crossRatio (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₁) w₁) (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₂) w₂)
        (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₃) w₃) (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₄) w₄) =
      ((P g₁ w₁ 0 * P g₃ w₃ 1 - P g₁ w₁ 1 * P g₃ w₃ 0) * (P g₂ w₂ 0 * P g₄ w₄ 1 - P g₂ w₂ 1 * P g₄ w₄ 0)) /
      ((P g₁ w₁ 0 * P g₄ w₄ 1 - P g₁ w₁ 1 * P g₄ w₄ 0) * (P g₂ w₂ 0 * P g₃ w₃ 1 - P g₂ w₂ 1 * P g₃ w₃ 0)) := by exact @_root_.P2MW.S_CerednikDrinfeld_Omega_crossRatio_pmoebius_eq_div_symp.solution K₀ _ K _ _ _ g₁ g₂ g₃ g₄ w₁ w₂ w₃ w₄ hw₁ hw₂ hw₃ hw₄
