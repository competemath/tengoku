import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import Tengoku.FltAnthropic.P2M.Sol.S_CerednikDrinfeld_Omega_crossRatio_pmoebius_pmoebius_sub_one_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CerednikDrinfeld_Omega_crossRatio_pmoebius_pmoebius_sub_one_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

/--
@isnad1 id=eq.4h7v.s12.8297e1dea71a from=translated src=- shape=0add43aa vocab=42f9bbe2
-/
theorem CerednikDrinfeld.Omega.crossRatio_pmoebius_pmoebius_sub_one_eq
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    (g : GL (Fin 2) K₀) {a b : K} (z z₀ : K)
    (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K)
    (hΦ : (z * (algebraMap K₀ K (g 1 0) * b + algebraMap K₀ K (g 1 1)) - (algebraMap K₀ K (g 0 0) * b + algebraMap K₀ K (g 0 1))) ≠ 0)
    (hΦ₀ : (z₀ * (algebraMap K₀ K (g 1 0) * a + algebraMap K₀ K (g 1 1)) - (algebraMap K₀ K (g 0 0) * a + algebraMap K₀ K (g 0 1))) ≠ 0) :
    crossRatio z z₀ (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) a) (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) b) - 1 =
      (z - z₀) * (a - b) * algebraMap K₀ K (Matrix.det (g : Matrix (Fin 2) (Fin 2) K₀)) /
        ((z * (algebraMap K₀ K (g 1 0) * b + algebraMap K₀ K (g 1 1)) - (algebraMap K₀ K (g 0 0) * b + algebraMap K₀ K (g 0 1))) *
          (z₀ * (algebraMap K₀ K (g 1 0) * a + algebraMap K₀ K (g 1 1)) - (algebraMap K₀ K (g 0 0) * a + algebraMap K₀ K (g 0 1)))) := by exact @_root_.P2MW.S_CerednikDrinfeld_Omega_crossRatio_pmoebius_pmoebius_sub_one_eq.solution K₀ _ K _ _ _ g a b z z₀ ha hb hΦ hΦ₀
