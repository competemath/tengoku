import Tengoku.FltAnthropic.Definitions.Def_LocalLanglands_HeckeCosetLocal
import Tengoku.FltAnthropic.P2M.Sol.S_LocalGL2_finite_image_integralSubgroup_mul_singleton

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LocalGL2_finite_image_integralSubgroup_mul_singleton.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped Pointwise
open LocalGL2
theorem LocalGL2.finite_image_integralSubgroup_mul_singleton
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})] (g : GL (Fin 2) K) :
    (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K)) * {g}) :
      Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite := by exact @_root_.P2MW.S_LocalGL2_finite_image_integralSubgroup_mul_singleton.solution R _ _ _ K _ _ _ ϖ hϖ _ g
