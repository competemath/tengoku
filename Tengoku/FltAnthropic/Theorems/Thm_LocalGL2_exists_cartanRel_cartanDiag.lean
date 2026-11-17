import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_LocalLanglands_CartanDecomposition
import Tengoku.FltAnthropic.P2M.Sol.S_LocalGL2_exists_cartanRel_cartanDiag

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LocalGL2_exists_cartanRel_cartanDiag.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open Matrix LocalGL2
theorem LocalGL2.exists_cartanRel_cartanDiag
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ)
    (g : Matrix (Fin 2) (Fin 2) R) (hg : g.det ≠ 0) :
    ∃ a b : ℕ, a ≤ b ∧ CartanRel g (cartanDiag ϖ a b) := by exact @_root_.P2MW.S_LocalGL2_exists_cartanRel_cartanDiag.solution R _ _ _ ϖ hϖ g hg
