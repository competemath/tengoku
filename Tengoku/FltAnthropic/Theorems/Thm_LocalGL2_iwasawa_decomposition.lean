import Tengoku.FltAnthropic.Definitions.Def_LocalLanglands_HeckeCosetLocal
import Tengoku.FltAnthropic.P2M.Sol.S_LocalGL2_iwasawa_decomposition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LocalGL2_iwasawa_decomposition.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem LocalGL2.iwasawa_decomposition (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] (g : GL (Fin 2) K) :
    ∃ b k : GL (Fin 2) K, k ∈ LocalGL2.integralSubgroup R K ∧
      (b : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ g = b * k := by exact @_root_.P2MW.S_LocalGL2_iwasawa_decomposition.solution R _ _ _ K _ _ _ g
