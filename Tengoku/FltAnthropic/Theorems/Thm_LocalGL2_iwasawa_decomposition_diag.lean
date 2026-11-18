import Tengoku.FltAnthropic.Definitions.Def_LocalLanglands_HeckeCosetLocal
import Tengoku.FltAnthropic.P2M.Sol.S_LocalGL2_iwasawa_decomposition_diag

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LocalGL2_iwasawa_decomposition_diag.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=ex.0h3v.s10.cf85575fba6c from=translated src=- shape=a61e8e80 vocab=fcb0cceb
-/
theorem LocalGL2.iwasawa_decomposition_diag (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] (g : GL (Fin 2) K) :
    ∃ (z : K) (a₁ a₂ : Kˣ) (k : GL (Fin 2) K), k ∈ LocalGL2.integralSubgroup R K ∧
      (g : Matrix (Fin 2) (Fin 2) K) = !![1, z; 0, 1] * !![(a₁ : K), 0; 0, (a₂ : K)] * k := by exact @_root_.P2MW.S_LocalGL2_iwasawa_decomposition_diag.solution R _ _ _ K _ _ _ g
