import Tengoku.FltAnthropic.Definitions.Def_IharaLemma_IdempotentSplitting
import Tengoku.Seed.Algebra.Module.LocalizedModule.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_IharaLemma_IdempotentSplitting_isLocalizedModule_toCorner_maximalIdeal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IharaLemma_IdempotentSplitting_isLocalizedModule_toCorner_maximalIdeal.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=islocali.0h4v.s7.b8aa98428ca1 from=translated src=- shape=6ae5c7fb vocab=ea78c178
-/
theorem IharaLemma.IdempotentSplitting.isLocalizedModule_toCorner_maximalIdeal {B : Type}
    [CommRing B] (S : IharaLemma.IdempotentSplitting B) (i : Fin S.n) {M : Type}
    [AddCommGroup M] [Module B M] :
    IsLocalizedModule (S.𝔪 i).primeCompl (IharaLemma.toCorner (M := M) (S.e i)) := by exact @_root_.P2MW.S_IharaLemma_IdempotentSplitting_isLocalizedModule_toCorner_maximalIdeal.solution B _ S i M _ _
