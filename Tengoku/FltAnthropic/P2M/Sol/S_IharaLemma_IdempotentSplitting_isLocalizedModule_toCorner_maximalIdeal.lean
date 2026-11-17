import Tengoku.FltAnthropic.Definitions.Def_IharaLemma_IdempotentSplitting
import Tengoku.Seed.Algebra.Module.LocalizedModule.Basic
import Tengoku.FltAnthropic.Theorems.Thm_IharaLemma_isLocalizedModule_toCorner

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IharaLemma_IdempotentSplitting_isLocalizedModule_toCorner_maximalIdeal.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IharaLemma_IdempotentSplitting_isLocalizedModule_toCorner_maximalIdeal

open IharaLemma

/--
@isnad1 id=islocali.0h4v.s7.b8aa98428ca1 from=translated src=- shape=6ae5c7fb vocab=ea78c178
-/
theorem solution {B : Type} [CommRing B] (S : IdempotentSplitting B) (i : Fin S.n) {M : Type}
    [AddCommGroup M] [Module B M] :
    IsLocalizedModule (S.𝔪 i).primeCompl (toCorner (M := M) (S.e i)) :=
  IharaLemma.isLocalizedModule_toCorner (S.idem i) (S.𝔪 i) (S.notMem i)
    (S.mem_of_isMaximal_of_ne i)
