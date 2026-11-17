import Tengoku.FltAnthropic.Definitions.Def_IharaLemma_IdempotentSplitting
import Tengoku.Seed.RingTheory.Finiteness.Cardinality
import Tengoku.FltAnthropic.P2M.Sol.S_IharaLemma_IdempotentSplitting_finite_cornerRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IharaLemma_IdempotentSplitting_finite_cornerRing.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=finite.0h4v.s6.68214a3eb9b0 from=translated src=- shape=6344f2bf vocab=650c140c
-/
theorem IharaLemma.IdempotentSplitting.finite_cornerRing {𝒪 : Type} [CommRing 𝒪] {B : Type}
    [CommRing B] [Algebra 𝒪 B] (S : IharaLemma.IdempotentSplitting B) (i : Fin S.n)
    [Module.Finite 𝒪 B] : Module.Finite 𝒪 (S.CornerRing i) := by exact @_root_.P2MW.S_IharaLemma_IdempotentSplitting_finite_cornerRing.solution 𝒪 _ B _ _ S i _
