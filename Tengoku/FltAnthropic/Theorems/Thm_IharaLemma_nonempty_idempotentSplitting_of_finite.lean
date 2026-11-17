import Tengoku.FltAnthropic.Definitions.Def_IharaLemma_IdempotentSplitting
import Tengoku.Seed.RingTheory.AdicCompletion.Basic
import Tengoku.Seed.RingTheory.Finiteness.Defs
import Tengoku.Seed.RingTheory.Noetherian.Defs
import Tengoku.FltAnthropic.P2M.Sol.S_IharaLemma_nonempty_idempotentSplitting_of_finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IharaLemma_nonempty_idempotentSplitting_of_finite.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem IharaLemma.nonempty_idempotentSplitting_of_finite (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    [IsNoetherianRing 𝒪] (B : Type) [CommRing B] [Algebra 𝒪 B] [Module.Finite 𝒪 B]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] :
    Nonempty (IharaLemma.IdempotentSplitting B) := by exact @_root_.P2MW.S_IharaLemma_nonempty_idempotentSplitting_of_finite.solution 𝒪 _ _ _ B _ _ _ _
