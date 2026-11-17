import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_IharaLemma_IdempotentSplitting
import Tengoku.FltAnthropic.P2M.Sol.S_IharaLemma_IdempotentSplitting_mem_maxIdeal_iff_apply_toCornerRing_eq_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IharaLemma_IdempotentSplitting_mem_maxIdeal_iff_apply_toCornerRing_eq_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open IharaLemma

theorem IharaLemma.IdempotentSplitting.mem_maxIdeal_iff_apply_toCornerRing_eq_zero
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
    (Sp : IdempotentSplitting B) (i : Fin Sp.n)
    (π : Sp.CornerRing i →ₐ[𝒪] IsLocalRing.ResidueField 𝒪) (x : B) :
    x ∈ Sp.𝔪 i ↔ π (Sp.toCornerRing i x) = 0 := by exact @_root_.P2MW.S_IharaLemma_IdempotentSplitting_mem_maxIdeal_iff_apply_toCornerRing_eq_zero.solution 𝒪 _ _ B _ _ Sp i π x
