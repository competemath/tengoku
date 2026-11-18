import Tengoku.Seed.RingTheory.Ideal.GoingUp
import Tengoku.Seed.RingTheory.Jacobson.Ideal
import Tengoku.Seed.RingTheory.LocalRing.MaximalIdeal.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_IsLocalRing_map_maximalIdeal_le_jacobson_bot_of_isIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsLocalRing_map_maximalIdeal_le_jacobson_bot_of_isIntegral.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=le.0h2v.s7.810ccfc0a588 from=translated src=- shape=7521a994 vocab=a097fe8c
-/
theorem IsLocalRing.map_maximalIdeal_le_jacobson_bot_of_isIntegral {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R] [Algebra.IsIntegral R S] :
    (IsLocalRing.maximalIdeal R).map (algebraMap R S) ≤ Ideal.jacobson (⊥ : Ideal S) := by exact @_root_.P2MW.S_IsLocalRing_map_maximalIdeal_le_jacobson_bot_of_isIntegral.solution R S _ _ _ _ _
