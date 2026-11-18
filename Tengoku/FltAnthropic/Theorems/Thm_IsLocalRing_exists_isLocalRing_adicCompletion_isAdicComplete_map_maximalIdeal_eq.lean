import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsLocalRing_exists_isLocalRing_adicCompletion_isAdicComplete_map_maximalIdeal_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsLocalRing_exists_isLocalRing_adicCompletion_isAdicComplete_map_maximalIdeal_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open IsLocalRing in

theorem IsLocalRing.exists_isLocalRing_adicCompletion_isAdicComplete_map_maximalIdeal_eq
    (O : Type u) [CommRing O] [IsNoetherianRing O] [IsLocalRing O] :
    ∃ (_ : IsLocalRing (AdicCompletion (maximalIdeal O) O))
      (_ : IsLocalHom (algebraMap O (AdicCompletion (maximalIdeal O) O))),
      IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal O) O)) (AdicCompletion (maximalIdeal O) O) ∧
      Ideal.map (algebraMap O (AdicCompletion (maximalIdeal O) O)) (maximalIdeal O) =
        maximalIdeal (AdicCompletion (maximalIdeal O) O) ∧
      ∀ x : AdicCompletion (maximalIdeal O) O, ∃ o : O,
        x - algebraMap O (AdicCompletion (maximalIdeal O) O) o ∈ maximalIdeal (AdicCompletion (maximalIdeal O) O) := by exact @_root_.P2MW.S_IsLocalRing_exists_isLocalRing_adicCompletion_isAdicComplete_map_maximalIdeal_eq.solution O _ _ _
