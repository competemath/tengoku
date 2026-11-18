import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsLocalRing_faithfullyFlat_adicCompletion_maximalIdeal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsLocalRing_faithfullyFlat_adicCompletion_maximalIdeal.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
set_option autoImplicit false

/--
@isnad1 id=faithful.0h1v.s6.85028dee5ad7 from=translated src=- shape=d7071ce9 vocab=eca1334a
-/
theorem IsLocalRing.faithfullyFlat_adicCompletion_maximalIdeal
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    Module.FaithfullyFlat R (AdicCompletion (IsLocalRing.maximalIdeal R) R) := by exact @_root_.P2MW.S_IsLocalRing_faithfullyFlat_adicCompletion_maximalIdeal.solution R _ _ _
