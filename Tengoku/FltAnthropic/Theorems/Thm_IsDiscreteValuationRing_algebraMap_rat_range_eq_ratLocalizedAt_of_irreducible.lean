import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Flat
import Tengoku.FltAnthropic.P2M.Sol.S_IsDiscreteValuationRing_algebraMap_rat_range_eq_ratLocalizedAt_of_irreducible

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsDiscreteValuationRing_algebraMap_rat_range_eq_ratLocalizedAt_of_irreducible.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=eq.1h2v.s6.734990b727b2 from=translated src=- shape=62a6738c vocab=d7976cf3
-/
theorem IsDiscreteValuationRing.algebraMap_rat_range_eq_ratLocalizedAt_of_irreducible
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R ℚ] [IsFractionRing R ℚ]
    (p : ℕ) [Fact p.Prime] (hp : Irreducible (p : R)) :
    (algebraMap R ℚ).range = GaloisRep.ratLocalizedAt p := by exact @_root_.P2MW.S_IsDiscreteValuationRing_algebraMap_rat_range_eq_ratLocalizedAt_of_irreducible.solution R _ _ _ _ _ p _ hp
