import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v

open IsLocalRing

theorem IsLocalRing.exists_valuationSubring_isDiscreteValuationRing_dominates
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] (hR : ¬ IsField R)
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K] :
    ∃ V : ValuationSubring K, IsDiscreteValuationRing ↥V ∧
      (∀ r : R, algebraMap R K r ∈ V) ∧
      (∀ r : R, r ∈ maximalIdeal R ↔ algebraMap R K r ∈ V.nonunits) := by exact @_root_.P2MW.S_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates.solution R _ _ _ _ hR K _ _ _
