import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_ValuationSubring_exists_isDiscreteValuationRing_dominates_of_finiteDimensional

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ValuationSubring_exists_isDiscreteValuationRing_dominates_of_finiteDimensional.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v

open IsLocalRing

theorem ValuationSubring.exists_isDiscreteValuationRing_dominates_of_finiteDimensional
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (W : ValuationSubring F) (hW : IsDiscreteValuationRing ↥W) :
    ∃ V : ValuationSubring E, IsDiscreteValuationRing ↥V ∧
      (∀ x : F, x ∈ W → algebraMap F E x ∈ V) ∧
      (∀ x : ↥W, x ∈ maximalIdeal ↥W → algebraMap F E (x : F) ∈ V.nonunits) := by exact @_root_.P2MW.S_ValuationSubring_exists_isDiscreteValuationRing_dominates_of_finiteDimensional.solution F E _ _ _ _ W hW
