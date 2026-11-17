import Tengoku.Seed.NumberTheory.NumberField.AdeleRing
import Tengoku.FltAnthropic.P2M.Sol.S_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
attribute [-instance] NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion

theorem NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact
    (F : Type) [Field F] [NumberField F]
    {C : Set (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)} (hC : IsCompact C) :
    {ξ : F | algebraMap F (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) ξ ∈ C}.Finite := by exact @_root_.P2MW.S_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact.solution F _ _ C hC
