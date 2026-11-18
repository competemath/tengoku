import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicCurve_isIntegral_adjoin_of_forall_mem_toValuationSubring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicCurve_isIntegral_adjoin_of_forall_mem_toValuationSubring.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
set_option autoImplicit false

open AlgebraicCurve
theorem AlgebraicCurve.isIntegral_adjoin_of_forall_mem_toValuationSubring
    {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F]
    (t z : F)
    (h : ∀ v : AlgebraicCurve.Place K F, t ∈ v.toValuationSubring → z ∈ v.toValuationSubring) :
    IsIntegral (Algebra.adjoin K ({t} : Set F)) z := by exact @_root_.P2MW.S_AlgebraicCurve_isIntegral_adjoin_of_forall_mem_toValuationSubring.solution K F _ _ _ x _ _ t z h
