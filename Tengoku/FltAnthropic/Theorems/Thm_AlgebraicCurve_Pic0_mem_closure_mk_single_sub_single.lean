import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicCurve_Pic0_mem_closure_mk_single_sub_single

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicCurve_Pic0_mem_closure_mk_single_sub_single.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
set_option autoImplicit false
open AlgebraicCurve

/--
@isnad1 id=mem.1h4v.s10.0e3cbef1f8dc from=translated src=- shape=5382ee51 vocab=daba1ffa
-/
theorem AlgebraicCurve.Pic0.mem_closure_mk_single_sub_single
    {K F : Type*} [Field K] [Field F] [Algebra K F] (h1 : ∀ v : Place K F, v.deg = 1)
    (V₀ : Place K F) (x : Pic0 K F) :
    x ∈ AddSubgroup.closure
      {y : Pic0 K F | ∃ (V : Place K F)
        (h : Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1 ∈ Divisor.degZero (K := K) (F := F)),
        y = Pic0.mk ⟨Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1, h⟩} := by exact @_root_.P2MW.S_AlgebraicCurve_Pic0_mem_closure_mk_single_sub_single.solution K F _ _ _ h1 V₀ x
