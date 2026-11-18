import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicCurve_Place_exists_sub_algebraMap_mem_maximalIdeal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicCurve_Place_exists_sub_algebraMap_mem_maximalIdeal.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

theorem AlgebraicCurve.Place.exists_sub_algebraMap_mem_maximalIdeal {K F : Type*} [Field K] [Field F]
    [Algebra K F] (u : AlgebraicCurve.Place K F) (hdeg : u.deg = 1) (b : u.toValuationSubring) :
    ∃ c : K, b - algebraMap K u.toValuationSubring c
      ∈ IsLocalRing.maximalIdeal u.toValuationSubring := by exact @_root_.P2MW.S_AlgebraicCurve_Place_exists_sub_algebraMap_mem_maximalIdeal.solution K F _ _ _ u hdeg b
