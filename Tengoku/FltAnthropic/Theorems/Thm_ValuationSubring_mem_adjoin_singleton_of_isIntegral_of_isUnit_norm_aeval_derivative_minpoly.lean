import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_ValuationSubring_mem_adjoin_singleton_of_isIntegral_of_isUnit_norm_aeval_derivative_minpoly

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ValuationSubring_mem_adjoin_singleton_of_isIntegral_of_isUnit_norm_aeval_derivative_minpoly.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open Polynomial

theorem ValuationSubring.mem_adjoin_singleton_of_isIntegral_of_isUnit_norm_aeval_derivative_minpoly
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    (𝒪 : ValuationSubring F) [Algebra 𝒪 L] [IsScalarTower 𝒪 F L]
    (c : L) (hc : IsIntegral 𝒪 c)
    (hgen : IntermediateField.adjoin F ({c} : Set L) = ⊤)
    (hdisc : ∃ u : 𝒪ˣ, algebraMap 𝒪 F u = Algebra.norm F (aeval c (derivative (minpoly F c))))
    (z : L) (hz : IsIntegral 𝒪 z) :
    z ∈ Algebra.adjoin 𝒪 ({c} : Set L) := by exact @_root_.P2MW.S_ValuationSubring_mem_adjoin_singleton_of_isIntegral_of_isUnit_norm_aeval_derivative_minpoly.solution F L _ _ _ 𝒪 _ _ c hc hgen hdisc z hz
