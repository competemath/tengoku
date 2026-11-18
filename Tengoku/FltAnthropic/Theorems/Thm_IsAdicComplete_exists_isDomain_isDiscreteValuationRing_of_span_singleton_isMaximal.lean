import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsAdicComplete_exists_isDomain_isDiscreteValuationRing_of_span_singleton_isMaximal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsAdicComplete_exists_isDomain_isDiscreteValuationRing_of_span_singleton_isMaximal.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

theorem IsAdicComplete.exists_isDomain_isDiscreteValuationRing_of_span_singleton_isMaximal
    {𝓞 : Type u} [CommRing 𝓞] (ϖ : 𝓞) (hϖ : ϖ ∈ nonZeroDivisors 𝓞)
    [(Ideal.span {ϖ}).IsMaximal] [IsAdicComplete (Ideal.span {ϖ}) 𝓞] :
    ∃ (_ : IsDomain 𝓞) (_ : IsDiscreteValuationRing 𝓞),
      Irreducible ϖ ∧ IsLocalRing.maximalIdeal 𝓞 = Ideal.span {ϖ} := by exact @_root_.P2MW.S_IsAdicComplete_exists_isDomain_isDiscreteValuationRing_of_span_singleton_isMaximal.solution 𝓞 _ ϖ hϖ _ _
