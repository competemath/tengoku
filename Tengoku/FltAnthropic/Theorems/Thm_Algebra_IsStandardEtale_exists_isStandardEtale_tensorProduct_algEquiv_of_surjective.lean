import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_IsStandardEtale_exists_isStandardEtale_tensorProduct_algEquiv_of_surjective

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_IsStandardEtale_exists_isStandardEtale_tensorProduct_algEquiv_of_surjective.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.IsStandardEtale.exists_isStandardEtale_tensorProduct_algEquiv_of_surjective
    {C C₀ : Type} [CommRing C] [CommRing C₀] [Algebra C C₀] (hC : Function.Surjective (algebraMap C C₀))
    (S₀ : Type) [CommRing S₀] [Algebra C₀ S₀] [Algebra.IsStandardEtale C₀ S₀] :
    ∃ (S : Type) (_ : CommRing S) (_ : Algebra C S), Algebra.IsStandardEtale C S ∧ Nonempty (C₀ ⊗[C] S ≃ₐ[C₀] S₀) := by exact @_root_.P2MW.S_Algebra_IsStandardEtale_exists_isStandardEtale_tensorProduct_algEquiv_of_surjective.solution C C₀ _ _ _ hC S₀ _ _ _
