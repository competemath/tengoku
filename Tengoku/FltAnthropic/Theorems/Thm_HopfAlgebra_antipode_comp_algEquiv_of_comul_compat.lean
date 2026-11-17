import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_antipode_comp_algEquiv_of_comul_compat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_antipode_comp_algEquiv_of_comul_compat.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped TensorProduct in
theorem HopfAlgebra.antipode_comp_algEquiv_of_comul_compat
    (K : Type*) [CommRing K]
    (H₁ : Type*) [CommRing H₁] [HopfAlgebra K H₁]
    (H₂ : Type*) [CommRing H₂] [HopfAlgebra K H₂]
    (φ : H₁ ≃ₐ[K] H₂)
    (hφcomul : ∀ x, Coalgebra.comul (R := K) (φ x) =
        (TensorProduct.map φ.toLinearMap φ.toLinearMap) (Coalgebra.comul (R := K) x)) :
    ∀ x, φ (HopfAlgebra.antipode K x) = HopfAlgebra.antipode K (φ x) := by exact @_root_.P2MW.S_HopfAlgebra_antipode_comp_algEquiv_of_comul_compat.solution K _ H₁ _ _ H₂ _ _ φ hφcomul
