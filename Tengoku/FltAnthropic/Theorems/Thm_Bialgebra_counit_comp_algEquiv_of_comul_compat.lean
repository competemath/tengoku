import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Bialgebra_counit_comp_algEquiv_of_comul_compat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Bialgebra_counit_comp_algEquiv_of_comul_compat.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped TensorProduct in
/--
@isnad1 id=eq.1h5v.s11.5d19b0c2c13f from=translated src=- shape=f5e64c62 vocab=4a5f8b3e
-/
theorem Bialgebra.counit_comp_algEquiv_of_comul_compat
    (K : Type*) [CommRing K]
    (B₁ : Type*) [CommRing B₁] [Bialgebra K B₁]
    (B₂ : Type*) [CommRing B₂] [Bialgebra K B₂]
    (φ : B₁ ≃ₐ[K] B₂)
    (hφcomul : ∀ x, Coalgebra.comul (R := K) (φ x) =
        (_root_.TensorProduct.map φ.toLinearMap φ.toLinearMap) (Coalgebra.comul (R := K) x)) :
    ∀ x, Coalgebra.counit (R := K) (φ x) = Coalgebra.counit (R := K) x := by exact @_root_.P2MW.S_Bialgebra_counit_comp_algEquiv_of_comul_compat.solution K _ B₁ _ _ B₂ _ _ φ hφcomul
