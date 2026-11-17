import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Flat
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_exists_withConv_equiv_ratLocalizedAt_of_algEquiv_baseChange_rat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_exists_withConv_equiv_ratLocalizedAt_of_algEquiv_baseChange_rat.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped NNReal TensorProduct
open scoped TensorProduct in
/--
@isnad1 id=ex.3h6v.s16.14dcad0caeb6 from=translated src=- shape=3a854824 vocab=e9bf4a5d
-/
theorem HopfAlgebra.exists_withConv_equiv_ratLocalizedAt_of_algEquiv_baseChange_rat
    (p : ℕ) [Fact p.Prime]
    {N : Type} [AddCommGroup N]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) N]
    (A : Type) [CommRing A] [HopfAlgebra ℚ A]
    (eA : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ) ≃ N)
    (heA_add : ∀ f g, eA (f * g) = eA f + eA g)
    (heA_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ)),
      (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f))
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    (ψ : (ℚ ⊗[(GaloisRep.ratLocalizedAt p)] H) ≃ₐ[ℚ] A)
    (hψcomul : ∀ x, Coalgebra.comul (R := ℚ) (ψ x) =
        (TensorProduct.map ψ.toLinearMap ψ.toLinearMap) (Coalgebra.comul (R := ℚ) x)) :
    ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ N,
      (∀ f g, e (f * g) = e f + e g) ∧
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
        (∀ h : H, g h = σ (f h)) → e g = σ • (e f) := by exact @_root_.P2MW.S_HopfAlgebra_exists_withConv_equiv_ratLocalizedAt_of_algEquiv_baseChange_rat.solution p _ N _ _ A _ _ eA heA_add heA_act H _ _ ψ hψcomul
