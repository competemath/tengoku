import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Flat
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_exists_finiteFlat_hopfOrder_ratLocalizedAt_of_algEquiv_baseChange_padic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_exists_finiteFlat_hopfOrder_ratLocalizedAt_of_algEquiv_baseChange_padic.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped NNReal TensorProduct
open scoped TensorProduct in
theorem HopfAlgebra.exists_finiteFlat_hopfOrder_ratLocalizedAt_of_algEquiv_baseChange_padic
    (p : ℕ) [Fact p.Prime]
    (A : Type) [CommRing A] [HopfAlgebra ℚ A]
    (hAfin : Module.Finite ℚ A) (hAcocomm : Coalgebra.IsCocomm ℚ A)
    (Hp : Type) [CommRing Hp] [HopfAlgebra ℤ_[p] Hp]
    (hfin : Module.Finite ℤ_[p] Hp) (hflat : Module.Flat ℤ_[p] Hp)
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] Hp)
    (φ : (ℚ_[p] ⊗[ℚ] A) ≃ₐ[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] Hp))
    (hφcomul : ∀ x, Coalgebra.comul (R := ℚ_[p]) (φ x) =
        (TensorProduct.map φ.toLinearMap φ.toLinearMap) (Coalgebra.comul (R := ℚ_[p]) x)) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
      Module.Finite (GaloisRep.ratLocalizedAt p) H ∧
      Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
      ∃ ψ : (ℚ ⊗[(GaloisRep.ratLocalizedAt p)] H) ≃ₐ[ℚ] A,
        ∀ x, Coalgebra.comul (R := ℚ) (ψ x) =
          (TensorProduct.map ψ.toLinearMap ψ.toLinearMap) (Coalgebra.comul (R := ℚ) x) := by exact @_root_.P2MW.S_HopfAlgebra_exists_finiteFlat_hopfOrder_ratLocalizedAt_of_algEquiv_baseChange_padic.solution p _ A _ _ hAfin hAcocomm Hp _ _ hfin hflat hcocomm φ hφcomul
