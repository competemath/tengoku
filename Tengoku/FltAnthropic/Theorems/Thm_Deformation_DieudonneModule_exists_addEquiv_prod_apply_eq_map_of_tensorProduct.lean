import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_DatumAndHonda
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_WittVectorHom
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_WittHomColimit
import Tengoku.FltAnthropic.P2M.Sol.S_Deformation_DieudonneModule_exists_addEquiv_prod_apply_eq_map_of_tensorProduct

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Deformation_DieudonneModule_exists_addEquiv_prod_apply_eq_map_of_tensorProduct.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped TensorProduct

universe v

theorem Deformation.DieudonneModule.exists_addEquiv_prod_apply_eq_map_of_tensorProduct
    (p : ℕ) [Fact p.Prime]
    (B₁ B₂ : Type v) [CommRing B₁] [CommRing B₂] [Bialgebra (ZMod p) B₁] [Bialgebra (ZMod p) B₂] :
    ∃ (i₁ : B₁ →ₐc[ZMod p] B₁ ⊗[ZMod p] B₂) (i₂ : B₂ →ₐc[ZMod p] B₁ ⊗[ZMod p] B₂)
      (q₁ : B₁ ⊗[ZMod p] B₂ →ₐc[ZMod p] B₁) (q₂ : B₁ ⊗[ZMod p] B₂ →ₐc[ZMod p] B₂),
      (i₁ : B₁ →ₐ[ZMod p] B₁ ⊗[ZMod p] B₂) = Algebra.TensorProduct.includeLeft ∧
      (i₂ : B₂ →ₐ[ZMod p] B₁ ⊗[ZMod p] B₂) = Algebra.TensorProduct.includeRight ∧
      (∀ x y, q₁ (x ⊗ₜ[ZMod p] y) = Coalgebra.counit (R := ZMod p) y • x) ∧
      (∀ x y, q₂ (x ⊗ₜ[ZMod p] y) = Coalgebra.counit (R := ZMod p) x • y) ∧
      ∃ e : Deformation.DieudonneModule (ZMod p) p (B₁ ⊗[ZMod p] B₂) ≃+
          Deformation.DieudonneModule (ZMod p) p B₁ × Deformation.DieudonneModule (ZMod p) p B₂,
        (∀ z, e z = (Deformation.DieudonneModule.map (ZMod p) p q₁ z,
          Deformation.DieudonneModule.map (ZMod p) p q₂ z)) ∧
        (∀ m₁ m₂, e.symm (m₁, m₂) = Deformation.DieudonneModule.map (ZMod p) p i₁ m₁ +
          Deformation.DieudonneModule.map (ZMod p) p i₂ m₂) ∧
        (∀ z, e (Deformation.DieudonneModule.frobenius (ZMod p) p (B₁ ⊗[ZMod p] B₂) z) =
          (Deformation.DieudonneModule.frobenius (ZMod p) p B₁ (e z).1,
            Deformation.DieudonneModule.frobenius (ZMod p) p B₂ (e z).2)) ∧
        (∀ z, e (Deformation.DieudonneModule.verschiebung (ZMod p) p (B₁ ⊗[ZMod p] B₂) z) =
          (Deformation.DieudonneModule.verschiebung (ZMod p) p B₁ (e z).1,
            Deformation.DieudonneModule.verschiebung (ZMod p) p B₂ (e z).2)) := by exact @_root_.P2MW.S_Deformation_DieudonneModule_exists_addEquiv_prod_apply_eq_map_of_tensorProduct.solution p _ B₁ B₂ _ _ _ _
