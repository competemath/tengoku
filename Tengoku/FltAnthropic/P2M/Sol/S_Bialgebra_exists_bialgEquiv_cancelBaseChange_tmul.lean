import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Bialgebra_exists_bialgEquiv_cancelBaseChange_tmul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Bialgebra_exists_bialgEquiv_cancelBaseChange_tmul

set_option autoImplicit false

open scoped TensorProduct

open Bialgebra in

/--
@isnad1 id=ex.0h4v.s12.ba22542fb299 from=translated src=- shape=2f54e38e vocab=6ff0fff0
-/
theorem solution
    (R R' S : Type*) [CommRing R] [CommRing R'] [CommRing S] [Algebra R R'] [Algebra R' S] [Algebra R S]
    [IsScalarTower R R' S] (C : Type*) [CommRing C] [Bialgebra R C] :
    ∃ e : S ⊗[R'] (R' ⊗[R] C) ≃ₐc[S] S ⊗[R] C, ∀ (s : S) (r : R') (c : C), e (s ⊗ₜ (r ⊗ₜ c)) = (r • s) ⊗ₜ c := by
  classical
  let e₀ : S ⊗[R'] (R' ⊗[R] C) ≃ₐ[S] S ⊗[R] C := Algebra.TensorProduct.cancelBaseChange R R' S S C
  have he₀ : ∀ (s : S) (r : R') (c : C), e₀ (s ⊗ₜ (r ⊗ₜ c)) = (r • s) ⊗ₜ c := fun s r c =>
    Algebra.TensorProduct.cancelBaseChange_tmul R R' S S C s r c
  have he₁ : ∀ c : C, e₀ ((1 : S) ⊗ₜ ((1 : R') ⊗ₜ c)) = (1 : S) ⊗ₜ c := fun c => by rw [he₀, one_smul]
  refine ⟨BialgEquiv.ofAlgEquiv e₀ ?_ ?_, he₀⟩
  ·
    apply Algebra.TensorProduct.ext
    · ext
    · apply Algebra.TensorProduct.ext
      · ext
      · ext c
        simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
          Algebra.TensorProduct.includeRight_apply, AlgEquiv.coe_toAlgHom, Bialgebra.counitAlgHom_apply]
        rw [he₁]
        simp [TensorProduct.counit_tmul]
  ·
    apply Algebra.TensorProduct.ext
    · ext
    · apply Algebra.TensorProduct.ext
      · ext
      · ext c
        simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
          Algebra.TensorProduct.includeRight_apply, AlgEquiv.coe_toAlgHom, Bialgebra.comulAlgHom_apply]
        rw [he₁]

        let 𝓡 := Coalgebra.Repr.arbitrary R c
        have hc : Coalgebra.comul (R := R) c = 𝓡.index.sum fun i => 𝓡.left i ⊗ₜ[R] 𝓡.right i := 𝓡.eq.symm
        simp only [TensorProduct.comul_tmul, CommSemiring.comul_apply, hc, TensorProduct.tmul_sum, map_sum,
          TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, Algebra.TensorProduct.map_tmul]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [AlgEquiv.coe_toAlgHom, he₁]
