import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Bialgebra_counit_comp_algEquiv_of_comul_compat.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Bialgebra_counit_comp_algEquiv_of_comul_compat

open scoped TensorProduct

/--
@isnad1 id=eq.1h5v.s11.5d19b0c2c13f from=translated src=- shape=f5e64c62 vocab=4a5f8b3e
-/
theorem solution
    (K : Type*) [CommRing K]
    (B₁ : Type*) [CommRing B₁] [Bialgebra K B₁]
    (B₂ : Type*) [CommRing B₂] [Bialgebra K B₂]
    (φ : B₁ ≃ₐ[K] B₂)
    (hφcomul : ∀ x, Coalgebra.comul (R := K) (φ x) =
        (_root_.TensorProduct.map φ.toLinearMap φ.toLinearMap) (Coalgebra.comul (R := K) x)) :
    ∀ x, Coalgebra.counit (R := K) (φ x) = Coalgebra.counit (R := K) x := by
  intro x

  let η : B₁ →ₗ[K] K := (Coalgebra.counit (R := K) (A := B₂)).comp φ.toLinearMap
  have hηx : η x = Coalgebra.counit (R := K) (φ x) := rfl
  rw [← hηx]

  have key : ∀ y : B₁,
      (TensorProduct.lid K B₁) ((η.rTensor B₁) (Coalgebra.comul (R := K) y)) = y := by
    intro y
    apply φ.injective
    have hnat : ∀ z : K ⊗[K] B₁,
        φ ((TensorProduct.lid K B₁) z) = (TensorProduct.lid K B₂) (φ.toLinearMap.lTensor K z) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul r b => simp [TensorProduct.lid_tmul, map_smul]
      | add u v hu hv => simp [map_add, hu, hv]
    rw [hnat]
    have hcomp2 : φ.toLinearMap.lTensor K ∘ₗ η.rTensor B₁
        = (Coalgebra.counit (R := K) (A := B₂)).rTensor B₂
          ∘ₗ _root_.TensorProduct.map φ.toLinearMap φ.toLinearMap := by
      ext a b
      simp [η, TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
    rw [show φ.toLinearMap.lTensor K (η.rTensor B₁ (Coalgebra.comul y))
          = (Coalgebra.counit (R := K) (A := B₂)).rTensor B₂
              ((_root_.TensorProduct.map φ.toLinearMap φ.toLinearMap) (Coalgebra.comul y)) from
        congrFun (congrArg DFunLike.coe hcomp2) _]
    rw [← hφcomul y]
    have hax := Coalgebra.rTensor_counit_comp_comul (R := K) (A := B₂)
    have hax' := congrFun (congrArg DFunLike.coe hax) (φ y)
    simp only [LinearMap.comp_apply] at hax'
    rw [hax']
    simp [TensorProduct.lid_tmul]

  have A' : Coalgebra.counit (R := K)
      ((TensorProduct.lid K B₁) ((η.rTensor B₁) (Coalgebra.comul (R := K) x)))
      = Coalgebra.counit (R := K) x := by rw [key x]
  have hG_eq : Coalgebra.counit (R := K)
      ((TensorProduct.lid K B₁) ((η.rTensor B₁) (Coalgebra.comul (R := K) x)))
      = η x := by
    have hnat2 : ∀ z : K ⊗[K] B₁,
        Coalgebra.counit (R := K) ((TensorProduct.lid K B₁) z)
          = (TensorProduct.lid K K) ((Coalgebra.counit (R := K) (A := B₁)).lTensor K z) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul r b => simp [TensorProduct.lid_tmul, map_smul]
      | add u v hu hv => simp [map_add, hu, hv]
    rw [hnat2]
    have hswap : (Coalgebra.counit (R := K) (A := B₁)).lTensor K ∘ₗ η.rTensor B₁
        = η.rTensor K ∘ₗ (Coalgebra.counit (R := K) (A := B₁)).lTensor B₁ := by
      ext a b; simp [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul]
    rw [show (Coalgebra.counit (R := K) (A := B₁)).lTensor K (η.rTensor B₁ (Coalgebra.comul x))
          = η.rTensor K ((Coalgebra.counit (R := K) (A := B₁)).lTensor B₁ (Coalgebra.comul x)) from
        congrFun (congrArg DFunLike.coe hswap) _]
    have hax1 := Coalgebra.lTensor_counit_comp_comul (R := K) (A := B₁)
    have hax1' := congrFun (congrArg DFunLike.coe hax1) x
    simp only [LinearMap.comp_apply] at hax1'
    rw [hax1']
    simp [LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
  rw [← hG_eq]; exact A'
