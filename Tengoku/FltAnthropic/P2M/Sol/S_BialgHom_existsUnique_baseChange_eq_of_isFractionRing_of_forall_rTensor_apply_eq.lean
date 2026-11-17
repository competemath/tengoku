import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_LinearMap_existsUnique_baseChange_eq_of_isFractionRing_of_forall_rTensor_apply_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_BialgHom_existsUnique_baseChange_eq_of_isFractionRing_of_forall_rTensor_apply_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_BialgHom_existsUnique_baseChange_eq_of_isFractionRing_of_forall_rTensor_apply_eq

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

universe u

open scoped TensorProduct

namespace BialgDescent

section Inj

variable (O : Type u) [CommRing O] (K : Type u) [Field K] [Algebra O K] [FaithfulSMul O K]
  (X : Type u) [AddCommGroup X] [Module O X] [Module.Flat O X]

/--
@isnad1 id=injectiv.0h3v.s10.9b8967703897 from=translated src=- shape=13b29d4c vocab=90d50a4c
-/
theorem mk_one_injective : Function.Injective (TensorProduct.mk O K X 1) := by
  have h1 : Function.Injective ((Algebra.linearMap O K).rTensor X) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (FaithfulSMul.algebraMap_injective O K)
  have h2 : (TensorProduct.mk O K X 1 : X → K ⊗[O] X) =
      (Algebra.linearMap O K).rTensor X ∘ (TensorProduct.lid O X).symm := by
    funext x
    simp [LinearMap.rTensor_tmul]
  rw [h2]
  exact h1.comp (TensorProduct.lid O X).symm.injective

end Inj

section Axioms

variable {O : Type u} [CommRing O] {K : Type u} [Field K] [Algebra O K]
  {A : Type u} [CommRing A] [Bialgebra O A] {B : Type u} [CommRing B] [Bialgebra O B]

noncomputable def Ψ : (K ⊗[O] A) ⊗[K] (K ⊗[O] A) →ₗ[O] K ⊗[O] (A ⊗[O] A) :=
  (TensorProduct.lid K K).toLinearMap.restrictScalars O |>.rTensor (A ⊗[O] A) |>.comp
    ((TensorProduct.AlgebraTensorModule.tensorTensorTensorComm O K O K K K A A).symm.toLinearMap.restrictScalars O)

/--
@isnad1 id=eq.0h7v.s12.1ad77bda82b4 from=translated src=- shape=59c168fc vocab=079969e8
-/
theorem Ψ_tmul (k k' : K) (a a' : A) :
    Ψ ((k ⊗ₜ[O] a) ⊗ₜ[K] (k' ⊗ₜ[O] a')) = (k * k') ⊗ₜ[O] (a ⊗ₜ[O] a') := by
  show (((TensorProduct.lid K K).toLinearMap.restrictScalars O).rTensor (A ⊗[O] A))
      ((TensorProduct.AlgebraTensorModule.tensorTensorTensorComm O K O K K K A A).symm
        ((k ⊗ₜ[O] a) ⊗ₜ[K] (k' ⊗ₜ[O] a'))) = _
  rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_symm_tmul, LinearMap.rTensor_tmul]
  show (TensorProduct.lid K K (k ⊗ₜ[K] k')) ⊗ₜ[O] (a ⊗ₜ[O] a') = _
  rw [TensorProduct.lid_tmul, smul_eq_mul]

/--
@isnad1 id=eq.0h4v.s13.06c10aa6175d from=translated src=- shape=3d2036d4 vocab=653f97ca
-/
theorem Ψ_comul_one_tmul (a : A) :
    Ψ (Coalgebra.comul (R := K) ((1 : K) ⊗ₜ[O] a)) = (1 : K) ⊗ₜ[O] Coalgebra.comul (R := O) a := by
  rw [TensorProduct.comul_tmul, CommSemiring.comul_apply]
  induction (Coalgebra.comul (R := O) a) using TensorProduct.induction_on with
  | zero => rw [TensorProduct.tmul_zero, LinearEquiv.map_zero, LinearMap.map_zero, TensorProduct.tmul_zero]
  | tmul x y =>
    rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, Ψ_tmul, one_mul]
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy, TensorProduct.tmul_add]

/--
@isnad1 id=eq.1h7v.s14.4cc36e1e3ffa from=translated src=- shape=232b1228 vocab=c694cbc2
-/
theorem Ψ_map_gK (gK : K ⊗[O] B →ₗ[K] K ⊗[O] A) (f : B →ₗ[O] A) (hgf : ∀ b, gK ((1 : K) ⊗ₜ b) = (1 : K) ⊗ₜ f b)
    (t : B ⊗[O] B) :
    Ψ (TensorProduct.map gK gK
        (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm O K O K K K B B (((1 : K) ⊗ₜ[K] (1 : K)) ⊗ₜ[O] t))) =
      (1 : K) ⊗ₜ[O] TensorProduct.map f f t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [TensorProduct.tmul_zero, LinearEquiv.map_zero, LinearMap.map_zero, LinearMap.map_zero, LinearMap.map_zero,
      TensorProduct.tmul_zero]
  | tmul b b' =>
    rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, TensorProduct.map_tmul, hgf, hgf, Ψ_tmul, one_mul,
      TensorProduct.map_tmul]
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, map_add, hx, hy, map_add, TensorProduct.tmul_add]

variable [FaithfulSMul O K] [Module.Flat O A]

/--
@isnad1 id=and.1h6v.s12.48fa417ae1ed from=translated src=- shape=7464cc04 vocab=eb0016f0
-/
theorem isBialgHom_of_baseChange (gK : K ⊗[O] B →ₐc[K] K ⊗[O] A) (f : B →ₗ[O] A)
    (hgf : ∀ b, gK ((1 : K) ⊗ₜ b) = (1 : K) ⊗ₜ f b) :
    (∀ b b', f (b * b') = f b * f b') ∧ f 1 = 1 ∧
      (Coalgebra.counit ∘ₗ f = Coalgebra.counit) ∧
      (TensorProduct.map f f ∘ₗ Coalgebra.comul = Coalgebra.comul ∘ₗ f) := by
  have hιA := mk_one_injective O K A
  refine ⟨fun b b' => hιA ?_, hιA ?_, ?_, ?_⟩
  · show (1 : K) ⊗ₜ[O] f (b * b') = (1 : K) ⊗ₜ[O] (f b * f b')
    calc (1 : K) ⊗ₜ[O] f (b * b') = gK ((1 : K) ⊗ₜ[O] (b * b')) := (hgf _).symm
      _ = gK (((1 : K) ⊗ₜ[O] b) * ((1 : K) ⊗ₜ[O] b')) := by rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      _ = gK ((1 : K) ⊗ₜ[O] b) * gK ((1 : K) ⊗ₜ[O] b') := map_mul gK _ _
      _ = ((1 : K) ⊗ₜ[O] f b) * ((1 : K) ⊗ₜ[O] f b') := by rw [hgf, hgf]
      _ = (1 : K) ⊗ₜ[O] (f b * f b') := by rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  · show (1 : K) ⊗ₜ[O] f 1 = (1 : K) ⊗ₜ[O] (1 : A)
    rw [← hgf]
    exact map_one gK
  · apply LinearMap.ext
    intro b
    rw [LinearMap.comp_apply]
    apply FaithfulSMul.algebraMap_injective O K
    have h1 : Coalgebra.counit (R := K) (gK ((1 : K) ⊗ₜ[O] b)) = Coalgebra.counit (R := K) ((1 : K) ⊗ₜ[O] b) :=
      LinearMap.congr_fun gK.counit_comp ((1 : K) ⊗ₜ[O] b)
    rw [hgf, TensorProduct.counit_tmul, TensorProduct.counit_tmul, CommSemiring.counit_apply] at h1
    rwa [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
  · apply LinearMap.ext
    intro b
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    haveI : Module.Flat O (A ⊗[O] A) := inferInstance
    apply mk_one_injective O K (A ⊗[O] A)
    show (1 : K) ⊗ₜ[O] TensorProduct.map f f (Coalgebra.comul b) = (1 : K) ⊗ₜ[O] Coalgebra.comul (f b)
    have h2 : Coalgebra.comul (R := K) (gK ((1 : K) ⊗ₜ[O] b)) =
        TensorProduct.map gK.toLinearMap gK.toLinearMap (Coalgebra.comul (R := K) ((1 : K) ⊗ₜ[O] b)) :=
      (LinearMap.congr_fun gK.map_comp_comul ((1 : K) ⊗ₜ[O] b)).symm
    rw [← Ψ_comul_one_tmul, ← hgf, h2, TensorProduct.comul_tmul, CommSemiring.comul_apply]
    exact (Ψ_map_gK gK.toLinearMap f hgf (Coalgebra.comul b)).symm

end Axioms

end BialgDescent

/--
@isnad1 id=existsun.3h8v.s13.b139d423f306 from=translated src=- shape=f96bac42 vocab=d3df71a9
-/
theorem solution
    (O : Type u) [CommRing O] [IsDomain O] (K : Type u) [Field K] [Algebra O K] [IsFractionRing O K]
    (Oh : Type u) [CommRing Oh] [Algebra O Oh]
    (Kh : Type u) [CommRing Kh] [Algebra O Kh] [Algebra K Kh] [Algebra Oh Kh] [IsScalarTower O K Kh] [IsScalarTower O Oh Kh]
    (hinj : Function.Injective (algebraMap Oh Kh))
    (hcap : ∀ (x : K) (y : Oh), algebraMap K Kh x = algebraMap Oh Kh y → ∃ z : O, algebraMap O K z = x)
    (A : Type u) [CommRing A] [Bialgebra O A] [Module.Free O A] [Module.Finite O A]
    (B : Type u) [CommRing B] [Bialgebra O B] [Module.Free O B] [Module.Finite O B]
    (gK : K ⊗[O] B →ₐc[K] K ⊗[O] A) (gOh : Oh ⊗[O] B →ₐc[Oh] Oh ⊗[O] A)
    (hagree : ∀ b : B,
      ((IsScalarTower.toAlgHom O K Kh).toLinearMap.rTensor A) (gK ((1 : K) ⊗ₜ b)) =
        ((IsScalarTower.toAlgHom O Oh Kh).toLinearMap.rTensor A) (gOh ((1 : Oh) ⊗ₜ b))) :
    ∃! g : B →ₐc[O] A,
      Bialgebra.TensorProduct.map (BialgHom.id K K) g = gK ∧ Bialgebra.TensorProduct.map (BialgHom.id Oh Oh) g = gOh := by
  classical
  haveI : FaithfulSMul O K := (faithfulSMul_iff_algebraMap_injective O K).mpr (IsFractionRing.injective O K)

  obtain ⟨f, ⟨hfK, hfOh⟩, huniq⟩ :=
    LinearMap.existsUnique_baseChange_eq_of_isFractionRing_of_forall_rTensor_apply_eq O K Oh Kh hinj hcap B A
      gK.toLinearMap gOh.toLinearMap hagree
  have hgf : ∀ b, gK ((1 : K) ⊗ₜ b) = (1 : K) ⊗ₜ f b := fun b => by
    have := LinearMap.congr_fun hfK ((1 : K) ⊗ₜ b)
    rw [LinearMap.baseChange_tmul] at this
    exact this.symm
  have hgfOh : ∀ b, gOh ((1 : Oh) ⊗ₜ b) = (1 : Oh) ⊗ₜ f b := fun b => by
    have := LinearMap.congr_fun hfOh ((1 : Oh) ⊗ₜ b)
    rw [LinearMap.baseChange_tmul] at this
    exact this.symm
  obtain ⟨hmul, hone, hcounit, hcomul⟩ := BialgDescent.isBialgHom_of_baseChange gK f hgf
  let g : B →ₐc[O] A :=
    { toLinearMap := f
      counit_comp := hcounit
      map_comp_comul := hcomul
      map_one' := hone
      map_mul' := hmul }
  have hg : (g : B → A) = f := rfl

  have hbc : ∀ (S : Type u) [CommRing S] [Algebra O S] (gS : S ⊗[O] B →ₐc[S] S ⊗[O] A)
      (hS : ∀ b, gS ((1 : S) ⊗ₜ b) = (1 : S) ⊗ₜ f b), Bialgebra.TensorProduct.map (BialgHom.id S S) g = gS := by
    intro S _ _ gS hS
    apply DFunLike.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul s b =>
      rw [Bialgebra.TensorProduct.map_tmul, BialgHom.id_apply]
      have : s ⊗ₜ[O] b = s • ((1 : S) ⊗ₜ[O] b) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this, map_smul, hS, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  refine ⟨g, ⟨hbc K gK hgf, hbc Oh gOh hgfOh⟩, ?_⟩

  rintro g' ⟨hg'K, -⟩
  have hK' : (g' : B →ₗ[O] A).baseChange K = f.baseChange K := by
    rw [hfK]
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul k b =>
      rw [LinearMap.baseChange_tmul, ← hg'K]
      show k ⊗ₜ[O] g' b = Bialgebra.TensorProduct.map (BialgHom.id K K) g' (k ⊗ₜ[O] b)
      rw [Bialgebra.TensorProduct.map_tmul, BialgHom.id_apply]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have heq : (g' : B →ₗ[O] A) = f := by
    apply LinearMap.baseChangeHom_injective (R := O) (S := K) (M := B) (N := A)
    rw [LinearMap.baseChangeHom_apply, LinearMap.baseChangeHom_apply, hK']
  apply DFunLike.ext
  intro b
  exact LinearMap.congr_fun heq b
