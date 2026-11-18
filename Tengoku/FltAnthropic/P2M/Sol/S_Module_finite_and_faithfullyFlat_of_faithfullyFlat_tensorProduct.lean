import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Module_finite_and_faithfullyFlat_of_faithfullyFlat_tensorProduct.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Module_finite_and_faithfullyFlat_of_faithfullyFlat_tensorProduct

set_option autoImplicit false

universe u v w

open TensorProduct

/--
@isnad1 id=and.0h3v.s8.da7288923b77 from=translated src=- shape=9206b6b6 vocab=c2a79257
-/
theorem solution
    {R : Type u} [CommRing R] (W : Type v) [CommRing W] [Algebra R W] [Module.FaithfullyFlat R W]
    (M : Type w) [AddCommGroup M] [Module R M]
    [Module.Finite W (W ⊗[R] M)] [Module.FaithfullyFlat W (W ⊗[R] M)] :
    Module.Finite R M ∧ Module.FaithfullyFlat R M := by
  have hfin : Module.Finite R M := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat W
  have hflat : Module.Flat R M := Module.Flat.of_flat_tensorProduct R M W
  refine ⟨hfin, (Module.FaithfullyFlat.iff_flat_and_lTensor_reflects_triviality R M).mpr ⟨hflat, ?_⟩⟩
  intro N _ _ hN

  have e₁ : (W ⊗[R] M) ⊗[W] (W ⊗[R] N) ≃ₗ[W] (W ⊗[R] M) ⊗[R] N :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R W W (W ⊗[R] M) N
  have e₂ : (W ⊗[R] M) ⊗[R] N ≃ₗ[R] W ⊗[R] (M ⊗[R] N) := TensorProduct.assoc R W M N
  haveI : Subsingleton (W ⊗[R] (M ⊗[R] N)) := inferInstance
  haveI h1 : Subsingleton ((W ⊗[R] M) ⊗[W] (W ⊗[R] N)) :=
    (e₁.toEquiv.trans e₂.toEquiv).subsingleton
  haveI h2 : Subsingleton (W ⊗[R] N) :=
    (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right W (W ⊗[R] M)).mp h1
  exact (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right R W).mp h2
