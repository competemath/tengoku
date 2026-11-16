import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_isUnramifiedAt_iff_isUnramifiedAt_fiber.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Algebra_isUnramifiedAt_iff_isUnramifiedAt_fiber

set_option autoImplicit false

open scoped TensorProduct

namespace L2aFAux

/--
@isnad1 id=iff.0h3v.s7.a7217a33cfce from=translated src=- shape=8c33e136 vocab=3beb21b5
-/
theorem isUnramifiedAt_iff_subsingleton {S B : Type*} [CommRing S] [CommRing B] [Algebra S B]
    [Algebra.EssFiniteType S B] (q : Ideal B) [q.IsPrime] :
    Algebra.IsUnramifiedAt S q ↔ Subsingleton (q.ResidueField ⊗[B] Ω[B⁄S]) := by
  have h : Algebra.IsUnramifiedAt S q ↔
      (⟨q, inferInstance⟩ : PrimeSpectrum B) ∈ Algebra.unramifiedLocus S B := Iff.rfl
  rw [h, Algebra.unramifiedLocus_eq_compl_support, Set.mem_compl_iff,
    Module.mem_support_iff_nontrivial_residueField_tensorProduct, not_nontrivial_iff_subsingleton]

end L2aFAux

open L2aFAux in
/--
@isnad1 id=iff.1h5v.s11.3554564504d7 from=translated src=- shape=bb1e47e2 vocab=ac036554
-/
theorem solution
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Algebra.EssFiniteType R A]
    (P : Ideal R) [P.IsPrime] (Q : Ideal A) [Q.IsPrime] [Q.LiesOver P]
    (Q' : Ideal (P.Fiber A)) [Q'.IsPrime]
    (hQ' : Q = Q'.comap Algebra.TensorProduct.includeRight.toRingHom) :
    Algebra.IsUnramifiedAt R Q ↔ Algebra.IsUnramifiedAt P.ResidueField Q' := by
  letI : Algebra A (P.Fiber A) := Algebra.TensorProduct.rightAlgebra
  rw [isUnramifiedAt_iff_subsingleton, isUnramifiedAt_iff_subsingleton]

  let e1 : P.Fiber A ⊗[A] Ω[A⁄R] ≃ₗ[P.Fiber A] Ω[P.Fiber A⁄P.ResidueField] :=
    KaehlerDifferential.tensorKaehlerEquiv R P.ResidueField A (P.Fiber A)
  let e2 : Q'.ResidueField ⊗[P.Fiber A] Ω[P.Fiber A⁄P.ResidueField] ≃ₗ[Q'.ResidueField]
      Q'.ResidueField ⊗[A] Ω[A⁄R] :=
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl Q'.ResidueField Q'.ResidueField)
      e1.symm).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A (P.Fiber A) Q'.ResidueField
        Q'.ResidueField Ω[A⁄R])

  have hQ'' : Q = Q'.comap (Algebra.ofId A (P.Fiber A)).toRingHom := hQ'
  let g : Q.ResidueField →ₐ[A] Q'.ResidueField :=
    Ideal.ResidueField.mapₐ Q Q' (Algebra.ofId A (P.Fiber A)) hQ''
  letI : Algebra Q.ResidueField Q'.ResidueField := g.toRingHom.toAlgebra
  haveI : IsScalarTower A Q.ResidueField Q'.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun a => (g.commutes a).symm
  let e3 : Q'.ResidueField ⊗[A] Ω[A⁄R] ≃ₗ[Q'.ResidueField]
      Q'.ResidueField ⊗[Q.ResidueField] (Q.ResidueField ⊗[A] Ω[A⁄R]) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A Q.ResidueField Q'.ResidueField
      Q'.ResidueField Ω[A⁄R]).symm
  rw [(e2.trans e3).toEquiv.subsingleton_congr,
    Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right Q.ResidueField Q'.ResidueField]
