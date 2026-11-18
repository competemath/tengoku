import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_Ideal_height_eq_height_under_of_isIntegrallyClosed_of_isIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Ideal_height_eq_height_under_of_finiteType_of_isIntegral.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Ideal_height_eq_height_under_of_finiteType_of_isIntegral

set_option autoImplicit false

universe u

/--
@isnad1 id=eq.0h4v.s7.87935f71d2e6 from=translated src=- shape=20aec0c2 vocab=7c9b6ffb
-/
theorem solution
    (k A B : Type u) [Field k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    [Algebra A B] [IsScalarTower k A B] [FaithfulSMul A B] [Algebra.IsIntegral A B]
    (q : Ideal B) [q.IsPrime] :
    q.height = (q.under A).height := by
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  obtain ⟨d, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  letI : Algebra (MvPolynomial (Fin d) k) A := g.toRingHom.toAlgebra
  letI : Algebra (MvPolynomial (Fin d) k) B := ((algebraMap A B).comp g.toRingHom).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin d) k) A B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FaithfulSMul (MvPolynomial (Fin d) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ A).mpr hinj
  haveI : FaithfulSMul (MvPolynomial (Fin d) k) B :=
    (faithfulSMul_iff_algebraMap_injective _ B).mpr
      ((FaithfulSMul.algebraMap_injective A B).comp hinj)
  haveI : Algebra.IsIntegral (MvPolynomial (Fin d) k) A := ⟨hint⟩
  haveI : Algebra.IsIntegral (MvPolynomial (Fin d) k) B := Algebra.IsIntegral.trans A
  rw [Ideal.height_eq_height_under_of_isIntegrallyClosed_of_isIntegral (MvPolynomial (Fin d) k) B q,
    Ideal.height_eq_height_under_of_isIntegrallyClosed_of_isIntegral (MvPolynomial (Fin d) k) A
      (q.under A), Ideal.under_under]
