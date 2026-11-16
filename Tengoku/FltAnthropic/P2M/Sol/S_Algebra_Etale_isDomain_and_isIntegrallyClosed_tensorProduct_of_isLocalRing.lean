import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_Algebra_Etale_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_Etale_isDomain_and_isIntegrallyClosed_tensorProduct_of_isLocalRing.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Algebra_Etale_isDomain_and_isIntegrallyClosed_tensorProduct_of_isLocalRing

set_option autoImplicit false

universe u v w

open scoped TensorProduct
open IsLocalRing

namespace EtaleBCNormalAux

/--
@isnad1 id=etale.1h4v.s8.82aef312dcc5 from=translated src=- shape=eac289f1 vocab=f7f126a8
-/
theorem etale_of_ringEquiv_base {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (e : R ≃+* S) (he : ∀ r, e r = algebraMap R S r) [Algebra.Etale R T] : Algebra.Etale S T := by
  let e' : R ≃ₐ[R] S := AlgEquiv.ofRingEquiv (f := e) (fun r => by rw [he]; rfl)
  haveI : Algebra.FormallyUnramified R S := Algebra.FormallyUnramified.of_equiv e'
  haveI : Algebra.FiniteType R S := Algebra.FiniteType.equiv inferInstance e'
  haveI : Algebra.FormallyEtale S T := Algebra.FormallyEtale.of_restrictScalars (R := R)
  haveI : Algebra.FinitePresentation S T :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R S T
  exact Algebra.Etale.mk

/--
@isnad1 id=and.0h4v.s6.897039d46f1c from=translated src=- shape=dffca62e vocab=fe9fc4b7
-/
theorem isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime'
    (P : Type v) [CommRing P] [IsDomain P] [IsIntegrallyClosed P]
    (A : Type (max v w)) [CommRing A] [Algebra P A] [Algebra.Etale P A]
    (q : Ideal A) [q.IsPrime] (A_q : Type (max v w)) [CommRing A_q] [Algebra A A_q] [IsLocalization.AtPrime A_q q] :
    IsDomain A_q ∧ IsIntegrallyClosed A_q := by
  letI : Algebra (ULift.{w} P) A := ULift.algebra' P A
  haveI : IsScalarTower P (ULift.{w} P) A :=
    IsScalarTower.of_algebraMap_eq (R := P) (S := ULift.{w} P) (A := A) (fun _ => rfl)
  let e : P ≃+* ULift.{w} P := ULift.ringEquiv.symm
  haveI : IsDomain (ULift.{w} P) := MulEquiv.isDomain P e.symm.toMulEquiv
  haveI : IsIntegrallyClosed (ULift.{w} P) := IsIntegrallyClosed.of_equiv e
  haveI : Algebra.Etale (ULift.{w} P) A := etale_of_ringEquiv_base e (fun _ => rfl)
  exact Algebra.Etale.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime (ULift.{w} P) A q A_q

end EtaleBCNormalAux

open EtaleBCNormalAux in
/--
@isnad1 id=and.0h3v.s7.38ee09acfa19 from=translated src=- shape=b4e71c5b vocab=955c0eb7
-/
theorem solution
    {W : Type*} [CommRing W] (B W' : Type*) [CommRing B] [CommRing W'] [Algebra W B] [Algebra W W']
    [Algebra.Etale W W'] [IsDomain B] [IsIntegrallyClosed B] [IsLocalRing (B ⊗[W] W')] :
    IsDomain (B ⊗[W] W') ∧ IsIntegrallyClosed (B ⊗[W] W') := by
  haveI : IsLocalization.AtPrime (B ⊗[W] W') (maximalIdeal (B ⊗[W] W')) :=
    IsLocalization.of_le_isUnit (fun x hx => by
      (simp [Ideal.primeCompl, mem_maximalIdeal, mem_nonunits_iff] at hx; exact hx))
  exact isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime' B (B ⊗[W] W') (maximalIdeal _) (B ⊗[W] W')
