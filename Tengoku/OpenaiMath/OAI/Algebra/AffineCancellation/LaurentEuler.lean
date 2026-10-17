import Tengoku.OpenaiMath.OAI.Algebra.AffineCancellation.LaurentDerivation

namespace OAI

noncomputable section

namespace ComplexCancellation.LaurentEuler
open LaurentPolynomial
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
def linear : LaurentPolynomial R →ₗ[k] LaurentPolynomial R :=
  (Finsupp.lsum k (fun n : ℤ => n • (AddMonoidAlgebra.lsingle n : R →ₗ[k] LaurentPolynomial R))) ∘ₗ
    (AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap
/--
@isnad1 id=eq.0h4v.s9.f1d3e9cd913b from=translated src=- shape=90f6fcb7 vocab=5167a7fb
-/
lemma linear_single (n : ℤ) (r : R) : linear (k := k) (C r*T n)=n • (C r*T n) := by
  rw [← single_eq_C_mul_T]
  change Finsupp.lsum k _ (Finsupp.single n r)=_
  rw [Finsupp.lsum_single]
  rfl
/--
@isnad1 id=eq.0h4v.s9.bc75dcafa849 from=translated src=- shape=be5f45d9 vocab=daa37a54
-/
lemma linear_mul (r s : LaurentPolynomial R) :
    linear (k := k) (r*s)=r*linear (k := k) s+s*linear (k := k) r := by
  induction r using LaurentPolynomial.induction_on' with
  | add r s hr hs => simp only [add_mul,map_add,hr,hs]; ring
  | C_mul_T n a =>
    induction s using LaurentPolynomial.induction_on' with
    | add r s hr hs => simp only [mul_add,map_add,hr,hs]; ring
    | C_mul_T m b =>
      have he : C a*T n*(C b*T m)=C (a*b)*T (n+m) := by rw [map_mul,T_add]; ring
      rw [he,linear_single,linear_single,linear_single,← he,add_zsmul]
      simp only [mul_smul_comm]
      rw [mul_comm (C b*T m),add_comm]
def derivation : Derivation k (LaurentPolynomial R) (LaurentPolynomial R) :=
  Derivation.mk' linear (by intro r s; exact linear_mul r s)
/--
@isnad1 id=eq.0h4v.s9.e0b3a0a02368 from=translated src=- shape=d2ab58eb vocab=f51e1348
-/
@[simp] lemma monomial (n : ℤ) (r : R) : derivation (k := k) (C r*T n)=n • (C r*T n) := linear_single n r
/--
@isnad1 id=eq.0h3v.s8.11d8721a057d from=translated src=- shape=43dcb8b2 vocab=6522f3e2
-/
@[simp] lemma coefficient (r : R) : derivation (k := k) (C r)=0 := by simpa using monomial (k := k) 0 r
/--
@isnad1 id=eq.0h3v.s8.e22b49ce97ba from=translated src=- shape=682d77ca vocab=4e79d363
-/
@[simp] lemma T_apply (n : ℤ) : derivation (k := k) (T n : LaurentPolynomial R)=n • T n := by simpa using monomial (k := k) n (1 : R)
end ComplexCancellation.LaurentEuler

namespace ComplexCancellation.LaurentEuler
open LaurentPolynomial
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
/--
@isnad1 id=eq.0h4v.s9.4e630f899563 from=translated src=- shape=928f45ae vocab=3a2d92ed
-/
lemma commute_extension (D : Derivation k R R) (r : LaurentPolynomial R) :
    derivation (k := k) (LaurentDerivation.extension D r)=LaurentDerivation.extension D (derivation (k := k) r) := by
  induction r using LaurentPolynomial.induction_on' with
  | add r s hr hs => simp only [map_add,hr,hs]
  | C_mul_T n a => rw [LaurentDerivation.extension_monomial (k := k),monomial (k := k),monomial (k := k),map_zsmul,LaurentDerivation.extension_monomial (k := k)]
/--
@isnad1 id=eq.0h5v.s10.d5852b48f5eb from=translated src=- shape=65ff12d3 vocab=c26d7b91
-/
lemma commute_replica (D : Derivation k R R) (c : R) (r : LaurentPolynomial R) :
    derivation (k := k) (C c*LaurentDerivation.extension D r)=C c*LaurentDerivation.extension D (derivation (k := k) r) := by
  rw [Derivation.leibniz,coefficient,smul_zero,add_zero,smul_eq_mul,commute_extension]
end ComplexCancellation.LaurentEuler

end

end OAI
