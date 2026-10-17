import Tengoku.OpenaiMath.OAI.Algebra.AffineCancellation.Cylinder
import Tengoku.OpenaiMath.OAI.Algebra.AffineCancellation.Dimension

namespace OAI

noncomputable section

namespace ComplexCancellation.Rees
open MvPolynomial
abbrev Poly := MvPolynomial (Fin 6) ℂ
def xp : Poly := X 2^2+X 3^3+X 1^2*X 4
def relation : Poly := xp^2*X 4-(1+2*X 2*xp)*X 5-X 1^2*X 5^2-X 0^3*X 1*X 3
abbrev B := Poly ⧸ Ideal.span {relation}
def π : Poly →ₐ[ℂ] B := Ideal.Quotient.mkₐ ℂ _
def q : B := π (X 0)
/--
@isnad1 id=eq.0h0v.s9.7fb2df8cc7d3 from=translated src=- shape=8cc970ed vocab=017cd489
-/
lemma relation_zero : π relation=0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
/--
@isnad1 id=isleftre.0h0v.s6.615f95b4c58e from=translated src=- shape=25b03439 vocab=80fc9209
-/
lemma q_regular : IsLeftRegular q := by
  apply Cylinder.regular_quotient_of_prime (MvPolynomial.X_prime (i := 0))
  intro h
  have he := map_dvd (MvPolynomial.eval (fun i : Fin 6 => if i=5 then (1:ℂ) else 0)) h
  norm_num [relation,xp,Fin.ext_iff] at he
abbrev L := LaurentPolynomial A
def c : A →ₐ[ℂ] L := IsScalarTower.toAlgHom ℂ A L
def aπ : P →ₐ[ℂ] A := Ideal.Quotient.mkₐ ℂ _
def a (i : Fin 5) : L := c (aπ (X i))
def values : Fin 6 → L := ![LaurentPolynomial.T 1,a 0*LaurentPolynomial.T (-1),
  a 1,a 2,a 3*LaurentPolynomial.T 2,a 4*LaurentPolynomial.T 2]
def eval : Poly →ₐ[ℂ] L := aeval values
/--
@isnad1 id=eq.0h0v.s10.1efbbd851dd2 from=translated src=- shape=026c73e9 vocab=fddee970
-/
lemma eval_xp : eval xp = c (aπ ComplexCancellation.x) := by
  simp only [xp,eval,aeval_X,values,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,
    ComplexCancellation.x,ComplexCancellation.s,ComplexCancellation.p,ComplexCancellation.u,
    ComplexCancellation.F,map_add,map_mul,map_pow,a]
  have ht : (LaurentPolynomial.T (-1):L)^2*LaurentPolynomial.T 2=1 := by
    rw [LaurentPolynomial.T_pow,← LaurentPolynomial.T_add]; norm_num
  linear_combination c (aπ (X 0))^2*c (aπ (X 3))*ht
/--
@isnad1 id=eq.0h0v.s9.68ec9d658bcc from=translated src=- shape=8cc970ed vocab=be4444fe
-/
lemma eval_relation : eval relation = 0 := by
  have h : c (aπ H) = 0 := by
    rw [show aπ H=0 from Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp)),map_zero]
  have hh : eval relation = c (aπ H)*LaurentPolynomial.T 2 := by
    simp only [relation,map_sub,map_mul,map_add,map_pow,map_one,map_ofNat,eval_xp]
    simp only [eval,aeval_X,values,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
    simp only [H,ComplexCancellation.F,ComplexCancellation.J,ComplexCancellation.p,
      ComplexCancellation.s,ComplexCancellation.u,map_sub,map_mul,map_add,map_pow,map_one,map_ofNat,a]
    have ht : (LaurentPolynomial.T (-1):L)^2*LaurentPolynomial.T 2=1 := by
      rw [LaurentPolynomial.T_pow,← LaurentPolynomial.T_add]; norm_num
    have ht' : (LaurentPolynomial.T 1:L)^3*LaurentPolynomial.T (-1)=LaurentPolynomial.T 2 := by
      rw [LaurentPolynomial.T_pow,← LaurentPolynomial.T_add]; norm_num
    linear_combination
      -(c (aπ (X 0)))^2*c (aπ (X 4))^2*LaurentPolynomial.T 2*ht -
      c (aπ (X 0))*c (aπ (X 2))*ht'

  rw [hh,h,zero_mul]
def embedding : B →ₐ[ℂ] L := Ideal.Quotient.liftₐ _ eval (by
  intro r hr
  obtain ⟨t,rfl⟩ := Ideal.mem_span_singleton.mp hr
  rw [map_mul,eval_relation,zero_mul])
/--
@isnad1 id=eq.0h1v.s10.598774062053 from=translated src=- shape=fd2727ee vocab=d6177c65
-/
@[simp] lemma embedding_π (r : Poly) : embedding (π r)=eval r := Ideal.Quotient.lift_mk _ _ _

abbrev Bq := Localization.Away q
def loc : B →ₐ[ℂ] Bq := IsScalarTower.toAlgHom ℂ B Bq
def Q : Bqˣ := (IsLocalization.Away.algebraMap_isUnit q).unit
/--
@isnad1 id=eq.0h0v.s10.0c1fde172ab3 from=translated src=- shape=571dadcb vocab=4891d30b
-/
lemma Q_val : (Q : Bq)=loc q := IsUnit.unit_spec _
/--
@isnad1 id=injectiv.0h0v.s10.f9d4f661804a from=translated src=- shape=91c1b9c9 vocab=396e9ca7
-/
lemma loc_injective : Function.Injective loc := by
  apply IsLocalization.injectiveₛ (M := Submonoid.powers q) Bq
  rintro r ⟨n,rfl⟩
  exact isLeftRegular_iff_isRegular.mp (q_regular.pow n)
def backValues : Fin 5 → Bq := ![(Q:Bq)*loc (π (X 1)),loc (π (X 2)),
  loc (π (X 3)),(↑(Q⁻¹):Bq)^2*loc (π (X 4)),(↑(Q⁻¹):Bq)^2*loc (π (X 5))]
def backEval : P →ₐ[ℂ] Bq := aeval backValues
/--
@isnad1 id=eq.0h0v.s11.879e69902ef4 from=translated src=- shape=026c73e9 vocab=1f917dd6
-/
lemma backEval_x : backEval ComplexCancellation.x = loc (π xp) := by
  simp only [ComplexCancellation.x,ComplexCancellation.p,ComplexCancellation.s,
    ComplexCancellation.u,ComplexCancellation.F,backEval,map_add,map_mul,map_pow,aeval_X,
    backValues,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,xp]
  simp only [mul_pow]
  have h : (Q:Bq)^2*(↑(Q⁻¹):Bq)^2=1 := by rw [← mul_pow,Units.mul_inv,one_pow]
  linear_combination loc (π (X 1))^2*loc (π (X 4))*h
/--
@isnad1 id=eq.0h0v.s10.4db124926484 from=translated src=- shape=8cc970ed vocab=c387349e
-/
lemma backEval_H : backEval H=0 := by
  have h : loc (π relation)=0 := by rw [relation_zero,map_zero]
  have he : (Q:Bq)^2*backEval H=loc (π relation) := by
    simp only [H,map_sub,map_mul,map_add,map_pow,map_one,map_ofNat,backEval_x]
    simp only [ComplexCancellation.p,ComplexCancellation.s,ComplexCancellation.u,
      ComplexCancellation.F,ComplexCancellation.J,backEval,aeval_X,backValues,
      Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
    simp only [relation,map_sub,map_mul,map_add,map_pow,map_one,map_ofNat]
    rw [show loc (π (X 0))=(Q:Bq) from Q_val.symm]
    have h2 : (Q:Bq)^2*(↑(Q⁻¹):Bq)^2=1 := by rw [← mul_pow,Units.mul_inv,one_pow]
    have h4 : (Q:Bq)^4*(↑(Q⁻¹):Bq)^4=1 := by rw [← mul_pow,Units.mul_inv,one_pow]
    linear_combination
      (loc (π xp)^2*loc (π (X 4))-(1+2*loc (π (X 2))*loc (π xp))*loc (π (X 5)))*h2-
      loc (π (X 1))^2*loc (π (X 5))^2*h4
  apply (Q.isUnit.pow 2).mul_right_inj.mp
  rw [mul_zero,he,h]
def backCoefficients : A →ₐ[ℂ] Bq := Ideal.Quotient.liftₐ _ backEval (by
  intro r hr
  obtain ⟨t,rfl⟩ := Ideal.mem_span_singleton.mp hr
  rw [map_mul,backEval_H,zero_mul])
/--
@isnad1 id=eq.0h1v.s11.2ab4785facc4 from=translated src=- shape=fd2727ee vocab=706689c3
-/
@[simp] lemma backCoefficients_aπ (r : P) : backCoefficients (aπ r)=backEval r :=
  Ideal.Quotient.lift_mk _ _ _
def backward : L →ₐ[ℂ] Bq where
  __ := LaurentPolynomial.eval₂ backCoefficients.toRingHom Q
  commutes' r := by
    change LaurentPolynomial.eval₂ backCoefficients.toRingHom Q (LaurentPolynomial.C (algebraMap ℂ A r)) = _
    rw [LaurentPolynomial.eval₂_C]
    exact backCoefficients.commutes r
/--
@isnad1 id=eq.0h0v.s10.9f58cb108fed from=translated src=- shape=9eaf15bf vocab=84a19934
-/
lemma backward_embedding : backward.comp embedding=loc := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change backward (eval (X i))=loc (π (X i))
  fin_cases i <;> simp [eval,values,Matrix.cons_val,backward,a,c,backEval,backValues,
    backCoefficients_aπ,IsScalarTower.toAlgHom]
  · exact Q_val
  · rw [mul_right_comm,Units.mul_inv,one_mul]
  · rw [mul_right_comm,← mul_pow,Units.inv_mul,one_pow,one_mul]
  · rw [mul_right_comm,← mul_pow,Units.inv_mul,one_pow,one_mul]
/--
@isnad1 id=injectiv.0h0v.s9.98e0ccfd59f5 from=translated src=- shape=91c1b9c9 vocab=4278f3a4
-/
lemma embedding_injective : Function.Injective embedding := by
  apply Function.Injective.of_comp (f := backward)
  rw [← AlgHom.coe_comp,backward_embedding]
  exact loc_injective
instance : IsDomain B := Function.Injective.isDomain embedding embedding_injective
instance : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℂ B
end ComplexCancellation.Rees

end

end OAI
