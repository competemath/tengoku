import Tengoku.OpenaiMath.OAI.Algebra.AffineCancellation.Model

namespace OAI

noncomputable section

namespace ComplexCancellation.PolynomialDerivation
open TrivSqZeroExt
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
def dual (D : Derivation k R R) : R →ₐ[k] TrivSqZeroExt R R where
  toFun r := inl r + inr (D r)
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' r s := by apply TrivSqZeroExt.ext <;> simp
  map_mul' r s := by
    apply TrivSqZeroExt.ext <;>
      simp [Derivation.leibniz,smul_eq_mul,mul_comm]
  commutes' r := by apply TrivSqZeroExt.ext <;> simp [algebraMap_eq_inl']
/--
@isnad1 id=eq.0h4v.s8.62eb3a77e748 from=translated src=- shape=4c557f57 vocab=ec864bbf
-/
@[simp] lemma dual_fst (D : Derivation k R R) (r : R) : fst (dual D r)=r := by simp [dual]
/--
@isnad1 id=eq.0h4v.s8.a8d0a7d9b880 from=translated src=- shape=b3560366 vocab=294313a6
-/
@[simp] lemma dual_snd (D : Derivation k R R) (r : R) : snd (dual D r)=D r := by simp [dual]
def fromDual (g : R →ₐ[k] TrivSqZeroExt R R)
    (hg : ∀ r, fst (g r)=r) : Derivation k R R :=
  Derivation.mk' (((sndHom R R).restrictScalars k).comp g.toLinearMap) (by
    intro r s
    change snd (g (r*s)) = r * snd (g s)+s * snd (g r)
    rw [map_mul,snd_mul,hg,hg]
    simp only [smul_eq_mul,op_smul_eq_mul,mul_comm])
variable {S : Type*} [CommRing S] [Algebra k S]
def along (f : R →ₐ[k] S) (D : Derivation k R R) : R →ₐ[k] TrivSqZeroExt S S where
  toFun r := inl (f r)+inr (f (D r))
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' r s := by apply TrivSqZeroExt.ext <;> simp
  map_mul' r s := by
    apply TrivSqZeroExt.ext <;>
      simp [Derivation.leibniz,smul_eq_mul,mul_comm]
  commutes' r := by
    apply TrivSqZeroExt.ext <;> simp [algebraMap_eq_inl']
/--
@isnad1 id=eq.0h6v.s8.948b9ad78cfb from=translated src=- shape=6a994ada vocab=b3582648
-/
@[simp] lemma along_fst (f : R →ₐ[k] S) (D : Derivation k R R) (r : R) :
    fst (along f D r)=f r := by simp [along]
/--
@isnad1 id=eq.0h6v.s8.2ede03bf9975 from=translated src=- shape=c37b3fae vocab=3a57f2c3
-/
@[simp] lemma along_snd (f : R →ₐ[k] S) (D : Derivation k R R) (r : R) :
    snd (along f D r)=f (D r) := by simp [along]

variable {ι : Type*}
def mvDual (D : Derivation k R R) (d : ι → MvPolynomial ι R) :
    MvPolynomial ι R →ₐ[k] TrivSqZeroExt (MvPolynomial ι R) (MvPolynomial ι R) where
  __ := MvPolynomial.eval₂Hom (along (IsScalarTower.toAlgHom k R (MvPolynomial ι R)) D).toRingHom
    (fun i => inl (MvPolynomial.X i)+inr (d i))
  commutes' a := by
    change MvPolynomial.eval₂ _ _ (MvPolynomial.C (algebraMap k R a)) = _
    rw [MvPolynomial.eval₂_C]
    exact (along (IsScalarTower.toAlgHom k R (MvPolynomial ι R)) D).commutes a
/--
@isnad1 id=eq.0h6v.s10.ce1a38a18e69 from=translated src=- shape=ededa667 vocab=026d75a1
-/
lemma mvDual_C (D : Derivation k R R) (d : ι → MvPolynomial ι R) (r : R) :
    mvDual D d (MvPolynomial.C r)=inl (MvPolynomial.C r)+inr (MvPolynomial.C (D r)) :=
  MvPolynomial.eval₂_C _ _ _
/--
@isnad1 id=eq.0h6v.s9.bd75f0d007f2 from=translated src=- shape=4033c7f6 vocab=d5432d96
-/
lemma mvDual_X (D : Derivation k R R) (d : ι → MvPolynomial ι R) (i : ι) :
    mvDual D d (MvPolynomial.X i)=inl (MvPolynomial.X i)+inr (d i) :=
  MvPolynomial.eval₂_X _ _ _
/--
@isnad1 id=eq.0h6v.s9.8dfa10e2d10c from=translated src=- shape=56110b72 vocab=5a6627a8
-/
lemma mvDual_fst (D : Derivation k R R) (d : ι → MvPolynomial ι R) (p : MvPolynomial ι R) :
    fst (mvDual D d p)=p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [mvDual_C]
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => simp [mvDual_X,hp]
def mv (D : Derivation k R R) (d : ι → MvPolynomial ι R) :
    Derivation k (MvPolynomial ι R) (MvPolynomial ι R) := fromDual (mvDual D d) (mvDual_fst D d)
/--
@isnad1 id=eq.0h6v.s9.e0bbfb7900e0 from=translated src=- shape=20017a28 vocab=92714ad8
-/
@[simp] lemma mv_C (D : Derivation k R R) (d : ι → MvPolynomial ι R) (r : R) :
    mv D d (MvPolynomial.C r)=MvPolynomial.C (D r) := by
  change snd (mvDual D d (MvPolynomial.C r))=_
  simp [mvDual_C]
/--
@isnad1 id=eq.0h6v.s8.0692a7bbfcb1 from=translated src=- shape=1816d299 vocab=3c99e1ae
-/
@[simp] lemma mv_X (D : Derivation k R R) (d : ι → MvPolynomial ι R) (i : ι) :
    mv D d (MvPolynomial.X i)=d i := by
  change snd (mvDual D d (MvPolynomial.X i))=_
  simp [mvDual_X]
end ComplexCancellation.PolynomialDerivation

end

end OAI
