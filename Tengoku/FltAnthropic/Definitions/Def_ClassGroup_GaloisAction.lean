import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ClassGroup_ModP

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open scoped NumberField nonZeroDivisors
open Polynomial

section Fidl
variable {R : Type*} [CommRing R] [IsDomain R]
variable {R' : Type*} [CommRing R'] [IsDomain R']
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
variable (L : Type*) [Field L] [Algebra R' L] [IsFractionRing R' L]

end Fidl

section ClassGroupFunctoriality
variable {R : Type*} [CommRing R] [IsDomain R]
variable {R' : Type*} [CommRing R'] [IsDomain R']

def Ideal.mapNonZero (g : R ≃+* R') (P : (Ideal R)⁰) : (Ideal R')⁰ :=
  ⟨(P : Ideal R).map (g : R →+* R'), by
    have hinj : Function.Injective ((g : R →+* R') : R → R') := g.injective
    refine mem_nonZeroDivisors_iff_ne_zero.mpr fun hbot => ?_
    refine mem_nonZeroDivisors_iff_ne_zero.mp P.2 ?_
    rw [Ideal.zero_eq_bot] at hbot ⊢
    exact (Ideal.map_eq_bot_iff_of_injective hinj).mp hbot⟩

@[simp] lemma Ideal.coe_mapNonZero (g : R ≃+* R') (P : (Ideal R)⁰) :
    (Ideal.mapNonZero g P : Ideal R') = (P : Ideal R).map (g : R →+* R') := rfl

variable [IsDedekindDomain R] [IsDedekindDomain R']

end ClassGroupFunctoriality

section GalRestrict

def algAutToRingAut (A B : Type*) [CommSemiring A] [Semiring B] [Algebra A B] :
    (B ≃ₐ[A] B) →* (B ≃+* B) where
  toFun := AlgEquiv.toRingEquiv
  map_one' := RingEquiv.ext fun _ => rfl
  map_mul' _ _ := RingEquiv.ext fun _ => rfl

@[simp] lemma algAutToRingAut_apply {A B : Type*} [CommSemiring A] [Semiring B] [Algebra A B]
    (e : B ≃ₐ[A] B) (x : B) : algAutToRingAut A B e x = e x := rfl

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [Algebra.IsAlgebraic K L]
  [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]

noncomputable def galRestrictionDatum : (L ≃ₐ[K] L) →* (B ≃+* B) :=
  (algAutToRingAut A B).comp (galRestrict A K L B).toMonoidHom

@[simp] lemma galRestrictionDatum_apply (g : L ≃ₐ[K] L) (x : B) :
    galRestrictionDatum A K L B g x = galRestrict A K L B g x := rfl

end GalRestrict

namespace JacobiSumStickelberger

section ClassGroupCarrier

variable (p : ℕ) [NeZero p]

section DedekindAction

variable (R : Type*) [CommRing R] [IsDomain R]

end DedekindAction

section Cyclotomic

variable (K : Type*) [Field K] [NumberField K]

noncomputable def cycloGalEquiv [IsCyclotomicExtension {p} ℚ K] :
    (K ≃ₐ[ℚ] K) ≃* (ZMod p)ˣ :=
  IsCyclotomicExtension.autEquivPow K
    (Polynomial.cyclotomic.irreducible_rat (Nat.pos_of_ne_zero (NeZero.ne p)))

noncomputable def clRingAction [IsCyclotomicExtension {p} ℚ K] :
    (ZMod p)ˣ →* ((𝓞 K) ≃+* (𝓞 K)) :=
  (galRestrictionDatum ℤ ℚ K (𝓞 K)).comp (cycloGalEquiv p K).symm.toMonoidHom

end Cyclotomic

end ClassGroupCarrier

end JacobiSumStickelberger
