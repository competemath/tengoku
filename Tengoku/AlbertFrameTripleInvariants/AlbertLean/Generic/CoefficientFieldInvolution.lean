import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.NestedReciprocalField

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms fieldEquiv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms fieldEquiv_twice` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms fieldEquiv_commutes_reciprocal` (it only prints; the queue checks the axioms of every declaration). -/

/-! Extend a coefficient involution to the existing rational-function field.
It fixes the indeterminate and commutes with reciprocal substitution whenever
the reciprocal parameter is fixed. No additional field tower is introduced. -/

noncomputable section
namespace AlbertLean.Generic.CoefficientFieldInvolution

open Polynomial AlbertLean.Generic.NestedReciprocalField

variable {B : Type*} [Field B] (e : B ≃+* B)

def numerator : Polynomial B →+* Omega B :=
  (algebraMap (Polynomial B) (Omega B)).comp (Polynomial.mapRingHom e.toRingHom)

/--
@isnad1 id=injectiv.0h2v.s8.fce0154264f7 from=translated src=- shape=5223c867 vocab=4a764022
-/
theorem numerator_injective : Function.Injective (numerator e) :=
  (polynomialMap_injective B).comp (Polynomial.map_injective _ e.injective)

def fieldHom : Omega B →+* Omega B := IsFractionRing.lift (numerator_injective e)

/--
@isnad1 id=eq.0h3v.s10.50aa660db202 from=translated src=- shape=8e6c6653 vocab=5e4954a0
-/
@[simp] theorem fieldHom_polynomial (p : Polynomial B) :
    fieldHom e (algebraMap (Polynomial B) (Omega B) p) = numerator e p :=
  IsFractionRing.lift_algebraMap _ p

/--
@isnad1 id=eq.0h3v.s10.b95de7c1e745 from=translated src=- shape=c5af5ce2 vocab=114bdee4
-/
@[simp] theorem fieldHom_base (b : B) :
    fieldHom e (algebraMap B (Omega B) b) = algebraMap B (Omega B) (e b) := by
  rw [← polynomialMap_C B b, fieldHom_polynomial]
  simp [numerator]

/--
@isnad1 id=eq.0h2v.s9.d6290c30599d from=translated src=- shape=f1d920b3 vocab=785b2603
-/
@[simp] theorem fieldHom_T : fieldHom e (T B) = T B := by
  simp [T, numerator]

/--
@isnad1 id=eq.1h2v.s10.a04dc26a52b6 from=translated src=- shape=524277b3 vocab=c52d64b4
-/
theorem fieldHom_involutive (he : Function.Involutive e) :
    (fieldHom e).comp (fieldHom e) = RingHom.id (Omega B) := by
  apply IsFractionRing.ringHom_ext (A := Polynomial B)
  have h : ((fieldHom e).comp (fieldHom e)).comp
      (algebraMap (Polynomial B) (Omega B)) =
      algebraMap (Polynomial B) (Omega B) := by
    ext b
    · simp only [RingHom.comp_apply, polynomialMap_C, fieldHom_base]
      rw [he b]
    · change fieldHom e (fieldHom e (T B)) = T B
      rw [fieldHom_T, fieldHom_T]
  exact fun p => RingHom.congr_fun h p

def fieldEquiv (he : Function.Involutive e) : Omega B ≃+* Omega B where
  toFun := fieldHom e
  invFun := fieldHom e
  left_inv z := RingHom.congr_fun (fieldHom_involutive e he) z
  right_inv z := RingHom.congr_fun (fieldHom_involutive e he) z
  map_add' := map_add _
  map_mul' := map_mul _

/--
@isnad1 id=eq.1h3v.s11.7ae9c53dbb6d from=translated src=- shape=5195d235 vocab=7809b248
-/
@[simp] theorem fieldEquiv_base (he : Function.Involutive e) (b : B) :
    fieldEquiv e he (algebraMap B (Omega B) b) = algebraMap B (Omega B) (e b) :=
  fieldHom_base e b

/--
@isnad1 id=eq.1h2v.s11.280f8f0811d2 from=translated src=- shape=a96f93b2 vocab=8b5f4a04
-/
@[simp] theorem fieldEquiv_T (he : Function.Involutive e) :
    fieldEquiv e he (T B) = T B := fieldHom_T e

/--
@isnad1 id=eq.1h3v.s12.334677da941f from=translated src=- shape=08f592c6 vocab=59afbc00
-/
@[simp] theorem fieldEquiv_twice (he : Function.Involutive e) (z : Omega B) :
    fieldEquiv e he (fieldEquiv e he z) = z :=
  RingHom.congr_fun (fieldHom_involutive e he) z

/-- Commutation reduces to constants and the single indeterminate.
@isnad1 id=eq.2h3v.s10.9994894633a3 from=translated src=- shape=49b87a27 vocab=a5267830
-/
theorem fieldHom_commutes_reciprocal (m : B) (hm : m ≠ 0) (hem : e m = m) :
    (fieldHom e).comp (reciprocalHom B m hm) =
      (reciprocalHom B m hm).comp (fieldHom e) := by
  apply IsFractionRing.ringHom_ext (A := Polynomial B)
  have h : ((fieldHom e).comp (reciprocalHom B m hm)).comp
      (algebraMap (Polynomial B) (Omega B)) =
      ((reciprocalHom B m hm).comp (fieldHom e)).comp
        (algebraMap (Polynomial B) (Omega B)) := by
    ext b
    · simp only [RingHom.comp_apply, polynomialMap_C, reciprocalHom_base,
        fieldHom_base]
    · change fieldHom e (reciprocalHom B m hm (T B)) =
        reciprocalHom B m hm (fieldHom e (T B))
      rw [reciprocalHom_T, map_div₀, fieldHom_base, hem, fieldHom_T,
        reciprocalHom_T]
  exact fun p => RingHom.congr_fun h p

/--
@isnad1 id=commute.3h3v.s12.5ecaf47c98c4 from=translated src=- shape=8009eaf7 vocab=87d56a8e
-/
theorem fieldEquiv_commutes_reciprocal (he : Function.Involutive e)
    (m : B) (hm : m ≠ 0) (hem : e m = m) :
    Function.Commute (fieldEquiv e he) (reciprocalEquiv B m hm) :=
  fun z => RingHom.congr_fun (fieldHom_commutes_reciprocal e m hm hem) z

end AlbertLean.Generic.CoefficientFieldInvolution
