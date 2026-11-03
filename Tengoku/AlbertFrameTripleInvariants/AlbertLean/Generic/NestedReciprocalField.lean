import Tengoku.Seed.Algebra.Polynomial.Reverse
import Tengoku.Seed.Algebra.Polynomial.AlgebraMap
import Tengoku.Seed.RingTheory.Localization.FractionRing
import Tengoku.Seed.Algebra.MvPolynomial.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms reciprocalEquiv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms reciprocalEquiv_T` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms branchPolynomial_ne_zero` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Reciprocal involution on a nested rational function field

For an arbitrary field `B`, put `Omega = Frac(B[T])`.  Given `m != 0` in B,
this constructs the actual field involution `T |-> m/T`, fixing B.  The
nineteen-variable base field used by the generic chart is supplied below as
`B = Frac(k[BaseVar])`.
-/

noncomputable section

namespace AlbertLean.Generic.NestedReciprocalField

open Polynomial

universe u

section OneVariable

variable (B : Type u) [Field B]

abbrev Omega := FractionRing (Polynomial B)

def T : Omega B := algebraMap (Polynomial B) (Omega B) Polynomial.X

/--
@isnad1 id=injectiv.0h1v.s9.63df5488cc58 from=translated src=- shape=cbb71054 vocab=6d3a961f
-/
theorem polynomialMap_injective :
    Function.Injective (algebraMap (Polynomial B) (Omega B)) :=
  IsFractionRing.injective (Polynomial B) (Omega B)

/--
@isnad1 id=ne.0h1v.s7.8d21b89bd585 from=translated src=- shape=bbb5e9b9 vocab=9185a63a
-/
theorem T_ne_zero : T B ≠ 0 := by
  intro h
  apply Polynomial.X_ne_zero (R := B)
  apply polynomialMap_injective B
  simpa only [map_zero, T] using h

/--
@isnad1 id=eq.0h2v.s10.4e377f505b95 from=translated src=- shape=0662dc59 vocab=72d228e5
-/
@[simp] theorem polynomialMap_C (b : B) :
    algebraMap (Polynomial B) (Omega B) (Polynomial.C b) =
      algebraMap B (Omega B) b :=
  (IsScalarTower.algebraMap_apply B (Polynomial B) (Omega B) b).symm

/-- The branch numerator is nonzero for every constant `m`; this is the
degree-two coefficient argument in the polynomial ring, transported through
the injective fraction-field map.
@isnad1 id=ne.0h2v.s10.38a645ef8c85 from=translated src=- shape=1d297f9d vocab=2f00b7e1
-/
theorem branchPolynomial_ne_zero (m : B) :
    T B ^ 2 - algebraMap B (Omega B) m ≠ 0 := by
  intro h
  have hp : (Polynomial.X ^ 2 - Polynomial.C m : Polynomial B) = 0 := by
    apply (polynomialMap_injective B)
    rw [map_zero]
    simpa only [map_sub, map_pow, polynomialMap_C, T] using h
  have hc := congrArg (fun p : Polynomial B => p.coeff 2) hp
  simpa using hc

/--
@isnad1 id=eq.0h1v.s9.8609e3aec3ee from=translated src=- shape=efeec863 vocab=27889277
-/
theorem evalT_eq_algebraMap :
    Polynomial.eval₂RingHom (algebraMap B (Omega B)) (T B) =
      algebraMap (Polynomial B) (Omega B) := by
  ext <;> simp [T]

/--
@isnad1 id=injectiv.0h1v.s9.326df2175e93 from=translated src=- shape=7bb71a3d vocab=1e209b57
-/
theorem evalInvT_injective : Function.Injective
    (Polynomial.eval₂RingHom (algebraMap B (Omega B)) (T B)⁻¹) := by
  intro p q hpq
  suffices p - q = 0 by exact sub_eq_zero.mp this
  apply Polynomial.reverse_eq_zero.mp
  apply (polynomialMap_injective B)
  rw [map_zero]
  rw [← evalT_eq_algebraMap B]
  letI : Invertible ((T B)⁻¹) := invertibleOfNonzero (inv_ne_zero (T_ne_zero B))
  have hz : Polynomial.eval₂ (algebraMap B (Omega B)) ((T B)⁻¹) (p - q) = 0 := by
    change (Polynomial.eval₂RingHom (algebraMap B (Omega B)) ((T B)⁻¹)) (p-q) = 0
    rw [map_sub, hpq, sub_self]
  have hrev := (Polynomial.eval₂_reverse_eq_zero_iff
    (algebraMap B (Omega B)) ((T B)⁻¹) (p - q)).2 hz
  change Polynomial.eval₂ (algebraMap B (Omega B)) (T B) (p - q).reverse = 0
  simpa only [invOf_eq_inv, inv_inv] using hrev

def scale (m : B) : Polynomial B →+* Polynomial B :=
  Polynomial.compRingHom (Polynomial.C m * Polynomial.X)

/--
@isnad1 id=injectiv.1h2v.s7.0e49f759c25d from=translated src=- shape=1e6a7049 vocab=318b822d
-/
theorem scale_injective (m : B) (hm : m ≠ 0) :
    Function.Injective (scale B m) := by
  intro p q hpq
  apply sub_eq_zero.mp
  apply (Polynomial.comp_C_mul_X_eq_zero_iff
    (p := p - q) (mem_nonZeroDivisors_iff_ne_zero.mpr hm)).mp
  change (p - q).comp (Polynomial.C m * Polynomial.X) = 0
  rw [Polynomial.sub_comp]
  change scale B m p - scale B m q = 0
  exact sub_eq_zero.mpr hpq

def numeratorMap (m : B) : Polynomial B →+* Omega B :=
  Polynomial.eval₂RingHom (algebraMap B (Omega B))
    (algebraMap B (Omega B) m / T B)

/--
@isnad1 id=eq.0h2v.s9.a8c73e7e6687 from=translated src=- shape=a6d3683a vocab=11f2a0f8
-/
theorem numeratorMap_eq (m : B) : numeratorMap B m =
    (Polynomial.eval₂RingHom (algebraMap B (Omega B)) (T B)⁻¹).comp
      (scale B m) := by
  ext
  · simp [numeratorMap, scale]
  · simp [numeratorMap, scale, div_eq_mul_inv]

/--
@isnad1 id=injectiv.1h2v.s8.91cdc880aab9 from=translated src=- shape=349057ba vocab=72c49d32
-/
theorem numeratorMap_injective (m : B) (hm : m ≠ 0) :
    Function.Injective (numeratorMap B m) := by
  rw [numeratorMap_eq]
  exact (evalInvT_injective B).comp (scale_injective B m hm)

/-- The field endomorphism induced by `T |-> m/T`.-/
def reciprocalHom (m : B) (hm : m ≠ 0) : Omega B →+* Omega B :=
  IsFractionRing.lift (numeratorMap_injective B m hm)

/--
@isnad1 id=eq.1h3v.s10.9b3666ac4419 from=translated src=- shape=c017862e vocab=ef5baab8
-/
@[simp] theorem reciprocalHom_algebraMap (m : B) (hm : m ≠ 0)
    (p : Polynomial B) :
    reciprocalHom B m hm (algebraMap (Polynomial B) (Omega B) p) =
      numeratorMap B m p := by
  exact IsFractionRing.lift_algebraMap _ _

/--
@isnad1 id=eq.1h3v.s10.d524efc670a9 from=translated src=- shape=188f0b72 vocab=da1c1ec2
-/
@[simp] theorem reciprocalHom_base (m : B) (hm : m ≠ 0) (b : B) :
    reciprocalHom B m hm (algebraMap B (Omega B) b) =
      algebraMap B (Omega B) b := by
  rw [← polynomialMap_C B b, reciprocalHom_algebraMap]
  simp [numeratorMap]

/--
@isnad1 id=eq.1h2v.s10.263f679a51fe from=translated src=- shape=6341ebd8 vocab=e96412c3
-/
@[simp] theorem reciprocalHom_T (m : B) (hm : m ≠ 0) :
    reciprocalHom B m hm (T B) = algebraMap B (Omega B) m / T B := by
  simp [T, numeratorMap]

/--
@isnad1 id=eq.1h2v.s9.2653bd4c135a from=translated src=- shape=67708eb9 vocab=8260ded7
-/
theorem reciprocalHom_involutive (m : B) (hm : m ≠ 0) :
    (reciprocalHom B m hm).comp (reciprocalHom B m hm) = RingHom.id _ := by
  apply IsFractionRing.ringHom_ext (A := Polynomial B)
  have h : ((reciprocalHom B m hm).comp (reciprocalHom B m hm)).comp
      (algebraMap (Polynomial B) (Omega B)) =
      algebraMap (Polynomial B) (Omega B) := by
    ext b
    · simp only [RingHom.comp_apply, polynomialMap_C, reciprocalHom_base]
    · change reciprocalHom B m hm (reciprocalHom B m hm (T B)) = T B
      rw [reciprocalHom_T, map_div₀, reciprocalHom_base, reciprocalHom_T]
      exact div_div_cancel₀ ((map_ne_zero (algebraMap B (Omega B))).mpr hm)
  intro p
  exact RingHom.congr_fun h p

/-- The actual reciprocal field automorphism.-/
def reciprocalEquiv (m : B) (hm : m ≠ 0) : Omega B ≃+* Omega B where
  toFun := reciprocalHom B m hm
  invFun := reciprocalHom B m hm
  left_inv x := by
    have h := RingHom.congr_fun (reciprocalHom_involutive B m hm) x
    exact h
  right_inv x := by
    have h := RingHom.congr_fun (reciprocalHom_involutive B m hm) x
    exact h
  map_add' := map_add _
  map_mul' := map_mul _

/--
@isnad1 id=eq.1h2v.s11.de5b653bc597 from=translated src=- shape=036d0aaa vocab=4c5da9e2
-/
@[simp] theorem reciprocalEquiv_T (m : B) (hm : m ≠ 0) :
    reciprocalEquiv B m hm (T B) = algebraMap B (Omega B) m / T B :=
  reciprocalHom_T B m hm

end OneVariable

section NineteenBaseVariables

variable (k : Type u) [Field k]

abbrev OffDiagonal := {ij : Fin 4 × Fin 4 // ij.1 ≠ ij.2}
/-- Four diagonal, three gauge, and twelve off-diagonal labels.-/
abbrev BaseVar := Fin 4 ⊕ (Fin 3 ⊕ OffDiagonal)
abbrev BasePolynomial := MvPolynomial BaseVar k
abbrev GenericBase := FractionRing (BasePolynomial k)
/-- The requested nested twenty-parameter field.-/
abbrev GenericOmega := Omega (GenericBase k)

end NineteenBaseVariables

end AlbertLean.Generic.NestedReciprocalField
