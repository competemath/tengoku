import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_MvPolynomial_CrossingQuotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace MvPolynomial

namespace CrossingQuotient

variable {W : Type*} [CommRing W] (t : W)

abbrev U : CrossingQuotient W t := mk t (X 0)

abbrev V : CrossingQuotient W t := mk t (X 1)

/--
@isnad1 id=eq.0h2v.s11.b20640e32dad from=translated src=- shape=5bba5d13 vocab=94752f60
-/
theorem U_mul_V : U t * V t = algebraMap W (CrossingQuotient W t) t := mk_X_mul_mk_X t

/--
@isnad1 id=eq.1h5v.s9.110ea44ba9ba from=translated src=- shape=2891ca1e vocab=50b3b652
-/
theorem aeval_rel_eq_zero {A : Type*} [CommRing A] [Algebra W A] (a b : A)
    (h : a * b = algebraMap W A t) :
    aeval ![a, b] (X 0 * X 1 - C t : MvPolynomial (Fin 2) W) = 0 := by
  rw [map_sub, map_mul, aeval_X, aeval_X, aeval_C]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [h, sub_self]

def lift {A : Type*} [CommRing A] [Algebra W A] (a b : A) (h : a * b = algebraMap W A t) :
    CrossingQuotient W t →ₐ[W] A :=
  Ideal.Quotient.liftₐ (Ideal.span {(X 0 * X 1 - C t : MvPolynomial (Fin 2) W)}) (aeval ![a, b])
    (fun p hp => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hp
      rw [map_mul, aeval_rel_eq_zero t a b h, mul_zero])

/--
@isnad1 id=eq.1h6v.s12.9c73489f35b9 from=translated src=- shape=59ff86c1 vocab=22e9eb24
-/
theorem lift_mk {A : Type*} [CommRing A] [Algebra W A] (a b : A) (h : a * b = algebraMap W A t)
    (p : MvPolynomial (Fin 2) W) : lift t a b h (mk t p) = aeval ![a, b] p := rfl

/--
@isnad1 id=eq.1h5v.s11.2a08e4f666d4 from=translated src=- shape=fecec6d4 vocab=2f237833
-/
@[simp] theorem lift_U {A : Type*} [CommRing A] [Algebra W A] (a b : A)
    (h : a * b = algebraMap W A t) : lift t a b h (U t) = a := by
  rw [lift_mk, aeval_X]; rfl

/--
@isnad1 id=eq.1h5v.s11.7c46af5e3bdc from=translated src=- shape=e3874679 vocab=e951512c
-/
@[simp] theorem lift_V {A : Type*} [CommRing A] [Algebra W A] (a b : A)
    (h : a * b = algebraMap W A t) : lift t a b h (V t) = b := by
  rw [lift_mk, aeval_X]; rfl

def resolutionChart (e : ℕ) (i : Fin e) : CrossingQuotient W (t ^ e) →ₐ[W] CrossingQuotient W t :=
  lift (t ^ e) (algebraMap W _ (t ^ (i : ℕ)) * U t) (algebraMap W _ (t ^ (e - 1 - i)) * V t) (by
    have hi : (i : ℕ) + (e - 1 - i) + 1 = e := by have := i.2; omega
    rw [mul_mul_mul_comm, U_mul_V, ← map_mul, ← map_mul, ← pow_add, ← pow_succ, hi])

/--
@isnad1 id=eq.0h4v.s12.8053de71689c from=translated src=- shape=751a6f46 vocab=d207bcef
-/
theorem resolutionChart_U (e : ℕ) (i : Fin e) :
    resolutionChart t e i (U (t ^ e)) = algebraMap W _ (t ^ (i : ℕ)) * U t := lift_U _ _ _ _

/--
@isnad1 id=eq.0h4v.s12.d0f81b0c665b from=translated src=- shape=afaeb59f vocab=198664b0
-/
theorem resolutionChart_V (e : ℕ) (i : Fin e) :
    resolutionChart t e i (V (t ^ e)) = algebraMap W _ (t ^ (e - 1 - i)) * V t := lift_V _ _ _ _

def transitionUp : CrossingQuotient W t →ₐ[W] Localization.Away (V t) :=
  lift t (IsLocalization.Away.invSelf (V t))
    (algebraMap W _ t * algebraMap (CrossingQuotient W t) _ (V t)) (by
      rw [mul_left_comm, mul_comm (IsLocalization.Away.invSelf (V t)),
        IsLocalization.Away.mul_invSelf, mul_one,
        IsScalarTower.algebraMap_apply W (CrossingQuotient W t) (Localization.Away (V t))])

/--
@isnad1 id=eq.0h2v.s14.cdcf9684c8db from=translated src=- shape=60a2849c vocab=327db804
-/
theorem transitionUp_U :
    transitionUp t (U t) = IsLocalization.Away.invSelf (V t) := lift_U _ _ _ _

/--
@isnad1 id=eq.0h2v.s15.4d2e5d6ddb01 from=translated src=- shape=bc7c7474 vocab=84b15214
-/
theorem transitionUp_V : transitionUp t (V t) =
    algebraMap W _ t * algebraMap (CrossingQuotient W t) (Localization.Away (V t)) (V t) :=
  lift_V _ _ _ _

def transitionDown : CrossingQuotient W t →ₐ[W] Localization.Away (U t) :=
  lift t (algebraMap W _ t * algebraMap (CrossingQuotient W t) _ (U t))
    (IsLocalization.Away.invSelf (U t)) (by
      rw [mul_assoc, IsLocalization.Away.mul_invSelf, mul_one,
        IsScalarTower.algebraMap_apply W (CrossingQuotient W t) (Localization.Away (U t))])

/--
@isnad1 id=eq.0h2v.s15.17b149cc9e7a from=translated src=- shape=bc7c7474 vocab=6eaa5eac
-/
theorem transitionDown_U : transitionDown t (U t) =
    algebraMap W _ t * algebraMap (CrossingQuotient W t) (Localization.Away (U t)) (U t) :=
  lift_U _ _ _ _

/--
@isnad1 id=eq.0h2v.s14.a69e93f8226c from=translated src=- shape=60a2849c vocab=185d3f00
-/
theorem transitionDown_V :
    transitionDown t (V t) = IsLocalization.Away.invSelf (U t) := lift_V _ _ _ _

end CrossingQuotient

end MvPolynomial

end
