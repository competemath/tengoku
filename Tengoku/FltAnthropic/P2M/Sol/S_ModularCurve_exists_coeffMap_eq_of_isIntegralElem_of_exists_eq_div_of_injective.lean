import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LaurentCoeff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_exists_coeffMap_eq_of_isIntegralElem_of_exists_eq_div_of_injective.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_exists_coeffMap_eq_of_isIntegralElem_of_exists_eq_div_of_injective
set_option autoImplicit false

open ModularCurve

namespace GaussQExp

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S]

/--
@isnad1 id=injectiv.1h3v.s7.b9b889a30d7b from=translated src=- shape=e9a217a9 vocab=4399a17a
-/
lemma coeffMap_injective (φ : R →+* S) (hφ : Function.Injective φ) :
    Function.Injective (coeffMap φ : LaurentSeries R →+* LaurentSeries S) := by
  intro x y h
  ext k
  have := congrArg (fun z : LaurentSeries S => z.coeff k) h
  simp only [coeffMap_coeff] at this
  exact hφ this

/--
@isnad1 id=isintegr.0h1v.s5.500d91d5d131 from=translated src=- shape=46b8a2f7 vocab=d8d5bb8e
-/
lemma isIntegrallyClosed_laurentSeries [IsDomain R] [IsPrincipalIdealRing R] :
    IsIntegrallyClosed (LaurentSeries R) := by
  haveI : Nonempty (GCDMonoid (PowerSeries R)) := ⟨UniqueFactorizationMonoid.toGCDMonoid _⟩
  haveI : IsIntegrallyClosed (PowerSeries R) := GCDMonoid.toIsIntegrallyClosed
  refine isIntegrallyClosed_of_isLocalization (LaurentSeries R)
    (Submonoid.powers (PowerSeries.X : PowerSeries R)) ?_
  exact powers_le_nonZeroDivisors_of_noZeroDivisors PowerSeries.X_ne_zero

/--
@isnad1 id=ex.3h4v.s9.b8d87babdb30 from=translated src=- shape=17a25465 vocab=82bb5478
-/
theorem main [IsDomain R] [IsPrincipalIdealRing R] {K : Type*} [Field K] (φ : R →+* K)
    (hφ : Function.Injective φ) (y : LaurentSeries K)
    (hy : ∃ a b : LaurentSeries R, b ≠ 0 ∧ y = coeffMap φ a / coeffMap φ b)
    (hint : (coeffMap φ).IsIntegralElem y) :
    ∃ c : LaurentSeries R, coeffMap φ c = y := by
  set Φ : LaurentSeries R →+* LaurentSeries K := coeffMap φ with hΦ
  have hinj : Function.Injective Φ := coeffMap_injective φ hφ
  haveI := isIntegrallyClosed_laurentSeries (R := R)
  let F := FractionRing (LaurentSeries R)
  let ψ : F →+* LaurentSeries K := IsFractionRing.lift hinj
  obtain ⟨a, b, hb, rfl⟩ := hy
  set z : F := algebraMap (LaurentSeries R) F a / algebraMap (LaurentSeries R) F b with hz
  have hψz : ψ z = Φ a / Φ b := by
    simp only [hz, map_div₀, ψ, IsFractionRing.lift_algebraMap]
  obtain ⟨p, hpm, hp⟩ := hint
  have hzint : IsIntegral (LaurentSeries R) z := by
    refine ⟨p, hpm, ?_⟩
    apply ψ.injective
    rw [map_zero, Polynomial.hom_eval₂, hψz]
    have hcomp : ψ.comp (algebraMap (LaurentSeries R) F) = Φ := by
      ext x
      simp [ψ, IsFractionRing.lift_algebraMap]
    rw [hcomp]
    exact hp
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.mp hzint
  refine ⟨c, ?_⟩
  have := congrArg ψ hc
  rw [hψz] at this
  simpa [ψ, IsFractionRing.lift_algebraMap] using this

end GaussQExp

/--
@isnad1 id=ex.3h4v.s9.b8d87babdb30 from=translated src=- shape=17a25465 vocab=82bb5478
-/
theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] (φ : R →+* K) (hφ : Function.Injective φ)
    (y : LaurentSeries K)
    (hy : ∃ a b : LaurentSeries R, b ≠ 0 ∧ y = coeffMap φ a / coeffMap φ b)
    (hint : (coeffMap φ).IsIntegralElem y) :
    ∃ c : LaurentSeries R, coeffMap φ c = y :=
  GaussQExp.main φ hφ y hy hint
