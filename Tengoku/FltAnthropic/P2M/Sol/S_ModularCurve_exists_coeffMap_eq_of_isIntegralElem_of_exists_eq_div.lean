import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LaurentCoeff
import Tengoku.Seed.RingTheory.PowerSeries.Ideal
import Tengoku.Seed.RingTheory.Polynomial.RationalRoot
import Tengoku.Seed.RingTheory.IntegralClosure.IntegrallyClosed
import Tengoku.Seed.Algebra.GCDMonoid.IntegrallyClosed
import Tengoku.Seed.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_exists_coeffMap_eq_of_isIntegralElem_of_exists_eq_div.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_exists_coeffMap_eq_of_isIntegralElem_of_exists_eq_div

open ModularCurve

private lemma coeffMap_intCast_injective_s18 :
    Function.Injective (ModularCurve.coeffMap (Int.castRingHom ℚ) : LaurentSeries ℤ →+* LaurentSeries ℚ) := by
  intro x y h
  ext k
  have := congrArg (fun z : LaurentSeries ℚ => z.coeff k) h
  simp only [ModularCurve.coeffMap_coeff, eq_intCast] at this
  exact_mod_cast this

private lemma isIntegrallyClosed_laurentSeries_int_s18 : IsIntegrallyClosed (LaurentSeries ℤ) := by
  haveI : Nonempty (GCDMonoid (PowerSeries ℤ)) := ⟨UniqueFactorizationMonoid.toGCDMonoid _⟩
  haveI : IsIntegrallyClosed (PowerSeries ℤ) := GCDMonoid.toIsIntegrallyClosed
  refine isIntegrallyClosed_of_isLocalization (LaurentSeries ℤ) (Submonoid.powers (PowerSeries.X : PowerSeries ℤ)) ?_
  exact powers_le_nonZeroDivisors_of_noZeroDivisors PowerSeries.X_ne_zero

/--
@isnad1 id=ex.2h1v.s9.d0dc479fb36d from=translated src=- shape=f6c6b98f vocab=ab8bb0ce
-/
theorem solution (y : LaurentSeries ℚ)
    (hy : ∃ a b : LaurentSeries ℤ, b ≠ 0 ∧ y = ModularCurve.coeffMap (Int.castRingHom ℚ) a / ModularCurve.coeffMap (Int.castRingHom ℚ) b)
    (hint : (ModularCurve.coeffMap (Int.castRingHom ℚ)).IsIntegralElem y) :
    ∃ c : LaurentSeries ℤ, ModularCurve.coeffMap (Int.castRingHom ℚ) c = y := by
  set φ : LaurentSeries ℤ →+* LaurentSeries ℚ := ModularCurve.coeffMap (Int.castRingHom ℚ) with hφ
  have hinj : Function.Injective φ := coeffMap_intCast_injective_s18
  haveI := isIntegrallyClosed_laurentSeries_int_s18
  let K := FractionRing (LaurentSeries ℤ)
  let ψ : K →+* LaurentSeries ℚ := IsFractionRing.lift hinj
  obtain ⟨a, b, hb, rfl⟩ := hy

  set z : K := algebraMap (LaurentSeries ℤ) K a / algebraMap (LaurentSeries ℤ) K b with hz
  have hψz : ψ z = φ a / φ b := by
    simp only [hz, map_div₀, ψ, IsFractionRing.lift_algebraMap]

  obtain ⟨p, hpm, hp⟩ := hint
  have hzint : IsIntegral (LaurentSeries ℤ) z := by
    refine ⟨p, hpm, ?_⟩
    have hψinj : Function.Injective ψ := ψ.injective
    apply hψinj
    rw [map_zero, Polynomial.hom_eval₂, hψz]
    have hcomp : ψ.comp (algebraMap (LaurentSeries ℤ) K) = φ := by
      ext x
      simp [ψ, IsFractionRing.lift_algebraMap]
    rw [hcomp]
    exact hp
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.mp hzint
  refine ⟨c, ?_⟩
  have := congrArg ψ hc
  rw [hψz] at this
  simpa [ψ, IsFractionRing.lift_algebraMap] using this
