/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Numerical.Mukai.SqrtToddK3
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Numerical.Mukai.VectorClass
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Numerical.GrothendieckGroup.MukaiVector

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The Mukai class specialized to numerical K3 data -/

open Finset
universe u v

namespace AlgebraicGeometry.Numerical.K3

open NumericalVarietyData

variable {A : Type u} [CommRing A] [Algebra ℚ A]
variable {N : Type v} [AddCommGroup N]
variable {V : NumericalVarietyData 2 A N}

/--
@isnad1 id=eq.1h4v.s6.71a8d1bf1fb4 from=translated src=- shape=fb6bbff9 vocab=3092e3a6
-/
theorem mukaiComp_one (hK3 : IsK3 V) (E : N) : V.mukaiComp E 1 = V.chComp E 1 := by
  rw [mukaiComp, Finset.sum_range_succ, Finset.sum_range_one]
  simp [K3.sqrtToddComp_one hK3]

/--
@isnad1 id=eq.1h4v.s7.f66985a7a2b6 from=translated src=- shape=2c1f690c vocab=b50b3567
-/
theorem mukaiComp_two (hK3 : IsK3 V) (E : N) :
    V.mukaiComp E 2 =
      V.chComp E 2 + algebraMap ℚ A (V.rank E : ℚ) * V.sqrtToddComp 2 := by
  simp [mukaiComp, Finset.sum_range_succ, K3.sqrtToddComp_one hK3, V.chComp_zero]
  ring

/--
@isnad1 id=eq.1h4v.s7.bc6d7d376ae7 from=translated src=- shape=fca6597b vocab=a4149a32
-/
theorem degree_mukaiComp_two (hK3 : IsK3 V) (E : N) :
    V.ring.degree (V.mukaiComp E 2) = mukaiS V E := by
  rw [mukaiComp_two hK3, map_add, NumericalRingData.degree_algebraMap_mul,
    K3.degree_sqrtToddComp_two hK3, mukaiS]
  ring

section Comparison

variable {Λ : Type*} [AddCommGroup Λ] (D : IntegralMukaiData V Λ)

/--
@isnad1 id=eq.0h6v.s6.88dd5bc2c811 from=translated src=- shape=4f5ec0ce vocab=2e278095
-/
theorem mukaiVector_fst_eq (E : N) : (D.mukaiVector E).1 = V.rank E := rfl

/--
@isnad1 id=eq.1h7v.s9.cc400258955f from=translated src=- shape=ea413451 vocab=e5dc1aec
-/
theorem b_mukaiVector_snd_eq_degree (hK3 : IsK3 V) (E F : N) :
    ((D.b (D.mukaiVector E).2.1 (D.c₁ F) : ℤ) : ℚ) =
      V.ring.degree (V.mukaiComp E 1 * V.chComp F 1) := by
  rw [mukaiComp_one hK3]
  exact D.b_spec E F

/--
@isnad1 id=eq.2h6v.s7.c55de8b1e015 from=translated src=- shape=d20ff574 vocab=93e3ca2e
-/
theorem mukaiVector_thd_eq_degree (hHRR : V.SatisfiesHRR) (hK3 : IsK3 V) (E : N) :
    (((D.mukaiVector E).2.2 : ℤ) : ℚ) = V.ring.degree (V.mukaiComp E 2) := by
  rw [degree_mukaiComp_two hK3]
  exact mukaiSInt_spec V hHRR hK3 E

end Comparison

end AlgebraicGeometry.Numerical.K3
