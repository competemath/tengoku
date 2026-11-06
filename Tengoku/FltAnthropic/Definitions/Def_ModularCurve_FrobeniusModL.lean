import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0ModL
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_Correspondence
import Tengoku.FltAnthropic.Theorems.Thm_ModularCurve_pow_char_eq_qExpand_of_coeff_fixed
import Tengoku.FltAnthropic.Theorems.Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open HahnSeries IntermediateField AlgebraicCurve Polynomial

namespace ModularCurve

section ExpandSeam

variable {R : Type*} [CommRing R] (p : ℕ) [NeZero p]

theorem qExpand_ofPowerSeries_eq_expand (u : PowerSeries R) :
    qExpand R p (HahnSeries.ofPowerSeries ℤ R u)
      = HahnSeries.ofPowerSeries ℤ R (PowerSeries.expand p (NeZero.ne p) u) := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  ext k
  by_cases hpk : (p : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hpk
    rw [qExpand_coeff_mul]
    rcases lt_or_ge m 0 with hm | hm
    · have hpm : (p : ℤ) * m < 0 := mul_neg_of_pos_of_neg hp0 hm
      rw [ofPowerSeries_coeff_of_neg _ hm, ofPowerSeries_coeff_of_neg _ hpm]
    · lift m to ℕ using hm with m
      have hcast : ((p : ℤ) * (m : ℤ)) = ((p * m : ℕ) : ℤ) := by push_cast; ring
      rw [HahnSeries.ofPowerSeries_apply_coeff, hcast, HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_expand_mul]
  · rw [qExpand_coeff_of_not_dvd p _ hpk]
    rcases lt_or_ge k 0 with hk | hk
    · exact (ofPowerSeries_coeff_of_neg _ hk).symm
    · lift k to ℕ using hk with k
      rw [HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_expand_of_not_dvd p (NeZero.ne p) u
          (fun ⟨m, hm⟩ => hpk ⟨m, by exact_mod_cast hm⟩)]

end ExpandSeam

section KeyLemma

variable {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]

theorem pow_char_single_one_eq (n : ℤ) :
    (HahnSeries.single n (1 : R)) ^ p
      = coeffMap (frobenius R p) (qExpand R p (HahnSeries.single n (1 : R))) := by
  rw [HahnSeries.single_pow, one_pow, show (p • n : ℤ) = (p : ℤ) * n from nsmul_eq_mul p n,
    qExpand_single, coeffMap_single, show frobenius R p 1 = 1 from map_one _]

theorem pow_char_ofPowerSeries_eq (u : PowerSeries R) :
    (HahnSeries.ofPowerSeries ℤ R u) ^ p
      = coeffMap (frobenius R p) (qExpand R p (HahnSeries.ofPowerSeries ℤ R u)) := by
  haveI : ExpChar R p := ExpChar.prime (Fact.out : p.Prime)
  rw [qExpand_ofPowerSeries_eq_expand p u, coeffMap_ofPowerSeries, ← map_pow]
  congr 1
  exact (MvPowerSeries.map_frobenius_expand p (NeZero.ne p) (f := u)).symm

theorem pow_char_eq_coeffMap_frobenius_qExpand (s : LaurentSeries R) :
    s ^ p = coeffMap (frobenius R p) (qExpand R p s) := by
  conv_lhs => rw [← LaurentSeries.single_order_mul_powerSeriesPart s]
  conv_rhs => rw [← LaurentSeries.single_order_mul_powerSeriesPart s]
  rw [mul_pow, map_mul, map_mul, pow_char_single_one_eq p s.order]
  congr 1
  exact pow_char_ofPowerSeries_eq p s.powerSeriesPart

end KeyLemma

section FrobeniusIdentity

variable (K : Type*) [Field K] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]

theorem intCast_pow_char_eq (n : ℤ) : ((n : K) : K) ^ ℓ = (n : K) := by
  have h : (frobenius K ℓ).comp (Int.castRingHom K) = Int.castRingHom K := RingHom.ext_int _ _
  exact (RingHom.congr_fun h n :)

omit [Fact ℓ.Prime] in

theorem charP_laurentSeriesC : CharP (LaurentSeries K) ℓ :=
  charP_of_injective_algebraMap (algebraMap K (LaurentSeries K)).injective ℓ

end FrobeniusIdentity

section FrobeniusEndomorphism

variable (K : Type*) [Field K] (N : ℕ) (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]

end FrobeniusEndomorphism

section PlacesDivisors

variable (K : Type*) [Field K] (N : ℕ) (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]

end PlacesDivisors

section Jacobian

variable (K : Type*) [Field K] (N : ℕ) (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]

variable {K N ℓ}

end Jacobian

end ModularCurve

end
