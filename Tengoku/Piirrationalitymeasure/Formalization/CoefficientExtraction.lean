import Tengoku.Piirrationalitymeasure.Formalization.CoefficientSeries
import Tengoku.Piirrationalitymeasure.Formalization.CoefficientResidue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Exact positive coefficient extraction after the Mobius substitution, equation (4.5). -/

namespace PiIrrationality

set_option maxRecDepth 100000

open HahnSeries PowerSeries

local instance : CharZero (LaurentSeries ℚ) := algebraRat.charZero _

/--
@isnad1 id=eq.0h0v.s9.6a905f33309a from=translated src=- shape=41bf02fb vocab=9b6128d3
-/
theorem mobiusLaurent_denominator :
    25 - mobiusLaurent ^ 2 = -100 * single 1 1 / (1 - single 1 1) ^ 2 := by
  unfold mobiusLaurent
  field_simp [one_sub_laurentX_ne_zero]
  ring

/--
@isnad1 id=eq.0h0v.s11.3b49e55a571e from=translated src=- shape=254a71b5 vocab=8cec2196
-/
theorem mobiusLaurent_quartic :
    mobiusLaurent ^ 4 + 6 * mobiusLaurent ^ 2 + 25 =
      400 * (2 + 6 * single 1 1 + 9 * single 1 1 ^ 2 +
        6 * single 1 1 ^ 3 + 2 * single 1 1 ^ 4) / (1 - single 1 1) ^ 4 := by
  unfold mobiusLaurent
  field_simp [one_sub_laurentX_ne_zero]
  ring

/--
@isnad1 id=ne.0h0v.s7.d314dfbfb678 from=translated src=- shape=1df60f11 vocab=6a1af212
-/
theorem mobiusLaurent_denominator_ne_zero : 25 - mobiusLaurent ^ 2 ≠ 0 := by
  rw [mobiusLaurent_denominator]
  exact div_ne_zero (mul_ne_zero (by norm_num) laurentX_ne_zero)
    (pow_ne_zero _ one_sub_laurentX_ne_zero)

set_option maxHeartbeats 2000000 in
/--
@isnad1 id=eq.0h0v.s11.7b644cdcab2d from=translated src=- shape=9187b124 vocab=acb61c29
-/
theorem Sseries_coe_formula :
    (Sseries : LaurentSeries ℚ) =
      (1 + single 1 1) ^ 3714 *
        (2 + 6 * single 1 1 + 9 * single 1 1 ^ 2 +
          6 * single 1 1 ^ 3 + 2 * single 1 1 ^ 4) ^ 3714 / (1 - single 1 1) ^ 7430 := by
  have h := congrArg (HahnSeries.ofPowerSeries ℤ ℚ) Sseries_clearing_identity
  simp only [PSeries, map_mul, map_pow, map_add, map_sub, map_ofNat, map_one,
    HahnSeries.ofPowerSeries_X] at h
  apply (eq_div_iff (pow_ne_zero _ one_sub_laurentX_ne_zero)).mpr
  exact h

set_option exponentiation.threshold 20000 in
private theorem mobius_base_collect {K : Type*} [Field K] [CharZero K]
    (u v x d : K) (hx : x ≠ 0) (hd : d ≠ 0) :
    (-5 * u / d) ^ 3714 * (400 * v / d ^ 4) ^ 3714 /
      (-100 * x / d ^ 2) ^ 5570 =
        (25 * 2 ^ 3716) * (u ^ 3714 * v ^ 3714 / d ^ 7430) / x ^ 5570 := by
  field_simp
  ring

set_option maxHeartbeats 2000000 in
/--
@isnad1 id=eq.0h0v.s10.c89bfab3a634 from=translated src=- shape=51151847 vocab=dcb0e650
-/
theorem mobiusLaurent_base_formula :
    mobiusLaurent ^ 3714 * (mobiusLaurent ^ 4 + 6 * mobiusLaurent ^ 2 + 25) ^ 3714 /
      (25 - mobiusLaurent ^ 2) ^ 5570 =
        (25 * 2 ^ 3716) * (Sseries : LaurentSeries ℚ) / single 1 1 ^ 5570 := by
  rw [Sseries_coe_formula, mobiusLaurent_quartic, mobiusLaurent_denominator]
  unfold mobiusLaurent
  exact mobius_base_collect (1 + single 1 1)
    (2 + 6 * single 1 1 + 9 * single 1 1 ^ 2 + 6 * single 1 1 ^ 3 + 2 * single 1 1 ^ 4)
    (single 1 1) (1 - single 1 1) laurentX_ne_zero one_sub_laurentX_ne_zero

private theorem density_power_factor {K : Type*} [Field K]
    (n : ℕ) (t q a d : K) (ha : a ≠ 0) :
    (5 * t ^ (2 * 1857 * n) * q ^ (3714 * n) / a ^ (5570 * n + 1)) * d =
      (5 * d / a) * (t ^ 3714 * q ^ 3714 / a ^ 5570) ^ n := by
  rw [show 2 * 1857 * n = 3714 * n by omega, pow_succ a (5570 * n)]
  simp only [pow_mul, mul_pow, div_pow]
  field_simp

/--
@isnad1 id=eq.0h0v.s10.12950c05e64e from=translated src=- shape=512e2fca vocab=fc8caaec
-/
theorem mobiusLaurent_prefactor :
    5 * laurentDerivation ℚ mobiusLaurent / (25 - mobiusLaurent ^ 2) =
      1 / (2 * single 1 1) := by
  rw [mobiusLaurent_derivation, mobiusLaurent_denominator]
  field_simp [laurentX_ne_zero, one_sub_laurentX_ne_zero]
  ring

/--
@isnad1 id=eq.0h2v.s8.f35862811c02 from=translated src=- shape=7cc0593e vocab=e6df06e1
-/
theorem laurent_single_div_X_pow (k : ℕ) (c : ℚ) :
    single (-((k : ℕ) : ℤ)) c = (c : LaurentSeries ℚ) / single 1 1 ^ k := by
  have h : (single (-(k : ℤ)) c : LaurentSeries ℚ) =
      HahnSeries.C c * single (-(k : ℤ)) 1 := by
    simp only [HahnSeries.C_apply, single_mul_single, zero_add, mul_one]
  rw [h, eq_ratCast, RatFunc.single_zpow, zpow_neg, zpow_natCast, div_eq_mul_inv]

/--
@isnad1 id=eq.0h1v.s8.3ca0d129c92f from=translated src=- shape=417f2481 vocab=b9acfc34
-/
theorem mobiusDensity_series (n : ℕ) :
    mobiusDensity n =
      single (-((5570 * n + 1 : ℕ) : ℤ)) (((25 * (2 : ℚ) ^ 3716) ^ n) / 2) *
        ((Sseries ^ n : PowerSeries ℚ) : LaurentSeries ℚ) := by
  rw [mobiusDensity, density_power_factor n _ _ _ _ mobiusLaurent_denominator_ne_zero,
    mobiusLaurent_prefactor, mobiusLaurent_base_formula, laurent_single_div_X_pow,
    PowerSeries.coe_pow]
  push_cast
  simp only [mul_pow, div_pow, ← pow_mul]
  rw [pow_succ (single 1 (1 : ℚ) : LaurentSeries ℚ) (5570 * n)]
  field_simp [laurentX_ne_zero]

/--
@isnad1 id=eq.0h1v.s7.1a8724e6ceab from=translated src=- shape=2d1540b8 vocab=fb7953fc
-/
theorem laurentCoeffRat_zero_eq_Sseries (n : ℕ) :
    laurentCoeffRat n 0 = (25 * (2 : ℚ) ^ 3716) ^ n / 2 * coeff (5570 * n) (Sseries ^ n) := by
  have h := mobiusDensity_residue n
  rw [mobiusDensity_series] at h
  change (single _ _ * ((Sseries ^ n : PowerSeries ℚ) : LaurentSeries ℚ)).coeff (-1) = _ at h
  rw [coeff_single_mul] at h
  have hi : -1 - (-((5570 * n + 1 : ℕ) : ℤ)) = ((5570 * n : ℕ) : ℤ) := by omega
  rw [hi, LaurentSeries.coeff_coe_powerSeries] at h
  exact h.symm

/--
@isnad1 id=lt.0h1v.s7.3963018ca2cf from=translated src=- shape=fd693309 vocab=88b06917
-/
theorem Sseries_diagonal_coeff_pos (n : ℕ) : 0 < coeff (5570 * n) (Sseries ^ n) := by
  by_cases hn : n = 0
  · subst n
    simp
  · exact Sseries_pow_coeff_pos (Nat.pos_of_ne_zero hn) _

/--
@isnad1 id=lt.0h1v.s4.46289d290da4 from=translated src=- shape=33d07d30 vocab=bda28b77
-/
theorem laurentCoeffRat_zero_pos (n : ℕ) : 0 < laurentCoeffRat n 0 := by
  rw [laurentCoeffRat_zero_eq_Sseries]
  exact mul_pos (by positivity) (Sseries_diagonal_coeff_pos n)

/--
@isnad1 id=eq.0h1v.s7.5bf12e2e7013 from=translated src=- shape=10b549a9 vocab=a3cea8ea
-/
theorem paper_pi_coeff_extraction (n : ℕ) :
    |-laurentCoeffRat n 0 / 2| =
      (25 * (2 : ℚ) ^ 3716) ^ n / 4 * coeff (5570 * n) (Sseries ^ n) := by
  rw [abs_div, abs_neg, abs_of_pos (laurentCoeffRat_zero_pos n),
    laurentCoeffRat_zero_eq_Sseries]
  norm_num only [abs_of_pos (by norm_num : (0 : ℚ) < 2)]
  generalize (25 * (2 : ℚ) ^ 3716) ^ n = a
  ring

end PiIrrationality
