import Tengoku.FourierJacobiCoreEvaluation.FourierJacobi.Algebra.EulerFactors
import Tengoku.Seed.Analysis.Complex.Basic
import Tengoku.Seed.Analysis.Real.Sqrt
import Tengoku.Seed.Tactic.Positivity
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Nonvanishing and the real interpretation of the principal answer

The assumptions here are exactly norm-one Satake parameters and 0 < t < 1.
In particular, the final denominator does not require any Weyl regularity.
-/

namespace FourierJacobi
namespace Algebra

/--
@isnad1 id=ne.1h1v.s4.fe0d29a6f828 from=translated src=- shape=cfb6b4ae vocab=40d8595a
-/
theorem unit_ne_zero {z : ℂ} (hz : ‖z‖ = 1) : z ≠ 0 := by
  intro h
  simp [h] at hz

/--
@isnad1 id=ne.2h2v.s5.82c67b5cb6b1 from=translated src=- shape=c43a3da8 vocab=1c533807
-/
theorem one_sub_mul_ne_zero_of_norm_lt_one {z x : ℂ}
    (hz : ‖z‖ = 1) (hx : ‖x‖ < 1) : 1 - z * x ≠ 0 := by
  intro he
  have hh := congrArg norm (sub_eq_zero.mp he)
  simp only [norm_one, norm_mul, hz, one_mul] at hh
  linarith

/--
@isnad1 id=ne.2h2v.s5.1b2d763d5d79 from=translated src=- shape=c43a3da8 vocab=19167fdc
-/
theorem one_add_mul_ne_zero_of_norm_lt_one {z x : ℂ}
    (hz : ‖z‖ = 1) (hx : ‖x‖ < 1) : 1 + z * x ≠ 0 := by
  have hn : ‖-z‖ = 1 := by simpa using hz
  simpa using one_sub_mul_ne_zero_of_norm_lt_one hn hx

/--
@isnad1 id=lt.2h1v.s5.13df3051392e from=translated src=- shape=57fd8941 vocab=62705b3a
-/
theorem coe_norm_lt_one {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    ‖(t : ℂ)‖ < 1 := by
  simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht₀] using ht₁

/--
@isnad1 id=ne.3h2v.s6.3cee3d8a5e47 from=translated src=- shape=9ce0b734 vocab=ca4c69d7
-/
theorem principal_final_denominator_ne_zero {t : ℝ} {d : ℂ}
    (ht₀ : 0 ≤ t) (ht₁ : t < 1) (hd : ‖d‖ = 1) :
    (1 + d * (t : ℂ)) * (1 + (t : ℂ) / d) ≠ 0 := by
  have hx := coe_norm_lt_one ht₀ ht₁
  have hi : ‖d⁻¹‖ = 1 := by simp [hd]
  exact mul_ne_zero (one_add_mul_ne_zero_of_norm_lt_one hd hx)
    (by simpa [div_eq_mul_inv, mul_comm] using
      one_add_mul_ne_zero_of_norm_lt_one hi hx)

/--
@isnad1 id=ne.3h3v.s5.2e4a0ad6c3ca from=translated src=- shape=27282035 vocab=073096bf
-/
theorem fourFactors_ne_zero {a b x : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hx : ‖x‖ < 1) :
    fourFactors a b x ≠ 0 := by
  have hai : ‖a⁻¹‖ = 1 := by simp [ha]
  have hbi : ‖b⁻¹‖ = 1 := by simp [hb]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero
    (one_sub_mul_ne_zero_of_norm_lt_one ha hx)
    (one_sub_mul_ne_zero_of_norm_lt_one hai hx))
    (one_sub_mul_ne_zero_of_norm_lt_one hb hx))
    (one_sub_mul_ne_zero_of_norm_lt_one hbi hx)

/--
@isnad1 id=eq.1h1v.s6.a56d1a82c88e from=translated src=- shape=d9f3c438 vocab=1b38f9b3
-/
theorem unit_satake_real {a : ℂ} (ha : ‖a‖ = 1) :
    a + 2 + a⁻¹ = ((2 + 2 * a.re : ℝ) : ℂ) := by
  rw [Complex.inv_eq_conj ha]
  apply Complex.ext <;> simp
  ring

/--
@isnad1 id=eq.1h2v.s6.416e74accac1 from=translated src=- shape=2968883c vocab=0ac63782
-/
theorem principal_final_denominator_normSq {t : ℝ} {d : ℂ} (hd : ‖d‖ = 1) :
    (1 + d * (t : ℂ)) * (1 + (t : ℂ) / d) =
      (Complex.normSq (1 + d * (t : ℂ)) : ℂ) := by
  rw [← Complex.mul_conj]
  congr 1
  simp [div_eq_mul_inv, Complex.inv_eq_conj hd, mul_comm]

/-- The branch of the square root used by the paper.-/
noncomputable def inverseSqrt (q : ℝ) : ℝ := (Real.sqrt q)⁻¹

/--
@isnad1 id=lt.1h1v.s4.9a2075e9aa09 from=translated src=- shape=35bd48ee vocab=8f07fb61
-/
theorem inverseSqrt_pos {q : ℝ} (hq : 1 < q) : 0 < inverseSqrt q := by
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by linarith))

/--
@isnad1 id=lt.1h1v.s4.402360ad66c4 from=translated src=- shape=3965f485 vocab=8f07fb61
-/
theorem inverseSqrt_lt_one {q : ℝ} (hq : 1 < q) : inverseSqrt q < 1 := by
  have hs : 1 < Real.sqrt q := by
    have h := Real.sq_sqrt (show 0 ≤ q by linarith)
    have hnon := Real.sqrt_nonneg q
    nlinarith
  exact (inv_lt_one₀ (by linarith : 0 < Real.sqrt q)).mpr hs

/--
@isnad1 id=eq.1h1v.s5.a60042a1f00e from=translated src=- shape=2a9d897f vocab=68a8c49f
-/
theorem inverseSqrt_sq {q : ℝ} (hq : 0 ≤ q) : inverseSqrt q ^ 2 = q⁻¹ := by
  rw [inverseSqrt, inv_pow, Real.sq_sqrt hq]

end Algebra
end FourierJacobi
