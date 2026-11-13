import Tengoku.Rankamplificationtotient.RankAmplification.PSeriesEuler
import Tengoku.Rankamplificationtotient.RankAmplification.PrimeSums
import Tengoku.Seed.Analysis.Complex.ExponentialBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Comparing the Mertens product with a convergent Euler product The finite product at exponent one is compared factor-by-factor with the convergent product at exponent `1 + δ`. -/

namespace RankAmplification

open scoped BigOperators Nat.Prime

noncomputable section

/-- A real-variable inequality used in the factorwise Euler-product comparison.-/
theorem inverse_one_sub_le_exp_mul_inverse_one_sub {a b t : ℝ}
    (hb : 0 ≤ b) (hba : b ≤ a) (ha : a ≤ 1 / 2) (ht : 0 ≤ t)
    (hdiff : a - b ≤ a * t) :
    (1 - a)⁻¹ ≤ Real.exp (2 * a * t) * (1 - b)⁻¹ := by
  have ha0 : 0 ≤ a := hb.trans hba
  have hda : 0 < 1 - a := by linarith
  have hdb : 0 < 1 - b := by linarith
  have hat : 0 ≤ a * t := mul_nonneg ha0 ht
  have hscale : 1 ≤ 2 * (1 - a) := by linarith
  have hquot : (a - b) / (1 - a) ≤ 2 * a * t := by
    apply (div_le_iff₀ hda).2
    calc
      a - b ≤ a * t := hdiff
      _ ≤ (2 * a * t) * (1 - a) := by
        have hscale0 : 0 ≤ 2 * (1 - a) - 1 := sub_nonneg.mpr hscale
        nlinarith [mul_nonneg hat hscale0]
  have hratio : (1 - b) / (1 - a) ≤ Real.exp (2 * a * t) := by
    calc
      (1 - b) / (1 - a) = 1 + (a - b) / (1 - a) := by
        field_simp
        ring
      _ ≤ 1 + 2 * a * t := add_le_add le_rfl hquot
      _ ≤ Real.exp (2 * a * t) := by simpa [add_comm] using Real.add_one_le_exp (2 * a * t)
  calc
    (1 - a)⁻¹ = ((1 - b) / (1 - a)) * (1 - b)⁻¹ := by
      field_simp
    _ ≤ Real.exp (2 * a * t) * (1 - b)⁻¹ :=
      mul_le_mul_of_nonneg_right hratio (inv_nonneg.mpr hdb.le)

/-- One prime factor at exponent one is controlled by its factor at exponent `1 + δ`.-/
theorem mertensFactor_le_softenedFactor {p : ℕ} (hp : p.Prime) {δ : ℝ} (hδ : 0 ≤ δ) :
    (1 - (p : ℝ)⁻¹)⁻¹ ≤
      Real.exp (2 * δ * (Real.log p / p)) *
        (1 - (p : ℝ) ^ (-(1 + δ)))⁻¹ := by
  let P : ℝ := p
  let a : ℝ := P⁻¹
  let b : ℝ := P ^ (-(1 + δ))
  let t : ℝ := δ * Real.log P
  have hP1 : 1 < P := by
    change (1 : ℝ) < (p : ℝ)
    exact_mod_cast hp.one_lt
  have hP0 : 0 < P := zero_lt_one.trans hP1
  have hb : 0 ≤ b := Real.rpow_nonneg hP0.le _
  have hba : b ≤ a := by
    rw [show a = P ^ (-1 : ℝ) by simp [a, Real.rpow_neg_one]]
    exact Real.rpow_le_rpow_of_exponent_le hP1.le (by linarith)
  have ha : a ≤ 1 / 2 := by
    have hP2 : (2 : ℝ) ≤ P := by
      change (2 : ℝ) ≤ (p : ℝ)
      exact_mod_cast hp.two_le
    simpa [a, one_div] using (inv_le_inv₀ hP0 zero_lt_two).2 hP2
  have ht : 0 ≤ t := mul_nonneg hδ (Real.log_nonneg hP1.le)
  have hbform : b = a * Real.exp (-t) := by
    dsimp only [a, b, t]
    rw [Real.rpow_def_of_pos hP0]
    rw [show P⁻¹ = Real.exp (-Real.log P) by
      rw [Real.exp_neg, Real.exp_log hP0]]
    rw [← Real.exp_add]
    congr 1
    ring
  have hone : 1 - Real.exp (-t) ≤ t := by
    linarith [Real.add_one_le_exp (-t)]
  have hdiff : a - b ≤ a * t := by
    rw [hbform]
    calc
      a - a * Real.exp (-t) = a * (1 - Real.exp (-t)) := by ring
      _ ≤ a * t := mul_le_mul_of_nonneg_left hone (inv_nonneg.mpr hP0.le)
  have hmain := inverse_one_sub_le_exp_mul_inverse_one_sub hb hba ha ht hdiff
  have hexp : 2 * (p : ℝ)⁻¹ * (δ * Real.log p) =
      2 * δ * (Real.log p * (p : ℝ)⁻¹) := by ring
  simp only [a, b, t, P] at hmain
  rw [hexp] at hmain
  simpa only [a, b, t, P, div_eq_mul_inv] using hmain

/-- Product form of the factorwise comparison.-/
theorem mertensProduct_le_exp_mul_softened (R : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    mertensProduct R ≤
      Real.exp (2 * δ * primeLogReciprocalSum R) * softenedMertensProduct R (1 + δ) := by
  unfold mertensProduct softenedMertensProduct
  calc
    (∏ p ∈ Nat.primesLE R, (1 - (p : ℝ)⁻¹)⁻¹) ≤
        ∏ p ∈ Nat.primesLE R,
          (Real.exp (2 * δ * (Real.log p / p)) *
            (1 - (p : ℝ) ^ (-(1 + δ)))⁻¹) := by
      apply Finset.prod_le_prod
      · intro p hp
        have pp := Nat.prime_of_mem_primesLE hp
        exact le_of_lt (inv_pos.mpr (sub_pos.mpr
          (inv_lt_one_of_one_lt₀ (by exact_mod_cast pp.one_lt))))
      · intro p hp
        exact mertensFactor_le_softenedFactor (Nat.prime_of_mem_primesLE hp) hδ
    _ = Real.exp (2 * δ * primeLogReciprocalSum R) *
        ∏ p ∈ Nat.primesLE R, (1 - (p : ℝ) ^ (-(1 + δ)))⁻¹ := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum]
      simp only [← Finset.mul_sum, primeLogReciprocalSum]

/-- The correction exponent is uniformly bounded at `δ = 1 / log R`.-/
theorem mertens_correction_le {R : ℕ} (hR : 3 ≤ R) :
    2 * (Real.log R)⁻¹ * primeLogReciprocalSum R ≤ 4 * Real.log 4 := by
  have hR2 : 2 ≤ R := hR.trans' (by norm_num)
  have hRpos : 0 < (R : ℝ) := by positivity
  have hlog : 1 < Real.log (R : ℝ) := by
    apply (Real.lt_log_iff_exp_lt hRpos).2
    exact Real.exp_one_lt_three.trans_le (by exact_mod_cast hR)
  have hlog0 : 0 < Real.log (R : ℝ) := zero_lt_one.trans hlog
  have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hprime := primeLogReciprocalSum_le hR2
  calc
    2 * (Real.log R)⁻¹ * primeLogReciprocalSum R ≤
        2 * (Real.log R)⁻¹ * (Real.log 4 * (1 + Real.log R)) :=
      mul_le_mul_of_nonneg_left hprime (mul_nonneg (by norm_num) (inv_nonneg.mpr hlog0.le))
    _ = 2 * Real.log 4 * ((1 + Real.log R) / Real.log R) := by
      field_simp
    _ ≤ 2 * Real.log 4 * 2 := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hlog4)
      apply (div_le_iff₀ hlog0).2
      nlinarith
    _ = 4 * Real.log 4 := by ring

/-- Explicit Mertens-product upper bound, completing Lemma 2.2.-/
theorem mertensProduct_le_log (R : ℕ) (hR : 3 ≤ R) :
    mertensProduct R ≤ Real.exp (4 * Real.log 4) * (1 + Real.log R) := by
  have hlog : 0 < Real.log (R : ℝ) :=
    Real.log_pos (by exact_mod_cast lt_of_lt_of_le (by norm_num) hR)
  have hδ : 0 ≤ (Real.log (R : ℝ))⁻¹ := inv_nonneg.mpr hlog.le
  calc
    mertensProduct R ≤
        Real.exp (2 * (Real.log R)⁻¹ * primeLogReciprocalSum R) *
          softenedMertensProduct R (1 + (Real.log R)⁻¹) :=
      mertensProduct_le_exp_mul_softened R hδ
    _ ≤ Real.exp (4 * Real.log 4) *
          softenedMertensProduct R (1 + (Real.log R)⁻¹) := by
      apply mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mertens_correction_le hR))
      rw [← smoothRpowTsum_eq_softenedMertensProduct R (by positivity)]
      exact tsum_nonneg fun n ↦ Real.rpow_nonneg (Nat.cast_nonneg n.1) _
    _ ≤ Real.exp (4 * Real.log 4) *
          (1 + 1 / ((1 + (Real.log R)⁻¹) - 1)) := by
      gcongr
      exact softenedMertensProduct_le R _ (by simp [hlog])
    _ = Real.exp (4 * Real.log 4) * (1 + Real.log R) := by
      rw [show (1 + (Real.log R)⁻¹) - 1 = (Real.log R)⁻¹ by ring,
        one_div, inv_inv]

end

end RankAmplification
