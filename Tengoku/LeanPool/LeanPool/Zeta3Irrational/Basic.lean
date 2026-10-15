/-
Copyright (c) 2026 Junqi Liu, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junqi Liu, Jujian Zhang
-/
module

public import Tengoku.LeanPool.LeanPool.Zeta3Irrational.LegendrePoly
public import Tengoku.LeanPool.LeanPool.Zeta3Irrational.D
public import Tengoku
import Tengoku.LeanPool.LeanPool.Zeta3Irrational.Bound
import Tengoku.LeanPool.LeanPool.Zeta3Irrational.Chebyshev
import Tengoku.LeanPool.LeanPool.Zeta3Irrational.LinearForm

/-!
# LeanPool.Zeta3Irrational.Basic
-/

@[expose] public section

namespace LeanPool.Zeta3Irrational

open scoped Nat
open BigOperators Polynomial

/-- The transformed three-variable form of the Apéry integral. -/
noncomputable abbrev JJ' (n : ℕ) : ℝ :=
    ∫ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    (x.2.1 * (1 - x.2.1) * x.2.2 * (1 - x.2.2) * x.1 * (1 - x.1) /
    (1 - (1 - x.2.1 * x.2.2) * x.1)) ^ n / (1 - (1 - x.2.1 * x.2.2) * x.1)

/-- The extended nonnegative integral associated to `JJ'`. -/
noncomputable abbrev JJENN (n : ℕ) : ENNReal :=
    ∫⁻ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1, ENNReal.ofReal
    ((x.2.1 * (1 - x.2.1) * x.2.2 * (1 - x.2.2) * x.1 * (1 - x.1) /
    (1 - (1 - x.2.1 * x.2.2) * x.1)) ^ n / (1 - (1 - x.2.1 * x.2.2) * x.1))

/--
@isnad1 id=lt.1h1v.s7.8808b498df11 from=translated src=- shape=246c2040 vocab=15740c9d
-/
lemma pos_aux (x : ℝ × ℝ × ℝ)
    (hx : (0 < x.1 ∧ x.1 < 1) ∧ (0 < x.2.1 ∧ x.2.1 < 1) ∧
      0 < x.2.2 ∧ x.2.2 < 1) :
    0 < (1 - (1 - x.2.1 * x.2.2) * x.1) := by
  simp only [sub_pos]
  suffices (1 - x.2.1 * x.2.2) * x.1 < x.1 by linarith
  simp_all

private lemma JJ'_nonneg (x : ℝ × ℝ × ℝ) (hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1)
    (n : ℕ) :
    0 ≤ (x.2.1 * (1 - x.2.1) * x.2.2 * (1 - x.2.2) * x.1 * (1 - x.1) /
      (1 - (1 - x.2.1 * x.2.2) * x.1)) ^ n /
      (1 - (1 - x.2.1 * x.2.2) * x.1) := by
  simp only [Set.mem_prod, Set.mem_Ioo] at hx
  obtain ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩, hz0, hz1⟩ := hx
  apply div_nonneg
  · apply pow_nonneg
    apply div_nonneg
    · apply mul_nonneg _ (by linarith)
      apply mul_nonneg _ (by linarith)
      apply mul_nonneg _ (by linarith)
      apply mul_nonneg _ (by linarith)
      apply mul_nonneg (by linarith) (by linarith)
    · linarith [pos_aux x ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩, hz0, hz1⟩]
  · linarith [pos_aux x ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩, hz0, hz1⟩]

/--
@isnad1 id=le.0h1v.s7.3869bb105a9f from=translated src=- shape=2f3031b2 vocab=5c3e95e0
-/
lemma JJENN_upper (n : ℕ) : JJENN n ≤
    ENNReal.ofReal (2 * (1 / 30) ^ n * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3) := by
  calc
  _ ≤ ∫⁻ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    ENNReal.ofReal ((1 / 30) ^ n / (1 - (1 - x.2.1 * x.2.2) * x.1)) := by
    rw [JJENN, ← MeasureTheory.lintegral_indicator (by measurability),
        ← MeasureTheory.lintegral_indicator (by measurability)]
    apply MeasureTheory.lintegral_mono
    intro x
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases h : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
    · simp only [h, ↓reduceIte]
      simp only [Set.mem_prod, Set.mem_Ioo] at h
      apply ENNReal.ofReal_le_ofReal
      rw [div_le_div_iff_of_pos_right]
      · apply pow_le_pow_left₀
        · apply div_nonneg
          · apply mul_nonneg _ (by linarith)
            apply mul_nonneg _ (by linarith)
            apply mul_nonneg _ (by linarith)
            apply mul_nonneg _ (by linarith)
            apply mul_nonneg (by linarith) (by linarith)
          · linarith [pos_aux x h]
        · suffices x.2.1 * (1 - x.2.1) * x.2.2 * (1 - x.2.2) * x.1 * (1 - x.1) /
            (1 - (1 - x.2.1 * x.2.2) * x.1) < (1 / 30 : ℝ)by linarith
          apply bound'' <;> linarith
      · exact pos_aux x h
    · simp only [h, ↓reduceIte, le_refl]
  _ = ENNReal.ofReal ((1 / 30) ^ n) *
      ∫⁻ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    ENNReal.ofReal (1 / (1 - (1 - x.2.1 * x.2.2) * x.1)) := by
    rw [← MeasureTheory.lintegral_const_mul]
    · rw [← MeasureTheory.lintegral_indicator (by measurability),
        ← MeasureTheory.lintegral_indicator (by measurability)]
      congr
      ext x
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases h : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · simp only [h, ↓reduceIte]
        rw [← ENNReal.ofReal_mul, ← mul_one_div]
        apply pow_nonneg (by norm_num)
      · simp only [h, ↓reduceIte]
    · apply Measurable.ennreal_ofReal
      apply Measurable.const_div
      apply Measurable.const_sub
      apply Measurable.mul _ measurable_fst
      apply Measurable.const_sub
      apply Measurable.mul
      · exact Measurable.fun_comp measurable_fst measurable_snd
      · exact Measurable.fun_comp measurable_snd measurable_snd
  _ = ENNReal.ofReal (2 * (1 / 30) ^ n * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3) := by
    have h := JENN_eq_triple 0 0
    simp only [pow_zero, mul_one] at h
    rw [← h, J_ENN_rr]
    simp only [one_div, inv_pow, zero_lt_one, Finset.Icc_eq_empty_of_lt, Finset.sum_empty, mul_zero,
      sub_zero]
    rw [← ENNReal.ofReal_mul (by norm_num), ← mul_assoc]
    nth_rw 2 [mul_comm]

/--
@isnad1 id=integrab.0h1v.s8.62705299a954 from=translated src=- shape=288a2943 vocab=7f11633a
-/
lemma integrableOn_JJ' (n : ℕ) : MeasureTheory.Integrable (fun (x : ℝ × ℝ × ℝ) ↦
    (x.2.1 * (1 - x.2.1) * x.2.2 * (1 - x.2.2) * x.1 * (1 - x.1) /
      (1 - (1 - x.2.1 * x.2.2) * x.1)) ^ n /
    (1 - (1 - x.2.1 * x.2.2) * x.1))
    (MeasureTheory.volume.restrict (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1)) := by
  rw [MeasureTheory.Integrable]
  constructor
  · apply AEMeasurable.aestronglyMeasurable
    measurability
  · rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    set k := _
    change k < ⊤
    have : k = JJENN n := by
      simp only [k, JJENN]
      rw [← MeasureTheory.lintegral_indicator (by measurability),
        ← MeasureTheory.lintegral_indicator (by measurability)]
      congr
      ext x
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
      · simp only [hx, ↓reduceIte, norm_mul, norm_div, Real.norm_eq_abs, norm_pow]
        simp only [Set.mem_prod, Set.mem_Ioo] at hx
        rw [ENNReal.ofReal_eq_ofReal_iff]
        · congr 3
          · rw [abs_eq_self.2, abs_eq_self.2, abs_eq_self.2, abs_eq_self.2, abs_eq_self.2,
              abs_eq_self.2] <;> nlinarith
          · simp only [abs_eq_self, sub_nonneg]
            exact (mul_le_of_le_one_left (by linarith) (by nlinarith)).trans (by linarith)
          · simp only [abs_eq_self, sub_nonneg]
            exact (mul_le_of_le_one_left (by linarith) (by nlinarith)).trans (by linarith)
        · positivity
        · exact JJ'_nonneg x hx n
      · simp only [hx, ↓reduceIte]
    rw [this]
    apply LE.le.trans_lt (JJENN_upper n)
    simp only [one_div, inv_pow, ENNReal.ofReal_lt_top]

/--
@isnad1 id=measurab.0h0v.s6.7766c8bc3228 from=translated src=- shape=22405c80 vocab=e497dd65
-/
lemma Measurable_one_div_aux :
    Measurable fun (x : ℝ × ℝ × ℝ) ↦
      ENNReal.ofReal (1 / (1 - (1 - x.2.1 * x.2.2) * x.1)) := by
  apply Measurable.ennreal_ofReal
  apply Measurable.const_div
  apply Measurable.const_sub
  apply Measurable.mul _ measurable_fst
  apply Measurable.const_sub
  apply Measurable.mul
  · exact Measurable.fun_comp measurable_fst measurable_snd
  · exact Measurable.fun_comp measurable_snd measurable_snd

/--
@isnad1 id=and.2h2v.s7.2f8f47612481 from=translated src=- shape=81d96b21 vocab=6ea7e3e1
-/
lemma ineq_aux (x : ℝ × ℝ) (z : ℝ)
    (hx : (0 < x.1 ∧ x.1 < 1) ∧ 0 < x.2 ∧ x.2 < 1) (hz : 0 ≤ z ∧ z ≤ 1) :
    0 ≤ (1 - z) / (1 - (1 - x.1 * x.2) * z) ∧
      (1 - z) / (1 - (1 - x.1 * x.2) * z) ≤ 1 := by
  constructor
  · apply div_nonneg (by linarith)
    simp only [sub_nonneg]
    refine (mul_le_of_le_one_left (by linarith) ?_).trans (by linarith)
    simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
    nlinarith
  · rw [div_le_iff₀]
    · simp only [one_mul, tsub_le_iff_right, sub_add, le_sub_self_iff, zero_add]
      by_cases h0 : z = 0
      · simp [h0]
      · suffices (1 - x.1 * x.2) * z < z by linarith
        rw [mul_lt_iff_lt_one_left]
        · simp only [sub_lt_self_iff]; nlinarith
        · by_contra!
          have : z = 0 := by linarith
          exact h0 this
    · simp only [sub_pos]
      rw [mul_comm]
      suffices z * (1 - x.1 * x.2) ≤ (1 - x.1 * x.2) by nlinarith
      apply mul_le_of_le_one_left (by nlinarith) hz.2

/--
@isnad1 id=ne.2h2v.s7.7a60511528af from=translated src=- shape=86272e1c vocab=2b02f4f0
-/
lemma ineq_aux1 (x : ℝ × ℝ) (z : ℝ)
    (hx : (0 < x.1 ∧ x.1 < 1) ∧ 0 < x.2 ∧ x.2 < 1) (hz : 0 ≤ z ∧ z ≤ 1) :
    1 - (1 - x.1 * x.2) * z ≠ 0 := by
  suffices (1 - x.1 * x.2) * z < 1 by linarith
  rw [mul_comm]
  suffices z * (1 - x.1 * x.2) ≤ (1 - x.1 * x.2) by nlinarith
  apply mul_le_of_le_one_left (by nlinarith) hz.2

/--
@isnad1 id=eq.2h2v.s8.37cd1926aa37 from=translated src=- shape=b655ea6c vocab=e8c1b4b7
-/
lemma fun_eq_aux (x : ℝ × ℝ) (y : ℝ)
    (hx : (0 < x.1 ∧ x.1 < 1) ∧ 0 < x.2 ∧ x.2 < 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    deriv (fun z => (1 - z) / (1 - (1 - x.1 * x.2) * z)) y =
    (fun z => - x.1 * x.2 / (1 - (1 - x.1 * x.2) * z) ^ 2) y := by
  rw [deriv_fun_div]
  · rw [deriv_const_sub, deriv_const_sub, deriv_const_mul _ differentiableAt_id]
    simp only [deriv_id'', neg_mul, one_mul, neg_sub, mul_one]
    congr
    ring
  · apply DifferentiableAt.const_sub differentiableAt_id _
  · apply DifferentiableAt.const_sub (DifferentiableAt.const_mul differentiableAt_id _)
  · exact ineq_aux1 x y hx hy

/--
@isnad1 id=summable.0h0v.s5.f6f427d6493f from=translated src=- shape=8f57b2fc vocab=72262d31
-/
lemma Summable_of_zeta_two' : Summable (fun (n : ℕ) ↦ 1 / ((n : ℝ) + 1) ^ 2) := by
  norm_cast
  simp only [Nat.cast_pow]
  rw [summable_nat_add_iff (k := 1) (f := fun k => 1 / (k ^ 2 : ℝ))]
  simp

/--
@isnad1 id=lt.0h0v.s6.de1123a5d64a from=translated src=- shape=72d47527 vocab=6a944134
-/
lemma zeta3_pos : 0 < ∑' (n : ℕ), 1 / ((n : ℝ) + 1) ^ 3 := by
  apply Summable.tsum_pos (g := fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 3) (i := 1)
  · apply summable_of_sum_range_le (c := Real.pi ^ 2 / 6)
    · intro _
      positivity
    · intro n
      suffices
          ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1) ^ 3 ≤
            ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1) ^ 2 by
        have : ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1) ^ 2 ≤ Real.pi ^ 2 / 6 := by
          suffices
              ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1) ^ 2 ≤
                ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 2 by
            have h : ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 2 = (riemannZeta 2).re := by
              rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simp)]
              simp_rw [← Complex.ofReal_natCast]
              norm_cast
            rw [h, riemannZeta_two] at this
            norm_cast at *
          apply Summable.sum_le_tsum
          · intro i _
            positivity
          · exact Summable_of_zeta_two'
        linarith
      apply Finset.sum_le_sum
      intro i _
      rw [div_le_div_iff₀, one_mul, one_mul]
      · apply pow_le_pow_right₀ <;> linarith
      · positivity
      · positivity
  · intro m
    simp only [one_div, pow_succ]
    positivity
  · positivity

/--
@isnad1 id=lt.0h0v.s6.5d075ad3ec4d from=translated src=- shape=7db04f45 vocab=6a944134
-/
lemma zeta3_le_zeta2 :
    ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 <
      ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 2 := by
  apply Summable.tsum_lt_tsum_of_nonneg
    (f := fun n => 1 / ((n : ℝ) + 1) ^ 3)
    (g := fun n => 1 / ((n : ℝ) + 1) ^ 2) (i := 2)
  · intro n
    positivity
  · intro n
    rw [div_le_div_iff₀, one_mul, one_mul]
    · apply pow_le_pow_right₀ <;> linarith
    · positivity
    · positivity
  · norm_num
  · exact Summable_of_zeta_two'

/--
@isnad1 id=eventual.0h0v.s6.75b27d08859b from=translated src=- shape=0765a9ad vocab=4aa41fc0
-/
lemma eventually_d_pow_three_le_exp :
    ∀ᶠ n : ℕ in Filter.atTop,
      (d (Finset.Icc 1 n) : ℝ) ^ 3 ≤ (Real.exp (339 / 100 : ℝ)) ^ n := by
  have hpsi_nat :
      ∀ᶠ n : ℕ in Filter.atTop,
        Chebyshev.psi (n : ℝ) ≤ (113 / 100 : ℝ) * (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually ChebyshevAux.eventually_psi_le_mul
  filter_upwards [hpsi_nat] with n hn
  have hlog : Real.log (Nat.lcmUpto n : ℝ) ≤ (113 / 100 : ℝ) * (n : ℝ) := by
    simpa [Chebyshev.psi_eq_log_lcmUpto n] using hn
  have hlcm : (Nat.lcmUpto n : ℝ) ≤ Real.exp ((113 / 100 : ℝ) * (n : ℝ)) :=
    (Real.log_le_iff_le_exp (by exact_mod_cast Nat.lcmUpto_pos n)).mp hlog
  change (Nat.lcmUpto n : ℝ) ^ 3 ≤ (Real.exp (339 / 100 : ℝ)) ^ n
  calc
    (Nat.lcmUpto n : ℝ) ^ 3 ≤ (Real.exp ((113 / 100 : ℝ) * (n : ℝ))) ^ 3 := by
      gcongr
    _ = (Real.exp (339 / 100 : ℝ)) ^ n := by
      rw [← Real.exp_nat_mul ((113 / 100 : ℝ) * (n : ℝ)) 3,
        ← Real.exp_nat_mul (339 / 100 : ℝ) n]
      congr 1
      ring

end LeanPool.Zeta3Irrational
