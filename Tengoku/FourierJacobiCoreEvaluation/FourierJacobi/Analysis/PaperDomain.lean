import Tengoku.FourierJacobiCoreEvaluation.FourierJacobi.Analysis.CoreParameters

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The literal paper quotient on its natural parameter domain

The four-factor products are independently matched, with multiplicities, to
the algebraic expressions. Their nonvanishing below is proved from unitary
Satake parameters and the stated interior or signed-endpoint conditions.
No Weyl-wall exclusions are needed for these denominator statements.
-/

noncomputable section

namespace FourierJacobi.Analysis

open FourierJacobi.Algebra

/--
@isnad1 id=eq.0h4v.s4.78612f264a57 from=translated src=- shape=0e38dc21 vocab=6df93c03
-/
theorem paperD1_eq_d₁ (q : ℝ) (a b d : ℂ) :
    paperD1 q a b d = d₁ (inverseSqrt q : ℂ) a b d := by
  simp only [paperD1, satakeTuple, d₁, fourFactors,
    Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, mul_one]
  ring

/--
@isnad1 id=eq.0h4v.s4.69b2333c517d from=translated src=- shape=0e38dc21 vocab=5e861d1a
-/
theorem paperD2_eq_d₂ (q : ℝ) (a b d : ℂ) :
    paperD2 q a b d = d₂ (inverseSqrt q : ℂ) a b d := by
  simp only [paperD2, satakeTuple, d₂, fourFactors,
    Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, mul_one, div_eq_mul_inv]
  ring

/--
@isnad1 id=ne.1h1v.s4.ddd7d68e40c9 from=translated src=- shape=aa240375 vocab=0ada3d96
-/
theorem paperC_ne_zero (q : ℝ) (hq : 1 < q) : paperC q ≠ 0 := by
  rw [paperC_eq_poincare q (by linarith)]
  exact poincare_coe_ne_zero _

/--
@isnad1 id=ne.4h4v.s6.0e97192e3b36 from=translated src=- shape=ec5ffcf5 vocab=ebb57b55
-/
theorem paperD1_ne_zero_of_norm_le_one (q : ℝ) (hq : 1 < q)
    (a b d : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ ≤ 1) :
    paperD1 q a b d ≠ 0 := by
  rw [paperD1_eq_d₁]
  apply fourFactors_ne_zero ha hb
  have ht₀ := inverseSqrt_pos hq
  have ht₁ := inverseSqrt_lt_one hq
  have htn : ‖(inverseSqrt q : ℂ)‖ = inverseSqrt q := by
    simp [abs_of_pos ht₀]
  rw [norm_mul, htn]
  nlinarith

/--
@isnad1 id=ne.4h4v.s6.75c19506cebd from=translated src=- shape=2bd8a714 vocab=72e63858
-/
theorem paperD2_ne_zero_interior (q : ℝ) (hq : 1 < q)
    (a b d : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hd : inverseSqrt q < ‖d‖) : paperD2 q a b d ≠ 0 := by
  rw [paperD2_eq_d₂]
  apply fourFactors_ne_zero ha hb
  have ht₀ := inverseSqrt_pos hq
  have hd₀ : 0 < ‖d‖ := lt_trans ht₀ hd
  have htn : ‖(inverseSqrt q : ℂ)‖ = inverseSqrt q := by
    simp [abs_of_pos ht₀]
  rw [norm_div, htn]
  exact (div_lt_one hd₀).mpr hd

/-- In the open interior, the actual denominator is nonzero even on Weyl walls.
@isnad1 id=ne.5h4v.s6.5c4fa87abfb8 from=translated src=- shape=f94cd92e vocab=4122a6f8
-/
theorem paper_denominator_interior_ne_zero (q : ℝ) (hq : 1 < q)
    (a b d : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hdlo : inverseSqrt q < ‖d‖) (hdhi : ‖d‖ ≤ 1) :
    paperC q * paperD1 q a b d * paperD2 q a b d ≠ 0 :=
  mul_ne_zero
    (mul_ne_zero (paperC_ne_zero q hq)
      (paperD1_ne_zero_of_norm_le_one q hq a b d ha hb hdhi))
    (paperD2_ne_zero_interior q hq a b d ha hb hdlo)

/--
@isnad1 id=ne.2h2v.s5.8807ac67e00b from=translated src=- shape=91bea6f4 vocab=9a226037
-/
theorem fourFactors_one_ne_zero (a b : ℂ) (ha : a ≠ 1) (hb : b ≠ 1) :
    fourFactors a b 1 ≠ 0 := by
  have hai : a⁻¹ ≠ 1 := by simpa using ha
  have hbi : b⁻¹ ≠ 1 := by simpa using hb
  simp only [fourFactors, mul_one]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero
    (sub_ne_zero.mpr ha.symm) (sub_ne_zero.mpr hai.symm))
    (sub_ne_zero.mpr hb.symm)) (sub_ne_zero.mpr hbi.symm)

/--
@isnad1 id=eq.1h3v.s5.553714ab0712 from=translated src=- shape=4f2b47a1 vocab=da4f6037
-/
theorem paperD2_special_positive (q : ℝ) (hq : 1 < q) (a b : ℂ) :
    paperD2 q a b (inverseSqrt q : ℂ) = fourFactors a b 1 := by
  rw [paperD2_eq_d₂, d₂]
  have htne : (inverseSqrt q : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (inverseSqrt_pos hq)
  rw [div_self htne]

/--
@isnad1 id=eq.3h3v.s5.4144087726c3 from=translated src=- shape=2872b024 vocab=57f3fbe3
-/
theorem paperD2_special_negative (q : ℝ) (hq : 1 < q) (a b : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    paperD2 q a b (-(inverseSqrt q : ℂ)) = satakeNumerator a b := by
  rw [paperD2_eq_d₂]
  have htne : (inverseSqrt q : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (inverseSqrt_pos hq)
  exact special_negative_d₂ _ _ _ htne (unit_ne_zero ha) (unit_ne_zero hb)

/--
@isnad1 id=ne.5h3v.s6.bf5a7edf7dc0 from=translated src=- shape=4ff183bf vocab=f97931e5
-/
theorem paper_denominator_special_positive_ne_zero (q : ℝ) (hq : 1 < q)
    (a b : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) :
    paperC q * paperD1 q a b (inverseSqrt q : ℂ) *
      paperD2 q a b (inverseSqrt q : ℂ) ≠ 0 := by
  have htn : ‖(inverseSqrt q : ℂ)‖ ≤ 1 :=
    (coe_norm_lt_one (inverseSqrt_pos hq).le (inverseSqrt_lt_one hq)).le
  apply mul_ne_zero
    (mul_ne_zero (paperC_ne_zero q hq)
      (paperD1_ne_zero_of_norm_le_one q hq a b _ ha hb htn))
  rw [paperD2_special_positive q hq]
  exact fourFactors_one_ne_zero a b ha₁ hb₁

/--
@isnad1 id=ne.5h3v.s6.f9a9c95b8116 from=translated src=- shape=e3b14f0d vocab=39eedf41
-/
theorem paper_denominator_special_negative_ne_zero (q : ℝ) (hq : 1 < q)
    (a b : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a ≠ -1) (hb₁ : b ≠ -1) :
    paperC q * paperD1 q a b (-(inverseSqrt q : ℂ)) *
      paperD2 q a b (-(inverseSqrt q : ℂ)) ≠ 0 := by
  have htn : ‖-(inverseSqrt q : ℂ)‖ ≤ 1 := by
    simpa only [norm_neg] using
      (coe_norm_lt_one (inverseSqrt_pos hq).le (inverseSqrt_lt_one hq)).le
  apply mul_ne_zero
    (mul_ne_zero (paperC_ne_zero q hq)
      (paperD1_ne_zero_of_norm_le_one q hq a b _ ha hb htn))
  rw [paperD2_special_negative q hq a b ha hb]
  apply satakeNumerator_unitary_ne_zero ha hb
  · intro he
    apply ha₁
    linear_combination he
  · intro he
    apply hb₁
    linear_combination he

/-- Both literal special denominators are justified from precisely the endpoint
exclusions a,b ≠ ε, where ε is a sign. This asserts no endpoint series convergence.
@isnad1 id=ne.6h4v.s7.87f04ce704ee from=translated src=- shape=2cd05841 vocab=39eedf41
-/
theorem paper_denominator_special_ne_zero (q : ℝ) (hq : 1 < q)
    (a b ε : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hε : ε = 1 ∨ ε = -1) (haε : a ≠ ε) (hbε : b ≠ ε) :
    paperC q * paperD1 q a b (ε * (inverseSqrt q : ℂ)) *
      paperD2 q a b (ε * (inverseSqrt q : ℂ)) ≠ 0 := by
  rcases hε with rfl | rfl
  · simpa only [one_mul] using
      paper_denominator_special_positive_ne_zero q hq a b ha hb haε hbε
  · simpa only [neg_one_mul] using
      paper_denominator_special_negative_ne_zero q hq a b ha hb haε hbε

end FourierJacobi.Analysis
