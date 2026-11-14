import Tengoku.Piirrationalitymeasure.Formalization.Statements

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The parameter-dependent saving integral of (6.1)--(6.4). -/

namespace PiIrrationality

open MeasureTheory
open Set

noncomputable def savingChi (X Y Z : ℝ) : ℝ :=
  if Int.fract (X + 1 / 2) + 2 * Int.fract Y < Int.fract Z then 1 else 0

noncomputable def savingDensity (A B C t : ℝ) : ℝ :=
  savingChi (A * t) (B * t) (C * t) / t ^ 2

noncomputable def savingOmega (A B C : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), savingDensity A B C t

noncomputable def savingPhi (p : ℝ × ℝ) : ℝ := savingOmega p.1 p.2 1

theorem savingChi_nonneg (X Y Z : ℝ) : 0 ≤ savingChi X Y Z := by
  unfold savingChi
  split_ifs <;> norm_num

theorem savingChi_le_one (X Y Z : ℝ) : savingChi X Y Z ≤ 1 := by
  unfold savingChi
  split_ifs <;> norm_num

theorem savingDensity_nonneg (A B C t : ℝ) : 0 ≤ savingDensity A B C t :=
  div_nonneg (savingChi_nonneg _ _ _) (sq_nonneg t)

theorem measurable_savingDensity (A B C : ℝ) : Measurable (savingDensity A B C) := by
  have hA : Measurable (fun t : ℝ => Int.fract (A * t + 1 / 2)) := by fun_prop
  have hB : Measurable (fun t : ℝ => 2 * Int.fract (B * t)) := by fun_prop
  have hC : Measurable (fun t : ℝ => Int.fract (C * t)) := by fun_prop
  have hchi : Measurable (fun t : ℝ => savingChi (A * t) (B * t) (C * t)) :=
    Measurable.ite (measurableSet_lt (hA.add hB) hC) measurable_const measurable_const
  exact hchi.div (measurable_id.pow_const 2)

theorem savingChi_eq_zero_of_no_wrap {X Y Z : ℝ}
    (hX0 : 0 ≤ X) (hX1 : X < 1 / 2) (hY0 : 0 ≤ Y) (hY1 : Y < 1)
    (hZ0 : 0 ≤ Z) (hZ1 : Z < 1) (hq : 0 ≤ X + 2 * Y - Z) :
    savingChi X Y Z = 0 := by
  unfold savingChi
  rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩,
    Int.fract_eq_self.mpr ⟨hY0, hY1⟩, Int.fract_eq_self.mpr ⟨hZ0, hZ1⟩]
  exact ite_eq_right (by linarith)

theorem savingDensity_initial_zero {A B C K t : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hAK : A ≤ K) (hBK : B ≤ K) (hCK : C ≤ K) (hq : 0 ≤ A + 2 * B - C)
    (ht0 : 0 < t) (ht1 : t ≤ 1 / (4 * (K + 1))) : savingDensity A B C t = 0 := by
  have hden : 0 < 4 * (K + 1) := by positivity
  have hmul := (le_div_iff₀ hden).mp ht1
  have hKt : K * t < 1 / 4 := by nlinarith
  have hAt := mul_le_mul_of_nonneg_right hAK ht0.le
  have hBt := mul_le_mul_of_nonneg_right hBK ht0.le
  have hCt := mul_le_mul_of_nonneg_right hCK ht0.le
  have hz := savingChi_eq_zero_of_no_wrap (mul_nonneg hA ht0.le) (by linarith : A * t < 1 / 2)
    (mul_nonneg hB ht0.le) (by linarith : B * t < 1)
    (mul_nonneg hC ht0.le) (by linarith : C * t < 1)
    (show 0 ≤ A * t + 2 * (B * t) - C * t by nlinarith [mul_nonneg hq ht0.le])
  simp only [savingDensity, hz, zero_div]

theorem savingDensity_integrableOn {A B C : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hq : 0 ≤ A + 2 * B - C) :
    IntegrableOn (savingDensity A B C) (Ioi (0 : ℝ)) := by
  let K := A + B + C
  let delta := 1 / (4 * (K + 1))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hd : 0 < delta := by dsimp [delta]; positivity
  have hz : ∀ t ∈ Ioc (0 : ℝ) delta, savingDensity A B C t = 0 := by
    intro t ht
    exact savingDensity_initial_zero hA hB hC hK
      (by dsimp [K]; linarith) (by dsimp [K]; linarith) (by dsimp [K]; linarith) hq ht.1 ht.2
  have hfirst : IntegrableOn (savingDensity A B C) (Ioc (0 : ℝ) delta) := by
    have hzero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioc (0 : ℝ) delta) volume :=
      integrableOn_zero
    exact hzero.congr_fun (fun t ht => (hz t ht).symm) measurableSet_Ioc
  have hpower : IntegrableOn (fun t : ℝ => 1 / t ^ 2) (Ioi delta) := by
    apply (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hd).congr_fun
      _ measurableSet_Ioi
    intro t ht
    dsimp only
    rw [Real.rpow_neg (hd.trans ht).le, Real.rpow_two, one_div]
  have htail : IntegrableOn (savingDensity A B C) (Ioi delta) := by
    apply hpower.mono' (measurable_savingDensity A B C).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (savingDensity_nonneg A B C t)]
    exact div_le_div_of_nonneg_right (savingChi_le_one _ _ _) (sq_nonneg t)
  have hu : Ioc (0 : ℝ) delta ∪ Ioi delta = Ioi (0 : ℝ) := by
    ext t
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (⟨ht, _⟩ | ht) <;> linarith
    · intro ht
      by_cases htd : t ≤ delta
      · exact Or.inl ⟨ht, htd⟩
      · exact Or.inr (lt_of_not_ge htd)
  rw [← hu]
  exact hfirst.union htail

theorem savingOmega_nonneg (A B C : ℝ) : 0 ≤ savingOmega A B C :=
  integral_nonneg (fun t => savingDensity_nonneg A B C t)

theorem savingOmega_homogeneous (A B C : ℝ) {c : ℝ} (hc : 0 < c) :
    savingOmega (c * A) (c * B) (c * C) = c * savingOmega A B C := by
  have he : savingDensity (c * A) (c * B) (c * C) =
      fun t : ℝ => c ^ 2 * savingDensity A B C (c * t) := by
    funext t
    unfold savingDensity
    rw [show A * (c * t) = c * A * t by ring,
      show B * (c * t) = c * B * t by ring, show C * (c * t) = c * C * t by ring,
      mul_pow]
    field_simp [hc.ne']
  unfold savingOmega
  rw [he, integral_const_mul, integral_comp_mul_left_Ioi _ 0 hc, mul_zero, smul_eq_mul]
  field_simp

theorem savingOmega_eq_scaled_phi (alpha beta : ℝ) {c : ℝ} (hc : 0 < c) :
    savingOmega (c * alpha) (c * beta) c = c * savingPhi (alpha, beta) := by
  simpa only [savingPhi, Prod.fst, Prod.snd, mul_one] using
    savingOmega_homogeneous alpha beta 1 hc

theorem savingPhi_integrableOn {p : ℝ × ℝ} (hp : Admissible p) :
    IntegrableOn (savingDensity p.1 p.2 1) (Ioi (0 : ℝ)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  apply savingDensity_integrableOn <;> linarith

end PiIrrationality
