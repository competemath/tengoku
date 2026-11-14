import Tengoku.Piirrationalitymeasure.Formalization.GeneralSavingLogVariation
import Tengoku.Piirrationalitymeasure.Formalization.OldPointPartition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The unconditional one-sided old-point saving expansion (6.30). -/

namespace PiIrrationality

noncomputable def oldPointSavingModel :
    SavingRadialModel ((1 : ℤ) : ℝ) ((2 : ℤ) : ℝ) ((3 : ℤ) : ℝ) where
  domain := {h | 0 ≤ h.2 ∧ h.1 = h.2 / 2}
  scale_mem := by
    intro h hh t ht
    change 0 ≤ t * h.2 ∧ t * h.1 = (t * h.2) / 2
    exact ⟨mul_nonneg ht hh.1, by rw [hh.2]; ring⟩
  variation := fun h => h.2
  variation_smul := by intro h hh t ht; rfl
  bound := 1
  bound_nonneg := by norm_num
  variation_bound := by
    intro h hh
    dsimp [parameterNormOne]
    linarith [abs_nonneg h.1]
  radius := 1 / 30
  radius_pos := by norm_num
  measure_eq := by
    intro h hh hsmall
    norm_num only [Int.cast_one, Int.cast_ofNat]
    have he : h.2 < 1 / 15 := by
      dsimp [parameterNormOne] at hsmall
      linarith [abs_nonneg h.1, le_abs_self h.2]
    have hpair : h = (h.2 / 2, h.2) := Prod.ext hh.2 rfl
    rw [hpair, oldPoint_measure hh.1 he, oldPoint_measure_zero]
    ring

theorem savingPhi_oldPoint_log_variation :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ e : ℝ, 0 < e → e ≤ r →
      |savingPhi (oldPoint + e • ((1 : ℝ) / 2, 1)) - savingPhi oldPoint -
        e * Real.log (1 / e)| ≤ C * e := by
  obtain ⟨r, C, hr, hC, hmodel⟩ := oldPointSavingModel.phi_log_variation
    (a := 1) (b := 2) (c := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨2 * r / 3, 3 * C / 2 + |Real.log (3 / 2)|, by positivity, by positivity, ?_⟩
  intro e he her
  let h : ℝ × ℝ := e • ((1 : ℝ) / 2, 1)
  have hmem : h ∈ oldPointSavingModel.domain := by
    change 0 ≤ e * 1 ∧ e * (1 / 2) = (e * 1) / 2
    constructor <;> nlinarith
  have hn : parameterNormOne h = 3 * e / 2 := by
    dsimp [h, parameterNormOne]
    rw [abs_of_pos (by positivity : 0 < e * (1 / 2)), abs_of_pos (by positivity : 0 < e * 1)]
    ring
  have hv : oldPointSavingModel.variation h = e := by simp [oldPointSavingModel, h]
  have hb := hmodel h hmem (by rw [hn]; positivity) (by rw [hn]; linarith)
  have hp : ((1 : ℝ) / 3, (2 : ℝ) / 3) = oldPoint := rfl
  norm_num only [Int.cast_one, Int.cast_ofNat] at hb
  rw [hp, hn, hv] at hb
  have hlog : Real.log (1 / (3 * e / 2)) = Real.log (1 / e) - Real.log (3 / 2) := by
    rw [show 3 * e / 2 = (3 / 2) * e by ring,
      Real.log_div one_ne_zero (mul_ne_zero (by norm_num) he.ne'),
      Real.log_div one_ne_zero he.ne', Real.log_mul (by norm_num) he.ne', Real.log_one]
    ring
  rw [hlog] at hb
  let E := savingPhi (oldPoint + h) - savingPhi oldPoint - e * Real.log (1 / e)
  have hb' : |E + e * Real.log (3 / 2)| ≤ C * (3 * e / 2) := by
    convert hb using 1
    congr 1
    dsimp [E]
    ring
  have ht := abs_sub (E + e * Real.log (3 / 2)) (e * Real.log (3 / 2))
  rw [add_sub_cancel_right, abs_mul, abs_of_pos he] at ht
  change |E| ≤ _
  nlinarith only [ht, hb']

end PiIrrationality
