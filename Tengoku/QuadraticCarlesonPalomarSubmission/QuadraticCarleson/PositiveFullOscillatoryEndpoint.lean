import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.PositiveStoppingBadEndpoint
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.PositiveStoppingGoodEstimate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The full-real oscillatory endpoint theorem

The canonical stopping decomposition, the genuine good-part L² estimate,
and the recombined low/high bad-part estimates give the normalized
`L log₁ L` bound for the original input's oscillatory operator.
-/

open MeasureTheory Set
open scoped ENNReal NNReal Function

namespace QuadraticCarleson
namespace PositiveFullOscillatoryEndpoint

open CalderonZygmundDyadicStopping CalderonZygmundStoppingIntervals
open PositiveEndpointOptimization PositiveLevelIntegration
open PositiveHighHeightEstimate PositiveLowFullEstimate OscillatoryReduction
open PositiveStoppingBadEstimate PositiveGoodOscillatory

/--
@isnad1 id=eq.0h1v.s5.8b73c53a921f from=translated src=- shape=da93758f vocab=e127b2a2
-/
theorem stoppingGoodPart_add_stoppingBadPart (f : ℝ → ℂ) :
    stoppingGoodPart f + stoppingBadPart f = f := by
  funext x
  simp [Pi.add_apply, stoppingBadPart]

/--
@isnad1 id=integrab.2h1v.s6.39e55791b520 from=translated src=- shape=3ee3b192 vocab=9d6bc711
-/
theorem integrable_stoppingGoodPart {f : ℝ → ℂ} (hf : Measurable f)
    (hfi : Integrable f) : Integrable (stoppingGoodPart f) := by
  convert hfi.sub (integrable_stoppingBadPart hf hfi) using 1
  funext x
  simp [Pi.sub_apply, stoppingBadPart]

/--
@isnad1 id=le.2h3v.s7.6cc57ca3b4f8 from=translated src=- shape=b4e69a8c vocab=c2dc1754
-/
theorem paperOscillatoryMaximal_add_le {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    paperOscillatoryMaximal (f+g) x ≤ paperOscillatoryMaximal f x +
      paperOscillatoryMaximal g x := by
  apply iSup_le
  intro lam
  rw [paperOscillatoryAction_add_of_integrable lam.1 lam.2 hf hg]
  apply (enorm_add_le _ _).trans
  exact add_le_add
    (le_iSup (fun μ : {μ : ℝ // μ ≠ 0} ↦ ‖paperOscillatoryAction μ.1 μ.2 f x‖ₑ) lam)
    (le_iSup (fun μ : {μ : ℝ // μ ≠ 0} ↦ ‖paperOscillatoryAction μ.1 μ.2 g x‖ₑ) lam)

/--
@isnad1 id=le.2h2v.s6.1cbecb67dfc5 from=translated src=- shape=19646c72 vocab=a33c9ede
-/
theorem paperOscillatoryMaximal_le_good_add_bad {f : ℝ → ℂ}
    (hf : Measurable f) (hfi : Integrable f) (x : ℝ) :
    paperOscillatoryMaximal f x ≤ paperOscillatoryMaximal (stoppingGoodPart f) x +
      paperOscillatoryMaximal (stoppingBadPart f) x := by
  calc
    _ = paperOscillatoryMaximal (stoppingGoodPart f + stoppingBadPart f) x := by
      rw [stoppingGoodPart_add_stoppingBadPart]
    _ ≤ _ := paperOscillatoryMaximal_add_le (integrable_stoppingGoodPart hf hfi)
      (integrable_stoppingBadPart hf hfi) x

/-- An outer-measure rule which only requires the two majorants to be
measurable; the operator itself may be an uncountable supremum.
@isnad1 id=le.3h4v.s7.e833e6c12490 from=translated src=- shape=cd8d4988 vocab=438dc3cc
-/
theorem outerLevelSet_le_of_exceptional_majorants {F L H : ℝ → ℝ≥0∞}
    (E : Set ℝ) (hL : Measurable L) (hH : Measurable H)
    (hp : ∀ x, x ∉ E → F x ≤ L x + H x) :
    volume {x | 1 < F x} ≤ volume E + 2 * (∫⁻ x, L x) + 4 * ∫⁻ x, H x ^ 2 := by
  have hs : {x | 1 < F x} ⊆
      E ∪ ({x | (1/2 : ℝ≥0∞) < L x} ∪ {x | (1/2 : ℝ≥0∞) < H x}) := by
    intro x hx
    by_cases he : x ∈ E
    · exact Or.inl he
    apply Or.inr
    by_cases hl : (1/2 : ℝ≥0∞) < L x
    · exact Or.inl hl
    apply Or.inr
    by_contra hh
    have hle := add_le_add (le_of_not_gt hl) (le_of_not_gt hh)
    simp only [one_div, ENNReal.inv_two_add_inv_two] at hle
    exact (not_lt_of_ge ((hp x he).trans hle)) hx
  apply (measure_mono hs).trans
  apply (measure_union_le _ _).trans
  apply (add_le_add le_rfl (measure_union_le _ _)).trans
  simpa only [add_assoc] using add_le_add le_rfl
    (add_le_add (half_levelSet_measure_le_two_lintegral hL)
      (half_levelSet_measure_le_four_sq_lintegral hH))

noncomputable def stoppingBadHalfConstant : ℝ≥0∞ :=
  5 + 4 * fullLowEndpointConstant + 16 * fullHighEndpointConstant

/--
@isnad1 id=lt.0h0v.s3.21823478c305 from=translated src=- shape=f463f024 vocab=bf5d91af
-/
theorem stoppingBadHalfConstant_lt_top : stoppingBadHalfConstant < ∞ := by
  unfold stoppingBadHalfConstant
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨by finiteness,
    ENNReal.mul_lt_top (by finiteness) fullLowEndpointConstant_lt_top⟩,
    ENNReal.mul_lt_top (by finiteness) fullHighEndpointConstant_lt_top⟩

/--
@isnad1 id=le.2h1v.s7.856347be649f from=translated src=- shape=6cdd15ff vocab=1f282684
-/
theorem stoppingBadPart_half_levelSet_le_orlicz {f : ℝ → ℂ}
    (hf : Measurable f) (hfi : Integrable f) :
    volume {x | (1/2 : ℝ≥0∞) < paperOscillatoryMaximal (stoppingBadPart f) x} ≤
      stoppingBadHalfConstant * ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 1 ‖f x‖) := by
  let z := stoppingCenter (f := f)
  let R := stoppingLength (f := f)
  let E := fivefoldExceptionalSet z R
  let L := fullLowMajorant f z R
  let H := highContributionMajorant fullHighCutoff (stoppingLevelBadPart f)
  have hR : ∀ c, 0 < R c := stoppingLength_pos
  have hd : Pairwise (Disjoint on fun c ↦ centeredInterval (z c) (R c)) :=
    centeredStoppingIntervals_pairwiseDisjoint
  have hH : Measurable H := measurable_highContributionMajorant fullHighCutoff
    (fun k ↦ memLp_disjointLevelAtomSum hf hfi (fullAmplitude_pos k).le z R hR hd)
  have hp (x : ℝ) (hx : x ∉ E) :
      paperOscillatoryMaximal (stoppingBadPart f) x ≤ L x + H x := by
    apply (paperOscillatoryMaximal_stoppingBadPart_le_low_add_high hf hfi x).trans
    apply add_le_add
    · rw [← paperFullLowContribution_eq_heightContribution hf hfi z R hR hd]
      exact paperFullLowContribution_le_majorant hf hfi z R hR hd hx
    · exact paperHighContribution_le_majorant _ _ x
  have hs := outerLevelSet_le_of_exceptional_majorants
    (F := fun x ↦ 2 * paperOscillatoryMaximal (stoppingBadPart f) x)
    (L := fun x ↦ 2 * L x) (H := fun x ↦ 2 * H x)
    E (measurable_const.mul (measurable_fullLowMajorant f z R))
      (measurable_const.mul hH)
    (fun x hx ↦ (mul_le_mul' le_rfl (hp x hx)).trans_eq (mul_add _ _ _))
  have hiL : (∫⁻ x, 2 * L x) = 2 * ∫⁻ x, L x :=
    lintegral_const_mul' _ _ (by finiteness)
  have hiH : (∫⁻ x, (2 * H x) ^ 2) = 4 * ∫⁻ x, H x ^ 2 := by
    simp only [mul_pow, show (2 : ℝ≥0∞)^2 = 4 by norm_num]
    exact lintegral_const_mul' _ _ (by finiteness)
  rw [hiL, hiH] at hs
  have hE : volume E ≤ 5 * ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 1 ‖f x‖) :=
    (volume_fivefoldExceptionalSet_le z R).trans
      (mul_le_mul' le_rfl ((tsum_stoppingLength_le_lintegral_norm hfi).trans
        (lintegral_norm_le_full_orlicz f)))
  have hLbound := lintegral_fullLowMajorant_le_orlicz hf z R hR hd
  have hHbound := fullHighMajorant_sq_lintegral_le_orlicz hf hfi z R hR hd
  have hset : {x | (1/2 : ℝ≥0∞) < paperOscillatoryMaximal (stoppingBadPart f) x} ⊆
      {x | 1 < 2 * paperOscillatoryMaximal (stoppingBadPart f) x} := by
    intro x hx
    change 1 < 2 * paperOscillatoryMaximal (stoppingBadPart f) x
    have h := ENNReal.mul_lt_mul_right (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by finiteness : (2 : ℝ≥0∞) ≠ ∞) hx
    simpa only [one_div, ENNReal.mul_inv_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by finiteness : (2 : ℝ≥0∞) ≠ ∞)] using h
  apply ((measure_mono hset).trans hs).trans
  apply (add_le_add (add_le_add hE
    (mul_le_mul' le_rfl (mul_le_mul' le_rfl hLbound)))
    (mul_le_mul' le_rfl (mul_le_mul' le_rfl hHbound))).trans_eq
  unfold stoppingBadHalfConstant
  ring

/--
@isnad1 id=le.1h1v.s7.b21f8bf897db from=translated src=- shape=39a0b0c3 vocab=f01e67ce
-/
theorem stoppingGoodPart_half_levelSet_le_orlicz {f : ℝ → ℂ}
    (hfi : Integrable f) :
    volume {x | (1/2 : ℝ≥0∞) < paperOscillatoryMaximal (stoppingGoodPart f) x} ≤
      (4 * stoppingGoodOscillatoryConstant) *
        ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 1 ‖f x‖) := by
  have h := stoppingGoodPart_oscillatory_levelSet_mul_le hfi (1/2)
  have hc : (4 : ℝ≥0∞) * (1/2 : ℝ≥0∞)^2 = 1 := by
    rw [show (4 : ℝ≥0∞) = 2^2 by norm_num, ← mul_pow, one_div,
      ENNReal.mul_inv_cancel (by norm_num) (by finiteness), one_pow]
  calc
    _ = 4 * ((1/2 : ℝ≥0∞)^2 *
        volume {x | (1/2 : ℝ≥0∞) < paperOscillatoryMaximal (stoppingGoodPart f) x}) := by
      rw [← mul_assoc, hc, one_mul]
    _ ≤ 4 * (stoppingGoodOscillatoryConstant * ∫⁻ x, ‖f x‖ₑ) := mul_le_mul' le_rfl h
    _ ≤ (4 * stoppingGoodOscillatoryConstant) *
        ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 1 ‖f x‖) := by
      rw [mul_assoc]
      exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (lintegral_norm_le_full_orlicz f))

noncomputable def fullOscillatoryEndpointConstant : ℝ≥0∞ :=
  4 * stoppingGoodOscillatoryConstant + stoppingBadHalfConstant

/--
@isnad1 id=lt.0h0v.s3.2fa2317c2cc2 from=translated src=- shape=f463f024 vocab=0774caa6
-/
theorem fullOscillatoryEndpointConstant_lt_top : fullOscillatoryEndpointConstant < ∞ :=
  ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (by finiteness)
    stoppingGoodOscillatoryConstant_lt_top, stoppingBadHalfConstant_lt_top⟩

/-- The actual all-height, full-real oscillatory maximal operator satisfies
the normalized `L log₁ L` endpoint estimate for every measurable integrable
input. All decomposition and analytic estimates are proved, not supplied.
@isnad1 id=le.2h1v.s7.ee55513d805e from=translated src=- shape=7196ad56 vocab=c832b9d8
-/
theorem paperOscillatoryMaximal_levelSet_le_orlicz {f : ℝ → ℂ}
    (hf : Measurable f) (hfi : Integrable f) :
    volume {x | 1 < paperOscillatoryMaximal f x} ≤ fullOscillatoryEndpointConstant *
      ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 1 ‖f x‖) := by
  have hs : {x | 1 < paperOscillatoryMaximal f x} ⊆
      {x | (1/2 : ℝ≥0∞) < paperOscillatoryMaximal (stoppingGoodPart f) x} ∪
        {x | (1/2 : ℝ≥0∞) < paperOscillatoryMaximal (stoppingBadPart f) x} := by
    intro x hx
    by_cases hg : (1/2 : ℝ≥0∞) < paperOscillatoryMaximal (stoppingGoodPart f) x
    · exact Or.inl hg
    apply Or.inr
    by_contra hb
    have hle := add_le_add (le_of_not_gt hg) (le_of_not_gt hb)
    simp only [one_div, ENNReal.inv_two_add_inv_two] at hle
    exact (not_lt_of_ge ((paperOscillatoryMaximal_le_good_add_bad hf hfi x).trans hle)) hx
  apply (measure_mono hs).trans
  apply (measure_union_le _ _).trans
  apply (add_le_add (stoppingGoodPart_half_levelSet_le_orlicz hfi)
    (stoppingBadPart_half_levelSet_le_orlicz hf hfi)).trans_eq
  unfold fullOscillatoryEndpointConstant
  ring

/--
@isnad1 id=le.0h1v.s6.9021a62a920a from=translated src=- shape=e509f0b7 vocab=c17138e3
-/
theorem paperOscillatoryMaximal_L0Infinity_levelSet_le_orlicz (f : L0Infinity) :
    volume {x | 1 < paperOscillatoryMaximal f x} ≤ fullOscillatoryEndpointConstant *
      ∫⁻ x, ENNReal.ofReal (‖f x‖ * paperLog 1 ‖f x‖) :=
  paperOscillatoryMaximal_levelSet_le_orlicz f.measurable_toFun f.integrable

end PositiveFullOscillatoryEndpoint
end QuadraticCarleson
