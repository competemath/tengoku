import Tengoku.Piirrationalitymeasure.Formalization.ParameterSaving

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Continuity of the saving integral, including its moving discontinuities. -/

namespace PiIrrationality

open MeasureTheory Set Filter
open scoped Topology

/--
@isnad1 id=eventual.1h2v.s5.d573a1600002 from=translated src=- shape=7342294a vocab=db42c819
-/
theorem ae_affine_ne_intCast {a : ℝ} (ha : a ≠ 0) (b : ℝ) :
    ∀ᵐ t : ℝ, ∀ m : ℤ, a * t + b ≠ (m : ℝ) := by
  have h := (countable_range (fun m : ℤ => ((m : ℝ) - b) / a)).ae_notMem volume
  filter_upwards [h] with t ht m hm
  apply ht
  exact ⟨m, (div_eq_iff ha).mpr (by linarith)⟩

/--
@isnad1 id=continuo.3h2v.s8.6776e4298d22 from=translated src=- shape=e4571a84 vocab=07177812
-/
theorem continuousAt_savingChi_parameters {p : ℝ × ℝ} {t : ℝ}
    (hA : p.1 * t + 1 / 2 ≠ (⌊p.1 * t + 1 / 2⌋ : ℝ))
    (hB : p.2 * t ≠ (⌊p.2 * t⌋ : ℝ))
    (hneq : Int.fract (p.1 * t + 1 / 2) + 2 * Int.fract (p.2 * t) ≠ Int.fract t) :
    ContinuousAt (fun x : ℝ × ℝ => savingChi (x.1 * t) (x.2 * t) t) p := by
  have hAcont : ContinuousAt (fun x : ℝ × ℝ => Int.fract (x.1 * t + 1 / 2)) p :=
    (continuousAt_fract hA).comp (f := fun x : ℝ × ℝ => x.1 * t + 1 / 2) (by fun_prop)
  have hBcont : ContinuousAt (fun x : ℝ × ℝ => Int.fract (x.2 * t)) p :=
    (continuousAt_fract hB).comp (f := fun x : ℝ × ℝ => x.2 * t) (by fun_prop)
  have hcont := hAcont.add (hBcont.const_mul 2)
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · apply (continuousAt_const (y := (1 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hcont.eventually_lt continuousAt_const hlt] with x hx
    exact ite_eq_left hx
  · apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [continuousAt_const.eventually_lt hcont hgt] with x hx
    exact ite_eq_right hx.not_gt

/--
@isnad1 id=eventual.3h1v.s7.4de358eaaf94 from=translated src=- shape=7ad7403e vocab=1c6de40e
-/
theorem ae_continuousAt_savingDensity {p : ℝ × ℝ}
    (hA : p.1 ≠ 0) (hB : p.2 ≠ 0) (hq : p.1 + 2 * p.2 - 1 ≠ 0) :
    ∀ᵐ t : ℝ, ContinuousAt (fun x : ℝ × ℝ => savingDensity x.1 x.2 1 t) p := by
  filter_upwards [ae_affine_ne_intCast hA (1 / 2), ae_affine_ne_intCast hB 0,
    ae_affine_ne_intCast hq (1 / 2)] with t htA htB htq
  have hneq : Int.fract (p.1 * t + 1 / 2) + 2 * Int.fract (p.2 * t) ≠ Int.fract t := by
    intro he
    apply htq (⌊p.1 * t + 1 / 2⌋ + 2 * ⌊p.2 * t⌋ - ⌊t⌋)
    simp only [Int.fract] at he
    push_cast
    nlinarith only [he]
  have hc := continuousAt_savingChi_parameters (htA _) (by simpa using htB ⌊p.2 * t⌋) hneq
  simpa only [savingDensity, one_mul] using hc.div_const (t ^ 2)

/--
@isnad1 id=continuo.3h1v.s6.cf49cedeed74 from=translated src=- shape=0b33acb7 vocab=ec1b1ad9
-/
theorem continuousAt_savingPhi {p : ℝ × ℝ}
    (hA : 0 < p.1) (hB : 0 < p.2) (hq : 0 < p.1 + 2 * p.2 - 1) :
    ContinuousAt savingPhi p := by
  let K := p.1 + p.2 + 2
  let delta := 1 / (4 * (K + 1))
  let bound := (Ioi delta).indicator (fun t : ℝ => 1 / t ^ 2)
  have hK : 0 ≤ K := by dsimp [K]; linarith
  have h1K : 1 ≤ K := by dsimp [K]; linarith
  have hd : 0 < delta := by dsimp [delta]; positivity
  have hnear : ∀ᶠ x : ℝ × ℝ in 𝓝 p,
      0 < x.1 ∧ 0 < x.2 ∧ 0 < x.1 + 2 * x.2 - 1 ∧ x.1 < K ∧ x.2 < K := by
    have hqcont : ContinuousAt (fun x : ℝ × ℝ => x.1 + 2 * x.2 - 1) p := by fun_prop
    filter_upwards [continuous_fst.continuousAt.eventually_const_lt hA,
      continuous_snd.continuousAt.eventually_const_lt hB,
      hqcont.eventually_const_lt hq,
      continuous_fst.continuousAt.eventually_lt_const (show p.1 < K by dsimp [K]; linarith),
      continuous_snd.continuousAt.eventually_lt_const (show p.2 < K by dsimp [K]; linarith)]
      with x hxA hxB hxq hxAK hxBK
    exact ⟨hxA, hxB, hxq, hxAK, hxBK⟩
  have hpower : IntegrableOn (fun t : ℝ => 1 / t ^ 2) (Ioi delta) := by
    apply (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hd).congr_fun
      _ measurableSet_Ioi
    intro t ht
    dsimp only
    rw [Real.rpow_neg (hd.trans ht).le, Real.rpow_two, one_div]
  have hbint : Integrable bound volume :=
    (integrable_indicator_iff measurableSet_Ioi).mpr hpower
  apply tendsto_integral_filter_of_dominated_convergence bound
  · exact Eventually.of_forall (fun x => (measurable_savingDensity x.1 x.2 1).aestronglyMeasurable)
  · filter_upwards [hnear] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (savingDensity_nonneg _ _ _ _)]
    by_cases hdt : delta < t
    · change savingDensity x.1 x.2 1 t ≤ (Ioi delta).indicator (fun t : ℝ => 1 / t ^ 2) t
      rw [indicator_of_mem (show t ∈ Ioi delta from hdt)]
      exact div_le_div_of_nonneg_right (savingChi_le_one _ _ _) (sq_nonneg t)
    · have hz := savingDensity_initial_zero hx.1.le hx.2.1.le (by norm_num) hK
        hx.2.2.2.1.le hx.2.2.2.2.le h1K hx.2.2.1.le ht (le_of_not_gt hdt)
      rw [hz]
      exact indicator_nonneg (fun t _ => by positivity) t
  · exact hbint.restrict
  · filter_upwards [ae_restrict_of_ae (ae_continuousAt_savingDensity hA.ne' hB.ne' hq.ne')]
      with t ht
    exact ht

/--
@isnad1 id=continuo.0h0v.s5.5c4859f6b497 from=translated src=- shape=57ebd691 vocab=f2847d1a
-/
theorem savingPhi_continuousOn : ContinuousOn savingPhi {p | Admissible p} := by
  intro p hp
  obtain ⟨h1, h2, h3, h4⟩ := hp
  exact (continuousAt_savingPhi (by linarith) (by linarith) (by linarith)).continuousWithinAt

end PiIrrationality
