import Tengoku.Piirrationalitymeasure.Formalization.SavingMeasurePolyhedral
import Tengoku.Piirrationalitymeasure.Formalization.GeneralSavingLogVariation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Uniform local polyhedrality and logarithmic variation for every permitted integer triple. -/

namespace PiIrrationality

open MeasureTheory
open scoped Topology

private theorem norm_le_parameterNormOne (z : ℝ × ℝ) : ‖z‖ ≤ parameterNormOne z := by
  rw [Prod.norm_def]
  simp only [Real.norm_eq_abs, parameterNormOne]
  exact max_le (le_add_of_nonneg_right (abs_nonneg _))
    (le_add_of_nonneg_left (abs_nonneg _))

theorem LocalPolyhedral.savingModel_exists {a b c : ℝ}
    (M : LocalPolyhedral (translatedSavingMeasure a b c)) :
    ∃ N : SavingRadialModel a b c,
      N.domain = Set.univ ∧ N.variation = M.tangent ∧ N.radius ≤ 1 := by
  obtain ⟨B, hB, hbound⟩ := M.tangent_bound
  obtain ⟨r, hr, hexact⟩ := Metric.eventually_nhds_iff.mp M.eventually_exact
  let N : SavingRadialModel a b c := {
    domain := Set.univ
    scale_mem := by simp
    variation := M.tangent
    variation_smul := fun h _ t ht => M.homogeneous h t ht
    bound := B
    bound_nonneg := hB
    variation_bound := fun h _ => (hbound h).trans
      (mul_le_mul_of_nonneg_left (norm_le_parameterNormOne h) hB)
    radius := Min.min (r / 2) 1
    radius_pos := lt_min (by positivity) (by norm_num)
    measure_eq := by
      intro h _ hh
      have hn : ‖h‖ < r := lt_of_le_of_lt
        ((norm_le_parameterNormOne h).trans (hh.trans (min_le_left _ _))) (by linarith)
      have he := hexact (by simpa only [dist_zero_right] using hn)
      linarith }
  exact ⟨N, rfl, rfl, min_le_right _ _⟩

noncomputable def generalSavingModel {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hq : a + 2 * b - c ≠ 0) :
    SavingRadialModel a b c :=
  (savingMeasurePolyhedral ha hb hc hq).savingModel_exists.choose

theorem generalSavingModel_spec {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hq : a + 2 * b - c ≠ 0) :
    (generalSavingModel ha hb hc hq).domain = Set.univ ∧
    (generalSavingModel ha hb hc hq).variation = (savingMeasurePolyhedral ha hb hc hq).tangent ∧
    (generalSavingModel ha hb hc hq).radius ≤ 1 :=
  (savingMeasurePolyhedral ha hb hc hq).savingModel_exists.choose_spec

theorem generalSavingModel_continuous {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hq : a + 2 * b - c ≠ 0) :
    Continuous (generalSavingModel ha hb hc hq).variation := by
  rw [(generalSavingModel_spec ha hb hc hq).2.1]
  exact (savingMeasurePolyhedral ha hb hc hq).continuous_tangent

theorem generalSavingModel_conewise_linear {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hq : a + 2 * b - c ≠ 0) :
    FiniteConewiseLinear (generalSavingModel ha hb hc hq).variation := by
  rw [(generalSavingModel_spec ha hb hc hq).2.1]
  exact (savingMeasurePolyhedral ha hb hc hq).conewise_linear

/-- Lemma 6.1, with one radius for every direction and both translation estimates.-/
theorem lemma61_general {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hq : a + 2 * b - c ≠ 0) :
    ∃ (D : ℝ × ℝ → ℝ) (rho L : ℝ),
      0 < rho ∧ 0 ≤ L ∧ Continuous D ∧ FiniteConewiseLinear D ∧
      (∀ v : ℝ × ℝ, ∀ s : ℝ, 0 ≤ s → D (s • v) = s * D v) ∧
      (∀ v : ℝ × ℝ, parameterNormOne v = 1 → ∀ s : ℝ, 0 ≤ s → s ≤ rho →
        translatedSavingMeasure a b c (s • v) - translatedSavingMeasure a b c 0 = s * D v) ∧
      (∀ z z' : ℝ × ℝ, parameterNormOne z ≤ rho → parameterNormOne z' ≤ rho →
        (∫ u in (0 : ℝ)..1,
          |translatedSavingChi a b c z' u - translatedSavingChi a b c z u|) ≤
            L * parameterNormOne (z' - z)) ∧
      (∀ z w : ℝ × ℝ, parameterNormOne z ≤ rho → parameterNormOne w ≤ rho →
        (∫ u in (0 : ℝ)..1,
          |translatedSavingChi a b c (z + u • w) u - translatedSavingChi a b c z u|) ≤
            L * parameterNormOne w) := by
  let M := generalSavingModel ha hb hc hq
  have hmem (z : ℝ × ℝ) : z ∈ M.domain := by
    rw [(generalSavingModel_spec ha hb hc hq).1]
    trivial
  have hr1 : M.radius ≤ 1 := (generalSavingModel_spec ha hb hc hq).2.2
  refine ⟨M.variation, M.radius, savingTranslationConstant a b c, M.radius_pos,
    savingTranslationConstant_nonneg a b c, generalSavingModel_continuous ha hb hc hq,
    generalSavingModel_conewise_linear ha hb hc hq, ?_, ?_, ?_, ?_⟩
  · exact fun v s hs => M.variation_smul v (hmem v) s hs
  · intro v hv s hs hsr
    rw [M.measure_eq (s • v) (hmem _), M.variation_smul v (hmem _) s hs]
    simpa only [parameterNormOne_smul, hv, mul_one, abs_of_nonneg hs] using hsr
  · exact fun z z' hz hz' => translatedSavingChi_integral_translation z z' ha.ne' hb.ne' hq
      (hz.trans hr1) (hz'.trans hr1)
  · exact fun z w hz hw => translatedSavingChi_integral_affine_translation z w ha.ne' hb.ne' hq
      (hz.trans hr1) (hw.trans hr1)

/-- Lemma 6.2 for an arbitrary positive integer triple with nonzero q.-/
theorem lemma62_general {a b c : ℤ}
    (ha : 0 < (a : ℝ)) (hb : 0 < (b : ℝ)) (hc : 0 < (c : ℝ))
    (hq : (a : ℝ) + 2 * b - c ≠ 0) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧
      (∀ h : ℝ × ℝ, 0 < parameterNormOne h → parameterNormOne h ≤ r →
        |savingPhi (((a : ℝ) / c, (b : ℝ) / c) + h) -
          savingPhi ((a : ℝ) / c, (b : ℝ) / c) -
          (generalSavingModel ha hb hc hq).variation h * Real.log (1 / parameterNormOne h)| ≤
            C * parameterNormOne h) ∧
      (∀ v : ℝ × ℝ, parameterNormOne v = 1 → ∀ e : ℝ, 0 < e → e ≤ r →
        |savingPhi (((a : ℝ) / c, (b : ℝ) / c) + e • v) -
          savingPhi ((a : ℝ) / c, (b : ℝ) / c) -
          e * (generalSavingModel ha hb hc hq).variation v * Real.log (1 / e)| ≤ C * e) := by
  let M := generalSavingModel ha hb hc hq
  have hmem (z : ℝ × ℝ) : z ∈ M.domain := by
    rw [(generalSavingModel_spec ha hb hc hq).1]
    trivial
  obtain ⟨r, C, hr, hC, hbound⟩ := M.phi_log_variation ha hb hc hq
  refine ⟨r, C, hr, hC, (fun h hh hhr => hbound h (hmem h) hh hhr), ?_⟩
  intro v hv e he her
  have hn : parameterNormOne (e • v) = e := by
    rw [parameterNormOne_smul, hv, mul_one, abs_of_pos he]
  simpa only [hn, M.variation_smul v (hmem v) e he.le] using
    hbound (e • v) (hmem _) (by rwa [hn]) (by rwa [hn])

end PiIrrationality
