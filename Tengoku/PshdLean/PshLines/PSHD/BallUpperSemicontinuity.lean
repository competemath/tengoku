import Tengoku.PshdLean.PshLines.PSHD.LineSections
import Tengoku.PshdLean.PshLines.PSHD.Measurability
import Tengoku.PshdLean.PshLines.BallSubmean

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Upper semicontinuity from ball averages

For a Borel function that is locally bounded above and subharmonic on every
affine complex-line section, the central value is dominated by ball averages,
the ball averages move continuously with the center, and shrinking ball
averages cannot exceed the central value. Together these give upper
semicontinuity; this is the passage from Steps 1-2 of Proposition 2.1 of
`pshd-vibe` to plurisubharmonicity.
-/

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace PshLines.PSHD

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The ball-deficit estimate for Borel functions that are subharmonic on
line sections: the ball average dominates the central value.-/
theorem LineSubharmonicOn.ball_deficit_le {u : E → ℝ} {D : Set E}
    (hl : LineSubharmonicOn u D) (hu : Measurable u) (μ : Measure E) [μ.IsAddHaarMeasure]
    (a : E) (R C : ℝ) (hBD : ball a R ⊆ D) (hC : ∀ y ∈ ball a R, u y ≤ C) :
    ∫⁻ x in ball a R, ENNReal.ofReal (C - u x) ∂μ ≤
      μ (ball 0 R) * ENNReal.ofReal (C - u a) := by
  let d : E → ℝ≥0∞ := fun x => ENNReal.ofReal (C - u x)
  let f : E → ℝ≥0∞ := (ball a R).indicator d
  have hm : Measurable f :=
    ((measurable_const.sub hu).ennreal_ofReal).indicator measurableSet_ball
  have hf : ∫⁻ x in ball a R, f x ∂μ = ∫⁻ x in ball a R, d x ∂μ :=
    setLIntegral_congr_fun measurableSet_ball (fun x hx => by simp [f, hx])
  have hrot (t : ℝ) :
      ∫⁻ v in ball 0 R, f (a + circleMap 0 1 t • v) ∂μ =
        ∫⁻ x in ball a R, d x ∂μ :=
    (lintegral_ball_add_circleMap_smul μ f a t R).trans hf
  have hc : Continuous (fun p : E × ℝ => a + circleMap 0 1 p.2 • p.1) := by
    fun_prop
  have hswap := lintegral_lintegral_swap
    (μ := μ.restrict (ball 0 R)) (ν := volume.restrict (Ioc 0 (2 * Real.pi)))
    (f := fun v t => f (a + circleMap 0 1 t • v)) (hm.comp hc.measurable).aemeasurable
  have hangle (v : E) (hv : v ∈ ball 0 R) :
      ∫⁻ t in Ioc 0 (2 * Real.pi), f (a + circleMap 0 1 t • v) ≤
        ENNReal.ofReal (2 * Real.pi) * d a := by
    have hD := affineClosedDisc_subset_ball a v (by simpa using hv)
    have heq :
        ∫⁻ t in Ioc 0 (2 * Real.pi), f (a + circleMap 0 1 t • v) =
          circleDeficit (fun x => (u x : EReal)) a v 1 C := by
      apply lintegral_congr
      intro t
      have ht := hD (circle_mem_affineClosedDisc a v (by norm_num : (0 : ℝ) ≤ 1) t)
      simp [f, d, ht, ← EReal.coe_sub]
    rw [heq]
    have h := hl.hasDiscSubmeanOn a v 1 (by norm_num) (hD.trans hBD) C
      (fun y hy => EReal.coe_le_coe_iff.mpr (hC y (hD hy)))
    simpa [d, ← EReal.coe_sub, EReal.real_coe_toENNReal] using h
  have hmul : (∫⁻ x in ball a R, d x ∂μ) * ENNReal.ofReal (2 * Real.pi) ≤
      (μ (ball 0 R) * d a) * ENNReal.ofReal (2 * Real.pi) := by
    calc
      (∫⁻ x in ball a R, d x ∂μ) * ENNReal.ofReal (2 * Real.pi) =
          ∫⁻ t in Ioc 0 (2 * Real.pi),
            ∫⁻ v in ball 0 R, f (a + circleMap 0 1 t • v) ∂μ := by
              simp_rw [hrot]
              simp
      _ = ∫⁻ v in ball 0 R,
          (∫⁻ t in Ioc 0 (2 * Real.pi), f (a + circleMap 0 1 t • v)) ∂μ := hswap.symm
      _ ≤ ∫⁻ _v in ball 0 R, ENNReal.ofReal (2 * Real.pi) * d a ∂μ :=
        setLIntegral_mono' measurableSet_ball hangle
      _ = (μ (ball 0 R) * d a) * ENNReal.ofReal (2 * Real.pi) := by
        rw [setLIntegral_const]; ring
  exact (ENNReal.mul_le_mul_iff_left
    (ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos (by norm_num) Real.pi_pos)))
    ENNReal.ofReal_ne_top).mp hmul

omit [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] in
/-- Rescaling a ball integral to the unit ball.-/
theorem lintegral_ball_eq_ofReal_mul_lintegral_unitBall [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (g : E → ℝ≥0∞) (z : E) {r : ℝ} (hr : 0 < r) :
    ∫⁻ x in ball z r, g x ∂μ =
      ENNReal.ofReal (r ^ Module.finrank ℝ E) * ∫⁻ y in ball 0 1, g (z + r • y) ∂μ := by
  have hr0 : r ≠ 0 := hr.ne'
  set h : E → ℝ≥0∞ := (ball (0 : E) r).indicator (fun x => g (z + x))
  have hpre : (ball (0 : E) 1).indicator (fun y => g (z + r • y)) = fun y => h (r • y) := by
    funext y
    have hiff : r • y ∈ ball (0 : E) r ↔ y ∈ ball (0 : E) 1 := by
      simp [mem_ball, dist_zero_right, norm_smul, abs_of_pos hr, hr]
    by_cases hy : y ∈ ball (0 : E) 1
    · simp [h, hy, hiff.mpr hy]
    · simp [h, hy, mt hiff.mp hy]
  have hmap : ∫⁻ y, h (r • y) ∂μ =
      ENNReal.ofReal |(r ^ Module.finrank ℝ E)⁻¹| * ∫⁻ x, h x ∂μ := by
    rw [← smul_eq_mul, ← lintegral_smul_measure, ← Measure.map_addHaar_smul μ hr0]
    exact (lintegral_map_equiv h (Homeomorph.smulOfNeZero r hr0).toMeasurableEquiv).symm
  have hone : ENNReal.ofReal (r ^ Module.finrank ℝ E) *
      ENNReal.ofReal |(r ^ Module.finrank ℝ E)⁻¹| = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), abs_of_pos (by positivity),
      mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one]
  calc ∫⁻ x in ball z r, g x ∂μ = ∫⁻ x, h x ∂μ := by
        rw [lintegral_indicator measurableSet_ball, lintegral_ball_add]
    _ = ENNReal.ofReal (r ^ Module.finrank ℝ E) * ∫⁻ y, h (r • y) ∂μ := by
        rw [hmap, ← mul_assoc, hone, one_mul]
    _ = _ := by rw [← hpre, lintegral_indicator measurableSet_ball]

/-- Along every ray the deficit is lower semicontinuous at the center, so by
Fatou's lemma small ball averages of the deficit exceed any number below the
central deficit.-/
theorem LineSubharmonicOn.exists_ball_deficit_gt {u : E → ℝ} {D : Set E} (hD : IsOpen D)
    (hl : LineSubharmonicOn u D) (hu : Measurable u) (μ : Measure E) [μ.IsAddHaarMeasure]
    {z : E} (hz : z ∈ D) (C : ℝ) {t : ℝ≥0∞} (ht : t < ENNReal.ofReal (C - u z))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ r ∈ Ioc 0 ρ, μ (ball 0 r) * t < ∫⁻ x in ball z r, ENNReal.ofReal (C - u x) ∂μ := by
  let s : ℕ → ℝ := fun k => ρ / (k + 1)
  have hs : ∀ k, 0 < s k := fun k => by positivity
  have hsρ : ∀ k, s k ≤ ρ := fun k =>
    div_le_self hρ.le (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  have hs0 : Tendsto s atTop (𝓝 0) := by
    simpa [s, div_eq_mul_inv] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ρ
  have hray : ∀ y : E, ENNReal.ofReal (C - u z) ≤
      liminf (fun k => ENNReal.ofReal (C - u (z + s k • y))) atTop := by
    intro y
    refine le_of_forall_lt_imp_le_of_dense fun a ha => ?_
    have hatop : a ≠ ⊤ := ne_top_of_lt ha
    have ha' : a.toReal < C - u z := (ENNReal.lt_ofReal_iff_toReal_lt hatop).mp ha
    have hline := hl.upperSemicontinuousAt_line hD hz y (C - a.toReal) (by
      simp only [zero_smul, add_zero]
      linarith)
    have hlim : Tendsto (fun k => ((s k : ℝ) : ℂ)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp hs0
    refine le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [hlim.eventually hline] with k hk
    simp only [Complex.coe_smul] at hk
    rw [← ENNReal.ofReal_toReal hatop]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hmeas : ∀ k, Measurable (fun y : E => ENNReal.ofReal (C - u (z + s k • y))) := fun k =>
    (measurable_const.sub (hu.comp
      (continuous_const.add (continuous_id.const_smul (s k))).measurable)).ennreal_ofReal
  have hlow : μ (ball 0 1) * ENNReal.ofReal (C - u z) ≤
      liminf (fun k => ∫⁻ y in ball 0 1, ENNReal.ofReal (C - u (z + s k • y)) ∂μ) atTop :=
    calc μ (ball 0 1) * ENNReal.ofReal (C - u z) =
        ∫⁻ _y in ball (0 : E) 1, ENNReal.ofReal (C - u z) ∂μ := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ y in ball (0 : E) 1,
          liminf (fun k => ENNReal.ofReal (C - u (z + s k • y))) atTop ∂μ :=
        lintegral_mono fun y => hray y
      _ ≤ _ := lintegral_liminf_le hmeas
  have hball0 : μ (ball (0 : E) 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hlt : μ (ball 0 1) * t < μ (ball 0 1) * ENNReal.ofReal (C - u z) :=
    (ENNReal.mul_lt_mul_iff_right hball0 measure_ball_lt_top.ne).mpr ht
  obtain ⟨k, hk⟩ := (eventually_lt_of_lt_liminf (hlt.trans_le hlow)).exists
  refine ⟨s k, ⟨hs k, hsρ k⟩, ?_⟩
  have hvol := Measure.addHaar_ball_mul_of_pos μ (0 : E) (hs k) 1
  rw [mul_one] at hvol
  rw [lintegral_ball_eq_ofReal_mul_lintegral_unitBall μ _ z (hs k), hvol, mul_assoc]
  exact (ENNReal.mul_lt_mul_iff_right (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    ENNReal.ofReal_ne_top).mpr hk

/-- **Upper semicontinuity from ball averages.** A nonnegative Borel function
that is locally bounded above and subharmonic on every connected component of
every affine complex-line section of an open set is upper semicontinuous there.-/
theorem LineSubharmonicOn.upperSemicontinuousOn {u : E → ℝ} {D : Set E} (hD : IsOpen D)
    (hl : LineSubharmonicOn u D) (hu : Measurable u) (hpos : ∀ x ∈ D, 0 ≤ u x)
    (hbdd : ∀ p ∈ D, ∃ r > 0, BddAbove (u '' ball p r)) : UpperSemicontinuousOn u D := by
  intro z hz
  suffices h : UpperSemicontinuousAt u z from h.upperSemicontinuousWithinAt D
  intro b hb
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact Eventually.of_forall fun x => (Subsingleton.elim z x) ▸ hb
  let μ : Measure E := Measure.addHaar
  obtain ⟨r₁, hr₁, C₀, hC₀⟩ := hbdd z hz
  obtain ⟨r₂, hr₂, hr₂D⟩ := Metric.isOpen_iff.mp hD z hz
  obtain ⟨ρ, hρ, h2ρ₁, h2ρ₂⟩ : ∃ ρ > 0, 2 * ρ ≤ r₁ ∧ 2 * ρ ≤ r₂ :=
    ⟨min r₁ r₂ / 2, by positivity, by linarith [min_le_left r₁ r₂],
      by linarith [min_le_right r₁ r₂]⟩
  have h2ρD : ball z (2 * ρ) ⊆ D := (ball_subset_ball h2ρ₂).trans hr₂D
  set b' := (u z + b) / 2 with hb'
  set C := max C₀ (b + 1) with hC
  have hCbound : ∀ x ∈ ball z (2 * ρ), u x ≤ C := fun x hx =>
    (hC₀ ⟨x, ball_subset_ball h2ρ₁ hx, rfl⟩).trans (le_max_left _ _)
  have hbC : b + 1 ≤ C := le_max_right _ _
  have ht : ENNReal.ofReal (C - b') < ENNReal.ofReal (C - u z) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  obtain ⟨r, ⟨hr, hrρ⟩, hlt⟩ := hl.exists_ball_deficit_gt hD hu μ hz C ht hρ
  let d' : E → ℝ≥0∞ := (ball z (2 * ρ)).indicator (fun x => ENNReal.ofReal (C - u x))
  have hd' : Measurable d' :=
    ((measurable_const.sub hu).ennreal_ofReal).indicator measurableSet_ball
  have hfin : ∫⁻ x, d' x ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono (g := (ball z (2 * ρ)).indicator
      (fun _ => ENNReal.ofReal C)) ?_)
    · rw [lintegral_indicator_const measurableSet_ball]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
    · intro x
      by_cases hx : x ∈ ball z (2 * ρ)
      · simp only [d', indicator_of_mem hx]
        exact ENNReal.ofReal_le_ofReal (by linarith [hpos x (h2ρD hx)])
      · simp [d', indicator_of_notMem hx]
  have hcont := continuousAt_lintegral_ball hd' hfin (Measure.addHaar_sphere μ z r)
  have hdeq : ∀ y, ball y r ⊆ ball z (2 * ρ) →
      ∫⁻ x in ball y r, d' x ∂μ = ∫⁻ x in ball y r, ENNReal.ofReal (C - u x) ∂μ :=
    fun y hy => setLIntegral_congr_fun measurableSet_ball
      (fun x hx => indicator_of_mem (hy hx) _)
  have hzsub : ball z r ⊆ ball z (2 * ρ) := ball_subset_ball (by linarith)
  have hev : ∀ᶠ y in 𝓝 z, μ (ball 0 r) * ENNReal.ofReal (C - b') <
      ∫⁻ x in ball y r, d' x ∂μ :=
    hcont.eventually (lt_mem_nhds (by simpa only [hdeq z hzsub] using hlt))
  filter_upwards [hev, ball_mem_nhds z hρ] with y hy hyz
  have hsub : ball y r ⊆ ball z (2 * ρ) :=
    ball_subset_ball' (by rw [mem_ball] at hyz; linarith)
  have hsm := hl.ball_deficit_le hu μ y r C (hsub.trans h2ρD) (fun x hx => hCbound x (hsub hx))
  rw [hdeq y hsub] at hy
  have htd := (ENNReal.mul_lt_mul_iff_right (measure_ball_pos μ 0 hr).ne'
    measure_ball_lt_top.ne).mp (hy.trans_le hsm)
  rw [ENNReal.ofReal_lt_ofReal_iff'] at htd
  linarith [htd.1]

end PshLines.PSHD
