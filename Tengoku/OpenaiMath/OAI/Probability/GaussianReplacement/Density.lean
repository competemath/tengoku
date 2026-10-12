import Tengoku.OpenaiMath.OAI.Probability.GaussianReplacement.MixedReplica

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace

def cubeKernel (δ : ℝ) : ℝ → ℝ≥0∞ :=
  Set.indicator (Set.Icc (-δ) δ) (fun _ => ENNReal.ofReal ((2*δ)⁻¹))

lemma measurable_cubeKernel (δ : ℝ) : Measurable (cubeKernel δ) :=
  measurable_const.indicator measurableSet_Icc

lemma lintegral_cubeKernel {δ : ℝ} (hδ : 0 < δ) : ∫⁻ z, cubeKernel δ z = 1 := by
  rw [cubeKernel, lintegral_indicator measurableSet_Icc, lintegral_const,
    Measure.restrict_apply_univ, Real.volume_Icc]
  rw [← ENNReal.ofReal_mul (by positivity)]
  have he : δ - -δ = 2*δ := by ring
  rw [he, inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one]

lemma rowKernel_cube {k d : ℕ} (δ : ℝ) (hδ : 0 ≤ δ) (s u : Vector d) (G : Rows k d) :
    rowKernel (cubeKernel δ) s u G =
      Set.indicator {v : Vector d | ∀ i, |label G v i - label G s i| ≤ δ}
        (fun _ => ENNReal.ofReal ((2*δ)⁻¹ ^ k)) u := by
  classical
  have hi (i : Fin k) : ⟪u-s, G i⟫ = label G u i-label G s i := inner_sub_left _ _ _
  have hab (x : ℝ) : x ∈ Set.Icc (-δ) δ ↔ |x| ≤ δ := abs_le.symm
  by_cases h : ∀ i, |label G u i-label G s i| ≤ δ
  · rw [Set.indicator_of_mem (show u ∈ {v : Vector d | ∀ i, |label G v i-label G s i| ≤ δ} from h)]
    unfold rowKernel
    have he (i : Fin k) : cubeKernel δ ⟪u-s, G i⟫ = ENNReal.ofReal ((2*δ)⁻¹) := by
      exact Set.indicator_of_mem ((hab _).2 (by simpa only [hi] using h i)) _
    simp_rw [he]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.ofReal_pow (by positivity)]
  · rw [Set.indicator_of_notMem (show u ∉ {v : Vector d | ∀ i, |label G v i-label G s i| ≤ δ} from h)]
    push Not at h
    obtain ⟨i, hi'⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact Set.indicator_of_notMem (by simpa only [hi, hab, not_le] using hi') _

lemma cubeAverage_eq_kernel {k d : ℕ} (ρ : Measure (Sphere d)) (δ : ℝ) (hδ : 0 ≤ δ)
    (s : Sphere d) (G : Rows k d) :
    cubeAverage ρ G (label G (s:Vector d)) δ =
      ∫⁻ u, rowKernel (cubeKernel δ) (s:Vector d) u G ∂sphereLift ρ := by
  have hm : Measurable (fun u : Vector d => rowKernel (cubeKernel δ) (s:Vector d) u G) :=
    measurable_rowKernel_left (cubeKernel δ) (measurable_cubeKernel δ) k (s:Vector d) G
  rw [sphereLift, lintegral_map hm continuous_subtype_val.measurable]
  simp_rw [rowKernel_cube δ hδ]
  have hset : MeasurableSet {u : Sphere d | ∀ i, |label G (u:Vector d) i - label G (s:Vector d) i| ≤ δ} := by
    rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (by unfold label; fun_prop) measurable_const
  change _ = ∫⁻ u : Sphere d, Set.indicator
    {u : Sphere d | ∀ i, |label G (u:Vector d) i-label G (s:Vector d) i| ≤ δ}
      (fun (_ : Sphere d) => ENNReal.ofReal ((2*δ)⁻¹ ^ k)) u ∂ρ
  rw [lintegral_indicator hset, lintegral_const, Measure.restrict_apply_univ]
  rfl

section AppendPi
variable {E : Type*} [MeasurableSpace E]

end AppendPi

lemma cubeAverage_scale_lower {k d : ℕ} (ρ : Measure (Sphere d)) (G : Rows k d)
    (y : Fin k → ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ENNReal.ofReal ((a/b)^k) * cubeAverage ρ G y a ≤ cubeAverage ρ G y b := by
  have hb : 0 < b := ha.trans_le hab
  unfold cubeAverage
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_pow]
  have he : a / b * (2*a)⁻¹ = (2*b)⁻¹ := by field_simp
  rw [he]
  exact mul_le_mul' le_rfl (measure_mono (fun u hu i => (hu i).trans hab))

lemma cubeAverage_scale_upper {k d : ℕ} (ρ : Measure (Sphere d)) (G : Rows k d)
    (y : Fin k → ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    cubeAverage ρ G y a ≤ ENNReal.ofReal ((b/a)^k) * cubeAverage ρ G y b := by
  have hb : 0 < b := ha.trans_le hab
  unfold cubeAverage
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_pow]
  have he : b / a * (2*b)⁻¹ = (2*a)⁻¹ := by field_simp
  rw [he]
  exact mul_le_mul' le_rfl (measure_mono (fun u hu i => (hu i).trans hab))

lemma tendsto_cube_of_recip_nat {k d : ℕ} (ρ : Measure (Sphere d)) (G : Rows k d)
    (y : Fin k → ℝ) {L : ℝ≥0∞}
    (h : Tendsto (fun j : ℕ => cubeAverage ρ G y (1/(j:ℝ))) atTop (𝓝 L)) :
    Tendsto (fun δ : ℝ => cubeAverage ρ G y δ) (𝓝[>] 0) (𝓝 L) := by
  have hj : Tendsto (fun t : ℝ => Nat.floor t) atTop atTop := tendsto_nat_floor_atTop
  have hj1 : Tendsto (fun t : ℝ => Nat.floor t + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hj
  have hratio : Tendsto (fun t : ℝ => (Nat.floor t:ℝ)/t) atTop (𝓝 1) :=
    tendsto_nat_floor_div_atTop
  have hratio1 : Tendsto (fun t : ℝ => ((Nat.floor t:ℝ)+1)/t) atTop (𝓝 1) := by
    have hz : Tendsto (fun t : ℝ => (1:ℝ)/t) atTop (𝓝 (0:ℝ)) := by
      simpa only [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 (0:ℝ)))
    have hh := hratio.add hz
    simpa only [add_zero, ← add_div] using hh
  have hlo : Tendsto (fun t : ℝ => ENNReal.ofReal ((t/((Nat.floor t:ℝ)+1))^k) *
      cubeAverage ρ G y (1/(Nat.floor t+1:ℕ))) atTop (𝓝 L) := by
    have hh := (hratio1.inv₀ (by norm_num)).pow k
    simp only [inv_div, inv_one, one_pow] at hh
    simpa only [ENNReal.ofReal_one, one_mul, Nat.cast_add, Nat.cast_one, Function.comp_def] using
      ENNReal.Tendsto.mul ((ENNReal.continuous_ofReal.tendsto 1).comp hh)
        (Or.inl (by simp)) (h.comp hj1) (Or.inr (by simp))
  have hhi : Tendsto (fun t : ℝ => ENNReal.ofReal ((t/(Nat.floor t:ℝ))^k) *
      cubeAverage ρ G y (1/(Nat.floor t:ℝ))) atTop (𝓝 L) := by
    have hh := (hratio.inv₀ (by norm_num)).pow k
    simp only [inv_div, inv_one, one_pow] at hh
    simpa only [ENNReal.ofReal_one, one_mul, Function.comp_def] using
      ENNReal.Tendsto.mul ((ENNReal.continuous_ofReal.tendsto 1).comp hh)
        (Or.inl (by simp)) (h.comp hj) (Or.inr (by simp))
  have ht : Tendsto (fun t : ℝ => cubeAverage ρ G y (1/t)) atTop (𝓝 L) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
      have ht0 : 0 < t := by linarith
      have hn : 0 < (Nat.floor t:ℝ) := by exact_mod_cast (Nat.floor_pos.mpr ht)
      have hn1 : 0 < (Nat.floor t:ℝ)+1 := by positivity
      have hlt : t < (Nat.floor t:ℝ)+1 := Nat.lt_floor_add_one t
      have hlow := cubeAverage_scale_lower ρ G y (one_div_pos.mpr hn1)
        ((one_div_le_one_div hn1 ht0).mpr hlt.le)
      simpa only [Nat.cast_add, Nat.cast_one, one_div, inv_div_inv] using hlow
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
      have ht0 : 0 < t := by linarith
      have hn : 0 < (Nat.floor t:ℝ) := by exact_mod_cast (Nat.floor_pos.mpr ht)
      have hle : (Nat.floor t:ℝ) ≤ t := Nat.floor_le ht0.le
      have hupp := cubeAverage_scale_upper ρ G y (one_div_pos.mpr ht0)
        ((one_div_le_one_div ht0 hn).mpr hle)
      simpa only [one_div, inv_div_inv] using hupp
  simpa only [Function.comp_def, one_div, inv_inv] using ht.comp tendsto_inv_nhdsGT_zero

lemma measurable_cubeAverage {k d : ℕ} (ρ : Measure (Sphere d)) [SFinite ρ] (δ : ℝ) :
    Measurable (fun z : Rows k d × (Fin k → ℝ) => cubeAverage ρ z.1 z.2 δ) := by
  have hset : MeasurableSet {z : (Rows k d × (Fin k → ℝ)) × Sphere d |
      ∀ i, |label z.1.1 (z.2:Vector d) i-z.1.2 i| ≤ δ} := by
    rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (by unfold label; fun_prop) measurable_const
  exact measurable_const.mul (measurable_measure_prodMk_left hset)

def extendedCubeDensity {k d : ℕ} (ρ : Measure (Sphere d)) (G : Rows k d)
    (y : Fin k → ℝ) : ℝ≥0∞ :=
  liminf (fun j : ℕ => cubeAverage ρ G y (1/(j:ℝ))) atTop

lemma measurable_extendedCubeDensity {k d : ℕ} (ρ : Measure (Sphere d)) [SFinite ρ] :
    Measurable (fun z : Rows k d × (Fin k → ℝ) => extendedCubeDensity ρ z.1 z.2) :=
  Measurable.liminf (fun j => measurable_cubeAverage ρ (1/(j:ℝ)))

lemma cubeAverage_lt_top {k d : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (G : Rows k d) (y : Fin k → ℝ) (δ : ℝ) : cubeAverage ρ G y δ < ∞ := by
  unfold cubeAverage
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

lemma exactDensity_eq_of_tendsto {k d : ℕ} (ρ : Measure (Sphere d))
    (G : Rows k d) (y : Fin k → ℝ) {L : ℝ≥0∞}
    (hL : Tendsto (fun j : ℕ => cubeAverage ρ G y (1/(j:ℝ))) atTop (𝓝 L))
    (hLt : L ≠ ∞) : exactDensity ρ G y = L := by
  have ht : Tendsto (fun j : ℕ => (cubeAverage ρ G y (1/(j:ℝ))).toReal)
      atTop (𝓝 L.toReal) := (ENNReal.continuousAt_toReal hLt).tendsto.comp hL
  unfold exactDensity
  dsimp only
  split_ifs with h
  · rw [tendsto_nhds_unique h.choose_spec ht, ENNReal.ofReal_toReal hLt]
  · exact False.elim (h ⟨L.toReal, ht⟩)

lemma measurable_exactDensity {k d : ℕ} (ρ : Measure (Sphere d)) [SFinite ρ] :
    Measurable (fun z : Rows k d × (Fin k → ℝ) => exactDensity ρ z.1 z.2) := by
  classical
  let f : ℕ → (Rows k d × (Fin k → ℝ)) → ℝ := fun j z =>
    (cubeAverage ρ z.1 z.2 (1/(j:ℝ))).toReal
  have hf (j : ℕ) : Measurable (f j) := (measurable_cubeAverage ρ _).ennreal_toReal
  let T : Set (Rows k d × (Fin k → ℝ)) := {z | ∃ L : ℝ, Tendsto (fun j => f j z) atTop (𝓝 L)}
  have hT : MeasurableSet T := measurableSet_exists_tendsto hf
  let g : (Rows k d × (Fin k → ℝ)) → ℝ := fun z =>
    if h : z ∈ T then h.choose else 0
  have hg : Measurable g := by
    apply measurable_of_tendsto_metrizable (fun j => (hf j).indicator hT)
    apply tendsto_pi_nhds.mpr
    intro z
    by_cases h : z ∈ T
    · simpa only [Set.indicator_of_mem h, g, dite_eq_left h] using h.choose_spec
    · simpa only [Set.indicator_of_notMem h, g, dite_eq_right h] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  convert hg.ennreal_ofReal using 1
  funext z
  unfold exactDensity
  dsimp [g, T, f]
  split_ifs <;> simp only [ENNReal.ofReal_zero]

def labelLaw {k d : ℕ} (ρ : Measure (Sphere d)) (G : Rows k d) : Measure (Fin k → ℝ) :=
  ρ.map (fun s : Sphere d => label G (s:Vector d))

instance labelLaw_isFiniteMeasure {k d : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (G : Rows k d) : IsFiniteMeasure (labelLaw ρ G) := by unfold labelLaw; infer_instance

lemma cubeAverage_eq_ball_ratio {k d : ℕ} (ρ : Measure (Sphere d)) (G : Rows k d)
    (y : Fin k → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    cubeAverage ρ G y δ = labelLaw ρ G (Metric.closedBall y δ) /
      volume (Metric.closedBall y δ) := by
  rw [labelLaw, Measure.map_apply (by unfold label; fun_prop)
    Metric.isClosed_closedBall.measurableSet, Real.volume_pi_closedBall y hδ.le]
  have hset : {s : Sphere d | ∀ i, |label G (s:Vector d) i-y i| ≤ δ} =
      (fun s : Sphere d => label G (s:Vector d)) ⁻¹' Metric.closedBall y δ := by
    ext s
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm,
      pi_norm_le_iff_of_nonneg hδ.le, Pi.sub_apply, Real.norm_eq_abs, Set.mem_ofPred_eq]
  unfold cubeAverage
  rw [hset, Fintype.card_fin, div_eq_mul_inv, mul_comm]
  congr 1
  rw [← ENNReal.ofReal_inv_of_pos (by positivity), inv_pow]

lemma tendsto_cube_scale : Tendsto (fun j : ℕ => 1/(j:ℝ)) atTop (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨tendsto_one_div_atTop_nhds_zero_nat, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with j hj
  simp only [Set.mem_Ioi]
  positivity

lemma ae_cube_tendsto_positive {k d : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (G : Rows k d) :
    ∀ᵐ (s : Sphere d) ∂ρ,
      Tendsto (fun j : ℕ => cubeAverage ρ G (label G (s:Vector d)) (1/(j:ℝ)))
        atTop (𝓝 (extendedCubeDensity ρ G (label G (s:Vector d)))) ∧
      0 < extendedCubeDensity ρ G (label G (s:Vector d)) := by
  have hlabel : ∀ᵐ y ∂labelLaw ρ G,
      Tendsto (fun j : ℕ => cubeAverage ρ G y (1/(j:ℝ)))
        atTop (𝓝 (extendedCubeDensity ρ G y)) ∧ 0 < extendedCubeDensity ρ G y := by
    filter_upwards [Besicovitch.ae_tendsto_rnDeriv volume (labelLaw ρ G),
      Measure.rnDeriv_ne_top volume (labelLaw ρ G)] with y hy hyt
    have ht := (hy.comp tendsto_cube_scale).inv
    have he : (fun j : ℕ => cubeAverage ρ G y (1/(j:ℝ))) =ᶠ[atTop]
        (fun j : ℕ => (volume (Metric.closedBall y (1/(j:ℝ))) /
          labelLaw ρ G (Metric.closedBall y (1/(j:ℝ))))⁻¹) := by
      filter_upwards [eventually_ge_atTop 1] with j hj
      have hjp : 0 < 1/(j:ℝ) := by positivity
      rw [cubeAverage_eq_ball_ratio ρ G y hjp,
        ENNReal.inv_div (Or.inl (measure_ne_top _ _))]
      exact Or.inr (by rw [Real.volume_pi_closedBall y hjp.le]; positivity)
    have htc := ht.congr' he.symm
    have heq : extendedCubeDensity ρ G y = (volume.rnDeriv (labelLaw ρ G) y)⁻¹ := htc.liminf_eq
    exact ⟨heq.symm ▸ htc, heq.symm ▸ ENNReal.inv_pos.mpr hyt⟩
  exact ae_of_ae_map (by unfold label; fun_prop) hlabel

lemma mixed_liminf_moment_le {A T : Type*} [MeasurableSpace A] [MeasurableSpace T]
    (μ : Measure A) (ν : Measure T) [SFinite ν]
    (f : ℕ → A × T → ℝ≥0∞) (hf : ∀ j, Measurable (f j)) (q : ℕ) :
    ∫⁻ a, (∫⁻ t, liminf (fun j => f j (a,t)) atTop ∂ν)^q ∂μ ≤
      liminf (fun j => ∫⁻ a, (∫⁻ t, f j (a,t) ∂ν)^q ∂μ) atTop := by
  calc
    _ ≤ ∫⁻ a, liminf (fun j => (∫⁻ t, f j (a,t) ∂ν)^q) atTop ∂μ := by
      apply lintegral_mono
      intro a
      have hfa (j : ℕ) : Measurable (fun t => f j (a,t)) :=
        (hf j).comp (measurable_const.prodMk measurable_id)
      calc
        _ ≤ (liminf (fun j => ∫⁻ t, f j (a,t) ∂ν) atTop)^q :=
          pow_le_pow_left' (lintegral_liminf_le hfa) q
        _ = _ := (show Monotone (fun x : ℝ≥0∞ => x^q) from
            fun _ _ h => pow_le_pow_left' h q).map_liminf_of_continuousAt _
              (ENNReal.continuous_pow q).continuousAt
    _ ≤ _ := lintegral_liminf_le (fun j =>
      (show Measurable (Function.uncurry (fun a t => f j (a,t))) from hf j).lintegral_prod_right.pow_const q)

instance gaussianRows_isProbabilityMeasure (k d : ℕ) : IsProbabilityMeasure (gaussianRows k d) := by
  unfold gaussianRows
  infer_instance

end CurrentProjection

end

end OAI
