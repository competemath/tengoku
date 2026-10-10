import Tengoku.OpenaiMath.OAI.Analysis.Daugavet.ProductSeparation

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

universe uB uR uIota uKappa

namespace ExactModuli.KW

section ProductModels
variable {κ : Type uKappa} {ι : Type uIota} [Fintype κ] [Fintype ι]
variable {B : Type uB} [MeasurableSpace B] {μ : Measure B} [IsProbabilityMeasure μ]

lemma whole_ball_estimate {R : Type uR} [MeasurableSpace R] {ν : Measure R}
    [IsProbabilityMeasure ν] {g : B × R → ℝ} {ψ U : B → ℝ}
    (hg : Integrable g (μ.prod ν)) (hψ : Integrable ψ μ) (hU : Integrable U μ)
    (hU0 : ∀ b, 0 ≤ U b) {m r q h : ℝ} (hm : ∫ b, U b ∂μ = m)
    (hm0 : 0 ≤ m) (hr : 0 ≤ r) (hq : 0 ≤ q) (hmq : m * q < 1) (hh : 0 < h)
    (hg1 : ∫ z, |g z| ∂(μ.prod ν) ≤ 1)
    {D : Set R} (hD : MeasurableSet D) (hDprob : 1 - m * q ≤ ν.real D)
    (hgood : ∀ b v, v ∈ D → |g (b, v) - ψ b| ≤ r * U b) :
    (∫ b, |normalizeFunction μ ψ b| ∂μ) ≤ 1 ∧
    (μ.prod ν).real {z | h < |g z - normalizeFunction μ ψ z.1|} ≤
      m * q + h⁻¹ * (2 * m * r + (1 - m * q)⁻¹ - 1) := by
  have hL : 0 < 1 - m * q := sub_pos.mpr hmq
  have hDpos := hL.trans_le hDprob
  have hN := old_norm_on_good_set hg hψ hU hU0 hm hr hg1 hD hDpos hgood
  have hinv : 1 / ν.real D ≤ 1 / (1 - m * q) := one_div_le_one_div_of_le hL hDprob
  have hR : 1 ≤ r * m + (1 - m * q)⁻¹ := by
    have hinv1 : 1 ≤ (1 - m * q)⁻¹ := by
      apply (one_le_inv₀ hL).mpr
      nlinarith
    nlinarith
  have hNb : (∫ b, |ψ b| ∂μ) ≤ r * m + (1 - m * q)⁻¹ := by
    simp only [one_div] at hinv hN
    linarith
  obtain ⟨hnorm, hcost⟩ := normalizeFunction_bounds hψ hR hNb
  refine ⟨hnorm, ?_⟩
  let ψ₀ := normalizeFunction μ ψ
  have hψ₀ : Integrable ψ₀ μ := integrable_normalizeFunction hψ
  let f : B × R → ℝ := fun z => |g z - ψ₀ z.1|
  let bnd : B × R → ℝ := fun z => r * U z.1 + |ψ z.1 - ψ₀ z.1|
  have hψpull : Integrable (fun z : B × R => ψ₀ z.1) (μ.prod ν) :=
    (measurePreserving_fst.integrable_comp hψ₀.aestronglyMeasurable).mpr hψ₀
  have hf : Integrable f (μ.prod ν) := (hg.sub hψpull).abs
  have hbi : Integrable bnd (μ.prod ν) :=
    ((measurePreserving_fst.integrable_comp hU.aestronglyMeasurable).mpr hU |>.const_mul r).add
      ((measurePreserving_fst.integrable_comp (hψ.sub hψ₀).abs.aestronglyMeasurable).mpr (hψ.sub hψ₀).abs)
  have hbint : (∫ z, bnd z ∂(μ.prod ν)) ≤ 2 * m * r + (1 - m * q)⁻¹ - 1 := by
    dsimp [bnd]
    rw [integral_add (f := fun z : B × R => r * U z.1)
      (g := fun z => |ψ z.1 - ψ₀ z.1|)
      (((measurePreserving_fst.integrable_comp hU.aestronglyMeasurable).mpr hU).const_mul r)
      ((measurePreserving_fst.integrable_comp (hψ.sub hψ₀).abs.aestronglyMeasurable).mpr (hψ.sub hψ₀).abs),
      integral_const_mul, mp_integral measurePreserving_fst hU.aestronglyMeasurable, hm,
      mp_integral (g := fun b => |ψ b - ψ₀ b|) measurePreserving_fst (hψ.sub hψ₀).abs.aestronglyMeasurable]
    dsimp [ψ₀] at *
    linarith
  have hmark := restricted_markov hf hbi (fun z => abs_nonneg _)
    (fun z => add_nonneg (mul_nonneg hr (hU0 _)) (abs_nonneg _))
    (hD.preimage measurable_snd) (fun z hz => by
      dsimp [f, bnd]
      exact (abs_sub_le (g z) (ψ z.1) (ψ₀ z.1)).trans
        (add_le_add (hgood z.1 z.2 hz) le_rfl)) hh
  have hcompl : (μ.prod ν).real (Prod.snd ⁻¹' D)ᶜ ≤ m * q := by
    rw [← Set.preimage_compl]
    have heq := (measurePreserving_snd : MeasurePreserving (@Prod.snd B R) (μ.prod ν) ν).measure_preimage hD.compl.nullMeasurableSet
    rw [measureReal_def, heq, ← measureReal_def, probReal_compl_eq_one_sub hD]
    linarith
  apply hmark.trans
  have hdiv := div_le_div_of_nonneg_right hbint hh.le
  apply add_le_add hcompl
  simpa only [div_eq_mul_inv, mul_comm] using hdiv

def oldCombination (x : B → ℝ) (u : κ → B → ℝ) (c : κ → ℝ) (b : B) : ℝ :=
  x b + ∑ k, c k * u k b

omit [IsProbabilityMeasure μ] in
lemma integrable_oldCombination [IsProbabilityMeasure μ] {x : B → ℝ} {u : κ → B → ℝ}
    (hx : Integrable x μ) (hu : ∀ k, Integrable (u k) μ) (c : κ → ℝ) :
    Integrable (oldCombination x u c) μ := by
  exact hx.add (integrable_finsetSum _ (fun k _ => (hu k).const_mul (c k)))

lemma enlargement_parameters {m h : ℝ} (_hm : 0 < m) (hh : 0 < h) (_hh1 : h < 1) :
    ∃ c r q p : ℝ, 0 < c ∧ c < h / 4 ∧ 0 < r ∧ 0 < q ∧ 1 < p ∧ p ≤ 3/2 ∧
      m * q < 1 ∧ m * q + h⁻¹ * (2 * m * r + (1 - m * q)⁻¹ - 1) < h ∧
      scale p < c ∧ 2 * ((scale p / c) ^ p + c) < h ∧ 10 * (108 * scale p / r) ^ p < q := by
  let c := h / 8
  have hc : 0 < c := by dsimp [c]; positivity
  have hc4 : c < h / 4 := by dsimp [c]; linarith
  have hc2 : 2 * c < h := by dsimp [c]; linarith
  let err := fun v : ℝ => m * v + h⁻¹ * (2 * m * v + (1 - m * v)⁻¹ - 1)
  have herrc : ContinuousAt err 0 := by
    dsimp [err]
    fun_prop (disch := norm_num)
  have herr0 : err 0 = 0 := by simp [err]
  have hevent : ∀ᶠ v in 𝓝 (0 : ℝ), m * v < 1 ∧ err v < h := by
    apply Filter.Eventually.and
    · exact (show ContinuousAt (fun v : ℝ => m * v) 0 by fun_prop).tendsto
        |>.eventually (Iio_mem_nhds (by norm_num))
    · exact herrc.tendsto.eventually (Iio_mem_nhds (by simpa only [herr0] using hh))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hevent
  let r := δ / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrd : dist r 0 < δ := by simpa only [Real.dist_eq, sub_zero, abs_of_pos hr] using (show r < δ by dsimp [r]; linarith)
  obtain ⟨hmr, herr⟩ := hball hrd
  have hs : ContinuousAt scale 1 := by unfold scale; fun_prop (disch := norm_num)
  have hs1 : scale 1 = 0 := by norm_num [scale]
  have hpowc : ContinuousAt (fun p : ℝ => (scale p / c) ^ p) 1 := by
    apply ContinuousAt.rpow (hs.div_const c) continuousAt_id
    right; norm_num
  have hpowr : ContinuousAt (fun p : ℝ => (108 * scale p / r) ^ p) 1 := by
    apply ContinuousAt.rpow ((hs.const_mul 108).div_const r) continuousAt_id
    right; norm_num
  have hpEv : ∀ᶠ p in 𝓝 (1 : ℝ), p < 3/2 ∧ scale p < c ∧
      2 * ((scale p / c) ^ p + c) < h ∧ 10 * (108 * scale p / r) ^ p < r := by
    filter_upwards [eventually_lt_nhds (by norm_num : (1 : ℝ) < 3/2),
      hs.tendsto.eventually (Iio_mem_nhds (by simpa only [hs1] using hc)),
      ((hpowc.add_const c).const_mul 2).tendsto.eventually (Iio_mem_nhds (by simpa [hs1] using hc2)),
      (hpowr.const_mul 10).tendsto.eventually (Iio_mem_nhds (by simpa [hs1] using hr))]
      with p hp₁ hp₂ hp₃ hp₄
    exact ⟨hp₁, hp₂, hp₃, hp₄⟩
  obtain ⟨ε, hε, hpball⟩ := Metric.eventually_nhds_iff.mp hpEv
  let p := 1 + ε / 2
  have hp : 1 < p := by dsimp [p]; linarith
  have hpd : dist p 1 < ε := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hp)]
    dsimp [p]; linarith
  obtain ⟨hpmax, hpc, hpc2, hpq⟩ := hpball hpd
  exact ⟨c, r, r, p, hc, hc4, hr, hr, hp, hpmax.le, hmr, herr, hpc, hpc2, hpq⟩

end ProductModels

end ExactModuli.KW

end

end OAI
