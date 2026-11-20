import Tengoku.PshdLean.PshLines.PSHD.GaussianEnergy
import Tengoku.Seed.Analysis.Fourier.LpSpace
import Tengoku.Seed.Analysis.Distribution.TemperedDistribution
import Tengoku.Seed.Geometry.Manifold.PartitionOfUnity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Measures with square-integrable Fourier transform

A finite measure whose transform is square integrable has a square-integrable
density with the same norm, as used in `pshd-vibe`, Lemma 1.4.
-/

noncomputable section

open MeasureTheory SchwartzMap Set Filter Metric
open scoped Topology ContDiff Manifold
open scoped RealInnerProductSpace FourierTransform ENNReal

namespace PshLines.PSHD

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- Testing the transform of a finite measure against a Schwartz function.
@isnad1 id=eq.0h3v.s8.fc444b56bb85 from=translated src=- shape=aaef8dc1 vocab=d41f110f
-/
theorem integral_fourier_schwartz_eq (η : Measure E) [IsFiniteMeasure η] (g : 𝓢(E, ℂ)) :
    ∫ x, 𝓕 g x ∂η = ∫ ξ, g ξ * measureFourier η ξ := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (μ := η) (ν := volume) (L := innerₗ E) (f := fun _ ↦ (1 : ℂ))
    (g := fun ξ : E ↦ g ξ)
    Real.continuous_fourierChar (by simpa using continuous_inner) (integrable_const 1)
    g.integrable
  simp only [← measureFourier_eq_vectorFourier, smul_eq_mul, one_mul] at h
  simp_rw [mul_comm (g _), h, flip_innerₗ]
  rfl

/-- The inverse `L²` transform of the transform of a finite measure represents the
measure on Schwartz tests.
@isnad1 id=eq.1h3v.s10.26870b38996e from=translated src=- shape=f5b4b5c0 vocab=ab3922b7
-/
theorem integral_schwartz_eq_fourierInv (η : Measure E) [IsFiniteMeasure η]
    (hF : MemLp (measureFourier η) 2) (g : 𝓢(E, ℂ)) :
    ∫ x, g x ∂η = ∫ x, g x * (𝓕⁻ (hF.toLp (measureFourier η)) : Lp ℂ 2 (volume : Measure E)) x := by
  have h1 : 𝓕 (η.toTemperedDistribution) =
      ((hF.toLp (measureFourier η) : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E, ℂ)) := by
    ext g
    rw [TemperedDistribution.fourier_apply, Measure.toTemperedDistribution_apply η,
      Lp.toTemperedDistribution_apply, integral_fourier_schwartz_eq]
    refine integral_congr_ae ?_
    filter_upwards [hF.coeFn_toLp] with x hx
    simp [hx]
  have h2 : η.toTemperedDistribution =
      ((𝓕⁻ (hF.toLp (measureFourier η)) : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E, ℂ)) := by
    rw [← Lp.fourierInv_toTemperedDistribution_eq, ← h1, FourierTransform.fourierInv_fourier_eq]
  have h3 := congrArg (fun T : 𝓢'(E, ℂ) ↦ T g) h2
  simpa using h3

section CompactDetermination

variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Compact sets generate the Borel sets of a proper metric space.
@isnad1 id=eq.0h1v.s5.ce244ca3371e from=translated src=- shape=9ef9b437 vocab=c8b7bb6b
-/
theorem borel_eq_generateFrom_isCompact :
    ‹MeasurableSpace X› = MeasurableSpace.generateFrom {K : Set X | IsCompact K} := by
  refine le_antisymm ?_ (MeasurableSpace.generateFrom_le fun K hK ↦ hK.isClosed.measurableSet)
  rw [BorelSpace.measurable_eq (α := X), borel_eq_generateFrom_isClosed]
  refine MeasurableSpace.generateFrom_le fun C hC ↦ ?_
  obtain ⟨x₀⟩ | hempty := isEmpty_or_nonempty X
  · simp [Set.eq_empty_of_isEmpty C]
  · rcases hempty with ⟨x₀⟩
    have hC' : C = ⋃ n : ℕ, C ∩ closedBall x₀ n := by
      ext x
      simp only [mem_iUnion, mem_inter_iff, mem_closedBall]
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_ge (dist x x₀)
        exact ⟨n, hx, hn⟩
      · rintro ⟨_, hx, _⟩
        exact hx
    rw [hC']
    exact MeasurableSet.iUnion fun n ↦ MeasurableSpace.measurableSet_generateFrom
      ((isCompact_closedBall x₀ n).inter_left hC)

/-- Measures finite on compact sets are determined by their values on compact sets.
@isnad1 id=eq.1h3v.s6.380b688f0eab from=translated src=- shape=56e61270 vocab=5a0e6c3f
-/
theorem Measure.ext_of_isCompact {μ ν : Measure X} [IsFiniteMeasureOnCompacts μ]
    (h : ∀ K, IsCompact K → μ K = ν K) : μ = ν := by
  obtain hX | ⟨⟨x₀⟩⟩ := isEmpty_or_nonempty X
  · ext s
    simp [Set.eq_empty_of_isEmpty s]
  refine Measure.ext_of_generateFrom_of_iUnion {K : Set X | IsCompact K}
    (fun n : ℕ ↦ closedBall x₀ n) ?_ ?_ ?_ (fun n ↦ isCompact_closedBall x₀ n)
    (fun n ↦ (isCompact_closedBall x₀ n).measure_lt_top.ne) h
  · exact borel_eq_generateFrom_isCompact
  · intro K hK L hL _
    exact hK.inter_right hL.isClosed
  · exact iUnion_closedBall_nat x₀

end CompactDetermination

/-- Smooth compactly supported tests determine compact-set masses of a finite measure
represented by a locally integrable density.
@isnad1 id=eq.3h4v.s8.ee2dd6c23edb from=translated src=- shape=92cb3158 vocab=d53dad63
-/
theorem measureReal_isCompact_eq_setIntegral (η : Measure E) [IsFiniteMeasure η]
    {f : E → ℂ} (hf : LocallyIntegrable f)
    (h : ∀ g : E → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ x, (g x : ℂ) ∂η = ∫ x, (g x : ℂ) * f x)
    {s : Set E} (hs : IsCompact s) :
    ((η.real s : ℝ) : ℂ) = ∫ x in s, f x := by
  obtain ⟨δ, δpos, hδ⟩ : ∃ δ, 0 < δ ∧ IsCompact (cthickening δ s) :=
    hs.exists_isCompact_cthickening
  obtain ⟨u, -, u_pos, u_lim⟩ : ∃ u, StrictAnti u ∧ (∀ (n : ℕ), u n ∈ Ioo 0 δ)
    ∧ Tendsto u atTop (𝓝 0) := exists_seq_strictAnti_tendsto' δpos
  let v : ℕ → Set E := fun n ↦ thickening (u n) s
  obtain ⟨K, K_compact, vK⟩ : ∃ K, IsCompact K ∧ ∀ n, v n ⊆ K :=
    ⟨_, hδ, fun n ↦ thickening_subset_cthickening_of_le (u_pos n).2.le _⟩
  have : ∀ n, ∃ (g : E → ℝ), Function.support g = v n ∧ ContDiff ℝ ∞ g ∧ Set.range g ⊆ Set.Icc 0 1
          ∧ ∀ x ∈ s, g x = 1 := by
    intro n
    rcases exists_contMDiff_support_eq_eq_one_iff 𝓘(ℝ, E) isOpen_thickening hs.isClosed
      (self_subset_thickening (u_pos n).1 s) with ⟨g, g_smooth, g_range, g_supp, hg⟩
    exact ⟨g, g_supp, g_smooth.contDiff, g_range, fun x hx ↦ (hg x).1 hx⟩
  choose g g_supp g_diff g_range hg using this
  have g_le : ∀ n x, ‖(g n x : ℂ)‖ ≤ 1 := by
    intro n x
    have := g_range n (mem_range_self (f := g n) x)
    rw [Complex.norm_real, Real.norm_of_nonneg this.1]
    exact this.2
  have g_zero : ∀ n x, x ∉ K → g n x = 0 := by
    intro n x hxK
    rw [← Function.notMem_support, g_supp]
    contrapose hxK
    exact vK n hxK
  have g_lim : ∀ x, Tendsto (fun n ↦ (g n x : ℂ)) atTop (𝓝 (s.indicator (fun _ ↦ (1 : ℂ)) x)) := by
    intro x
    by_cases hxs : x ∈ s
    · simp [hg _ x hxs, indicator_of_mem hxs]
    · simp_rw [indicator_of_notMem hxs]
      apply tendsto_const_nhds.congr'
      obtain ⟨ε, εpos, hε⟩ : ∃ ε, 0 < ε ∧ x ∉ thickening ε s := by
        rw [← hs.isClosed.closure_eq, closure_eq_iInter_thickening s] at hxs
        simpa using hxs
      filter_upwards [(tendsto_order.1 u_lim).2 _ εpos] with n hn
      have : g n x = 0 := by
        rw [← Function.notMem_support, g_supp]
        contrapose hε
        exact thickening_mono hn.le s hε
      simp [this]
  have L₁ : Tendsto (fun n ↦ ∫ x, (g n x : ℂ) ∂η) atTop (𝓝 ((η.real s : ℝ) : ℂ)) := by
    have := tendsto_integral_of_dominated_convergence (μ := η) (fun _ ↦ (1 : ℝ))
      (fun n ↦ (Complex.continuous_ofReal.comp (g_diff n).continuous).aestronglyMeasurable)
      (integrable_const 1) (fun n ↦ Eventually.of_forall (g_le n))
      (Eventually.of_forall g_lim)
    rwa [integral_indicator_const _ hs.measurableSet, Complex.real_smul, mul_one] at this
  have L₂ : Tendsto (fun n ↦ ∫ x, (g n x : ℂ) * f x) atTop (𝓝 (∫ x in s, f x)) := by
    rw [← integral_indicator hs.measurableSet]
    refine tendsto_integral_of_dominated_convergence (K.indicator fun x ↦ ‖f x‖)
      (fun n ↦ (Complex.continuous_ofReal.comp (g_diff n).continuous).aestronglyMeasurable.mul
        hf.aestronglyMeasurable) ?_ (fun n ↦ Eventually.of_forall fun x ↦ ?_)
      (Eventually.of_forall fun x ↦ ?_)
    · rw [integrable_indicator_iff K_compact.measurableSet]
      exact (hf.integrableOn_isCompact K_compact).norm
    · rw [norm_mul]
      by_cases hxK : x ∈ K
      · rw [indicator_of_mem hxK]
        exact mul_le_of_le_one_left (norm_nonneg _) (g_le n x)
      · simp [g_zero n x hxK, indicator_of_notMem hxK]
    · have := (g_lim x).mul_const (f x)
      convert this using 2
      by_cases hxs : x ∈ s <;> simp [hxs]
  exact tendsto_nhds_unique L₁ (by simpa only [h _ (g_diff _) (HasCompactSupport.intro
    K_compact (g_zero _))] using L₂)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- The squared `L²` seminorm as a lower integral.
@isnad1 id=eq.0h4v.s7.68b70c112de3 from=translated src=- shape=7c06a85b vocab=dd481e7e
-/
theorem lintegral_enorm_sq_eq_eLpNorm_sq {F' : Type*} [NormedAddCommGroup F']
    (μ : Measure E) (f : E → F') :
    ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ = eLpNorm f 2 μ ^ 2 := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := f) (p := 2) two_ne_zero
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two] at h
  simpa using h.symm

/-- **Square-integrable transforms give square-integrable densities.** A finite
measure whose transform lies in `L²` is absolutely continuous, with a nonnegative
density whose squared `L²` norm equals that of the transform.
@isnad1 id=ex.1h2v.s8.86277cfc07d6 from=translated src=- shape=fb3e23d5 vocab=88248399
-/
theorem exists_density_of_memLp_measureFourier (η : Measure E) [IsFiniteMeasure η]
    (hF : MemLp (measureFourier η) 2) :
    ∃ g : E → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x) ∧ MemLp g 2 ∧
      η = volume.withDensity (fun x ↦ ENNReal.ofReal (g x)) ∧
      ∫⁻ x, ENNReal.ofReal (g x) ^ 2 = ∫⁻ ξ, ‖measureFourier η ξ‖ₑ ^ 2 := by
  set F : Lp ℂ 2 (volume : Measure E) := hF.toLp (measureFourier η)
  set h : Lp ℂ 2 (volume : Measure E) := 𝓕⁻ F
  have hmem : MemLp (h : E → ℂ) 2 := Lp.memLp h
  have hloc : LocallyIntegrable (h : E → ℂ) := hmem.locallyIntegrable (by norm_num)
  have htest : ∀ g : E → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ x, (g x : ℂ) ∂η = ∫ x, (g x : ℂ) * h x := by
    intro g hg hgs
    have hs : HasCompactSupport (fun x ↦ (g x : ℂ)) := hgs.comp_left Complex.ofReal_zero
    have hd : ContDiff ℝ ∞ (fun x ↦ (g x : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
    simpa using integral_schwartz_eq_fourierInv η hF (hs.toSchwartzMap hd)
  have hK : ∀ K, IsCompact K → ((η.real K : ℝ) : ℂ) = ∫ x in K, h x :=
    fun K hK ↦ measureReal_isCompact_eq_setIntegral η hloc htest hK
  -- the imaginary part vanishes
  have him : (fun x ↦ (h x).im) =ᵐ[volume] 0 := by
    refine ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero'
      (hmem.im.locallyIntegrable (by norm_num)) fun K hK' ↦ ?_
    · have := congrArg Complex.im (hK K hK')
      rw [Complex.ofReal_im] at this
      rw [this]
      exact integral_im (hloc.integrableOn_isCompact hK')
  -- the real part, with a measurable representative
  have hre : MemLp (fun x ↦ (h x).re) 2 := hmem.re
  set u : E → ℝ := hre.aestronglyMeasurable.mk _ with hu_def
  have hu_meas : Measurable u := hre.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hu_ae : (fun x ↦ (h x).re) =ᵐ[volume] u := hre.aestronglyMeasurable.ae_eq_mk
  have hu_mem : MemLp u 2 := hre.ae_eq hu_ae
  have hu_loc : LocallyIntegrable u := hu_mem.locallyIntegrable (by norm_num)
  have hKu : ∀ K, IsCompact K → η.real K = ∫ x in K, u x := by
    intro K hK'
    have := congrArg Complex.re (hK K hK')
    rw [Complex.ofReal_re] at this
    rw [this, ← setIntegral_congr_ae hK'.measurableSet (hu_ae.mono fun x hx _ ↦ hx)]
    exact (integral_re (hloc.integrableOn_isCompact hK')).symm
  set ρp := volume.withDensity (fun x ↦ ENNReal.ofReal (u x)) with hρp
  set ρm := volume.withDensity (fun x ↦ ENNReal.ofReal (-u x)) with hρm
  have hρm_fin : IsFiniteMeasureOnCompacts ρm := by
    refine ⟨fun K hK' ↦ ?_⟩
    rw [hρm, withDensity_apply _ hK'.measurableSet]
    exact (hu_loc.integrableOn_isCompact hK').neg.lintegral_lt_top
  have hsum : ∀ K, IsCompact K → (η + ρm) K = ρp K := by
    intro K hK'
    have hint := hu_loc.integrableOn_isCompact hK'
    have h1 := hKu K hK'
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint] at h1
    rw [Measure.add_apply, hρm, hρp, withDensity_apply _ hK'.measurableSet,
      withDensity_apply _ hK'.measurableSet]
    have hp := hint.lintegral_lt_top
    have hm := hint.neg.lintegral_lt_top
    simp only [Pi.neg_apply] at hm
    rw [← ENNReal.toReal_eq_toReal_iff' (ENNReal.add_ne_top.mpr
      ⟨measure_ne_top η K, hm.ne⟩) hp.ne, ENNReal.toReal_add (measure_ne_top η K) hm.ne,
      ← measureReal_def, h1]
    ring
  have : IsFiniteMeasureOnCompacts (η + ρm) := ⟨fun K hK' ↦ by
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨measure_lt_top η K, hK'.measure_lt_top⟩⟩
  have heq : η + ρm = ρp := Measure.ext_of_isCompact hsum
  set N : Set E := {x | u x < 0}
  have hN : MeasurableSet N := measurableSet_lt hu_meas measurable_const
  have hρpN : ρp N = 0 := by
    rw [hρp, withDensity_apply _ hN]
    refine (setLIntegral_congr_fun hN fun x hx ↦ ?_).trans lintegral_zero
    exact ENNReal.ofReal_eq_zero.mpr (le_of_lt hx)
  have hρmNc : ρm Nᶜ = 0 := by
    rw [hρm, withDensity_apply _ hN.compl]
    refine (setLIntegral_congr_fun hN.compl fun x hx ↦ ?_).trans lintegral_zero
    have hx' : 0 ≤ u x := by simpa [N] using hx
    exact ENNReal.ofReal_eq_zero.mpr (by linarith)
  have hρm0 : ρm = 0 := by
    rw [← Measure.measure_univ_eq_zero, ← measure_add_measure_compl hN, hρmNc, add_zero]
    refine le_antisymm ?_ bot_le
    calc ρm N ≤ (η + ρm) N := by rw [Measure.add_apply]; exact le_add_self
      _ = 0 := by rw [heq, hρpN]
  have hu_nonneg : ∀ᵐ x ∂volume, 0 ≤ u x := by
    have h0 : ∫⁻ x, ENNReal.ofReal (-u x) = 0 := by
      have := congrArg (fun m : Measure E ↦ m univ) hρm0
      simpa [hρm, withDensity_apply _ MeasurableSet.univ] using this
    rw [lintegral_eq_zero_iff (by fun_prop)] at h0
    filter_upwards [h0] with x hx
    simpa [ENNReal.ofReal_eq_zero] using hx
  refine ⟨fun x ↦ max (u x) 0, by fun_prop, fun x ↦ le_max_right _ _, ?_, ?_, ?_⟩
  · have hae : (fun x ↦ ‖h x‖) =ᵐ[volume] fun x ↦ max (u x) 0 := by
      filter_upwards [hu_ae, him, hu_nonneg] with x hre hi hnn
      have hx : h x = ((u x : ℝ) : ℂ) := Complex.ext (by simpa using hre) (by simpa using hi)
      rw [hx, Complex.norm_real, Real.norm_of_nonneg hnn, max_eq_left hnn]
    exact hmem.norm.ae_eq hae
  · calc η = η + ρm := by rw [hρm0, add_zero]
      _ = ρp := heq
      _ = _ := by
        rw [hρp]
        congr 1
        funext x
        simp [ENNReal.ofReal_max]
  · have hae : (fun x ↦ ENNReal.ofReal (max (u x) 0) ^ 2) =ᵐ[volume] fun x ↦ ‖h x‖ₑ ^ 2 := by
      filter_upwards [hu_ae, him, hu_nonneg] with x hre hi hnn
      have hx : h x = ((u x : ℝ) : ℂ) := Complex.ext (by simpa using hre) (by simpa using hi)
      rw [hx, max_eq_left hnn, ← ofReal_norm, Complex.norm_real,
        Real.norm_of_nonneg hnn]
    rw [lintegral_congr_ae hae, lintegral_enorm_sq_eq_eLpNorm_sq,
      lintegral_enorm_sq_eq_eLpNorm_sq, ← eLpNorm_congr_ae hF.coeFn_toLp]
    congr 1
    have hnorm : ‖h‖ = ‖F‖ := by
      rw [← Lp.norm_fourier_eq h]
      simp [h]
    rw [Lp.norm_def, Lp.norm_def] at hnorm
    exact (ENNReal.toReal_eq_toReal_iff' (Lp.eLpNorm_ne_top h) (Lp.eLpNorm_ne_top F)).mp hnorm

end PshLines.PSHD
