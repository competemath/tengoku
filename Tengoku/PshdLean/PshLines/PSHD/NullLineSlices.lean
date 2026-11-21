import Tengoku.PshdLean.PshLines.PSHD.Crofton

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Null sets on almost every complex line through a point

Step 4 of Proposition 2.1 of `pshd-vibe` uses that a Lebesgue-null set meets
almost every complex line through a prescribed point in a planar null set.
Integrating over the unitary group and in polar coordinates reduces this to the
fact that a radial profile vanishing almost everywhere with the weight
`r ^ (2n-1)` also vanishes almost everywhere with the planar weight `r`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace PshLines.PSHD

attribute [local instance] InnerProductSpace.complexToReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

omit [CompleteSpace E] in
/-- A radial nonnegative integral over a nontrivial complex space vanishes only
if the corresponding radial integral over the complex plane vanishes.
@isnad1 id=eq.2h2v.s7.e8584960900e from=translated src=- shape=fc51507b vocab=c6e4585e
-/
theorem lintegral_norm_complex_eq_zero [Nontrivial E] {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    (h : ∫⁻ ζ : E, f ‖ζ‖ = 0) : ∫⁻ t : ℂ, f ‖t‖ = 0 := by
  have hae : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), f r = 0 := by
    rw [lintegral_fun_norm_addHaar volume hf] at h
    have hd : (Module.finrank ℝ E : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast Module.finrank_pos.ne'
    have hb : (volume : Measure E) (ball 0 1) ≠ 0 := (measure_ball_pos _ _ one_pos).ne'
    have h0 : ∫⁻ r in Ioi (0 : ℝ),
        ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) * f r = 0 := by
      simpa [hd, hb] using h
    rw [lintegral_eq_zero_iff (by fun_prop)] at h0
    filter_upwards [h0, ae_restrict_mem measurableSet_Ioi] with r hr hr0
    have hpos : ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) ≠ 0 := by
      simpa using pow_pos (mem_Ioi.mp hr0) _
    simpa [hpos] using hr
  rw [lintegral_fun_norm_addHaar volume hf]
  have : ∫⁻ r in Ioi (0 : ℝ),
      ENNReal.ofReal (r ^ (Module.finrank ℝ ℂ - 1)) * f r = 0 := by
    rw [lintegral_eq_zero_iff (by fun_prop)]
    filter_upwards [hae] with r hr
    simp [hr]
  rw [this, mul_zero]

/-- **Null sets on almost every line through a point.** A null set meets some
complex line through any prescribed point, with unit direction, in a planar
null set.
@isnad1 id=ex.1h3v.s8.2b805edfb983 from=translated src=- shape=6db8bf5f vocab=87e910c4
-/
theorem exists_unit_line_preimage_null [Nontrivial E] {N : Set E}
    (hN : (volume : Measure E) N = 0) (z : E) :
    ∃ e : E, ‖e‖ = 1 ∧ (volume : Measure ℂ) ((fun t : ℂ ↦ z + t • e) ⁻¹' N) = 0 := by
  set M := toMeasurable (volume : Measure E) N
  have hM : MeasurableSet M := measurableSet_toMeasurable _ _
  have hM0 : (volume : Measure E) M = 0 := by rw [measure_toMeasurable]; exact hN
  let g : E → ℝ≥0∞ := fun ζ ↦ M.indicator 1 (z + ζ)
  have hg : Measurable g :=
    (measurable_one.indicator hM).comp (measurable_const.add measurable_id)
  have hg0 : ∫⁻ ζ, g ζ = 0 := by
    have : ∫⁻ ζ, g ζ = (volume : Measure E) ((fun ζ ↦ z + ζ) ⁻¹' M) := by
      rw [← lintegral_indicator_one (hM.preimage (measurable_const_add z))]
      rfl
    rw [this, measure_preimage_add, hM0]
  obtain ⟨e₀, he₀⟩ := exists_norm_eq E zero_le_one
  let h : ℝ → ℝ≥0∞ := fun r ↦ unitaryAverage E g ((r : ℂ) • e₀)
  have hh : Measurable h :=
    (measurable_unitaryAverage hg).comp (by fun_prop)
  have havg : ∫⁻ ζ : E, h ‖ζ‖ = 0 := by
    have := lintegral_mul_radial_eq_unitaryAverage hg (k := fun _ ↦ 1) measurable_const
    simp only [mul_one] at this
    rw [← hg0, this]
    congr 1
    funext ζ
    exact (unitaryAverage_eq_norm_smul g he₀ ζ).symm
  have hplane := lintegral_norm_complex_eq_zero hh havg
  have hcont : Continuous fun p : UnitaryGroup E × ℂ ↦
      ((p.1⁻¹ : UnitaryGroup E) : E →L[ℂ] E) (p.2 • e₀) := by
    fun_prop
  have hswap : ∫⁻ U : UnitaryGroup E, ∫⁻ t : ℂ,
      g (((U⁻¹ : UnitaryGroup E) : E →L[ℂ] E) (t • e₀)) ∂volume ∂unitaryHaar E = 0 := by
    rw [lintegral_lintegral_swap]
    · rw [← hplane]
      congr 1
      funext t
      change unitaryAverage E g (t • e₀) = h ‖t‖
      have ht : ‖t • e₀‖ = ‖t‖ := by rw [norm_smul, he₀, mul_one]
      simp only [h, ← ht]
      exact unitaryAverage_eq_norm_smul g he₀ _
    · exact (hg.comp hcont.measurable).aemeasurable
  have hmU := hg.comp hcont.measurable
  have hmeas := Measurable.lintegral_prod_right' (ν := (volume : Measure ℂ)) hmU
  have hae := (lintegral_eq_zero_iff hmeas).mp hswap
  obtain ⟨U, hU⟩ := hae.exists
  refine ⟨((U⁻¹ : UnitaryGroup E) : E →L[ℂ] E) e₀, ?_, ?_⟩
  · rw [Unitary.norm_map, he₀]
  · refine measure_mono_null (preimage_mono (subset_toMeasurable (volume : Measure E) N)) ?_
    have hpre : MeasurableSet ((fun t : ℂ ↦ z + t • ((U⁻¹ : UnitaryGroup E) : E →L[ℂ] E) e₀) ⁻¹' M) :=
      hM.preimage (by fun_prop)
    rw [← lintegral_indicator_one hpre]
    simp only [g, Function.comp_def, map_smul, Pi.zero_apply] at hU
    exact hU

end PshLines.PSHD
