import Tengoku.PshdLean.PshLines.PSHD.UnitaryHaar
import Tengoku.Seed.MeasureTheory.Constructions.HaarToSphere
import Tengoku.Seed.MeasureTheory.Measure.Haar.InnerProductSpace
import Tengoku.Seed.Analysis.InnerProductSpace.Projection.Reflection
import Tengoku.Seed.LinearAlgebra.Complex.FiniteDimensional

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The complex hyperplane Crofton formula

Averaging Lebesgue measure on a fixed complex hyperplane over the unitary group
gives a multiple of `|ζ|⁻² dζ`, as in `pshd-vibe`, Lemma 1.4.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace PshLines.PSHD

section Radial

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [FiniteDimensional ℝ V] [Nontrivial V]

/-- Polar coordinates for radial nonnegative functions, as lower integrals.-/
theorem lintegral_fun_norm_addHaar (μ : Measure V) [μ.IsAddHaarMeasure]
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f ‖x‖ ∂μ = Module.finrank ℝ V * μ (ball 0 1) *
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (Module.finrank ℝ V - 1)) * f r := by
  calc ∫⁻ x, f ‖x‖ ∂μ = ∫⁻ x in ({0}ᶜ : Set V), f ‖x‖ ∂μ := by
        rw [restrict_compl_singleton]
    _ = ∫⁻ x : ({0}ᶜ : Set V), f ‖x.1‖ ∂(μ.comap (↑)) :=
        (lintegral_subtype_comap (measurableSet_singleton _).compl (fun x ↦ f ‖x‖)).symm
    _ = ∫⁻ p, f p.2.1 ∂(μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ V - 1))) := by
        simpa using (μ.measurePreserving_homeomorphUnitSphereProd.lintegral_comp_emb
          (Homeomorph.measurableEmbedding _) (fun p ↦ f p.2.1))
    _ = μ.toSphere univ *
          ∫⁻ r, f r.1 ∂(Measure.volumeIoiPow (Module.finrank ℝ V - 1)) := by
        rw [lintegral_prod _ (by fun_prop)]
        exact (lintegral_const (∫⁻ r, f r.1 ∂(Measure.volumeIoiPow
          (Module.finrank ℝ V - 1)))).trans (mul_comm _ _)
    _ = _ := by
        rw [Measure.toSphere_apply_univ, Measure.volumeIoiPow,
          lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop),
          ← lintegral_subtype_comap measurableSet_Ioi
            (fun r : ℝ ↦ ENNReal.ofReal (r ^ (Module.finrank ℝ V - 1)) * f r)]
        rfl

end Radial

section Transitive

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A complex reflection exchanges two vectors of equal norm with real inner product.-/
theorem reflection_sub_complex {v w : E} [(ℂ ∙ (v - w))ᗮ.HasOrthogonalProjection]
    (h : ‖v‖ = ‖w‖) (him : (⟪v, w⟫_ℂ).im = 0) :
    (ℂ ∙ (v - w))ᗮ.reflection v = w := by
  set R : E ≃ₗᵢ[ℂ] E := (ℂ ∙ (v - w))ᗮ.reflection
  suffices R v + R v = w + w by
    apply smul_right_injective E (by simp : (2 : ℂ) ≠ 0)
    simpa [two_smul] using this
  have h₁ : R (v - w) = -(v - w) :=
    Submodule.reflection_orthogonalComplement_singleton_eq_neg (v - w)
  have h₂ : R (v + w) = v + w := by
    apply Submodule.reflection_mem_subspace_eq_self
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    have hvw : ⟪w, v⟫_ℂ = ⟪v, w⟫_ℂ := by
      rw [← inner_conj_symm, Complex.conj_eq_iff_im.mpr him]
    rw [inner_add_left, inner_sub_right, inner_sub_right, hvw, inner_self_eq_norm_sq_to_K,
      inner_self_eq_norm_sq_to_K, h]
    ring
  convert! congr_arg₂ (· + ·) h₂ h₁ using 1
  · simp
  · abel

/-- Linear isometries act transitively on each sphere.-/
theorem exists_linearIsometryEquiv_apply_eq [FiniteDimensional ℂ E] {v w : E}
    (h : ‖v‖ = ‖w‖) : ∃ L : E ≃ₗᵢ[ℂ] E, L v = w := by
  by_cases hz : ⟪v, w⟫_ℂ = 0
  · refine ⟨(ℂ ∙ (v - w))ᗮ.reflection, reflection_sub_complex h (by simp [hz])⟩
  · set c : ℂ := ⟪v, w⟫_ℂ / ‖⟪v, w⟫_ℂ‖
    have hn : ‖⟪v, w⟫_ℂ‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have hc : ‖c‖ = 1 := by
      simp [c, hn]
    have hc0 : c ≠ 0 := by
      intro h0
      simp [h0] at hc
    let S : E ≃ₗᵢ[ℂ] E :=
      { LinearEquiv.smulOfNeZero ℂ E c hc0 with
        norm_map' := fun x ↦ by simp [norm_smul, hc] }
    have hS : S v = c • v := rfl
    have hnorm : ‖c • v‖ = ‖w‖ := by rw [norm_smul, hc, one_mul, h]
    have him : (⟪c • v, w⟫_ℂ).im = 0 := by
      rw [inner_smul_left]
      simp only [c, map_div₀, Complex.conj_ofReal]
      rw [div_mul_eq_mul_div, Complex.conj_mul', ← Complex.ofReal_pow]
      rw [← Complex.ofReal_div, Complex.ofReal_im]
    refine ⟨S.trans (ℂ ∙ (c • v - w))ᗮ.reflection, ?_⟩
    rw [LinearIsometryEquiv.trans_apply, hS]
    exact reflection_sub_complex hnorm him

end Transitive

section Average

attribute [local instance] InnerProductSpace.complexToReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E] in
/-- The action of an inverse unitary on a vector.-/
theorem continuous_unitary_inv_apply :
    Continuous fun p : UnitaryGroup E × E ↦ ((p.1⁻¹ : UnitaryGroup E) : E →L[ℂ] E) p.2 :=
  (continuous_subtype_val.comp continuous_fst.inv).clm_apply continuous_snd

theorem measurable_unitary_inv_apply :
    Measurable fun p : UnitaryGroup E × E ↦ ((p.1⁻¹ : UnitaryGroup E) : E →L[ℂ] E) p.2 :=
  continuous_unitary_inv_apply.measurable

variable (E) in
/-- Average of a nonnegative function over the unitary orbit of a point.-/
def unitaryAverage (g : E → ℝ≥0∞) (ζ : E) : ℝ≥0∞ :=
  ∫⁻ U, g (((U⁻¹ : UnitaryGroup E) : E →L[ℂ] E) ζ) ∂unitaryHaar E

theorem measurable_unitaryAverage {g : E → ℝ≥0∞} (hg : Measurable g) :
    Measurable (unitaryAverage E g) :=
  (hg.comp measurable_unitary_inv_apply).lintegral_prod_left'

omit [MeasurableSpace E] [BorelSpace E] in
/-- The orbit average is unitary invariant.-/
theorem unitaryAverage_apply_unitary (g : E → ℝ≥0∞) (V : UnitaryGroup E) (ζ : E) :
    unitaryAverage E g ((V : E →L[ℂ] E) ζ) = unitaryAverage E g ζ := by
  unfold unitaryAverage
  conv_rhs => rw [← lintegral_mul_left_eq_self _ V⁻¹]
  congr 1
  funext U
  simp only [mul_inv_rev, inv_inv, Submonoid.coe_mul]
  rfl

omit [MeasurableSpace E] [BorelSpace E] in
/-- The orbit average depends only on the norm.-/
theorem unitaryAverage_eq_norm_smul (g : E → ℝ≥0∞) {e₀ : E} (he₀ : ‖e₀‖ = 1) (ζ : E) :
    unitaryAverage E g ζ = unitaryAverage E g ((‖ζ‖ : ℂ) • e₀) := by
  obtain ⟨L, hL⟩ := exists_linearIsometryEquiv_apply_eq
    (v := (‖ζ‖ : ℂ) • e₀) (w := ζ) (by simp [norm_smul, he₀])
  conv_lhs => rw [← hL]
  exact unitaryAverage_apply_unitary g (Unitary.linearIsometryEquiv.symm L) _

/-- Unitary averaging does not change integrals against a radial weight.-/
theorem lintegral_mul_radial_eq_unitaryAverage {g : E → ℝ≥0∞} (hg : Measurable g)
    {k : ℝ → ℝ≥0∞} (hk : Measurable k) :
    ∫⁻ ζ, g ζ * k ‖ζ‖ = ∫⁻ ζ, unitaryAverage E g ζ * k ‖ζ‖ := by
  have hU : ∀ U : UnitaryGroup E,
      ∫⁻ ζ, g (((U⁻¹ : UnitaryGroup E) : E →L[ℂ] E) ζ) * k ‖ζ‖ = ∫⁻ ζ, g ζ * k ‖ζ‖ := by
    intro U
    set L : E ≃ₗᵢ[ℝ] E :=
      { (Unitary.linearIsometryEquiv U⁻¹).toLinearEquiv.restrictScalars ℝ with
        norm_map' := (Unitary.linearIsometryEquiv U⁻¹).norm_map }
    have hL : ∀ ζ, L ζ = ((U⁻¹ : UnitaryGroup E) : E →L[ℂ] E) ζ := fun _ ↦ rfl
    have h := (L.measurePreserving).lintegral_comp (f := fun ζ ↦ g ζ * k ‖ζ‖) (by fun_prop)
    simp only [hL, Unitary.norm_map] at h
    exact h
  calc ∫⁻ ζ, g ζ * k ‖ζ‖ = ∫⁻ U : UnitaryGroup E, ∫⁻ ζ, g ζ * k ‖ζ‖ ∂volume ∂unitaryHaar E := by
        rw [lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ U : UnitaryGroup E, ∫⁻ ζ,
          g (((U⁻¹ : UnitaryGroup E) : E →L[ℂ] E) ζ) * k ‖ζ‖ ∂volume ∂unitaryHaar E := by
        simp_rw [hU]
    _ = _ := by
        rw [lintegral_lintegral_swap]
        · congr 1
          funext ζ
          have hm : Measurable fun U : UnitaryGroup E ↦
              g (((U⁻¹ : UnitaryGroup E) : E →L[ℂ] E) ζ) :=
            hg.comp ((continuous_subtype_val.comp continuous_inv).clm_apply
              continuous_const).measurable
          rw [lintegral_mul_const _ hm]
          rfl
        · exact ((hg.comp measurable_unitary_inv_apply).mul
            (hk.comp (measurable_norm.comp measurable_snd))).aemeasurable

end Average

section Crofton

attribute [local instance] InnerProductSpace.complexToReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

/-- The Crofton constant attached to the hyperplane orthogonal to `e₀`.-/
def croftonConstant (e₀ : E) : ℝ≥0∞ :=
  Module.finrank ℝ (ℂ ∙ e₀)ᗮ * (volume : Measure (ℂ ∙ e₀)ᗮ) (ball 0 1) /
    (Module.finrank ℝ E * (volume : Measure E) (ball 0 1))

omit [FiniteDimensional ℂ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
theorem finrank_real_orthogonal_span_singleton (hn : 2 ≤ Module.finrank ℂ E) {e₀ : E}
    (he₀ : e₀ ≠ 0) :
    Module.finrank ℝ (ℂ ∙ e₀)ᗮ + 2 = Module.finrank ℝ E := by
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank ℂ E = m + 1 := ⟨Module.finrank ℂ E - 1, by omega⟩
  have : Fact (Module.finrank ℂ E = m + 1) := ⟨hm⟩
  rw [finrank_real_of_complex, finrank_real_of_complex,
    Submodule.finrank_orthogonal_span_singleton (n := m) he₀, hm]
  ring

/-- **Crofton formula for complex hyperplanes.** Averaging Lebesgue integrals
over the unitary images of a fixed complex hyperplane gives a multiple of the
weight `|ζ|⁻²`.-/
theorem lintegral_unitaryHaar_hyperplane_eq (hn : 2 ≤ Module.finrank ℂ E) {e₀ : E}
    (he₀ : ‖e₀‖ = 1) {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ U, ∫⁻ h : (ℂ ∙ e₀)ᗮ, g (((U⁻¹ : UnitaryGroup E) : E →L[ℂ] E) h) ∂volume
        ∂unitaryHaar E =
      croftonConstant e₀ * ∫⁻ ζ, g ζ * (ENNReal.ofReal ‖ζ‖ ^ 2)⁻¹ := by
  have he₀' : e₀ ≠ 0 := by
    intro h
    simp [h] at he₀
  have hdim := finrank_real_orthogonal_span_singleton hn he₀'
  have h4 : 4 ≤ Module.finrank ℝ E := by rw [finrank_real_of_complex]; omega
  set H := (ℂ ∙ e₀)ᗮ
  have hH : Nontrivial H := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    omega
  have hE : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℂ) (by omega)
  set φ : ℝ → ℝ≥0∞ := fun r ↦ unitaryAverage E g ((r : ℂ) • e₀) with hφ
  have hφm : Measurable φ :=
    (measurable_unitaryAverage hg).comp (by fun_prop)
  set m := Module.finrank ℝ H
  -- the hyperplane side
  have hL : ∫⁻ U, ∫⁻ h : H, g (((U⁻¹ : UnitaryGroup E) : E →L[ℂ] E) h) ∂volume
        ∂unitaryHaar E =
      m * (volume : Measure H) (ball 0 1) *
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (m - 1)) * φ r := by
    rw [lintegral_lintegral_swap]
    · have : ∀ h : H, unitaryAverage E g h = φ ‖h‖ := fun h ↦ by
        rw [unitaryAverage_eq_norm_smul g he₀]
        rfl
      show ∫⁻ h : H, unitaryAverage E g h = _
      simp_rw [this]
      exact lintegral_fun_norm_addHaar _ hφm
    · exact (hg.comp ((continuous_subtype_val.comp continuous_fst.inv).clm_apply
        (continuous_subtype_val.comp continuous_snd)).measurable).aemeasurable
  -- the Lebesgue side
  have hk : Measurable fun r : ℝ ↦ (ENNReal.ofReal r ^ 2)⁻¹ := by fun_prop
  have hR : ∫⁻ ζ, g ζ * (ENNReal.ofReal ‖ζ‖ ^ 2)⁻¹ =
      Module.finrank ℝ E * (volume : Measure E) (ball 0 1) *
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (m - 1)) * φ r := by
    rw [lintegral_mul_radial_eq_unitaryAverage hg hk]
    have : ∀ ζ : E, unitaryAverage E g ζ = φ ‖ζ‖ := fun ζ ↦ by
      rw [unitaryAverage_eq_norm_smul g he₀]
    simp_rw [this]
    rw [lintegral_fun_norm_addHaar (f := fun r ↦ φ r * (ENNReal.ofReal r ^ 2)⁻¹) _
      (hφm.mul hk)]
    congr 1
    refine setLIntegral_congr_fun measurableSet_Ioi fun r hr ↦ ?_
    have hr : 0 < r := hr
    have hpow : ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) * (ENNReal.ofReal r ^ 2)⁻¹ =
        ENNReal.ofReal (r ^ (m - 1)) := by
      rw [← hdim, show m + 2 - 1 = (m - 1) + 2 by omega, pow_add,
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hr.le, ENNReal.ofReal_pow hr.le,
        mul_assoc, ENNReal.mul_inv_cancel (pow_ne_zero _ (ENNReal.ofReal_pos.mpr hr).ne')
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top), mul_one]
    rw [mul_left_comm, hpow, mul_comm]
  rw [hL, hR, croftonConstant, ← mul_assoc, ENNReal.div_mul_cancel]
  · simp only [ne_eq, mul_eq_zero, Nat.cast_eq_zero, not_or]
    exact ⟨Module.finrank_pos.ne', (isOpen_ball.measure_pos _ (nonempty_ball.mpr one_pos)).ne'⟩
  · exact ENNReal.mul_ne_top (by simp) measure_ball_lt_top.ne

omit [CompleteSpace E] in
theorem croftonConstant_pos_ne_top (hn : 2 ≤ Module.finrank ℂ E) {e₀ : E} (he₀ : ‖e₀‖ = 1) :
    0 < croftonConstant e₀ ∧ croftonConstant e₀ ≠ ⊤ := by
  have he₀' : e₀ ≠ 0 := by
    intro h
    simp [h] at he₀
  have hdim := finrank_real_orthogonal_span_singleton hn he₀'
  have h4 : 4 ≤ Module.finrank ℝ E := by rw [finrank_real_of_complex]; omega
  have hH : Nontrivial (ℂ ∙ e₀)ᗮ := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hE : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hballH := (isOpen_ball (x := (0 : (ℂ ∙ e₀)ᗮ)) (ε := 1)).measure_pos volume
    (nonempty_ball.mpr one_pos)
  have hballE := (isOpen_ball (x := (0 : E)) (ε := 1)).measure_pos volume
    (nonempty_ball.mpr one_pos)
  unfold croftonConstant
  constructor
  · refine ENNReal.div_pos (mul_ne_zero (by simp; omega) hballH.ne') ?_
    exact ENNReal.mul_ne_top (by simp) measure_ball_lt_top.ne
  · refine ENNReal.div_ne_top (ENNReal.mul_ne_top (by simp) measure_ball_lt_top.ne) ?_
    exact mul_ne_zero (by simp; omega) hballE.ne'

end Crofton

end PshLines.PSHD
