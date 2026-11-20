import Tengoku.PshdLean.PshLines.PSHD.Crofton
import Tengoku.PshdLean.PshLines.PSHD.FourierEnergy
import Tengoku.PshdLean.PshLines.PSHD.FourierDensity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Projections onto complex hyperplanes

`pshd-vibe`, Lemma 1.4: for almost every complex hyperplane the projected
measure has a square-integrable density, and the integrated squared norms are a
fixed multiple of the Riesz energy of order `2n - 2`. Hyperplanes are written
as `U⁻¹ H₀` for a Haar-random unitary `U` and the fixed hyperplane
`H₀ = e₀ᗮ`; the projection is expressed in the coordinates of `H₀`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace PshLines.PSHD

attribute [local instance] InnerProductSpace.complexToReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

/-- Orthogonal projection onto the hyperplane `U⁻¹ H₀`, in the coordinates of `H₀`.-/
def unitaryProjection (e₀ : E) (U : UnitaryGroup E) (y : E) : (ℂ ∙ e₀)ᗮ :=
  (ℂ ∙ e₀)ᗮ.orthogonalProjectionOnto ((U : E →L[ℂ] E) y)

omit [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E] in
/--
@isnad1 id=continuo.0h3v.s10.adfa46d48444 from=translated src=- shape=ed65ea33 vocab=4a443d56
-/
theorem continuous_unitaryProjection (e₀ : E) (U : UnitaryGroup E) :
    Continuous (unitaryProjection e₀ U) :=
  (ℂ ∙ e₀)ᗮ.orthogonalProjectionOnto.continuous.comp (U : E →L[ℂ] E).continuous

omit [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E] in
/--
@isnad1 id=continuo.0h2v.s12.8d829a22c68c from=translated src=- shape=d357b3d9 vocab=52d74512
-/
theorem continuous_unitaryProjection_uncurry (e₀ : E) :
    Continuous fun p : UnitaryGroup E × E ↦ unitaryProjection e₀ p.1 p.2 :=
  (ℂ ∙ e₀)ᗮ.orthogonalProjectionOnto.continuous.comp
    ((continuous_subtype_val.comp continuous_fst).clm_apply continuous_snd)

/--
@isnad1 id=measurab.0h3v.s13.d7128463e077 from=translated src=- shape=41b8fafe vocab=768a63b7
-/
theorem measurable_lintegral_measureFourier_sq (μ : Measure E) [IsFiniteMeasure μ] (e₀ : E) :
    Measurable fun U : UnitaryGroup E ↦ ∫⁻ ξ : (ℂ ∙ e₀)ᗮ,
      ‖measureFourier μ (((U⁻¹ : UnitaryGroup E) : E →L[ℂ] E) ξ)‖ₑ ^ 2 :=
  Measurable.lintegral_prod_right' (((measurable_measureFourier μ).enorm.pow_const 2).comp
    ((continuous_subtype_val.comp continuous_fst.inv).clm_apply
      (continuous_subtype_val.comp continuous_snd)).measurable)

/-- The transform of a projected measure is the restriction of the rotated transform.
@isnad1 id=eq.0h5v.s13.4bed5c170ff5 from=translated src=- shape=7efa473e vocab=f94794c2
-/
theorem measureFourier_map_unitaryProjection (μ : Measure E) (e₀ : E) (U : UnitaryGroup E)
    (ξ : (ℂ ∙ e₀)ᗮ) :
    measureFourier (μ.map (unitaryProjection e₀ U)) ξ =
      measureFourier μ (((U⁻¹ : UnitaryGroup E) : E →L[ℂ] E) ξ) := by
  have hmap : μ.map (unitaryProjection e₀ U) =
      (μ.map (U : E →L[ℂ] E)).map (ℂ ∙ e₀)ᗮ.orthogonalProjectionOnto :=
    (Measure.map_map (ℂ ∙ e₀)ᗮ.orthogonalProjectionOnto.continuous.measurable
      (U : E →L[ℂ] E).continuous.measurable).symm
  rw [hmap, measureFourier_map_complexProjection, measureFourier_eq_integral_complex,
    measureFourier_eq_integral_complex, integral_map (U : E →L[ℂ] E).continuous.aemeasurable
      (by fun_prop)]
  congr 1
  funext y
  have h : inner ℂ ((U : E →L[ℂ] E) y) (ξ : E) =
      inner ℂ y (((U⁻¹ : UnitaryGroup E) : E →L[ℂ] E) ξ) := by
    rw [← Unitary.star_eq_inv, Unitary.coe_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right]
  rw [h]

/-- The constant `c_n = a_n / b_{2n,2n-2}` of the projection identity.-/
def projectionConstant (e₀ : E) : ℝ≥0∞ :=
  croftonConstant e₀ /
    ENNReal.ofReal (rieszFourierConstant (Module.finrank ℝ E)
      ((2 * (Module.finrank ℂ E - 1) : ℕ) : ℝ))

omit [FiniteDimensional ℂ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/--
@isnad1 id=eq.0h1v.s6.874b72a36f56 from=translated src=- shape=00536cf0 vocab=81df8253
-/
theorem finrank_real_eq_two_mul : Module.finrank ℝ E = 2 * Module.finrank ℂ E :=
  finrank_real_of_complex E

omit [FiniteDimensional ℂ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/--
@isnad1 id=and.1h1v.s7.fd84d1ffe015 from=translated src=- shape=5673c1d3 vocab=fa860217
-/
theorem rieszExponent_pos_lt (hn : 2 ≤ Module.finrank ℂ E) :
    0 < ((2 * (Module.finrank ℂ E - 1) : ℕ) : ℝ) ∧
      ((2 * (Module.finrank ℂ E - 1) : ℕ) : ℝ) < Module.finrank ℝ E := by
  rw [finrank_real_eq_two_mul]
  constructor
  · exact_mod_cast (by omega : 0 < 2 * (Module.finrank ℂ E - 1))
  · exact_mod_cast (by omega : 2 * (Module.finrank ℂ E - 1) < 2 * Module.finrank ℂ E)

omit [CompleteSpace E] in
/--
@isnad1 id=and.2h2v.s7.263a7daf836a from=translated src=- shape=de5f8d03 vocab=155b78de
-/
theorem projectionConstant_pos_ne_top (hn : 2 ≤ Module.finrank ℂ E) {e₀ : E}
    (he₀ : ‖e₀‖ = 1) : 0 < projectionConstant e₀ ∧ projectionConstant e₀ ≠ ⊤ := by
  obtain ⟨ha, hat⟩ := croftonConstant_pos_ne_top hn he₀
  obtain ⟨hs, hsd⟩ := rieszExponent_pos_lt (E := E) hn
  have hb := rieszFourierConstant_pos hs hsd
  exact ⟨ENNReal.div_pos ha.ne' ENNReal.ofReal_ne_top,
    ENNReal.div_ne_top hat (ENNReal.ofReal_pos.mpr hb).ne'⟩

/-- Integrated squared transforms over rotated hyperplanes equal a multiple of energy.
@isnad1 id=eq.2h3v.s13.1e48f1408838 from=translated src=- shape=6f8c70f9 vocab=5f6ac644
-/
theorem lintegral_unitaryHaar_measureFourier_sq (hn : 2 ≤ Module.finrank ℂ E) {e₀ : E}
    (he₀ : ‖e₀‖ = 1) (μ : Measure E) [IsFiniteMeasure μ] :
    ∫⁻ U, ∫⁻ ξ : (ℂ ∙ e₀)ᗮ, ‖measureFourier μ (((U⁻¹ : UnitaryGroup E) : E →L[ℂ] E) ξ)‖ₑ ^ 2
        ∂volume ∂unitaryHaar E =
      projectionConstant e₀ * rieszEnergy ((2 * (Module.finrank ℂ E - 1) : ℕ) : ℝ) μ := by
  obtain ⟨hs, hsd⟩ := rieszExponent_pos_lt (E := E) hn
  have hE : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℂ) (by omega)
  have hG : Measurable fun ζ : E ↦ ‖measureFourier μ ζ‖ₑ ^ 2 :=
    (measurable_measureFourier μ).enorm.pow_const 2
  rw [lintegral_unitaryHaar_hyperplane_eq hn he₀ hG,
    rieszEnergy_eq_lintegral_measureFourier μ hs hsd, projectionConstant]
  have hb := rieszFourierConstant_pos hs hsd
  have hk : ∫⁻ ζ, ‖measureFourier μ ζ‖ₑ ^ 2 * (ENNReal.ofReal ‖ζ‖ ^ 2)⁻¹ =
      ∫⁻ ζ, ENNReal.ofReal (‖measureFourier μ ζ‖ ^ 2 *
        ‖ζ‖ ^ (((2 * (Module.finrank ℂ E - 1) : ℕ) : ℝ) - Module.finrank ℝ E)) := by
    have hne : ∀ᵐ ζ : E ∂volume, ζ ≠ 0 := by
      simp [ae_iff, measure_singleton]
    refine lintegral_congr_ae (hne.mono fun ζ hζ ↦ ?_)
    have hr : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
    have hexp : (((2 * (Module.finrank ℂ E - 1) : ℕ) : ℝ) - Module.finrank ℝ E) = -2 := by
      rw [finrank_real_eq_two_mul]
      push_cast [Nat.cast_sub (by omega : 1 ≤ Module.finrank ℂ E)]
      ring
    dsimp only
    rw [hexp, Real.rpow_neg hr.le, Real.rpow_two, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow hr.le,
      ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ofReal_norm]
  rw [hk, div_eq_mul_inv, mul_assoc, ← mul_assoc _ (ENNReal.ofReal _),
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hb).ne' ENNReal.ofReal_ne_top, one_mul]

/-- **Projections onto complex hyperplanes** (`pshd-vibe`, Lemma 1.4). If a finite
measure has finite Riesz energy of order `2n - 2`, then for almost every hyperplane
the projected measure has a nonnegative square-integrable density, and the
integrated squared densities equal `c_n I_{2n-2}(μ)`.
@isnad1 id=ex.3h3v.s14.099468c83b28 from=translated src=- shape=57267c42 vocab=d16b48b6
-/
theorem exists_projection_densities (hn : 2 ≤ Module.finrank ℂ E) {e₀ : E}
    (he₀ : ‖e₀‖ = 1) (μ : Measure E) [IsFiniteMeasure μ]
    (hI : rieszEnergy ((2 * (Module.finrank ℂ E - 1) : ℕ) : ℝ) μ < ⊤) :
    ∃ g : UnitaryGroup E → (ℂ ∙ e₀)ᗮ → ℝ,
      (∀ᵐ U ∂unitaryHaar E, Measurable (g U) ∧ (∀ x, 0 ≤ g U x) ∧ MemLp (g U) 2 ∧
        μ.map (unitaryProjection e₀ U) =
          volume.withDensity (fun x ↦ ENNReal.ofReal (g U x)) ∧
        ∫⁻ x, ENNReal.ofReal (g U x) ^ 2 = ∫⁻ ξ : (ℂ ∙ e₀)ᗮ,
          ‖measureFourier μ (((U⁻¹ : UnitaryGroup E) : E →L[ℂ] E) ξ)‖ₑ ^ 2) ∧
      ∫⁻ U, ∫⁻ x, ENNReal.ofReal (g U x) ^ 2 ∂volume ∂unitaryHaar E =
        projectionConstant e₀ * rieszEnergy ((2 * (Module.finrank ℂ E - 1) : ℕ) : ℝ) μ := by
  set η : UnitaryGroup E → Measure (ℂ ∙ e₀)ᗮ := fun U ↦ μ.map (unitaryProjection e₀ U)
  have hη : ∀ U, IsFiniteMeasure (η U) := fun U ↦ Measure.isFiniteMeasure_map _ _
  have hsq : ∀ U, ∫⁻ ξ, ‖measureFourier (η U) ξ‖ₑ ^ 2 =
      ∫⁻ ξ : (ℂ ∙ e₀)ᗮ, ‖measureFourier μ (((U⁻¹ : UnitaryGroup E) : E →L[ℂ] E) ξ)‖ₑ ^ 2 :=
    fun U ↦ by simp_rw [η, measureFourier_map_unitaryProjection]
  have htot := lintegral_unitaryHaar_measureFourier_sq hn he₀ μ
  obtain ⟨_, hct⟩ := projectionConstant_pos_ne_top hn he₀
  have hfin : ∀ᵐ U ∂unitaryHaar E,
      ∫⁻ ξ : (ℂ ∙ e₀)ᗮ, ‖measureFourier μ (((U⁻¹ : UnitaryGroup E) : E →L[ℂ] E) ξ)‖ₑ ^ 2 < ⊤ := by
    refine ae_lt_top ?_ (htot ▸ ENNReal.mul_ne_top hct hI.ne)
    exact Measurable.lintegral_prod_right' (((measurable_measureFourier μ).enorm.pow_const 2).comp
      ((continuous_subtype_val.comp continuous_fst.inv).clm_apply
        (continuous_subtype_val.comp continuous_snd)).measurable)
  have hmem : ∀ᵐ U ∂unitaryHaar E, MemLp (measureFourier (η U)) 2 := by
    filter_upwards [hfin] with U hU
    refine ⟨(measurable_measureFourier (η U)).aestronglyMeasurable, ?_⟩
    have h2 := lintegral_enorm_sq_eq_eLpNorm_sq (volume : Measure (ℂ ∙ e₀)ᗮ)
      (measureFourier (η U))
    rw [hsq] at h2
    rw [h2] at hU
    refine lt_top_iff_ne_top.mpr fun htop ↦ ?_
    simp [htop] at hU
  classical
  let g : UnitaryGroup E → (ℂ ∙ e₀)ᗮ → ℝ := fun U ↦
    if h : MemLp (measureFourier (η U)) 2 then
      (exists_density_of_memLp_measureFourier (η U) h).choose else 0
  have hg : ∀ U (h : MemLp (measureFourier (η U)) 2), g U =
      (exists_density_of_memLp_measureFourier (η U) h).choose := fun U h ↦ by
    simp only [g, dite_eq_left h]
  refine ⟨g, ?_, ?_⟩
  · filter_upwards [hmem] with U hU
    have := (exists_density_of_memLp_measureFourier (η U) hU).choose_spec
    rw [hg U hU]
    exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.trans (hsq U)⟩
  · rw [← htot]
    refine lintegral_congr_ae ?_
    filter_upwards [hmem] with U hU
    have := (exists_density_of_memLp_measureFourier (η U) hU).choose_spec
    rw [hg U hU, this.2.2.2.2, hsq]

end PshLines.PSHD
