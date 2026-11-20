import Tengoku.PshdLean.PshLines.PSHD.LeviPositivity
import Tengoku.PshdLean.PshLines.PSHD.ComponentSections
import Tengoku.PshdLean.PshLines.PshLeviPositivity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Distributional Levi positivity by slicing along complex lines

Step 3 of Proposition 2.1 of `pshd-vibe`, following the article. Fix a direction
`a ≠ 0` and a nonnegative test function `χ`. Writing points as `w + t • a` with
`w ∈ (ℂ ∙ a)ᗮ` and `t ∈ ℂ`, the Levi pairing of `u` with `χ` in direction `a` is,
up to a positive Haar normalization, the integral over `w` of the planar pairings
of `t ↦ u (w + t • a)` with the Laplacian of `t ↦ χ (w + t • a)`. Each planar
pairing is nonnegative because the slice is subharmonic on its open parameter
set, and so the Levi distribution is positive.
-/

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal Distributions ContDiff

namespace PshLines.PSHD

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℂ E] in
/-- **Planar pairings on a line.** For a nonnegative Borel function which is
locally bounded above and subharmonic on every connected component of every
affine complex-line section of an open set, and a nonnegative smooth compactly
supported function there, the planar Levi pairing along any complex line is
nonnegative.-/
theorem LineSubharmonicOn.integral_line_mul_leviForm_nonneg {u : E → ℝ} {D : Set E}
    (hD : IsOpen D) (hl : LineSubharmonicOn u D) (hu : Measurable u)
    (hpos : ∀ x ∈ D, 0 ≤ u x) (hbdd : ∀ p ∈ D, ∃ r > 0, BddAbove (u '' ball p r))
    {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχD : tsupport χ ⊆ D)
    (hχn : ∀ x, 0 ≤ χ x) (w a : E) (ha : a ≠ 0) :
    0 ≤ ∫ t : ℂ, u (w + t • a) * leviForm χ (w + t • a) a := by
  let g : ℂ → E := fun t ↦ w + t • a
  have hg : Topology.IsClosedEmbedding g :=
    (Homeomorph.addLeft w).isClosedEmbedding.comp (isClosedEmbedding_smul_left ha)
  let O : Opens ℂ := ⟨g ⁻¹' D, hD.preimage hg.continuous⟩
  have hO : IsOpen (O : Set ℂ) := O.isOpen
  -- the slice satisfies the disc criterion on the whole open parameter set
  have hdisc : DiscPshOn (fun t : ℂ ↦ (u (g t) : EReal)) O :=
    discPshOn_of_connectedComponentIn hO fun t ht ↦ hl w a ha t ht
  -- the slice is nonnegative and locally bounded above, hence locally integrable
  have hbddO : ∀ p ∈ (O : Set ℂ), ∃ r > 0, BddAbove ((u ∘ g) '' ball p r) := by
    intro p hp
    obtain ⟨r, hr, C, hC⟩ := hbdd (g p) hp
    refine ⟨r / ‖a‖, div_pos hr (norm_pos_iff.mpr ha), C, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    refine hC ⟨g t, ?_, rfl⟩
    rw [mem_ball, dist_eq_norm] at ht ⊢
    have : g t - g p = (t - p) • a := by simp [g, sub_smul]
    rw [this, norm_smul, ← lt_div_iff₀ (norm_pos_iff.mpr ha)]
    exact ht
  have hL : LocallyIntegrableOn (u ∘ g) O volume :=
    locallyIntegrableOn_of_bddAbove hO (hu.comp hg.continuous.measurable)
      (fun t ht ↦ hpos _ ht) hbddO volume
  have hL' : LocallyIntegrableOn (fun t : ℂ ↦ ((u (g t) : EReal)).toReal) O volume := by
    simpa only [EReal.toReal_coe, Function.comp_def] using hL
  -- the restricted test function
  let ψ : 𝓓(O, ℝ) :=
    { toFun := χ ∘ g
      contDiff' := hχ.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
      hasCompactSupport' := hχc.comp_isClosedEmbedding hg
      tsupport_subset' := (tsupport_comp_subset_preimage χ hg.continuous).trans
        (preimage_mono hχD) }
  have hψn : ∀ t, 0 ≤ ψ t := fun t ↦ hχn (g t)
  have hpos' := hdisc.hasNonnegativeDistributionalLevi_of_locallyIntegrable hL'
    (Eventually.of_forall fun t ↦ ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩) 1 ψ hψn
  rw [distributionalLeviCLM_regularDistribution_apply] at hpos'
  have hlevi : ∀ t : ℂ, leviForm ψ t 1 = leviForm χ (w + t • a) a := by
    intro t
    have h2 : ContDiff ℝ 2 χ := hχ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    change (realHessian (fun t : ℂ ↦ χ (w + t • a)) t 1 1 +
      realHessian (fun t : ℂ ↦ χ (w + t • a)) t (Complex.I • (1 : ℂ))
        (Complex.I • (1 : ℂ))) / 4 = _
    rw [realHessian_complexLine h2, realHessian_complexLine h2]
    simp [leviForm]
  simpa [hlevi, g] using hpos'

/-- **Distributional Levi positivity by slicing** (Step 3 of Proposition 2.1,
as in the article). For a nonnegative Borel function which is locally bounded
above and subharmonic on every connected component of every affine complex-line
section of an open set, every constant-direction Levi distribution is positive:
by Fubini's theorem over `(ℂ ∙ a)ᗮ × ℂ`, its value on a nonnegative test function
is a positive multiple of an integral of nonnegative planar pairings.-/
theorem LineSubharmonicOn.hasNonnegativeDistributionalLevi_of_slices {Ω : Opens E} {u : E → ℝ}
    (hl : LineSubharmonicOn u Ω) (hu : Measurable u) (hpos : ∀ x ∈ Ω, 0 ≤ u x)
    (hbdd : ∀ p ∈ Ω, ∃ r > 0, BddAbove (u '' ball p r))
    (μ : Measure E) [μ.IsAddHaarMeasure] (huL : LocallyIntegrableOn u Ω μ) :
    HasNonnegativeDistributionalLevi (regularDistribution μ u huL) := by
  intro a χ hχn
  rw [distributionalLeviCLM_regularDistribution_apply]
  by_cases ha : a = 0
  · simp [ha]
  let W : Submodule ℂ E := (ℂ ∙ a)ᗮ
  have hc : IsCompl W (ℂ ∙ a) := (Submodule.isCompl_orthogonal (ℂ ∙ a)).symm
  let eₗ : (W × ℂ) ≃ₗ[ℂ] E :=
    ((LinearEquiv.refl ℂ W).prodCongr (LinearEquiv.toSpanNonzeroSingleton ℂ E a ha)).trans
      (Submodule.prodEquivOfIsCompl W (ℂ ∙ a) hc)
  let e : (W × ℂ) ≃L[ℂ] E := eₗ.toContinuousLinearEquiv
  have he : ∀ p : W × ℂ, e p = (p.1 : E) + p.2 • a := by
    intro p
    simp [e, eₗ]
  let ν : Measure (W × ℂ) := (Measure.addHaar : Measure W).prod volume
  let F : E → ℝ := fun x ↦ u x * leviForm χ x a
  have hF : Integrable F μ := integrable_mul_leviForm_testFunction huL χ a
  let eₘ : (W × ℂ) ≃ᵐ E := e.toHomeomorph.toMeasurableEquiv
  have heₘ : ∀ p, eₘ p = e p := fun _ ↦ rfl
  have : (ν.map eₘ).IsAddHaarMeasure := e.isAddHaarMeasure_map ν
  set c := (ν.map eₘ).addHaarScalarFactor μ
  have hmap : ν.map eₘ = c • μ := Measure.isAddLeftInvariant_eq_smul _ _
  have hcpos : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have hFν : Integrable F (ν.map eₘ) := by
    rw [hmap]
    exact hF.smul_measure ENNReal.coe_ne_top
  have hFe : Integrable (F ∘ eₘ) ν := (integrable_map_equiv eₘ F).mp hFν
  have hslice : 0 ≤ ∫ p, F (eₘ p) ∂ν := by
    rw [integral_prod (fun p ↦ F (eₘ p)) hFe]
    refine integral_nonneg fun w ↦ ?_
    simp only [heₘ, he, F]
    exact hl.integral_line_mul_leviForm_nonneg Ω.isOpen hu hpos hbdd χ.contDiff
      χ.hasCompactSupport χ.tsupport_subset hχn w a ha
  rw [← integral_map_equiv eₘ F, hmap, integral_smul_nnreal_measure] at hslice
  rw [NNReal.smul_def, smul_eq_mul] at hslice
  exact nonneg_of_mul_nonneg_right hslice (by exact_mod_cast hcpos)

end PshLines.PSHD
