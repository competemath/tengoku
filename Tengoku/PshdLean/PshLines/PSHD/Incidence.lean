import Tengoku.PshdLean.PshLines.PSHD.Projection
import Tengoku.PshdLean.PshLines.PSHD.IncidenceMeasure
import Tengoku.Seed.MeasureTheory.Integral.MeanInequalities

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Incidence

`pshd-vibe`, Lemma 1.5: probability measures of uniformly bounded
`(2n - 2)`-energy on subsets of a compact set force one affine complex line to
meet infinitely many of the subsets.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace PshLines.PSHD

section CauchySchwarz

variable {α : Type*} [MeasurableSpace α]

/-- Cauchy–Schwarz for a measure with density.
@isnad1 id=le.2h4v.s7.41590a246e30 from=translated src=- shape=79e80d1a vocab=91407423
-/
theorem withDensity_apply_le_sqrt (ν : Measure α) {f : α → ℝ≥0∞} (hf : AEMeasurable f ν)
    {A : Set α} (hA : MeasurableSet A) :
    ν.withDensity f A ≤ (∫⁻ x, f x ^ 2 ∂ν) ^ (1 / 2 : ℝ) * ν A ^ (1 / 2 : ℝ) := by
  have hind : AEMeasurable (A.indicator fun _ ↦ (1 : ℝ≥0∞)) ν :=
    (measurable_const.indicator hA).aemeasurable
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two hf hind
  rw [withDensity_apply _ hA, ← lintegral_indicator hA]
  have h1 : ∫⁻ x, A.indicator f x ∂ν = ∫⁻ x, (f * A.indicator fun _ ↦ (1 : ℝ≥0∞)) x ∂ν := by
    congr 1
    funext x
    by_cases hx : x ∈ A <;> simp [hx]
  have h2 : ∫⁻ x, (A.indicator (fun _ ↦ (1 : ℝ≥0∞)) x) ^ (2 : ℝ) ∂ν = ν A := by
    rw [← lintegral_indicator_one hA]
    congr 1
    funext x
    by_cases hx : x ∈ A <;> simp [hx]
  have h3 : ∫⁻ x, f x ^ (2 : ℝ) ∂ν = ∫⁻ x, f x ^ 2 ∂ν := by
    simp_rw [ENNReal.rpow_two]
  rw [h1]
  refine h.trans_eq ?_
  rw [h2, h3]

omit [MeasurableSpace α] in
/-- A pointwise geometric-mean lower bound integrates to a product lower bound.
@isnad1 id=le.3h5v.s7.651df566eb85 from=translated src=- shape=44e7ee20 vocab=f54161c1
-/
theorem sq_le_lintegral_mul_lintegral [MeasurableSpace α] (m : Measure α) [IsProbabilityMeasure m]
    {N V : α → ℝ≥0∞} (hN : AEMeasurable N m) (hV : AEMeasurable V m) {a : ℝ≥0∞}
    (h : ∀ᵐ U ∂m, a ≤ N U ^ (1 / 2 : ℝ) * V U ^ (1 / 2 : ℝ)) :
    a ^ 2 ≤ (∫⁻ U, N U ∂m) * ∫⁻ U, V U ∂m := by
  have hf : AEMeasurable (fun U ↦ N U ^ (1 / 2 : ℝ)) m := hN.pow_const _
  have hg : AEMeasurable (fun U ↦ V U ^ (1 / 2 : ℝ)) m := hV.pow_const _
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq m Real.HolderConjugate.two_two hf hg
  have hsq : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x := fun x ↦ by
    rw [← ENNReal.rpow_mul]
    norm_num
  simp_rw [hsq] at hH
  have ha : a ≤ ∫⁻ U, (fun U ↦ N U ^ (1 / 2 : ℝ)) U * (fun U ↦ V U ^ (1 / 2 : ℝ)) U ∂m := by
    calc a = ∫⁻ _, a ∂m := by rw [lintegral_const, measure_univ, mul_one]
      _ ≤ _ := lintegral_mono_ae h
  have := ha.trans hH
  calc a ^ 2 ≤ ((∫⁻ U, N U ∂m) ^ (1 / 2 : ℝ) * (∫⁻ U, V U ∂m) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ zero_le this 2
    _ = _ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num

end CauchySchwarz

section Main

attribute [local instance] InnerProductSpace.complexToReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E] in
/-- A fiber of a rotated hyperplane projection is an affine complex line.
@isnad1 id=ex.1h5v.s13.1f2454fe2548 from=translated src=- shape=2d7628be vocab=05508267
-/
theorem exists_eq_add_smul_of_unitaryProjection_eq (e₀ : E) (U : UnitaryGroup E)
    {c : (ℂ ∙ e₀)ᗮ} {y : E} (h : unitaryProjection e₀ U y = c) :
    ∃ t : ℂ, y = ((U⁻¹ : UnitaryGroup E) : E →L[ℂ] E) c +
      t • ((U⁻¹ : UnitaryGroup E) : E →L[ℂ] E) e₀ := by
  set z := (U : E →L[ℂ] E) y
  have hz : z - ((ℂ ∙ e₀)ᗮ.orthogonalProjectionOnto z : E) ∈ (ℂ ∙ e₀)ᗮᗮ :=
    Submodule.sub_starProjection_mem_orthogonal z
  rw [Submodule.orthogonal_orthogonal, Submodule.mem_span_singleton] at hz
  obtain ⟨t, ht⟩ := hz
  have hc : ((ℂ ∙ e₀)ᗮ.orthogonalProjectionOnto z : E) = c := congrArg Subtype.val h
  refine ⟨t, ?_⟩
  have hzy : ((U⁻¹ : UnitaryGroup E) : E →L[ℂ] E) z = y := by
    change ((U⁻¹ * U : UnitaryGroup E) : E →L[ℂ] E) y = y
    simp
  rw [← hzy, ← map_smul, ← map_add, ht, hc]
  congr 1
  abel

/-- **Incidence** (`pshd-vibe`, Lemma 1.5). Let `n ≥ 2`, `K` compact and `S j ⊆ K`
Borel. If probability measures `μ j` carried by `S j` have uniformly bounded
`(2n - 2)`-energy, then one affine complex line `c + ℂ v` meets `S j` for
infinitely many `j`.
@isnad1 id=ex.7h5v.s8.b0d64655e7dd from=translated src=- shape=1baf7cbd vocab=dfc555a6
-/
theorem exists_affineLine_frequently_meets (hn : 2 ≤ Module.finrank ℂ E) {K : Set E}
    (hK : IsCompact K) {S : ℕ → Set E} (hS : ∀ j, MeasurableSet (S j)) (hSK : ∀ j, S j ⊆ K)
    (μ : ℕ → Measure E) [∀ j, IsProbabilityMeasure (μ j)] (hμS : ∀ j, μ j (S j) = 1)
    {C : ℝ≥0∞} (hC : C < ⊤)
    (hI : ∀ j, rieszEnergy ((2 * (Module.finrank ℂ E - 1) : ℕ) : ℝ) (μ j) ≤ C) :
    ∃ c v : E, v ≠ 0 ∧ ∀ m : ℕ, ∃ j, m ≤ j ∧ ∃ t : ℂ, c + t • v ∈ S j := by
  have hE : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℂ) (by omega)
  obtain ⟨w, hw⟩ := exists_ne (0 : E)
  set e₀ : E := ((‖w‖⁻¹ : ℝ) : ℂ) • w
  have he₀ : ‖e₀‖ = 1 := by
    simp only [e₀, norm_smul, Complex.norm_real, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)
  set H := (ℂ ∙ e₀)ᗮ
  -- compact pieces of mass at least one half
  have hF : ∀ j, ∃ F ⊆ S j, IsCompact F ∧ (1 / 2 : ℝ≥0∞) < μ j F := fun j ↦
    (hS j).exists_lt_isCompact_of_ne_top (by simp [hμS j]) (by rw [hμS j]; norm_num)
  choose F hFS hFc hFμ using hF
  obtain ⟨M, hM⟩ := hK.isBounded.subset_closedBall (0 : E)
  set B : Set H := closedBall 0 M
  set lam : Measure (UnitaryGroup E × H) := (unitaryHaar E).prod (volume.restrict B)
  have hBfin : volume B < ⊤ := (isCompact_closedBall (0 : H) M).measure_lt_top
  have : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hBfin.ne
  have hlam : IsFiniteMeasure lam := inferInstance
  set Φ : UnitaryGroup E × E → UnitaryGroup E × H := fun p ↦ (p.1, unitaryProjection e₀ p.1 p.2)
  have hΦ : Continuous Φ := continuous_fst.prodMk (continuous_unitaryProjection_uncurry e₀)
  set I : ℕ → Set (UnitaryGroup E × H) := fun j ↦ Φ '' (univ ×ˢ F j)
  have hIc : ∀ j, IsCompact (I j) := fun j ↦ (isCompact_univ.prod (hFc j)).image hΦ
  have hIm : ∀ j, MeasurableSet (I j) := fun j ↦ (hIc j).isClosed.measurableSet
  have hslice : ∀ j U, Prod.mk U ⁻¹' I j = unitaryProjection e₀ U '' F j := by
    intro j U
    ext c
    simp only [I, Φ, mem_preimage, mem_image, mem_prod, mem_univ, true_and, Prod.mk.injEq,
      Prod.exists]
    constructor
    · rintro ⟨U', y, hy, rfl, hc⟩
      exact ⟨y, hy, hc⟩
    · rintro ⟨y, hy, hc⟩
      exact ⟨U, y, hy, rfl, hc⟩
  have hsliceB : ∀ j U, unitaryProjection e₀ U '' F j ⊆ B := by
    rintro j U _ ⟨y, hy, rfl⟩
    have hyK := hM (hSK j (hFS j hy))
    rw [mem_closedBall, dist_zero_right] at hyK ⊢
    calc ‖unitaryProjection e₀ U y‖ ≤ ‖(U : E →L[ℂ] E) y‖ :=
          (ℂ ∙ e₀)ᗮ.norm_orthogonalProjectionOnto_apply_le _
      _ = ‖y‖ := Unitary.norm_map U y
      _ ≤ M := hyK
  set c₀ := projectionConstant e₀
  obtain ⟨hc₀pos, hc₀top⟩ := projectionConstant_pos_ne_top hn he₀
  set δ : ℝ≥0∞ := (1 / 2 : ℝ≥0∞) ^ 2 / (c₀ * C)
  have hδpos : 0 < δ := ENNReal.div_pos (by norm_num) (ENNReal.mul_ne_top hc₀top hC.ne)
  have hδ : ∀ j, δ ≤ lam (I j) := by
    intro j
    obtain ⟨g, hgae, _⟩ := exists_projection_densities hn he₀ (μ j) ((hI j).trans_lt hC)
    set N : UnitaryGroup E → ℝ≥0∞ := fun U ↦ ∫⁻ ξ : H,
      ‖measureFourier (μ j) (((U⁻¹ : UnitaryGroup E) : E →L[ℂ] E) ξ)‖ₑ ^ 2
    set V : UnitaryGroup E → ℝ≥0∞ := fun U ↦ volume.restrict B (Prod.mk U ⁻¹' I j)
    have hNm : Measurable N := measurable_lintegral_measureFourier_sq (μ j) e₀
    have hVm : Measurable V := measurable_measure_prodMk_left (hIm j)
    have hlamI : lam (I j) = ∫⁻ U, V U ∂unitaryHaar E := Measure.prod_apply (hIm j)
    have hNint : ∫⁻ U, N U ∂unitaryHaar E ≤ c₀ * C := by
      rw [lintegral_unitaryHaar_measureFourier_sq hn he₀ (μ j)]
      gcongr
      exact hI j
    have hpt : ∀ᵐ U ∂unitaryHaar E, (1 / 2 : ℝ≥0∞) ≤ N U ^ (1 / 2 : ℝ) * V U ^ (1 / 2 : ℝ) := by
      filter_upwards [hgae] with U hU
      obtain ⟨hgm, -, -, hmap, hnorm⟩ := hU
      set A := unitaryProjection e₀ U '' F j
      have hA : MeasurableSet A := ((hFc j).image (continuous_unitaryProjection e₀ U)).isClosed.measurableSet
      have hVU : V U = volume A := by
        simp only [V, hslice]
        rw [Measure.restrict_apply hA, inter_eq_left.mpr (hsliceB j U)]
      calc (1 / 2 : ℝ≥0∞) ≤ μ j (F j) := (hFμ j).le
        _ ≤ μ j (unitaryProjection e₀ U ⁻¹' A) := measure_mono (subset_preimage_image _ _)
        _ = (μ j).map (unitaryProjection e₀ U) A :=
            (Measure.map_apply (continuous_unitaryProjection e₀ U).measurable hA).symm
        _ = volume.withDensity (fun x ↦ ENNReal.ofReal (g U x)) A := by rw [hmap]
        _ ≤ (∫⁻ x, ENNReal.ofReal (g U x) ^ 2) ^ (1 / 2 : ℝ) * volume A ^ (1 / 2 : ℝ) :=
            withDensity_apply_le_sqrt _ (ENNReal.measurable_ofReal.comp hgm).aemeasurable hA
        _ = N U ^ (1 / 2 : ℝ) * V U ^ (1 / 2 : ℝ) := by rw [hnorm, hVU]
    have hsq := sq_le_lintegral_mul_lintegral (unitaryHaar E) hNm.aemeasurable hVm.aemeasurable hpt
    rw [hlamI]
    have hle : (1 / 2 : ℝ≥0∞) ^ 2 ≤ (∫⁻ U, V U ∂unitaryHaar E) * (c₀ * C) := by
      calc (1 / 2 : ℝ≥0∞) ^ 2 ≤ (∫⁻ U, N U ∂unitaryHaar E) * ∫⁻ U, V U ∂unitaryHaar E := hsq
        _ ≤ (c₀ * C) * ∫⁻ U, V U ∂unitaryHaar E := by gcongr
        _ = _ := mul_comm _ _
    exact ENNReal.div_le_of_le_mul hle
  obtain ⟨⟨U, c⟩, hrec⟩ := exists_recurrent_of_measure_lower_bound lam hIm hδpos hδ
  refine ⟨((U⁻¹ : UnitaryGroup E) : E →L[ℂ] E) c, ((U⁻¹ : UnitaryGroup E) : E →L[ℂ] E) e₀,
    ?_, fun m ↦ ?_⟩
  · intro h0
    have := Unitary.norm_map U⁻¹ e₀
    rw [h0, norm_zero, he₀] at this
    exact zero_ne_one this
  · obtain ⟨j, hmj, hj⟩ := hrec m
    have hj' : c ∈ Prod.mk U ⁻¹' I j := hj
    rw [hslice] at hj'
    obtain ⟨y, hy, hyc⟩ := hj'
    obtain ⟨t, ht⟩ := exists_eq_add_smul_of_unitaryProjection_eq e₀ U hyc
    exact ⟨j, hmj, t, ht ▸ hFS j hy⟩

end Main

end PshLines.PSHD
