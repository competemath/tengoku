module

public import Tengoku.Carleson.Carleson.ToMathlib.MeasureTheory.Integral.Periodic

public section

namespace Function

namespace Periodic

open MeasureTheory Set Filter Function TopologicalSpace

open scoped Topology Filter ENNReal Interval NNReal

variable {E ε : Type*} [NormedAddCommGroup E] [TopologicalSpace ε] [ENormedAddMonoid ε]

variable [NormedSpace ℝ E]

variable {a b : ℝ} {f g : ℝ → E} {μ : Measure ℝ} {T : ℝ}

--TODO: use this in the proof of `intervalIntegral_add_eq` in mathlib?
/-- If `f` is a periodic function with period `T`, then its integral over `[t, t + T]` does not
depend on `t`.
@isnad1 id=eq.1h5v.s6.4383e2889fa6 from=translated src=- shape=44ae689c vocab=6bd40e17
-/
theorem setIntegral_Ioc_add_eq (hf : Periodic f T) (t s : ℝ) :
    ∫ x in Ioc t (t + T), f x = ∫ x in Ioc s (s + T), f x := by
  wlog! hT : 0 < T
  · rw [Ioc_eq_empty (by simpa), Ioc_eq_empty (by simpa)]
  have : VAddInvariantMeasure (AddSubgroup.zmultiples T) ℝ volume :=
    ⟨fun c s _ => measure_preimage_add _ _ _⟩
  apply IsAddFundamentalDomain.setIntegral_eq (G := AddSubgroup.zmultiples T)
  exacts [isAddFundamentalDomain_Ioc hT t, isAddFundamentalDomain_Ioc hT s, hf.map_vadd_zmultiples]

/--
@isnad1 id=eq.1h4v.s6.f456875d3ac9 from=translated src=- shape=b6038301 vocab=7827a1f6
-/
theorem setLIntegral_Ioc_add_eq {f : ℝ → ℝ≥0∞} (hf : Periodic f T) (t s : ℝ) :
    ∫⁻ x in Ioc t (t + T), f x = ∫⁻ x in Ioc s (s + T), f x := by
  wlog! hT : 0 < T
  · rw [Ioc_eq_empty (by simpa), Ioc_eq_empty (by simpa)]
  have : VAddInvariantMeasure (AddSubgroup.zmultiples T) ℝ volume :=
    ⟨fun c s _ => measure_preimage_add _ _ _⟩
  apply IsAddFundamentalDomain.setLIntegral_eq (G := AddSubgroup.zmultiples T)
  exacts [isAddFundamentalDomain_Ioc hT t, isAddFundamentalDomain_Ioc hT s,
    (hf.comp enorm).map_vadd_zmultiples]

--TODO: the assumption `p ≠ ⊤` is not necessary; this case should be proved as well
/--
@isnad1 id=eq.2h5v.s7.0c8c5457e41e from=translated src=- shape=9c413fef vocab=0607e6e2
-/
theorem eLpNorm {T : ℝ} {s t : ℝ} {f : ℝ → ℂ}
  (periodic_f : f.Periodic T)
  {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    eLpNorm f p (volume.restrict (Ioc t (t + T))) = eLpNorm f p (volume.restrict (Ioc s (s + T))) := by
  unfold MeasureTheory.eLpNorm
  split_ifs with p_zero --p_top
  · rfl
  --· sorry
  · rw [eLpNorm'_eq_lintegral_enorm, eLpNorm'_eq_lintegral_enorm, ]
    congr 1
    apply setLIntegral_Ioc_add_eq
    intro x
    simp only
    congr 2
    apply periodic_f

/--
@isnad1 id=aestrong.2h3v.s6.ac5a62c05171 from=translated src=- shape=1de99f03 vocab=bc5f5e77
-/
theorem aestronglyMeasurable {t T : ℝ} [hT : Fact (0 < T)] {f : ℝ → ℂ}
  (periodic_f : f.Periodic T) (hf : AEStronglyMeasurable f (volume.restrict (Ioc t (t + T)))) :
    AEStronglyMeasurable f := by
  rw [← Measure.restrict_univ (μ := volume), ← iUnion_Ioc_add_zsmul hT.out t]
  apply AEStronglyMeasurable.iUnion
  intro n
  have : AEStronglyMeasurable (f ∘ (fun x ↦ x - n • T))
      (volume.restrict (Ioc (t + n • T) (t + (n + 1) • T))) := by
    apply hf.comp_measurePreserving
    have : (Ioc (t + n • T) (t + (n + 1) • T)) = (fun x ↦ x - n • T) ⁻¹' (Ioc t (t + T)) := by
      rw [preimage_sub_const_Ioc, add_smul]
      ring_nf
    rw [this]
    apply MeasurePreserving.restrict_preimage (measurePreserving_sub_right _ _) measurableSet_Ioc
  convert! this
  ext x
  simp only [comp_apply]
  rw [periodic_f.sub_zsmul_eq]

/--
@isnad1 id=iff.1h3v.s6.52199e2a7f35 from=translated src=- shape=edffd2c0 vocab=bc5f5e77
-/
theorem aestronglyMeasurable_iff {t T : ℝ} [hT : Fact (0 < T)] {f : ℝ → ℂ}
  (periodic_f : f.Periodic T) :
    AEStronglyMeasurable f ↔ AEStronglyMeasurable f (volume.restrict (Ioc t (t + T))) :=
  ⟨fun hf ↦ hf.restrict, aestronglyMeasurable periodic_f⟩

/-
theorem locallyIntegrable_of {T : ℝ} [hT : Fact (0 < T)] {f : ℝ → ℂ}
  (periodic_f : f.Periodic T) (hf : IntegrableOn f (Ioc 0 T)) :
    LocallyIntegrable f := by
  rw [← Measure.restrict_univ (μ := volume), ← iUnion_Ioc_zsmul hT.out]
  #check locallyIntegrableOn_iff_locallyIntegrable_restrict
  apply LocallyIntegrableOn.iUnion
  intro n
  have : AEStronglyMeasurable (f ∘ (fun x ↦ x - n • T))
      (volume.restrict (Ioc (n • T) ((n + 1) • T))) := by
    apply hf.comp_measurePreserving
    have : (Ioc (n • T) ((n + 1) • T)) = (fun x ↦ x - n • T) ⁻¹' (Ioc 0 T) := by
      rw [preimage_sub_const_Ioc, add_smul]
      ring_nf
    rw [this]
    apply MeasurePreserving.restrict_preimage (measurePreserving_sub_right _ _) measurableSet_Ioc
  convert this
  ext x
  simp only [comp_apply]
  rw [periodic_f.sub_zsmul_eq]
-/

end Periodic

end Function

namespace AddCircle

open MeasureTheory

/--
@isnad1 id=eq.1h2v.s8.4c74417c5a83 from=translated src=- shape=238d5ba9 vocab=61a14502
-/
lemma volume_preimage_equivIoc {T : ℝ} [hT : Fact (0 < T)] {s : Set ℝ} (hs : MeasurableSet s) :
    volume ((fun x ↦ (equivIoc T 0 x : ℝ)) ⁻¹' s) = volume (s ∩ Set.Ioc 0 T) := by
  rw [← Measure.restrict_apply' measurableSet_Ioc,
    ← (AddCircle.measurePreserving_mk T 0).measure_preimage
      ((measurable_equivIoc T 0).subtype_coe.nullMeasurable hs),
    Measure.restrict_apply' measurableSet_Ioc, Measure.restrict_apply' measurableSet_Ioc]
  congr 1 with x
  simp only [zero_add, Set.mem_inter_iff, Set.mem_preimage, and_congr_left_iff]
  intro hx
  rw [equivIoc_coe_of_mem (by simp [hx])]

end AddCircle

open Set ENNReal

-- Analogous to `MeasureTheory.MemLp.memLp_liftIoc`
/--
@isnad1 id=eq.1h4v.s7.6cbdaf4116a1 from=translated src=- shape=6fbe6f7e vocab=98349e09
-/
theorem MeasureTheory.eLpNorm_eq_eLpNorm_liftIoc {T : ℝ} [hT : Fact (0 < T)] {t : ℝ} {f : ℝ → ℂ}
  (hf : AEStronglyMeasurable f (volume.restrict (Ioc t (t + T)))) {p : ℝ≥0∞} :
    eLpNorm f p (volume.restrict (Ioc t (t + T))) = eLpNorm (AddCircle.liftIoc T t f) p volume := by
  simp only [AddCircle.liftIoc, Set.domRestrict_def, Function.comp_def]
  rw [← Function.comp_def, eLpNorm_comp_measurePreserving (g := f) (p := p) hf]
  refine .comp (measurePreserving_subtype_coe measurableSet_Ioc) ?_
  exact AddCircle.measurePreserving_equivIoc T

--TODO: find better name
/--
@isnad1 id=eq.1h4v.s7.ce2b0660292d from=translated src=- shape=54687697 vocab=d2bb2f40
-/
theorem MeasureTheory.eLpNorm_eq_eLpNorm_liftIoc' {T : ℝ} [hT : Fact (0 < T)] {t : ℝ}
  {f : (AddCircle T) → ℂ} (hf : AEStronglyMeasurable f volume) {p : ℝ≥0∞} :
    eLpNorm (fun (x : ℝ) ↦ f x) p (volume.restrict (Ioc t (t + T))) = eLpNorm f p volume := by
  rw [eLpNorm_eq_eLpNorm_liftIoc]
  · congr with x
    unfold AddCircle.liftIoc
    simp
  apply hf.comp_measurePreserving (AddCircle.measurePreserving_mk T t)
