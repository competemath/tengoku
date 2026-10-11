module

public import Tengoku.Carleson.Carleson.ToMathlib.Topology.Instances.AddCircle.Defs
public import Tengoku

@[expose] public section

-- Upstreaming status: looks nice and clean
-- First lemmas augment mathlib ones (or replace some proofs),
-- remaining ones are new (and can perhaps be a new file indeed).

open Set Function MeasureTheory MeasureTheory.Measure TopologicalSpace AddSubgroup intervalIntegral

open scoped MeasureTheory NNReal ENNReal

open scoped Convolution

section AE

variable (T : ℝ) [hT : Fact (0 < T)]

/--
@isnad1 id=nullsing.0h1v.s5.e5c06df039ba from=translated src=- shape=8d0cb61e vocab=fbc3dcb6
-/
instance AddCircle.noAtoms_volume : NullSingletonClass (volume : Measure (AddCircle T)) where
  measure_singleton x := by simpa [hT.out.le] using AddCircle.volume_closedBall T (x := x) 0

variable {B : Type*} {T a : ℝ} [hT : Fact (0 < T)] (f : ℝ → B)

/--
@isnad1 id=eventual.0h4v.s6.51d10b6b59c7 from=translated src=- shape=9e1a69ef vocab=695e1eba
-/
theorem AddCircle.liftIoc_ae_eq_liftIco : liftIoc T a f =ᵐ[volume] liftIco T a f :=
  .mono (volume.ae_ne _) (fun _ ↦ liftIoc_eq_liftIco_of_ne)

end AE

namespace AddCircle

variable (T : ℝ) [hT : Fact (0 < T)]

-- Add before `measurableEquivIoc`
/--
@isnad1 id=measurab.0h2v.s8.008aa213f4c9 from=translated src=- shape=698b4e9b vocab=01457fc7
-/
theorem measurable_equivIoc (a : ℝ) : Measurable (equivIoc T a) :=
  measurable_of_measurable_on_compl_singleton _
    (continuousOn_iff_continuous_domRestrict.mp <| continuousOn_of_forall_continuousAt fun _x hx =>
      continuousAt_equivIoc T a hx).measurable

/--
@isnad1 id=measurab.0h2v.s8.54c1ae9aa84b from=translated src=- shape=698b4e9b vocab=7c242256
-/
theorem measurable_equivIco (a : ℝ) : Measurable (equivIco T a) :=
  measurable_of_measurable_on_compl_singleton _
    (continuousOn_iff_continuous_domRestrict.mp <| continuousOn_of_forall_continuousAt fun _x hx =>
      continuousAt_equivIco T a hx).measurable

-- Replacement for existing proof of `measurableEquivIoc` now that the proof of `measurable_toFun`
-- is extracted as a separate lemma. The name is primed here only to avoid a collision.
noncomputable def measurableEquivIoc' (a : ℝ) : AddCircle T ≃ᵐ Ioc a (a + T) where
  toEquiv := equivIoc T a
  measurable_toFun := measurable_equivIoc T a
  measurable_invFun := AddCircle.measurable_mk'.comp measurable_subtype_coe

-- Replacement for existing proof of `measurableEquivIco` now that the proof of `measurable_toFun`
-- is extracted as a separate lemma. The name is primed here only to avoid a collision.
noncomputable def measurableEquivIco' (a : ℝ) : AddCircle T ≃ᵐ Ico a (a + T) where
  toEquiv := equivIco T a
  measurable_toFun := measurable_equivIco T a
  measurable_invFun := AddCircle.measurable_mk'.comp measurable_subtype_coe

variable {E : Type*} (T a : ℝ) [hT : Fact (0 < T)] {f : ℝ → E}

/--
@isnad1 id=eq.0h2v.s8.e1af087796d0 from=translated src=- shape=db6e730e vocab=9fe8e20e
-/
lemma map_subtypeVal_map_equivIoc_volume :
    (volume.map (equivIoc T a)).map Subtype.val = volume.restrict (Ioc a (a + T)) := by
  have h := measurable_equivIoc T a
  rw [← (AddCircle.measurePreserving_mk T a).map_eq]
  rw [Measure.map_map measurable_subtype_coe h, Measure.map_map (measurable_subtype_coe.comp h)]
  · exact (Measure.map_congr <| Filter.Eventually.mono (self_mem_ae_restrict measurableSet_Ioc) <|
      fun x hx ↦ AddCircle.liftIoc_coe_apply hx).trans Measure.map_id
  · exact fun _ ↦ id

end AddCircle

namespace MeasureTheory

open AddCircle

variable {E : Type*} (T a : ℝ) [hT : Fact (0 < T)] {f : ℝ → E}

/--
@isnad1 id=aestrong.1h4v.s6.ac1824f7901f from=translated src=- shape=8d5a2919 vocab=a01f2da2
-/
@[fun_prop] protected theorem AEStronglyMeasurable.liftIoc [TopologicalSpace E]
    (hf : AEStronglyMeasurable f) : AEStronglyMeasurable (liftIoc T a f) :=
  (map_subtypeVal_map_equivIoc_volume T a ▸ hf.restrict).comp_measurable
    measurable_subtype_coe |>.comp_measurable (measurable_equivIoc T a)

/--
@isnad1 id=aestrong.1h4v.s6.a5e0103ed77b from=translated src=- shape=8d5a2919 vocab=bf14b012
-/
@[fun_prop] protected theorem AEStronglyMeasurable.liftIco [TopologicalSpace E]
    (hf : AEStronglyMeasurable f) : AEStronglyMeasurable (liftIco T a f) :=
  (hf.liftIoc T a).congr (liftIoc_ae_eq_liftIco f)

/--
@isnad1 id=aemeasur.1h4v.s6.ee02ad59a343 from=translated src=- shape=8d5a2919 vocab=2af33282
-/
@[fun_prop] protected theorem AEMeasurable.liftIoc [MeasurableSpace E] (hf : AEMeasurable f) :
    AEMeasurable (liftIoc T a f) :=
  (map_subtypeVal_map_equivIoc_volume T a ▸ hf.restrict).comp_measurable
    measurable_subtype_coe |>.comp_measurable (measurable_equivIoc T a)

/--
@isnad1 id=aemeasur.1h4v.s6.c2bb6ac91d9c from=translated src=- shape=8d5a2919 vocab=7226da9e
-/
@[fun_prop] protected theorem AEMeasurable.liftIco [MeasurableSpace E] (hf : AEMeasurable f) :
    AEMeasurable (liftIco T a f) :=
  (hf.liftIoc T a).congr (liftIoc_ae_eq_liftIco f)

/--
@isnad1 id=eq.0h1v.s7.4611a3f073ce from=translated src=- shape=23142dfa vocab=8e55e168
-/
theorem map_coe_addCircle_volume_eq :
    Measure.map (fun (x : ℝ) ↦ (x : AddCircle T)) volume =
      (⊤ : ℝ≥0∞) • (volume : Measure (AddCircle T)) := by
  have : (volume : Measure ℝ) =
      Measure.sum (fun (n : ℤ) ↦ volume.restrict (Ioc (n • T) ((n + 1) • T))) := by
    rw [← restrict_iUnion (Set.pairwise_disjoint_Ioc_zsmul T) (fun n ↦ measurableSet_Ioc),
      iUnion_Ioc_zsmul hT.out, restrict_univ]
  rw [this, Measure.map_sum (by fun_prop)]
  have A (n : ℤ) : Measure.map (fun (x : ℝ) ↦ (x : AddCircle T))
      (volume.restrict (Ioc (n • T) ((n + 1) • T)) ) = volume := by
    simp only [zsmul_eq_mul, Int.cast_add, Int.cast_one, add_mul, one_mul]
    exact (AddCircle.measurePreserving_mk T (n * T)).map_eq
  simp only [A]
  ext s hs
  simp [hs]

/--
@isnad1 id=quasimea.0h1v.s6.3da6f21d806d from=translated src=- shape=f18c46de vocab=4e50f7f1
-/
theorem quasiMeasurePreserving_coe_addCircle :
    QuasiMeasurePreserving (fun (x : ℝ) ↦ (x : AddCircle T)) := by
  refine ⟨by fun_prop, ?_⟩
  rw [map_coe_addCircle_volume_eq]
  exact smul_absolutelyContinuous

end MeasureTheory

namespace AddCircle

section Convolution

variable {𝕜 E E' F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup E'] [NormedAddCommGroup F]
  [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 E'] [NormedSpace 𝕜 F]
  [NormedSpace ℝ F] (L : E →L[𝕜] E' →L[𝕜] F) {f : ℝ → E} {g : ℝ → E'}

variable {T : ℝ} [hT : Fact (0 < T)] (a : ℝ)

/--
@isnad1 id=eq.2h9v.s10.5a2257c55bba from=translated src=- shape=80340980 vocab=d4f05c63
-/
theorem liftIco_convolution_liftIco (hf : f.Periodic T) (hg : g.Periodic T) :
    liftIco T a f ⋆[L] liftIco T a g = liftIco T a fun x ↦ ∫ y in a..a+T, L (f y) (g (x - y)) := by
  refine funext (fun q ↦ QuotientAddGroup.induction_on q (fun x ↦ ?_))
  have : Periodic (fun x ↦ ∫ y in a..a+T, L (f y) (g (x-y))) T := by
    intro; refine integral_congr (fun _ _ ↦ ?_); rw [add_sub_right_comm, hg]
  rw [convolution, ← AddCircle.intervalIntegral_preimage T a, liftIco_coe_apply_of_periodic a this]
  refine integral_congr (fun y _ ↦ ?_)
  rw [AddCircle.liftIco_coe_apply_of_periodic a hf, ← AddCircle.liftIco_coe_apply_of_periodic a hg]
  rfl

/--
@isnad1 id=eq.2h9v.s10.1109ea2960f8 from=translated src=- shape=80340980 vocab=c6a926d2
-/
theorem liftIoc_convolution_liftIoc (hf : f.Periodic T) (hg : g.Periodic T) :
    liftIoc T a f ⋆[L] liftIoc T a g = liftIoc T a fun x ↦ ∫ y in a..a+T, L (f y) (g (x - y)) := by
  have : Periodic (fun x ↦ ∫ y in a..a+T, L (f y) (g (x-y))) T := by
    intro; refine integral_congr (fun _ _ ↦ ?_); rw [add_sub_right_comm, hg]
  rw [← liftIco_eq_liftIoc a a hf, ← liftIco_eq_liftIoc a a hg, ← liftIco_eq_liftIoc a a this]
  exact liftIco_convolution_liftIco L a hf hg

end Convolution

section eLpNorm

variable {𝕜 B : Type*} [NormedAddCommGroup B]

variable (T : ℝ) [hT : Fact (0 < T)] (a a' : ℝ) {f : ℝ → B} (hf : AEStronglyMeasurable f)
include hf

/-- The norm of the lift of a function `f` is equal to the norm of `f` on that period.
@isnad1 id=eq.1h5v.s7.7a7136256c66 from=translated src=- shape=197f12da vocab=d9363b35
-/
theorem eLpNorm_liftIoc (p : ℝ≥0∞) :
    eLpNorm (AddCircle.liftIoc T a f) p = eLpNorm ((Set.Ioc a (a + T)).indicator f) p := by
  set I := Ioc a (a + T)
  have : I.indicator f = I.indicator (liftIoc T a f ∘ QuotientAddGroup.mk) := by
    ext x
    by_cases hx : x ∈ I
    · simpa [hx] using (liftIoc_coe_apply hx).symm
    · simp [hx]
  rw [this, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioc]
  exact (eLpNorm_comp_measurePreserving (hf.liftIoc T a) (AddCircle.measurePreserving_mk T a)).symm

/-- The norm of the lift of a function `f` is equal to the norm of `f` on that period.
@isnad1 id=eq.1h5v.s7.5d1a6cd9edfe from=translated src=- shape=860c8e18 vocab=0a3d92b6
-/
theorem eLpNorm_liftIoc' (p : ℝ≥0∞) :
    eLpNorm (AddCircle.liftIoc T a f) p = eLpNorm f p (volume.restrict ((Set.Ioc a (a + T)))) := by
  rw [eLpNorm_liftIoc _ _ hf, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioc]

/-- The norm of the lift of a function `f` is equal to the norm of `f` on that period.
@isnad1 id=eq.1h5v.s7.c4b95a8861ec from=translated src=- shape=197f12da vocab=fb7b1050
-/
theorem eLpNorm_liftIco (p : ℝ≥0∞) :
    eLpNorm (AddCircle.liftIco T a f) p = eLpNorm ((Set.Ico a (a + T)).indicator f) p := by
  rw [eLpNorm_congr_ae (liftIoc_ae_eq_liftIco f).symm, eLpNorm_liftIoc T a hf,
    eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ico,
    eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioc, restrict_Ico_eq_restrict_Ioc]

/-- The norm of the lift of a function `f` is equal to the norm of `f` on that period.
@isnad1 id=eq.1h5v.s7.21fb3cdf990d from=translated src=- shape=860c8e18 vocab=47585d18
-/
theorem eLpNorm_liftIco' (p : ℝ≥0∞) :
    eLpNorm (AddCircle.liftIco T a f) p = eLpNorm f p (volume.restrict (Set.Ico a (a + T))) := by
  rw [eLpNorm_liftIco _ _ hf, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ico]

/-- The norm of the lift of a periodic function `f` is equal to the norm of `f` on any period.
@isnad1 id=eq.2h6v.s7.ec7ef3b66d5f from=translated src=- shape=0c330ba4 vocab=3f28d2d0
-/
theorem eLpNorm_liftIoc_of_periodic (hfT : Periodic f T) (p : ℝ≥0∞) :
    eLpNorm (AddCircle.liftIoc T a f) p = eLpNorm ((Set.Ioc a' (a' + T)).indicator f) p := by
  rw [liftIoc_eq_liftIoc a a' hfT, eLpNorm_liftIoc T a' hf p]

/-- The norm of the lift of a periodic function `f` is equal to the norm of `f` on any period.
@isnad1 id=eq.2h6v.s7.dfddaa566069 from=translated src=- shape=c5e28731 vocab=3cd5e3cf
-/
theorem eLpNorm_liftIoc_of_periodic' (hfT : Periodic f T) (p : ℝ≥0∞) :
    eLpNorm (AddCircle.liftIoc T a f) p = eLpNorm f p (volume.restrict (Set.Ioc a' (a' + T))) := by
  rw [eLpNorm_liftIoc_of_periodic T a a' hf hfT,
    eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioc]

/-- The norm of the lift of a periodic function `f` is equal to the norm of `f` on any period.
@isnad1 id=eq.2h6v.s7.dddc4901089c from=translated src=- shape=0c330ba4 vocab=b8448206
-/
theorem eLpNorm_liftIco_of_periodic (hfT : Periodic f T) (p : ℝ≥0∞) :
    eLpNorm (AddCircle.liftIco T a f) p = eLpNorm ((Set.Ico a' (a' + T)).indicator f) p := by
  rw [liftIco_eq_liftIco a a' hfT, eLpNorm_liftIco T a' hf p]

/-- The norm of the lift of a periodic function `f` is equal to the norm of `f` on any period.
@isnad1 id=eq.2h6v.s7.6d4e2102510f from=translated src=- shape=c5e28731 vocab=efff4684
-/
theorem eLpNorm_liftIco_of_periodic' (hfT : Periodic f T) (p : ℝ≥0∞) :
    eLpNorm (AddCircle.liftIco T a f) p = eLpNorm f p (volume.restrict (Set.Ico a' (a' + T))) := by
  rw [eLpNorm_liftIco_of_periodic T a a' hf hfT,
    eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ico]

end eLpNorm

end AddCircle
