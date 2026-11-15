import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicHaar
import Tengoku.Seed.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open IsDedekindDomain NumberField MeasureTheory
open scoped Pointwise

noncomputable section

namespace NumberField.AdelicCentre

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/--
@isnad1 id=eq.0h2v.s9.9e95e383e268 from=translated src=- shape=0f87e643 vocab=b19d6966
-/
theorem center_eq_range_scalar :
    Subgroup.center (GL (Fin 2) (AdeleRing R K))
      = (Matrix.GeneralLinearGroup.scalar (Fin 2) : (AdeleRing R K)ˣ →* _).range :=
  Matrix.GeneralLinearGroup.center_eq_range_scalar

/--
@isnad1 id=injectiv.0h2v.s9.7aabca53ce48 from=translated src=- shape=acf966f2 vocab=3583299e
-/
theorem scalar_injective :
    Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 2) : (AdeleRing R K)ˣ →* _) :=
  fun a b h => by
    have := congrArg (fun g : GL (Fin 2) (AdeleRing R K) => (g : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 0 0) h
    exact Units.ext (by simpa using this)

abbrev AdelicPGL2 : Type _ :=
  GL (Fin 2) (AdeleRing R K) ⧸ Subgroup.center (GL (Fin 2) (AdeleRing R K))

/--
@isnad1 id=lt.1h5v.s10.6a60a7f38854 from=translated src=- shape=5e059543 vocab=9d350f5e
-/
theorem measure_image_mk_pos {m : MeasurableSpace (AdelicPGL2 R K)} (μ : Measure (AdelicPGL2 R K))
    [μ.IsOpenPosMeasure] {D : Set (GL (Fin 2) (AdeleRing R K))}
    (h : ∃ U : Set (GL (Fin 2) (AdeleRing R K)), IsOpen U ∧ U.Nonempty ∧ U ⊆ D) :
    0 < μ ((QuotientGroup.mk : GL (Fin 2) (AdeleRing R K) → AdelicPGL2 R K) '' D) := by
  obtain ⟨U, hU, hne, hsub⟩ := h
  exact ((QuotientGroup.isOpenMap_coe U hU).measure_pos μ (hne.image _)).trans_le
    (measure_mono (Set.image_mono hsub))

/--
@isnad1 id=lt.1h5v.s10.669ce99c1000 from=translated src=- shape=75c590b4 vocab=7ec14dcf
-/
theorem measure_image_mk_lt_top {m : MeasurableSpace (AdelicPGL2 R K)} (μ : Measure (AdelicPGL2 R K))
    [IsFiniteMeasureOnCompacts μ] {C : Set (GL (Fin 2) (AdeleRing R K))} (hC : IsCompact C) :
    μ ((QuotientGroup.mk : GL (Fin 2) (AdeleRing R K) → AdelicPGL2 R K) '' C) < ⊤ :=
  (hC.image QuotientGroup.continuous_mk).measure_lt_top

/--
@isnad1 id=le.1h4v.s11.1d3e8ed75ce5 from=translated src=- shape=5cc162c1 vocab=4a14a5c3
-/
theorem image_mk_subset_of_subset_mul_center {D C : Set (GL (Fin 2) (AdeleRing R K))}
    (h : D ⊆ C * ((Subgroup.center (GL (Fin 2) (AdeleRing R K)) : Set (GL (Fin 2) (AdeleRing R K))))) :
    (QuotientGroup.mk : _ → AdelicPGL2 R K) '' D ⊆ (QuotientGroup.mk : _ → AdelicPGL2 R K) '' C := by
  rintro _ ⟨d, hd, rfl⟩
  obtain ⟨c, hc, z, hz, rfl⟩ := h hd
  refine ⟨c, hc, ?_⟩
  rw [QuotientGroup.eq]
  simpa using hz

@[reducible] def pglBorel : MeasurableSpace (AdelicPGL2 R K) := borel _

/--
@isnad1 id=borelspa.0h2v.s8.edc8b3231c01 from=translated src=- shape=98925e46 vocab=40c86330
-/
theorem borelSpace_pglBorel : @BorelSpace (AdelicPGL2 R K) _ (pglBorel R K) :=
  @BorelSpace.mk _ _ (pglBorel R K) rfl

section NumberFieldCase

variable [Module.Free ℤ R] [Module.Finite ℤ R] [NumberField K]

/--
@isnad1 id=isclosed.0h2v.s9.20cf4d09e460 from=translated src=- shape=a10a9f8c vocab=4568ef77
-/
instance isClosed_center :
    IsClosed ((Subgroup.center (GL (Fin 2) (AdeleRing R K)) : Set (GL (Fin 2) (AdeleRing R K)))) := by
  have : ((Subgroup.center (GL (Fin 2) (AdeleRing R K)) : Set (GL (Fin 2) (AdeleRing R K))))
      = ⋂ g : GL (Fin 2) (AdeleRing R K), {z | g * z = z * g} := by
    ext z
    simp only [SetLike.mem_coe, Subgroup.mem_center_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [this]
  exact isClosed_iInter fun g =>
    isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)

/--
@isnad1 id=t2space.0h2v.s8.045088251044 from=translated src=- shape=98925e46 vocab=6259954b
-/
instance t2Space_adelicPGL2 : T2Space (AdelicPGL2 R K) := inferInstance

/--
@isnad1 id=locallyc.0h2v.s9.e11baf0e2583 from=translated src=- shape=4e6c09ca vocab=28b54990
-/
instance locallyCompactSpace_adelicPGL2 : LocallyCompactSpace (AdelicPGL2 R K) := inferInstance

/--
@isnad1 id=istopolo.0h2v.s9.feaf68d3d8f0 from=translated src=- shape=98925e46 vocab=77ba612d
-/
instance isTopologicalGroup_adelicPGL2 : IsTopologicalGroup (AdelicPGL2 R K) := inferInstance

def adelicPGLHaar : @Measure (AdelicPGL2 R K) (pglBorel R K) := by
  letI := pglBorel R K
  haveI := borelSpace_pglBorel R K
  exact Measure.haar

/--
@isnad1 id=ishaarme.0h2v.s9.28708117fc9a from=translated src=- shape=18ea43be vocab=0737e660
-/
theorem isHaarMeasure_adelicPGLHaar :
    @Measure.IsHaarMeasure (AdelicPGL2 R K) _ _ (pglBorel R K) (adelicPGLHaar R K) := by
  letI := pglBorel R K
  haveI := borelSpace_pglBorel R K
  exact Measure.isHaarMeasure_haarMeasure _

/--
@isnad1 id=lt.1h3v.s10.d280e3efc6e2 from=translated src=- shape=dd3c74a7 vocab=a78b10b8
-/
theorem adelicPGLHaar_image_pos {D : Set (GL (Fin 2) (AdeleRing R K))}
    (h : ∃ U : Set (GL (Fin 2) (AdeleRing R K)), IsOpen U ∧ U.Nonempty ∧ U ⊆ D) :
    0 < adelicPGLHaar R K ((QuotientGroup.mk : _ → AdelicPGL2 R K) '' D) := by
  letI := pglBorel R K
  haveI := borelSpace_pglBorel R K
  haveI := isHaarMeasure_adelicPGLHaar R K
  exact measure_image_mk_pos R K _ h

/--
@isnad1 id=lt.2h4v.s10.410c5a4615b3 from=translated src=- shape=434d35bc vocab=4ef4bd94
-/
theorem adelicPGLHaar_image_lt_top_of_subset {D C : Set (GL (Fin 2) (AdeleRing R K))} (hC : IsCompact C)
    (h : D ⊆ C * ((Subgroup.center (GL (Fin 2) (AdeleRing R K)) : Set (GL (Fin 2) (AdeleRing R K))))) :
    adelicPGLHaar R K ((QuotientGroup.mk : _ → AdelicPGL2 R K) '' D) < ⊤ := by
  letI := pglBorel R K
  haveI := borelSpace_pglBorel R K
  haveI := isHaarMeasure_adelicPGLHaar R K
  exact lt_of_le_of_lt (measure_mono (image_mk_subset_of_subset_mul_center R K h))
    (measure_image_mk_lt_top R K _ hC)

end NumberFieldCase

end NumberField.AdelicCentre

end
