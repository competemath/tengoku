import Tengoku.NavierStokesEuler.Euler.CylinderSpatialEmbedding
import Tengoku.NavierStokesEuler.Euler.CylinderAngleAverage
import Tengoku.Seed.Analysis.InnerProductSpace.Adjoint

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! A genuine bounded cylinder-to-spatial mean, defined by the adjoint of constant extension. -/

noncomputable section

namespace EulerCylinderSpatialMean

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerCylinderSpatialEmbedding EulerCylinderAngleAverage

variable (P : ℝ) [Fact (0 < P)]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

omit [CompleteSpace V] in
/--
@isnad1 id=eq.0h4v.s17.494246014d1f from=translated src=- shape=fc098711 vocab=10b0cb2a
-/
theorem embedding_translate (a : LiftTangent) (u : SpatialL2 V) :
    translate P a (embedding P u) = embedding P (EulerLpTranslation.translation a.1 u) := by
  apply Lp.ext
  filter_upwards [translate_ae P a (embedding P u),
    (measurePreserving_translation P (coveringMap P a)).quasiMeasurePreserving.ae (lift_ae P u),
    lift_ae P (EulerLpTranslation.translation a.1 u),
    (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure Space))
      (ν := (volume : Measure (AddCircle P)))).ae (EulerLpTranslation.translation_ae a.1 u)]
      with z ht hu he hs
  change (translate P a (embedding P u)) z = (embedding P (EulerLpTranslation.translation a.1 u)) z
  rw [ht]
  simp only [embedding_apply]
  rw [hu, he, hs]
  rfl

def mean : CylinderL2 P V →L[ℝ] SpatialL2 V := P⁻¹ • (embedding P).adjoint

/--
@isnad1 id=eq.0h3v.s20.374adb77b1c8 from=translated src=- shape=ad1d17c0 vocab=363c87d5
-/
@[simp] theorem mean_apply (u : CylinderL2 P V) :
    mean P u = P⁻¹ • (embedding P).adjoint u := rfl

/--
@isnad1 id=le.0h2v.s15.d5fb24cc6e4b from=translated src=- shape=bb97b638 vocab=2a47004c
-/
theorem mean_norm : ‖mean (V := V) P‖ ≤ P⁻¹*Real.sqrt P := by
  change ‖P⁻¹ • (embedding (V := V) P).adjoint‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Fact.out : 0 < P)),
    LinearIsometryEquiv.norm_map]
  exact mul_le_mul_of_nonneg_left (embedding_norm P) (inv_nonneg.mpr (le_of_lt (Fact.out : 0 < P)))

/--
@isnad1 id=eq.0h3v.s16.66f44073e830 from=translated src=- shape=77a8fcc1 vocab=9c9e5d8b
-/
theorem mean_embedding (u : SpatialL2 V) : mean P (embedding P u) = u := by
  apply ext_inner_right ℝ
  intro v
  rw [mean_apply, real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left, embedding_inner,
    ← mul_assoc, inv_mul_cancel₀ (ne_of_gt (Fact.out : 0 < P)), one_mul]

omit [CompleteSpace V] in
/--
@isnad1 id=eq.0h5v.s14.ef134278ae5a from=translated src=- shape=4b6ec763 vocab=7ed3ec6c
-/
theorem cylinder_translation_inner (a : LiftTangent) (u v : CylinderL2 P V) :
    inner ℝ (translate P a u) v = inner ℝ u (translate P (-a) v) := by
  have h := (translate P a).inner_map_map u (translate P (-a) v)
  rw [translate_add, add_neg_cancel, translate_zero] at h
  exact h

omit [Fact (0 < P)] [CompleteSpace V] in
/--
@isnad1 id=eq.0h4v.s16.51e4f6738c0f from=translated src=- shape=bc4c7bbf vocab=c95893f7
-/
theorem spatial_translation_inner (a : Space) (u v : SpatialL2 V) :
    inner ℝ (EulerLpTranslation.translation a u) v =
      inner ℝ u (EulerLpTranslation.translation (-a) v) := by
  have h := (EulerLpTranslation.translation a).inner_map_map u (EulerLpTranslation.translation (-a) v)
  rw [EulerLpTranslation.translation_add, add_neg_cancel, EulerLpTranslation.translation_zero] at h
  exact h

/-- The bounded mean commutes with actual spatial translations and removes angular translations.
@isnad1 id=eq.0h4v.s17.030c7d933fd3 from=translated src=- shape=8e435170 vocab=bb698b82
-/
theorem mean_translate (a : LiftTangent) (u : CylinderL2 P V) :
    mean P (translate P a u) = EulerLpTranslation.translation a.1 (mean P u) := by
  apply ext_inner_right ℝ
  intro v
  rw [mean_apply, real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left,
    cylinder_translation_inner, embedding_translate, spatial_translation_inner]
  change P⁻¹*inner ℝ u (embedding P (EulerLpTranslation.translation (-a.1) v)) =
    inner ℝ (P⁻¹ • (embedding P).adjoint u) (EulerLpTranslation.translation (-a.1) v)
  rw [real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left]

/-- Averaging over the angular translations does not change the actual spatial mean.
@isnad1 id=eq.0h3v.s17.c6605cf00799 from=translated src=- shape=f32a22c8 vocab=5008630c
-/
theorem mean_average (u : CylinderL2 P V) : mean P (average P u) = mean P u := by
  change mean P (P⁻¹ • (∫ s in (0 : ℝ)..P, angleCurve P u s)) = _
  rw [map_smul, ← (mean (V := V) P).intervalIntegral_comp_comm
    ((angleCurve_continuous P u).intervalIntegrable 0 P)]
  have he : (fun s : ℝ => mean P (angleCurve P u s)) = fun _ : ℝ => mean P u := by
    funext s
    change mean P (translate P (0,s) u) = _
    rw [mean_translate, EulerLpTranslation.translation_zero]
  rw [he, intervalIntegral.integral_const]
  simp only [sub_zero, smul_smul, inv_mul_cancel₀ (ne_of_gt (Fact.out : 0 < P)), one_smul]

end EulerCylinderSpatialMean
