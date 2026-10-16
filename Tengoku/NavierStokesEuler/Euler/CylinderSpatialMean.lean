import Tengoku.NavierStokesEuler.Euler.CylinderSpatialEmbedding
import Tengoku.NavierStokesEuler.Euler.CylinderAngleAverage
import Tengoku

/-! A genuine bounded cylinder-to-spatial mean, defined by the adjoint of constant extension. -/

noncomputable section

namespace EulerCylinderSpatialMean

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerCylinderSpatialEmbedding EulerCylinderAngleAverage

variable (P : ℝ) [Fact (0 < P)]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

omit [CompleteSpace V] in
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

@[simp] theorem mean_apply (u : CylinderL2 P V) :
    mean P u = P⁻¹ • (embedding P).adjoint u := rfl

theorem mean_norm : ‖mean (V := V) P‖ ≤ P⁻¹*Real.sqrt P := by
  change ‖P⁻¹ • (embedding (V := V) P).adjoint‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Fact.out : 0 < P)),
    LinearIsometryEquiv.norm_map]
  exact mul_le_mul_of_nonneg_left (embedding_norm P) (inv_nonneg.mpr (le_of_lt (Fact.out : 0 < P)))

theorem mean_embedding (u : SpatialL2 V) : mean P (embedding P u) = u := by
  apply ext_inner_right ℝ
  intro v
  rw [mean_apply, real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left, embedding_inner,
    ← mul_assoc, inv_mul_cancel₀ (ne_of_gt (Fact.out : 0 < P)), one_mul]

omit [Fact (0 < P)] [CompleteSpace V] in
theorem spatial_translation_inner (a : Space) (u v : SpatialL2 V) :
    inner ℝ (EulerLpTranslation.translation a u) v =
      inner ℝ u (EulerLpTranslation.translation (-a) v) := by
  have h := (EulerLpTranslation.translation a).inner_map_map u (EulerLpTranslation.translation (-a) v)
  rw [EulerLpTranslation.translation_add, add_neg_cancel, EulerLpTranslation.translation_zero] at h
  exact h

end EulerCylinderSpatialMean
