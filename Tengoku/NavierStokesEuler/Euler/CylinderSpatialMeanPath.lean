import Tengoku.NavierStokesEuler.Euler.CylinderSpatialMean
import Tengoku.NavierStokesEuler.Euler.ParameterSobolevProductGevrey

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Continuous-time and same-radius word estimates for the actual spatial mean. -/

noncomputable section

namespace EulerCylinderSpatialMean

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerCylinderSpatialEmbedding EulerParameterWordGevrey EulerGevrey
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)]
  {V K : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [TopologicalSpace K] [CompactSpace K]

private local instance : NormedAddCommGroup C(K,CylinderL2 P V) := inferInstance
private local instance : NormedSpace ℝ C(K,CylinderL2 P V) := inferInstance
private local instance : NormedAddCommGroup C(K,SpatialL2 V) := inferInstance
private local instance : NormedSpace ℝ C(K,SpatialL2 V) := inferInstance
private local instance : NormedAddCommGroup (C(K,CylinderL2 P V) →L[ℝ] C(K,SpatialL2 V)) := inferInstance
private local instance : NormedSpace ℝ (C(K,CylinderL2 P V) →L[ℝ] C(K,SpatialL2 V)) := inferInstance

def pathMean : C(K,CylinderL2 P V) →L[ℝ] C(K,SpatialL2 V) :=
  (mean P).compLeftContinuous ℝ K

omit [CompactSpace K] in
/--
@isnad1 id=eq.0h5v.s18.53672c125729 from=translated src=- shape=d27c5f1e vocab=9e9abec4
-/
@[simp] theorem pathMean_apply (p : C(K,CylinderL2 P V)) (t : K) :
    pathMean P p t = mean P (p t) := rfl

def spatialPathTranslation (a : Space) : C(K,SpatialL2 V) →L[ℝ] C(K,SpatialL2 V) :=
  (EulerLpTranslation.translation a).toContinuousLinearMap.compLeftContinuous ℝ K

omit [CompactSpace K] in
/--
@isnad1 id=eq.0h5v.s19.c71afe4a3964 from=translated src=- shape=79aba970 vocab=e4d6a3fa
-/
theorem pathMean_translation (p : C(K,CylinderL2 P V)) (a : LiftTangent) :
    pathMean P (pathTranslate P a p) = spatialPathTranslation a.1 (pathMean P p) := by
  apply ContinuousMap.ext
  intro t
  exact mean_translate P a (p t)

/--
@isnad1 id=le.0h3v.s16.1e4fb589f9a0 from=translated src=- shape=18ee178c vocab=139d14a3
-/
theorem pathMean_norm : ‖pathMean (K := K) (V := V) P‖ ≤ P⁻¹*Real.sqrt P := by
  have hc : 0 ≤ P⁻¹*Real.sqrt P :=
    mul_nonneg (inv_nonneg.mpr (le_of_lt (Fact.out : 0 < P))) (Real.sqrt_nonneg P)
  apply opNorm_le_bound _ hc
  intro p
  apply (ContinuousMap.norm_le _ (mul_nonneg hc (norm_nonneg p))).mpr
  intro t
  exact ((mean (V := V) P).le_of_opNorm_le (mean_norm P) (p t)).trans
    (mul_le_mul_of_nonneg_left (p.norm_coe_le_norm t) hc)

/-- All ordinary spatial derivatives of the mean are inherited from the actual mixed orbit.
@isnad1 id=contdiff.1h4v.s19.f968ee569f82 from=translated src=- shape=a9df9131 vocab=cdf61e4c
-/
theorem pathMean_orbit_contDiff (p : C(K,CylinderL2 P V))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p)) :
    ContDiff ℝ ∞ (fun a : Space => spatialPathTranslation a (pathMean P p)) := by
  have h := (pathMean (K := K) (V := V) P).contDiff.comp
    (hp.comp (contDiff_id.prodMk (contDiff_const : ContDiff ℝ ∞ (fun _ : Space => (0 : ℝ)))))
  simpa only [Function.comp_def, pathMean_translation, id_eq] using h

variable {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype ι]

/--
@isnad1 id=le.1h10v.s17.495b9bd9172a from=translated src=- shape=f7efbde0 vocab=7ad42b35
-/
theorem pathMean_block_bound (directions : ι → X) (q : ℕ)
    (f : X → C(K,CylinderL2 P V)) (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : X) :
    block directions q (fun y => pathMean P (f y)) n x ≤
      (P⁻¹*Real.sqrt P)*block directions q f n x := by
  have h := block_comp_clm_le (E := C(K,CylinderL2 P V)) (F := C(K,SpatialL2 V))
    directions q (pathMean (K := K) (V := V) P) f hf n x
  exact h.trans (mul_le_mul_of_nonneg_right (pathMean_norm P) (block_nonneg directions q f n x))

/--
@isnad1 id=le.2h13v.s17.3200f85c6977 from=translated src=- shape=fccbc9e9 vocab=3ca7cb2d
-/
theorem pathMean_block_majorant (directions : ι → X) (q : ℕ)
    (f : X → C(K,CylinderL2 P V)) (hf : ContDiff ℝ ∞ f) (R C : ℝ) (d : ℕ)
    (hb : ∀ n x, block directions q f n x ≤ C*majorant R d n) (n : ℕ) (x : X) :
    block directions q (fun y => pathMean P (f y)) n x ≤
      ((P⁻¹*Real.sqrt P)*C)*majorant R d n :=
  (pathMean_block_bound P directions q f hf n x).trans
    ((mul_le_mul_of_nonneg_left (hb n x)
      (mul_nonneg (inv_nonneg.mpr (le_of_lt (Fact.out : 0 < P))) (Real.sqrt_nonneg P))).trans_eq
      (mul_assoc (P⁻¹*Real.sqrt P) C _).symm)

end EulerCylinderSpatialMean
