import Tengoku.NavierStokesEuler.Euler.ContinuousTimeIntegral

/-!
# Actual profile normalization of continuous time paths

A positive scalar time profile gives inverse bounded linear scaling maps.
The norm of a normalized path is bounded directly by its profile estimate;
no quotient of the maximum and minimum profile enters that estimate.
-/

noncomputable section

namespace EulerContinuousTimeWeight

open Set ContinuousLinearMap EulerContinuousTimeIntegral

variable {K E : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Multiplication by the literal scalar profile. -/
def weight (g : C(K,ℝ)) : C(K,E) →L[ℝ] C(K,E) :=
  multiplier ⟨fun t => g t • ContinuousLinearMap.id ℝ E,
    g.continuous.smul continuous_const⟩

/--
@isnad1 id=eq.0h5v.s9.b294bcf0307b from=translated src=- shape=6c6e70ec vocab=8ac0d2aa
-/
@[simp] theorem weight_apply (g : C(K,ℝ)) (f : C(K,E)) (t : K) :
    weight g f t = g t • f t := rfl

/-- The reciprocal of a positive continuous profile is an actual continuous path. -/
def reciprocal (g : C(K,ℝ)) (hg : ∀ t, 0 < g t) : C(K,ℝ) :=
  ⟨fun t => (g t)⁻¹, g.continuous.inv₀ (fun t => (hg t).ne')⟩

/-- Profile division as a genuine bounded linear map. -/
def normalize (g : C(K,ℝ)) (hg : ∀ t, 0 < g t) : C(K,E) →L[ℝ] C(K,E) :=
  weight (reciprocal g hg)

/--
@isnad1 id=eq.1h5v.s9.16d733765608 from=translated src=- shape=013f3a81 vocab=9ae4abf4
-/
@[simp] theorem normalize_apply (g : C(K,ℝ)) (hg : ∀ t, 0 < g t) (f : C(K,E)) (t : K) :
    normalize g hg f t = (g t)⁻¹ • f t := rfl

/-- Weighting and normalization are actual inverse operators.
@isnad1 id=eq.1h4v.s9.29d586b31bf5 from=translated src=- shape=9b709f02 vocab=cf295f9d
-/
theorem normalize_weight (g : C(K,ℝ)) (hg : ∀ t, 0 < g t) (f : C(K,E)) :
    normalize g hg (weight g f) = f := by
  ext t
  simp only [normalize_apply, weight_apply, smul_smul, inv_mul_cancel₀ (hg t).ne', one_smul]

/-- Normalization and weighting are inverse in the other order too.
@isnad1 id=eq.1h4v.s9.427fa8242248 from=translated src=- shape=f7e20ddb vocab=cf295f9d
-/
theorem weight_normalize (g : C(K,ℝ)) (hg : ∀ t, 0 < g t) (f : C(K,E)) :
    weight g (normalize g hg f) = f := by
  ext t
  simp only [normalize_apply, weight_apply, smul_smul, mul_inv_cancel₀ (hg t).ne', one_smul]

/-- Literal pointwise control of a weighted path, with no profile extremum.
@isnad1 id=le.1h5v.s9.af3f101c1ddd from=translated src=- shape=12203fce vocab=7f26bb5e
-/
theorem weight_pointwise_bound (g : C(K,ℝ)) (hg : ∀ t, 0 ≤ g t) (f : C(K,E)) (t : K) :
    ‖weight g f t‖ ≤ g t * ‖f‖ := by
  rw [weight_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hg t)]
  exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm t) (hg t)

/-- A pointwise profile bound gives the normalized uniform norm directly.
@isnad1 id=le.3h5v.s9.b9f8fdba7a19 from=translated src=- shape=310f646b vocab=b546979d
-/
theorem normalize_norm_le (g : C(K,ℝ)) (hg : ∀ t, 0 < g t)
    (f : C(K,E)) (D : ℝ) (hD : 0 ≤ D) (hf : ∀ t, ‖f t‖ ≤ D*g t) :
    ‖normalize g hg f‖ ≤ D := by
  apply (ContinuousMap.norm_le _ hD).2
  intro t
  rw [normalize_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hg t))]
  calc
    _ ≤ (g t)⁻¹ * (D*g t) := mul_le_mul_of_nonneg_left (hf t) (inv_nonneg.mpr (hg t).le)
    _ = D := by field_simp [(hg t).ne']

/-- Scalar normalization commutes with every coefficient multiplier.
@isnad1 id=eq.1h5v.s10.8935a4ffbfef from=translated src=- shape=067a02cf vocab=252c83d5
-/
theorem normalize_multiplier (g : C(K,ℝ)) (hg : ∀ t, 0 < g t)
    (A : C(K,E →L[ℝ] E)) (f : C(K,E)) :
    normalize g hg (multiplier A f) = multiplier A (normalize g hg f) := by
  ext t
  simp only [normalize_apply, multiplier_apply, map_smul]

/-- Scalar weighting commutes with every coefficient multiplier.
@isnad1 id=eq.0h5v.s10.32a68b5316a5 from=translated src=- shape=12bc831f vocab=fd6b1975
-/
theorem weight_multiplier (g : C(K,ℝ)) (A : C(K,E →L[ℝ] E)) (f : C(K,E)) :
    weight g (multiplier A f) = multiplier A (weight g f) := by
  ext t
  simp only [weight_apply, multiplier_apply, map_smul]

end EulerContinuousTimeWeight
