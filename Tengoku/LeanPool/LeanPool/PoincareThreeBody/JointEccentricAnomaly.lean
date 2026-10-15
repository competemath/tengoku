/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
module

public import Tengoku.LeanPool.LeanPool.PoincareThreeBody.KeplerOrbit
public import Tengoku

/-!
# Joint analyticity of Kepler's equation

The existing one-variable inverse theorem gives analyticity of the eccentric anomaly in mean
anomaly for fixed eccentricity.  Poincaré's coefficient argument also needs analytic dependence
on eccentricity.  We obtain it by applying the analytic inverse-function theorem to the triangular
map `(e, E) ↦ (e, E - e sin E)`.
-/

@[expose] public section

namespace LeanPool.PoincareThreeBody

open Filter Topology

/-- Kepler's equation while retaining eccentricity as a coordinate. -/
noncomputable def eccentricKeplerMap (parameters : ℝ × ℝ) : ℝ × ℝ :=
  (parameters.1, eccentricMeanAnomaly parameters.1 parameters.2)

/-- The derivative of `eccentricKeplerMap`. -/
noncomputable def eccentricKeplerMapFDeriv (parameters : ℝ × ℝ) :
    ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![1, 0;
      -Real.sin parameters.2, 1 - parameters.1 * Real.cos parameters.2]).toContinuousLinearMap

/--
@isnad1 id=hasfderi.0h1v.s6.95e41db16e26 from=translated src=- shape=99fbcee6 vocab=179d7a58
-/
theorem hasFDerivAt_eccentricKeplerMap (parameters : ℝ × ℝ) :
    HasFDerivAt eccentricKeplerMap (eccentricKeplerMapFDeriv parameters) parameters := by
  have hraw :=
    HasFDerivAt.prodMk (𝕜 := ℝ) hasFDerivAt_fst
      (hasFDerivAt_snd.sub
        (hasFDerivAt_fst.mul
          ((Real.hasDerivAt_sin parameters.2).comp_hasFDerivAt parameters hasFDerivAt_snd)))
  unfold eccentricKeplerMap eccentricMeanAnomaly
  apply hraw.congr_fderiv
  apply ContinuousLinearMap.ext
  intro direction
  unfold eccentricKeplerMapFDeriv
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  simp [smul_smul, Function.comp_apply]
  ring

/--
@isnad1 id=analytic.0h1v.s6.0b4d510a06e8 from=translated src=- shape=1f4b4197 vocab=ccb4e12a
-/
theorem analyticAt_eccentricKeplerMap (parameters : ℝ × ℝ) :
    AnalyticAt ℝ eccentricKeplerMap parameters := by
  unfold eccentricKeplerMap eccentricMeanAnomaly
  exact analyticAt_fst.prod
    (analyticAt_snd.sub (analyticAt_fst.mul (Real.analyticAt_sin.comp analyticAt_snd)))

/--
@isnad1 id=eq.0h2v.s7.e3adb83dfc34 from=translated src=- shape=9a85a2a6 vocab=69ce66a3
-/
theorem eccentricKeplerMapFDeriv_apply (parameters direction : ℝ × ℝ) :
    eccentricKeplerMapFDeriv parameters direction =
      (direction.1,
        -Real.sin parameters.2 * direction.1 +
          (1 - parameters.1 * Real.cos parameters.2) * direction.2) := by
  unfold eccentricKeplerMapFDeriv
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  simp

/--
@isnad1 id=bijectiv.1h1v.s7.29b6dc844d15 from=translated src=- shape=6f46665d vocab=019c9aa2
-/
theorem eccentricKeplerMapFDeriv_bijective
    {parameters : ℝ × ℝ}
    (hdenominator : 1 - parameters.1 * Real.cos parameters.2 ≠ 0) :
    Function.Bijective (eccentricKeplerMapFDeriv parameters) := by
  constructor
  · intro x y hxy
    rw [eccentricKeplerMapFDeriv_apply, eccentricKeplerMapFDeriv_apply] at hxy
    injection hxy with hfirst hsecondRaw
    have hsecond : x.2 = y.2 := by
      rw [hfirst] at hsecondRaw
      apply mul_left_cancel₀ hdenominator
      linarith [hsecondRaw]
    exact Prod.ext hfirst hsecond
  · intro target
    let source : ℝ × ℝ :=
      (target.1,
        (target.2 + Real.sin parameters.2 * target.1) /
          (1 - parameters.1 * Real.cos parameters.2))
    refine ⟨source, ?_⟩
    rw [eccentricKeplerMapFDeriv_apply]
    apply Prod.ext
    · rfl
    · dsimp only [source]
      field_simp
      ring

/-- Eccentricity and eccentric anomaly as a joint function of eccentricity and mean anomaly. -/
noncomputable def jointEccentricAnomaly (parameters : ℝ × ℝ) : ℝ × ℝ :=
  (parameters.1, eccentricAnomaly parameters.1 parameters.2)

/--
@isnad1 id=eq.1h1v.s4.29c8b2984ece from=translated src=- shape=01b89e5b vocab=d1e49d82
-/
theorem eccentricKeplerMap_jointEccentricAnomaly
    {parameters : ℝ × ℝ} (heccentricity : 0 ≤ parameters.1) :
    eccentricKeplerMap (jointEccentricAnomaly parameters) = parameters := by
  apply Prod.ext
  · rfl
  · exact eccentricMeanAnomaly_eccentricAnomaly heccentricity parameters.2

/--
@isnad1 id=eq.2h1v.s5.42512b34a669 from=translated src=- shape=a3ab71ed vocab=9ca2e0d0
-/
theorem jointEccentricAnomaly_eccentricKeplerMap
    {parameters : ℝ × ℝ} (heccentricity : 0 ≤ parameters.1)
    (heccentricityOne : parameters.1 < 1) :
    jointEccentricAnomaly (eccentricKeplerMap parameters) = parameters := by
  apply Prod.ext
  · rfl
  · exact eccentricAnomaly_eccentricMeanAnomaly
      heccentricity heccentricityOne parameters.2

/-- The eccentric anomaly is jointly real analytic in eccentricity and mean anomaly throughout
the elliptic range `0 < e < 1`.
@isnad1 id=analytic.2h1v.s6.870c551694f1 from=translated src=- shape=a38cfb91 vocab=0f6ab6ee
-/
theorem analyticAt_jointEccentricAnomaly
    {parameters : ℝ × ℝ} (heccentricity : 0 < parameters.1)
    (heccentricityOne : parameters.1 < 1) :
    AnalyticAt ℝ jointEccentricAnomaly parameters := by
  let source := jointEccentricAnomaly parameters
  have hsourceFirst : source.1 = parameters.1 := rfl
  have hdenominator : 1 - source.1 * Real.cos source.2 ≠ 0 := by
    rw [hsourceFirst]
    exact (one_sub_eccentricity_mul_cos_pos heccentricity.le heccentricityOne).ne'
  have hderivBijective := eccentricKeplerMapFDeriv_bijective hdenominator
  let derivativeEquiv : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
    ContinuousLinearEquiv.ofBijective (eccentricKeplerMapFDeriv source)
      (LinearMap.ker_eq_bot.mpr hderivBijective.1)
      (LinearMap.range_eq_top.mpr hderivBijective.2)
  have hstrict : HasStrictFDerivAt eccentricKeplerMap
      (derivativeEquiv : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) source := by
    rw [ContinuousLinearEquiv.coe_ofBijective]
    exact (analyticAt_eccentricKeplerMap source).hasStrictFDerivAt.congr_fderiv
      (hasFDerivAt_eccentricKeplerMap source).fderiv
  let localInverse := hstrict.localInverse eccentricKeplerMap derivativeEquiv source
  have hsourceMap : eccentricKeplerMap source = parameters :=
    eccentricKeplerMap_jointEccentricAnomaly heccentricity.le
  have hlocalAnalytic : AnalyticAt ℝ localInverse parameters := by
    rw [← hsourceMap]
    change AnalyticAt ℝ
      (hstrict.localInverse eccentricKeplerMap derivativeEquiv source)
      (eccentricKeplerMap source)
    rw [HasStrictFDerivAt.localInverse_def]
    rcases analyticAt_eccentricKeplerMap source with ⟨series, hseries⟩
    have hcoefficient : series 1 =
        (continuousMultilinearCurryFin1 ℝ (ℝ × ℝ) (ℝ × ℝ)).symm derivativeEquiv := by
      apply (continuousMultilinearCurryFin1 ℝ (ℝ × ℝ) (ℝ × ℝ)).injective
      rw [LinearIsometryEquiv.apply_symm_apply]
      rw [← hseries.fderiv_eq, hstrict.hasFDerivAt.fderiv]
    have hinverseSeries :=
      (hstrict.toOpenPartialHomeomorph eccentricKeplerMap).hasFPowerSeriesAt_symm
        hstrict.mem_toOpenPartialHomeomorph_source hseries hcoefficient
    exact hinverseSeries.analyticAt
  have hleftInverse : ∀ᶠ candidate in 𝓝 source,
      jointEccentricAnomaly (eccentricKeplerMap candidate) = candidate := by
    filter_upwards [isOpen_lt continuous_const continuous_fst |>.mem_nhds heccentricity,
      isOpen_lt continuous_fst continuous_const |>.mem_nhds heccentricityOne] with
      candidate hpositive hless
    exact jointEccentricAnomaly_eccentricKeplerMap hpositive.le hless
  have heventually : jointEccentricAnomaly =ᶠ[𝓝 parameters] localInverse := by
    rw [← hsourceMap]
    exact hstrict.localInverse_unique hleftInverse
  exact hlocalAnalytic.congr heventually.symm

/--
@isnad1 id=analytic.2h2v.s6.c5fb13ad1260 from=translated src=- shape=482f0966 vocab=7f57a08d
-/
theorem analyticAt_eccentricAnomaly_joint
    {eccentricity meanAnomaly : ℝ} (heccentricity : 0 < eccentricity)
    (heccentricityOne : eccentricity < 1) :
    AnalyticAt ℝ (fun parameters : ℝ × ℝ ↦
      eccentricAnomaly parameters.1 parameters.2) (eccentricity, meanAnomaly) := by
  exact analyticAt_snd.comp
    (analyticAt_jointEccentricAnomaly heccentricity heccentricityOne)

end LeanPool.PoincareThreeBody
