import Tengoku.PshdLean.PshLines.Regularization.AdaptedKernelCoordinates
import Tengoku.PshdLean.PshLines.Regularization.HolomorphicPullback

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Radial kernels in adapted complex coordinates

The explicit inner-product radial profile is normalized against an arbitrary
additive Haar measure on the standard complex model.  Pulling this normalized
kernel back through `adaptedComplexModelEquiv` gives a smooth nonnegative
approximate-identity kernel on any compatible finite-dimensional complex normed
space.  Its support, dilation law, and unitary symmetry are expressed in the
adapted coordinates rather than in the original norm.
-/

noncomputable section

open Set Metric MeasureTheory
open scoped Topology ContDiff

namespace PshLines.Regularization.AdaptedRadialKernel

open FirstPass
open HolomorphicPullback

variable {n : ℕ}

/-- The explicit radial profile normalized against an arbitrary additive Haar
measure on the standard complex model.-/
noncomputable def coordinateRadialKernel
    (ν : Measure (ComplexModel n)) (R : ℝ) (hR : 0 < R) (j : ℕ)
    (x : ComplexModel n) : ℝ :=
  explicitRadialRaw R hR j x /
    ∫ y : ComplexModel n, explicitRadialRaw R hR j y ∂ν

variable (ν : Measure (ComplexModel n)) [ν.IsAddHaarMeasure]

/--
@isnad1 id=integrab.1h4v.s7.94a7d6f9015b from=translated src=- shape=cb99f92c vocab=32268a98
-/
theorem explicitRadialRaw_integrable (R : ℝ) (hR : 0 < R) (j : ℕ) :
    Integrable (explicitRadialRaw (n := n) R hR j) ν :=
  (explicitRadialRaw_contDiff R hR j).continuous.integrable_of_hasCompactSupport
    (explicitRadialRaw_hasCompactSupport R hR j)

/--
@isnad1 id=lt.1h4v.s7.0b1166904824 from=translated src=- shape=aef85f3c vocab=fbce5a7d
-/
theorem explicitRadialRaw_integral_pos (R : ℝ) (hR : 0 < R) (j : ℕ) :
    0 < ∫ x : ComplexModel n, explicitRadialRaw R hR j x ∂ν := by
  refine (integral_pos_iff_support_of_nonneg
    (explicitRadialRaw_nonneg R hR j)
    (explicitRadialRaw_integrable ν R hR j)).mpr ?_
  rw [explicitRadialRaw_support R hR j]
  exact measure_ball_pos ν 0 (by positivity)

omit [ν.IsAddHaarMeasure] in
/--
@isnad1 id=contdiff.1h4v.s7.9cc46df85d5b from=translated src=- shape=f4addbaa vocab=9a11a3c5
-/
theorem coordinateRadialKernel_contDiff (R : ℝ) (hR : 0 < R) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateRadialKernel ν R hR j) :=
  (explicitRadialRaw_contDiff R hR j).div_const _

/--
@isnad1 id=le.1h5v.s7.4c9ffe523815 from=translated src=- shape=681f4540 vocab=49186d85
-/
theorem coordinateRadialKernel_nonneg (R : ℝ) (hR : 0 < R) (j : ℕ)
    (x : ComplexModel n) : 0 ≤ coordinateRadialKernel ν R hR j x :=
  div_nonneg (explicitRadialRaw_nonneg R hR j x)
    (explicitRadialRaw_integral_pos ν R hR j).le

/--
@isnad1 id=eq.1h4v.s7.c5bc85f95b2b from=translated src=- shape=3ddc0b55 vocab=9e4f064b
-/
theorem coordinateRadialKernel_integral_one (R : ℝ) (hR : 0 < R) (j : ℕ) :
    ∫ x : ComplexModel n, coordinateRadialKernel ν R hR j x ∂ν = 1 := by
  simp_rw [coordinateRadialKernel, div_eq_mul_inv,
    mul_comm (explicitRadialRaw R hR j _), ← smul_eq_mul, integral_smul]
  exact inv_mul_cancel₀ (explicitRadialRaw_integral_pos ν R hR j).ne'

/--
@isnad1 id=eq.1h4v.s8.b2e5e29f2be2 from=translated src=- shape=dbdfe4db vocab=966eddfa
-/
theorem coordinateRadialKernel_support (R : ℝ) (hR : 0 < R) (j : ℕ) :
    Function.support (coordinateRadialKernel ν R hR j) =
      ball 0 (R / ((j : ℝ) + 1)) := by
  have hpos := explicitRadialRaw_integral_pos (n := n) ν R hR j
  change Function.support (fun x : ComplexModel n ↦
    explicitRadialRaw R hR j x /
      ∫ y : ComplexModel n, explicitRadialRaw R hR j y ∂ν) = _
  rw [Function.support_div, Function.support_const hpos.ne', inter_univ,
    explicitRadialRaw_support R hR j]

/--
@isnad1 id=eq.1h4v.s8.03b5c32a0b2c from=translated src=- shape=dbdfe4db vocab=20d067a9
-/
theorem coordinateRadialKernel_tsupport (R : ℝ) (hR : 0 < R) (j : ℕ) :
    tsupport (coordinateRadialKernel ν R hR j) =
      closedBall 0 (R / ((j : ℝ) + 1)) := by
  rw [tsupport, coordinateRadialKernel_support ν R hR j,
    closure_ball _ (by positivity : R / ((j : ℝ) + 1) ≠ 0)]

/--
@isnad1 id=hascompa.1h4v.s7.14cd76322d44 from=translated src=- shape=9560edc6 vocab=5e8fb85b
-/
theorem coordinateRadialKernel_hasCompactSupport
    (R : ℝ) (hR : 0 < R) (j : ℕ) :
    HasCompactSupport (coordinateRadialKernel ν R hR j) := by
  rw [HasCompactSupport, coordinateRadialKernel_tsupport ν R hR j]
  exact isCompact_closedBall _ _

/--
@isnad1 id=integrab.1h4v.s7.2a5f4296b0b7 from=translated src=- shape=f21e9bd2 vocab=d7601313
-/
theorem coordinateRadialKernel_integrable (R : ℝ) (hR : 0 < R) (j : ℕ) :
    Integrable (coordinateRadialKernel ν R hR j) ν :=
  (coordinateRadialKernel_contDiff ν R hR j).continuous.integrable_of_hasCompactSupport
    (coordinateRadialKernel_hasCompactSupport ν R hR j)

/--
@isnad1 id=eq.2h5v.s6.0214894e02c5 from=translated src=- shape=b78e8ea9 vocab=b191b25b
-/
theorem explicitRadialRaw_unitary (R : ℝ) (hR : 0 < R) (j : ℕ)
    (a : ℂ) (ha : ‖a‖ = 1) (x : ComplexModel n) :
    explicitRadialRaw R hR j (a • x) = explicitRadialRaw R hR j x := by
  simp [explicitRadialRaw, ContDiffBumpBase.ofInnerProductSpace, norm_smul, ha]

omit [ν.IsAddHaarMeasure] in
/--
@isnad1 id=eq.2h6v.s7.a302c84edefa from=translated src=- shape=e37344a1 vocab=b8a5a6af
-/
theorem coordinateRadialKernel_unitary (R : ℝ) (hR : 0 < R) (j : ℕ)
    (a : ℂ) (ha : ‖a‖ = 1) (x : ComplexModel n) :
    coordinateRadialKernel ν R hR j (a • x) =
      coordinateRadialKernel ν R hR j x := by
  rw [coordinateRadialKernel, coordinateRadialKernel,
    explicitRadialRaw_unitary R hR j a ha x]

/--
@isnad1 id=eq.1h6v.s8.557b9f08a36f from=translated src=- shape=3bbc8ca5 vocab=81e80b4a
-/
theorem coordinateRadialKernel_scale (R : ℝ) (hR : 0 < R) (a b : ℕ)
    (x : ComplexModel n) :
    coordinateRadialKernel ν R hR b x =
      (((b : ℝ) + 1) / ((a : ℝ) + 1)) ^
          Module.finrank ℝ (ComplexModel n) *
        coordinateRadialKernel ν R hR a
          ((((b : ℝ) + 1) / ((a : ℝ) + 1)) • x) := by
  let q : ℝ := ((b : ℝ) + 1) / ((a : ℝ) + 1)
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hqpow : q ^ Module.finrank ℝ (ComplexModel n) ≠ 0 :=
    pow_ne_zero _ hq.ne'
  have hint :
      (∫ y : ComplexModel n, explicitRadialRaw R hR b y ∂ν) =
        (q ^ Module.finrank ℝ (ComplexModel n))⁻¹ *
          ∫ y : ComplexModel n, explicitRadialRaw R hR a y ∂ν := by
    rw [show (fun y : ComplexModel n ↦ explicitRadialRaw R hR b y) =
        fun y ↦ explicitRadialRaw R hR a (q • y) by
      funext y
      exact explicitRadialRaw_scale R hR a b y]
    simpa only [smul_eq_mul] using
      (Measure.integral_comp_smul_of_nonneg ν
        (explicitRadialRaw (n := n) R hR a) q (hR := hq.le))
  rw [coordinateRadialKernel, coordinateRadialKernel,
    explicitRadialRaw_scale R hR a b, hint]
  dsimp [q]
  field_simp [hqpow, (explicitRadialRaw_integral_pos (n := n) ν R hR a).ne']

section Pullback

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The coordinate-normalized radial kernel pulled back to the original
complex normed space.-/
noncomputable def adaptedRadialKernel (μ : Measure E) (R : ℝ) (hR : 0 < R)
    (j : ℕ) (x : E) : ℝ :=
  coordinateRadialKernel (adaptedCoordinateMeasure μ) R hR j
    (adaptedComplexModelEquiv x)

variable (μ : Measure E) [μ.IsAddHaarMeasure]

/--
@isnad1 id=contdiff.1h4v.s8.7159770344b2 from=translated src=- shape=88680d31 vocab=faa3bfbe
-/
theorem adaptedRadialKernel_contDiff (R : ℝ) (hR : 0 < R) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (adaptedRadialKernel μ R hR j) := by
  let _ : (adaptedCoordinateMeasure μ).IsAddHaarMeasure :=
    adaptedCoordinateMeasure_isAddHaarMeasure μ
  exact (coordinateRadialKernel_contDiff (adaptedCoordinateMeasure μ) R hR j).comp
    ((adaptedComplexModelEquiv (E := E)).toContinuousLinearMap.restrictScalars ℝ).contDiff

/--
@isnad1 id=le.1h5v.s8.d85fa858e245 from=translated src=- shape=1e299b73 vocab=0fc335af
-/
theorem adaptedRadialKernel_nonneg (R : ℝ) (hR : 0 < R) (j : ℕ) (x : E) :
    0 ≤ adaptedRadialKernel μ R hR j x := by
  let _ : (adaptedCoordinateMeasure μ).IsAddHaarMeasure :=
    adaptedCoordinateMeasure_isAddHaarMeasure μ
  exact coordinateRadialKernel_nonneg (adaptedCoordinateMeasure μ) R hR j _

/--
@isnad1 id=eq.1h4v.s8.2fcb4146cf06 from=translated src=- shape=258f654b vocab=b65377ad
-/
theorem adaptedRadialKernel_integral_one (R : ℝ) (hR : 0 < R) (j : ℕ) :
    ∫ x : E, adaptedRadialKernel μ R hR j x ∂μ = 1 := by
  let _ : (adaptedCoordinateMeasure μ).IsAddHaarMeasure :=
    adaptedCoordinateMeasure_isAddHaarMeasure μ
  simpa only [adaptedRadialKernel] using
    (integral_comp_adaptedComplexModelEquiv μ
      (coordinateRadialKernel (adaptedCoordinateMeasure μ) R hR j))
      |>.trans (coordinateRadialKernel_integral_one
        (adaptedCoordinateMeasure μ) R hR j)

/--
@isnad1 id=hascompa.1h4v.s8.9ac889f041b3 from=translated src=- shape=33de6e54 vocab=8f7aee15
-/
theorem adaptedRadialKernel_hasCompactSupport
    (R : ℝ) (hR : 0 < R) (j : ℕ) :
    HasCompactSupport (adaptedRadialKernel μ R hR j) := by
  let _ : (adaptedCoordinateMeasure μ).IsAddHaarMeasure :=
    adaptedCoordinateMeasure_isAddHaarMeasure μ
  change HasCompactSupport (fun x : E ↦ coordinateRadialKernel
    (adaptedCoordinateMeasure μ) R hR j (adaptedComplexModelEquiv x))
  exact (coordinateRadialKernel_hasCompactSupport
    (adaptedCoordinateMeasure μ) R hR j).comp_homeomorph
      (adaptedComplexModelEquiv (E := E)).toHomeomorph

/--
@isnad1 id=integrab.1h4v.s8.0193f68cbaad from=translated src=- shape=a28e5f1f vocab=697941ff
-/
theorem adaptedRadialKernel_integrable (R : ℝ) (hR : 0 < R) (j : ℕ) :
    Integrable (adaptedRadialKernel μ R hR j) μ := by
  let _ : (adaptedCoordinateMeasure μ).IsAddHaarMeasure :=
    adaptedCoordinateMeasure_isAddHaarMeasure μ
  change Integrable (fun x : E ↦ coordinateRadialKernel
    (adaptedCoordinateMeasure μ) R hR j (adaptedComplexModelEquiv x)) μ
  exact (adaptedComplexModelEquiv_measurePreserving μ).integrable_comp_of_integrable
    (coordinateRadialKernel_integrable
      (adaptedCoordinateMeasure μ) R hR j)

/-- The pulled-back kernel is supported in the inverse image of its coordinate
closed ball.
@isnad1 id=le.1h4v.s10.344b9a03e269 from=translated src=- shape=6644e870 vocab=adad96e3
-/
theorem adaptedRadialKernel_tsupport_subset (R : ℝ) (hR : 0 < R) (j : ℕ) :
    tsupport (adaptedRadialKernel μ R hR j) ⊆
      adaptedComplexModelEquiv ⁻¹'
        closedBall 0 (R / ((j : ℝ) + 1)) := by
  let _ : (adaptedCoordinateMeasure μ).IsAddHaarMeasure :=
    adaptedCoordinateMeasure_isAddHaarMeasure μ
  apply closure_minimal
  · intro x hx
    have hx' : adaptedComplexModelEquiv x ∈
        Function.support
          (coordinateRadialKernel (adaptedCoordinateMeasure μ) R hR j) := hx
    rw [coordinateRadialKernel_support (adaptedCoordinateMeasure μ) R hR j] at hx'
    change adaptedComplexModelEquiv x ∈
      closedBall 0 (R / ((j : ℝ) + 1))
    rw [← closure_ball _ (by positivity : R / ((j : ℝ) + 1) ≠ 0)]
    exact subset_closure hx'
  · exact isClosed_closedBall.preimage adaptedComplexModelEquiv.continuous

/-- Norm form of `adaptedRadialKernel_tsupport_subset`.
@isnad1 id=le.1h4v.s10.36acbd1c07ee from=translated src=- shape=04791089 vocab=420c5dbc
-/
theorem adaptedRadialKernel_tsupport_subset_norm (R : ℝ) (hR : 0 < R) (j : ℕ) :
    tsupport (adaptedRadialKernel μ R hR j) ⊆
      {x | ‖adaptedComplexModelEquiv x‖ ≤ R / ((j : ℝ) + 1)} := by
  intro x hx
  exact mem_closedBall_zero_iff.mp
    (adaptedRadialKernel_tsupport_subset μ R hR j hx)

/--
@isnad1 id=eq.2h6v.s11.77d1b294243c from=translated src=- shape=aab6f4a9 vocab=927ffe61
-/
theorem adaptedRadialKernel_unitary (R : ℝ) (hR : 0 < R) (j : ℕ)
    (a : ℂ) (ha : ‖a‖ = 1) (x : E) :
    adaptedRadialKernel μ R hR j
        (adaptedComplexModelEquiv.symm (a • adaptedComplexModelEquiv x)) =
      adaptedRadialKernel μ R hR j x := by
  let _ : (adaptedCoordinateMeasure μ).IsAddHaarMeasure :=
    adaptedCoordinateMeasure_isAddHaarMeasure μ
  simp only [adaptedRadialKernel, ContinuousLinearEquiv.apply_symm_apply]
  exact coordinateRadialKernel_unitary
    (adaptedCoordinateMeasure μ) R hR j a ha _

/--
@isnad1 id=eq.1h6v.s11.fb5dfe86bf1d from=translated src=- shape=7a2c6202 vocab=f22a57f4
-/
theorem adaptedRadialKernel_scale (R : ℝ) (hR : 0 < R) (a b : ℕ) (x : E) :
    adaptedRadialKernel μ R hR b x =
      (((b : ℝ) + 1) / ((a : ℝ) + 1)) ^
          Module.finrank ℝ
            (ComplexModel (Module.finrank ℂ E)) *
        adaptedRadialKernel μ R hR a
          (adaptedComplexModelEquiv.symm
            (((((b : ℝ) + 1) / ((a : ℝ) + 1)) : ℝ) •
              adaptedComplexModelEquiv x)) := by
  let _ : (adaptedCoordinateMeasure μ).IsAddHaarMeasure :=
    adaptedCoordinateMeasure_isAddHaarMeasure μ
  simp only [adaptedRadialKernel, ContinuousLinearEquiv.apply_symm_apply]
  exact coordinateRadialKernel_scale
    (adaptedCoordinateMeasure μ) R hR a b _

end Pullback

end PshLines.Regularization.AdaptedRadialKernel
