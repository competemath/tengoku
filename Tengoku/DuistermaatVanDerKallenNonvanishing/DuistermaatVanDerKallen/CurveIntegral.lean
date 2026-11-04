import Tengoku.Seed.Topology.ContinuousMap.Compact
import Tengoku.Seed.Topology.Order.ProjIcc
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! A bounded primitive operator on continuous curves over the fixed unit
interval. A separate time-scale parameter can multiply this operator in the
Picard equation without varying the underlying Banach space. -/

open Set
open scoped Topology

namespace DuistermaatVanDerKallen

noncomputable section

abbrev CurveTime := Icc (0 : ℝ) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Continuous extension by clamping the time parameter to `[0,1]`.-/
def extendCurve (u : C(CurveTime, E)) : C(ℝ, E) :=
  ⟨IccExtend (by norm_num : (0 : ℝ) ≤ 1) u,
    u.continuous.Icc_extend'⟩

omit [NormedSpace ℝ E] [CompleteSpace E] in
@[simp] theorem extendCurve_apply (u : C(CurveTime, E)) (t : CurveTime) :
    extendCurve u t = u t := by
  simp [extendCurve, IccExtend]

/-- The primitive, anchored at zero, as a continuous curve.-/
def curvePrimitive (u : C(CurveTime, E)) : C(CurveTime, E) :=
  ⟨fun t => ∫ s in (0 : ℝ)..t.val, extendCurve u s,
    ((intervalIntegral.differentiable_integral_of_continuous (extendCurve u).continuous).continuous.comp
      continuous_subtype_val)⟩

theorem curvePrimitive_norm_le (u : C(CurveTime, E)) : ‖curvePrimitive u‖ ≤ ‖u‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg u)).2
  intro t
  change ‖∫ s in (0 : ℝ)..t.val, extendCurve u s‖ ≤ ‖u‖
  calc
    _ ≤ ‖u‖ * |t.val - 0| := intervalIntegral.norm_integral_le_of_norm_le_const
      (fun s _ => u.norm_coe_le_norm (projIcc 0 1 (by norm_num) s))
    _ ≤ ‖u‖ := by
      rw [sub_zero, abs_of_nonneg t.property.1]
      exact mul_le_of_le_one_right (norm_nonneg u) t.property.2

/-- Integration is bounded real-linear on the Banach space of continuous curves.-/
def curvePrimitiveCLM : C(CurveTime, E) →L[ℝ] C(CurveTime, E) :=
  LinearMap.mkContinuous
    { toFun := curvePrimitive
      map_add' := by
        intro u v
        ext t
        change (∫ s in (0 : ℝ)..t.val, extendCurve (u + v) s) = _
        exact intervalIntegral.integral_add
          ((extendCurve u).continuous.intervalIntegrable _ _)
          ((extendCurve v).continuous.intervalIntegrable _ _)
      map_smul' := by
        intro c u
        ext t
        change (∫ s in (0 : ℝ)..t.val, c • extendCurve u s) = _
        exact intervalIntegral.integral_smul c _ }
    1 (fun u => by simpa using curvePrimitive_norm_le u)

@[simp] theorem curvePrimitiveCLM_apply (u : C(CurveTime, E)) (t : CurveTime) :
    curvePrimitiveCLM u t = ∫ s in (0 : ℝ)..t.val, extendCurve u s := rfl

theorem curvePrimitiveCLM_norm_le : ‖curvePrimitiveCLM (E := E)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun u => by
    simpa only [one_mul, curvePrimitiveCLM, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk] using curvePrimitive_norm_le u)

/-- The primitive satisfies the integral form of the ODE with the original
curve as derivative, including at the two endpoints via the extension.-/
theorem curvePrimitive_hasDerivAt (u : C(CurveTime, E)) (t : CurveTime) :
    HasDerivAt (fun r : ℝ => ∫ s in (0 : ℝ)..r, extendCurve u s) (u t) t.val := by
  simpa only [extendCurve_apply] using
    intervalIntegral.integral_hasDerivAt_right
      ((extendCurve u).continuous.intervalIntegrable 0 t.val)
      (extendCurve u).continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      (extendCurve u).continuous.continuousAt

end

end DuistermaatVanDerKallen
