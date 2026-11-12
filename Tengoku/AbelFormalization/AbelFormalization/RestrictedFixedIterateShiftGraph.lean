import Tengoku.AbelFormalization.AbelFormalization.ImplicitRegularZeroGraphLift
import Tengoku.AbelFormalization.AbelFormalization.RestrictedFixedIterateShift

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Graph equation for a fixed-iterate bounded shift

The shift supplied by `restrictedFixedIterateShift` is represented by the
allowed equation
`E^[d] (v + eta) - E^[d] v - b(w) = 0`.
Its vertical derivative is positive, so adjoining this equation preserves
regular-zero membership.
-/

noncomputable section

open Set Function Filter
open scoped Topology ContDiff

namespace AbelFormalization

set_option autoImplicit false

/-- The implicit graph equation defining one fixed-iterate shift variable.-/
def restrictedFixedIterateShiftGraphEquation {p : ℕ} (d : ℕ)
    (D : RestrictedBox p)
    (b : RestrictedBox.analyticNearClosedBoxSubalgebra D) :
    ((ℝ × RestrictedBoxSpace p) × ℝ) → ℝ :=
  fun q ↦ E^[d] (q.1.1 + q.2) - E^[d] q.1.1 -
    (b : RestrictedBoxSpace p → ℝ) q.1.2

/-- The allowed graph equation is differentiable wherever the bounded
coefficient is analytic.
@isnad1 id=differen.1h7v.s8.b939abb2f547 from=translated src=- shape=ead009e6 vocab=f2af7d98
-/
theorem differentiableAt_restrictedFixedIterateShiftGraphEquation
    {p d : ℕ} (D : RestrictedBox p)
    (b : RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {v eta : ℝ} {w : RestrictedBoxSpace p} (hw : w ∈ D.openBox) :
    DifferentiableAt ℝ (restrictedFixedIterateShiftGraphEquation d D b)
      ((v, w), eta) := by
  have hbNhd : AnalyticOnNhd ℝ
      (b : RestrictedBoxSpace p → ℝ) D.closedBox :=
    D.analyticNearClosedBox_iff.mp b.property
  have hb : DifferentiableAt ℝ
      (b : RestrictedBoxSpace p → ℝ) w :=
    (hbNhd w (D.openBox_subset_closedBox hw)).differentiableAt
  have hE : Differentiable ℝ (E^[d]) := fun x ↦
    (hasDerivAt_E_iterate d x).differentiableAt
  unfold restrictedFixedIterateShiftGraphEquation
  fun_prop

/-- The vertical derivative of the graph equation, evaluated at `1`, is the
positive derivative of the fixed iterate.
@isnad1 id=eq.1h7v.s9.e26a33b88a20 from=translated src=- shape=77840a5d vocab=2c7cfceb
-/
theorem restrictedFixedIterateShiftGraphEquation_vertical_one
    {p d : ℕ} (D : RestrictedBox p)
    (b : RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {v eta : ℝ} {w : RestrictedBoxSpace p} (hw : w ∈ D.openBox) :
    graphLiftZBlock
        (fderiv ℝ (restrictedFixedIterateShiftGraphEquation d D b)
          ((v, w), eta)) 1 =
      deriv (E^[d]) (v + eta) := by
  have hh := differentiableAt_restrictedFixedIterateShiftGraphEquation
    (d := d) D b (v := v) (eta := eta) hw
  have hins : HasDerivAt (fun z : ℝ ↦ ((v, w), z)) ((0, 0), 1) eta :=
    (hasDerivAt_const eta (v, w)).prodMk (hasDerivAt_id eta)
  have hfrom := hh.hasFDerivAt.comp_hasDerivAt eta hins
  change HasDerivAt
    (fun z : ℝ ↦ restrictedFixedIterateShiftGraphEquation d D b
      ((v, w), z))
    (graphLiftZBlock
      (fderiv ℝ (restrictedFixedIterateShiftGraphEquation d D b)
        ((v, w), eta)) 1) eta at hfrom
  have hsum : HasDerivAt (fun z : ℝ ↦ v + z) 1 eta :=
    (hasDerivAt_id eta).const_add v
  have hcurve : HasDerivAt
      (fun z : ℝ ↦ restrictedFixedIterateShiftGraphEquation d D b
        ((v, w), z))
      (deriv (E^[d]) (v + eta)) eta := by
    have hmain :=
      ((hasDerivAt_E_iterate d (v + eta)).differentiableAt.hasDerivAt).comp
        eta hsum
    simpa only [restrictedFixedIterateShiftGraphEquation,
      Function.comp_apply,
      zero_add, mul_one] using
      (hmain.sub_const (E^[d] v)).sub_const
        ((b : RestrictedBoxSpace p → ℝ) w)
  exact hfrom.unique hcurve

/-- The vertical derivative block of the fixed-iterate graph equation is
surjective.
@isnad1 id=surjecti.1h7v.s9.2982e3fe5002 from=translated src=- shape=fa7da0ff vocab=8dad2544
-/
theorem surjective_graphLiftZBlock_restrictedFixedIterateShiftGraphEquation
    {p d : ℕ} (D : RestrictedBox p)
    (b : RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {v eta : ℝ} {w : RestrictedBoxSpace p} (hw : w ∈ D.openBox) :
    Function.Surjective
      (graphLiftZBlock
        (fderiv ℝ (restrictedFixedIterateShiftGraphEquation d D b)
          ((v, w), eta))) := by
  let V : ℝ →L[ℝ] ℝ := graphLiftZBlock
    (fderiv ℝ (restrictedFixedIterateShiftGraphEquation d D b)
      ((v, w), eta))
  let c : ℝ := deriv (E^[d]) (v + eta)
  have hc : 0 < c := by
    dsimp only [c]
    rw [deriv_E_iterate]
    exact Finset.prod_pos fun k _ ↦ Real.exp_pos (E^[k] (v + eta))
  have hVone : V 1 = c := by
    exact restrictedFixedIterateShiftGraphEquation_vertical_one D b hw
  intro y
  refine ⟨y / c, ?_⟩
  calc
    V (y / c) = V ((y / c) • (1 : ℝ)) := by simp
    _ = (y / c) • V 1 := map_smul V _ _
    _ = y := by
      rw [hVone]
      simpa [smul_eq_mul] using div_mul_cancel₀ y hc.ne'

end AbelFormalization
