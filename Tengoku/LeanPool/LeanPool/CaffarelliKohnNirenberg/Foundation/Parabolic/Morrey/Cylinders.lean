/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Basic
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Statements.MorreyVecMem
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.Finiteness
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.PoincareSobolevL1Slice
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.VectorNormAggregation
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Pressure.SliceIntegrability
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.SliceNormBounds
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.ProdSwap

/-!
# Cylinders

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Metric Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

/--
@isnad1 id=iff.0h4v.s5.69c4283016ad from=translated src=- shape=ae63feb2 vocab=23513065
-/
theorem morreyVecMem_iff_ball_lt_top {P τ : ℝ}
    (S : Set ParabolicPoint) (u : ParabolicPoint → Vec3) :
    morreyVecMem P τ S u ↔
      ∀ i : Fin 3,
        morreyBallNorm P τ (S.indicator (fun z => u z i)) < ⊤ := by
  rfl

end CKN.Foundation.Parabolic.Morrey

namespace CKN

/-! The metric-ball-to-cylinder inclusion used to recenter a small Morrey ball. -/

/-! Closure of a positive cylinder is contained in its closed parabolic ball. -/
/--
@isnad1 id=le.1h3v.s5.8244ad157716 from=translated src=- shape=50f86faf vocab=8724d463
-/
theorem step2_closure_cylinder_subset_closedBall
    {x : Vec3} {t r : ℝ} (hr : 0 < r) :
    closure (parabolicCylinder x t r) ⊆
      @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace (x, t) r := by
  rw [closure_parabolicCylinder hr]
  intro z hz
  change dist z ((x, t) : ParabolicPoint) ≤ r
  rw [dist_eq_parabolicDist z ((x, t) : ParabolicPoint)]
  change max (vec3EuclideanNorm (z.1 - x)) (Real.sqrt |z.2 - t|) ≤ r
  have htime : |z.2 - t| ≤ r ^ 2 := by
    rw [abs_le]
    constructor <;> linarith only [hz.2.1, hz.2.2, sq_nonneg r]
  have hsqrt : Real.sqrt |z.2 - t| ≤ r := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, by simpa [sq] using htime⟩
  exact max_le hz.1 hsqrt

/-! Parabolic distance from a point to its forward time-shifted copy. -/
/--
@isnad1 id=eq.1h2v.s5.ccf8a6c071cd from=translated src=- shape=5aeeb3e8 vocab=be76f450
-/
theorem step2_shifted_center_dist {w : ParabolicPoint} {r : ℝ} (hr : 0 < r) :
    @dist ParabolicPoint (@PseudoMetricSpace.toDist ParabolicPoint
      parabolicMetricSpace.toPseudoMetricSpace)
      ((w.1, w.2 + r ^ 2) : ParabolicPoint) w = r := by
  calc
    @dist ParabolicPoint (@PseudoMetricSpace.toDist ParabolicPoint
        parabolicMetricSpace.toPseudoMetricSpace)
        ((w.1, w.2 + r ^ 2) : ParabolicPoint) w =
        parabolicDist ((w.1, w.2 + r ^ 2) : ParabolicPoint) w :=
      dist_eq_parabolicDist _ _
    _ = r := by
      have hzero : vec3EuclideanNorm (0 : Vec3) ≤ r := by
        simp [vec3EuclideanNorm_zero, hr.le]
      simp [parabolicDist, max_eq_right hzero,
        abs_of_nonneg (sq_nonneg r), Real.sqrt_sq (le_of_lt hr)]

end CKN
