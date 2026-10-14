/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CompactBall
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Endgame.Localization
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays

/-!
# A first-round localization cutoff at arbitrary centre

Paper label `eq:local-equation` localizes the equation to a parabolic ball of
arbitrary centre and radius.  This file supplies the geometry and the smooth
cutoff that the first bootstrap round uses.  The open parabolic box
`B_r(x) × (t - r², t + r²)` is exactly the parabolic metric ball of `eq:parabolic-ball`
read through `spaceTimeSet`, the same set is its own preimage along the product
identification, and a ball sitting compactly inside the space-time domain
admits a smooth cutoff equal to one on the inner quarter-ball, supported inside
the three-eighths-ball, and contained in the product box of half radius.
-/

@[expose] public section

open Set Metric
open scoped Topology
open CKN.Foundation.Parabolic
open CKN.Core.Endgame

noncomputable section

namespace CKN.Core.Step4

/-- Equation `eq:local-equation`, in box form: `spaceTimeSet` applied to the spatial
ball `vec3Ball z₀.1 r` and the time interval `(z₀.2 - r², z₀.2 + r²)` is the parabolic
metric ball `Metric.ball z₀ r` of `eq:parabolic-ball`.
@isnad1 id=eq.0h2v.s6.d1ca14113bef from=translated src=- shape=5e741123 vocab=f4e0357c
-/
theorem parabolic_box_eq_ball (z₀ : ParabolicPoint) (r : ℝ) :
    spaceTimeSet (vec3Ball z₀.1 r) (Set.Ioo (z₀.2 - r ^ 2) (z₀.2 + r ^ 2)) =
      Metric.ball z₀ r :=
  (metricBall_eq_parabolicBall z₀ r).symm

/-- Equation `eq:local-equation`, preimage form: the product box of spatial ball and
open time interval is contained in the preimage of the parabolic metric ball under the
product identification `parabolicHomeomorph.symm`.
@isnad1 id=le.0h2v.s8.7bf57a7b6ea3 from=translated src=- shape=f919fd1b vocab=3cae1371
-/
theorem parabolic_box_subset_ball_preimage (z₀ : ParabolicPoint) (r : ℝ) :
    vec3Ball z₀.1 r ×ˢ Set.Ioo (z₀.2 - r ^ 2) (z₀.2 + r ^ 2) ⊆
      parabolicHomeomorph.symm ⁻¹' Metric.ball z₀ r := by
  rintro ⟨y, s⟩ hz
  rw [metricBall_eq_parabolicBall]
  exact hz

end CKN.Core.Step4
