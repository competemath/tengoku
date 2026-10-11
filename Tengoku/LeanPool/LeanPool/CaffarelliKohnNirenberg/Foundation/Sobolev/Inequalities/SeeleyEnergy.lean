/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.SeeleyBounds
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.SeeleySplit

/-!
# Change-of-variables energy bounds for the two-reflection extension

The closed-annulus Jacobian lower bounds turn the exact change-of-variables
identities into explicit pullback estimates.  The statements are written for
nonnegative extended-valued integrands, so no auxiliary measurability
assumptions are needed at this stage.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace CKN

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The part of the closed annulus lying in the outer unit-ball shell. -/
def seeleyOuterAnnulus : Set (Vec 3) :=
  {x | 1 < vecEuclideanNorm x ∧ vecEuclideanNorm x < 2}

theorem seeleyOuterAnnulus_subset_closedAnnulus :
    seeleyOuterAnnulus ⊆ seeleyClosedAnnulus := by
  intro x hx
  exact ⟨hx.1.le, hx.2.le⟩

theorem seeleyOuterAnnulus_measurableSet :
    MeasurableSet seeleyOuterAnnulus := by
  rw [seeleyOuterAnnulus]
  have hnorm : Continuous (vecEuclideanNorm (d := 3)) := by
    change Continuous (fun x : Vec 3 => Real.sqrt (vecNormSq x))
    exact (contDiff_vecNormSq (d := 3)).continuous.sqrt
  exact (isOpen_lt continuous_const hnorm).inter
    (isOpen_lt hnorm continuous_const) |>.measurableSet

theorem seeleyExtension_value_eq_reflection_combo
    (v : Vec 3 → ℝ) {x : Vec 3} (hx : x ∈ seeleyOuterAnnulus) :
    seeleyExtension v x =
      3 * v (seeleyReflectionOne x) - 2 * v (seeleyReflectionTwo x) := by
  have houtside : x ∉ euclideanClosedBall (0 : Vec 3) 1 := by
    intro hxC
    have hnorm := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
      (by norm_num)).mp hxC
    have hnorm' : vecEuclideanNorm x ≤ 1 := by
      simpa only [sub_zero] using hnorm
    linarith only [hx.1, hnorm']
  simp [seeleyExtension, seeleyExterior, houtside]

end
end CKN
