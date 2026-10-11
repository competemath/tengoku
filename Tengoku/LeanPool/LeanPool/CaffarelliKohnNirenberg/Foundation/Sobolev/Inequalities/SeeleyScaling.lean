/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.SeeleyPoincare

/-!
# Seeley Scaling

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal Pointwise

namespace CKN

noncomputable section

/-- Affine map transporting the unit ball to a ball centered at `x₀` with scale `r`. -/
def seeleyAffineMap (x₀ : Vec 3) (r : ℝ) (x : Vec 3) : Vec 3 :=
  x₀ + r • x

private theorem seeleyAffine_fderiv {x₀ : Vec 3} (r : ℝ)
    {f : Vec 3 → ℝ} (x : Vec 3) :
    fderiv ℝ (f ∘ seeleyAffineMap x₀ r) x =
      r • fderiv ℝ f (seeleyAffineMap x₀ r x) := by
  have hcomp :
      (fun x : Vec 3 => f (seeleyAffineMap x₀ r x)) =
        (fun x : Vec 3 => (fun y : Vec 3 => f (x₀ + y)) (r • x)) := by
    funext y
    rfl
  change fderiv ℝ (fun x : Vec 3 => f (seeleyAffineMap x₀ r x)) x = _
  rw [hcomp]
  have hfd :
      fderiv ℝ (fun x : Vec 3 => (fun y : Vec 3 => f (x₀ + y)) (r • x)) x =
        r • fderiv ℝ (fun y : Vec 3 => f (x₀ + y)) (r • x) := by
    simpa using
      (fderiv_comp_smul (𝕜 := ℝ) (f := fun y : Vec 3 => f (x₀ + y))
        (x := x) r)
  rw [hfd, fderiv_comp_add_left]
  simp [seeleyAffineMap]

theorem seeleyAffine_classicalGradient {x₀ : Vec 3} {r : ℝ}
    {f : Vec 3 → ℝ} (_ : ContDiff ℝ 1 f) (x : Vec 3) :
    classicalGradient (f ∘ seeleyAffineMap x₀ r) x =
      r • classicalGradient f (seeleyAffineMap x₀ r x) := by
  apply funext
  intro i
  rw [classicalGradient_apply, seeleyAffine_fderiv]
  rfl

end
end CKN
