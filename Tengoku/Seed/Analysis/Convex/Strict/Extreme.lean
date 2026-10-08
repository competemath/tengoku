/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Convex.Extreme
public import Tengoku.Seed.Analysis.Convex.StrictConvexSpace

import Tengoku.Seed.Algebra.CharP.Invertible

/-! # Extreme points of (strictly convex) sets

This file collects some results of extreme points of (strictly convex) sets.

## Main results
* `disjoint_interior_extremePoints`: the interior and extreme points of a set in a
  nontrivial topological vector space are disjoint.
* `StrictConvex.sdiff_interior_subset_extremePoints`:
  when `C` is a strictly convex set then `C \ interior C ⊆ extremePoints 𝕜 C`.
* `StrictConvex.extremePoints_eq_sdiff_interior`: the extreme points of a strictly convex set `S`
  in nontrivial normed space is exactly `S \ interior S`.

Corollaries of the above is that, in a nontrivial normed space, the extreme points of the
closed ball is contained in the sphere (see `extremePoints_closedBall_subset_sphere`).
And in a nontrivial strictly convex space, the extreme points of the closed ball is exactly the
sphere (see `StrictConvexSpace.extremePoints_closedBall_eq_sphere`). -/

public section

open Set Metric

open Filter in
open scoped Topology in
/--
@isnad1 id=disjoint.0h2v.s7.2cf4e0b09905 from=seed src=0 shape=1e089b31 vocab=0169dce5
-/
theorem disjoint_interior_extremePoints {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [Nontrivial E]
    (S : Set E) : Disjoint (interior S) (extremePoints ℝ S) := by
  refine Set.disjoint_iff.mpr fun x ⟨x_int, x_ext⟩ ↦ ?_
  rw [mem_interior_iff_mem_nhds] at x_int
  have h₁ : ∀ᶠ v in 𝓝[≠] 0, x - v ∈ S :=
    (tendsto_inf_left <| (continuous_sub_left _).tendsto' _ _ (sub_zero _)).eventually x_int
  have h₂ : ∀ᶠ v in 𝓝[≠] 0, x + v ∈ S :=
    (tendsto_inf_left <| (continuous_const_add _).tendsto' _ _ (add_zero _)).eventually x_int
  obtain ⟨v, ⟨hv₁, hv₂⟩, (v_ne : v ≠ 0)⟩ := h₁.and h₂ |>.and eventually_mem_nhdsWithin |>.exists
  have key : x ∈ openSegment ℝ (x - v) (x + v) := mem_openSegment_sub_add _ _
  grind only [x_ext.2 hv₁ hv₂ key]

/--
@isnad1 id=le.1h3v.s6.2c5a22ed229c from=seed src=0 shape=db761bc3 vocab=439476a2
-/
lemma StrictConvex.sdiff_interior_subset_extremePoints {𝕜 A : Type*} [Semiring 𝕜]
    [PartialOrder 𝕜] [AddCommMonoid A] [Module 𝕜 A] [TopologicalSpace A] {C : Set A}
    (hc : StrictConvex 𝕜 C) : C \ interior C ⊆ extremePoints 𝕜 C := by
  refine fun x hx ↦ ⟨hx.1, fun y hy z hz ⟨a, b, ha, hb, hab, hxab⟩ ↦ ?_⟩
  have hyz : y = z := by
    by_contra
    exact hx.2 <| hxab ▸ hc hy hz this ha hb hab
  rwa [← hyz, ← add_smul, hab, one_smul] at hxab

/--
@isnad1 id=le.1h3v.s6.2c5a22ed229c from=seed src=0 shape=db761bc3 vocab=439476a2
-/
@[deprecated (since := "2026-06-03")]
alias StrictConvex.diff_interior_subset_extremePoints :=
  StrictConvex.sdiff_interior_subset_extremePoints

section Normed
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

/-- In a nontrivial normed space, the extreme points of the closed ball is contained in
the sphere.
@isnad1 id=le.0h3v.s6.507f94a230dc from=seed src=0 shape=cc99709c vocab=220d6aa4
-/
theorem extremePoints_closedBall_subset_sphere [Nontrivial A] {x : A} {r : ℝ} :
    extremePoints ℝ (closedBall x r) ⊆ sphere x r := by
  rw [← closedBall_sdiff_ball, subset_sdiff, ← interior_closedBall' _]
  exact ⟨extremePoints_subset, disjoint_interior_extremePoints _ |>.symm⟩

/--
@isnad1 id=eq.1h2v.s7.3028c98159bc from=seed src=0 shape=fb3c0b90 vocab=8e4c0f5f
-/
theorem StrictConvex.extremePoints_eq_sdiff_interior [Nontrivial A] {S : Set A}
    (hS : StrictConvex ℝ S) : extremePoints ℝ S = S \ interior S :=
  antisymm (subset_sdiff.mpr ⟨extremePoints_subset, disjoint_interior_extremePoints _ |>.symm⟩)
    hS.sdiff_interior_subset_extremePoints

/--
@isnad1 id=eq.1h2v.s7.3028c98159bc from=seed src=0 shape=fb3c0b90 vocab=8e4c0f5f
-/
@[deprecated (since := "2026-06-03")]
alias StrictConvex.extremePoints_eq_diff_interior := StrictConvex.extremePoints_eq_sdiff_interior

/-- In a strictly convex space, the sphere is contained in the extreme points of the closed ball
when the radius is nonzero.
In a nontrivial space, they are equal, see `extremePoints_closedBall_eq_sphere`.
@isnad1 id=le.1h3v.s7.5ac03a1100db from=seed src=0 shape=b9c434c7 vocab=3459dcb9
-/
lemma StrictConvexSpace.sphere_subset_extremePoints_closedBall [StrictConvexSpace ℝ A]
    (a : A) {r : ℝ} (hr : r ≠ 0) : sphere a r ⊆ extremePoints ℝ (closedBall a r) := fun _ hx ↦ by
  rw [← frontier_closedBall _ hr, frontier, closure_closedBall] at hx
  exact (_root_.strictConvex_closedBall ℝ _ _).sdiff_interior_subset_extremePoints hx

/--
@isnad1 id=eq.0h3v.s6.d2555f44ddcd from=seed src=0 shape=a2201a3c vocab=ae9aa273
-/
theorem StrictConvexSpace.extremePoints_closedBall_eq_sphere [Nontrivial A] {x : A} {r : ℝ}
    [StrictConvexSpace ℝ A] : extremePoints ℝ (closedBall x r) = sphere x r := by
  rw [(_root_.strictConvex_closedBall ℝ x r).extremePoints_eq_sdiff_interior, interior_closedBall',
    closedBall_sdiff_ball]

end Normed

/--
@isnad1 id=eq.1h2v.s5.3b7039f3c379 from=seed src=0 shape=8d96a396 vocab=703456de
-/
@[simp] lemma Set.extremePoints_Icc {a b : ℝ} (hab : a ≤ b) :
    extremePoints ℝ (Icc a b) = {a, b} := by
  rw [Real.Icc_eq_closedBall, StrictConvexSpace.extremePoints_closedBall_eq_sphere]
  grind [Real.sphere_eq_pair]
