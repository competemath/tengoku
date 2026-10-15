/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import Tengoku.LeanPool.LeanPool.Feige.Constants
public import Tengoku.LeanPool.LeanPool.Feige.GrunbaumImport
import Tengoku.LeanPool.LeanPool.Feige.Grunbaum.SimplexCentroidCoordinates
public import Tengoku

/-!
# Weighted halfspaces on the Euclidean standard simplex

This file aligns the weighted linear form used in Feige's simplex argument
with the positive-dimensional Euclidean model used by the Grünbaum
formalization.
-/

@[expose] public section

open scoped BigOperators
open Set

namespace Feige

noncomputable section

/-- The weighted coordinate functional on Mathlib's Euclidean-space model. -/
def euclideanSimplexLinearForm {n : ℕ} (y : Fin n → ℝ) :
    Grunbaum.SimplexE n →L[ℝ] ℝ :=
  ∑ i, y i • (EuclideanSpace.proj i :
    Grunbaum.SimplexE n →L[ℝ] ℝ)

/--
@isnad1 id=eq.0h3v.s8.fafec73b3195 from=translated src=- shape=2a95a0c8 vocab=ceb638d0
-/
@[simp]
theorem euclideanSimplexLinearForm_apply {n : ℕ}
    (y : Fin n → ℝ) (x : Grunbaum.SimplexE n) :
    euclideanSimplexLinearForm y x = ∑ i, y i * x i := by
  simp [euclideanSimplexLinearForm]

/--
@isnad1 id=eq.0h3v.s8.b07020cb535b from=translated src=- shape=a31865c1 vocab=237f99f9
-/
theorem euclideanSimplexLinearForm_comp_simplexToEuclidean
    {n : ℕ} (y x : Fin n → ℝ) :
    euclideanSimplexLinearForm y (simplexToEuclidean n x) =
      simplexLinearForm y x := by
  simp [simplexLinearForm]

/--
@isnad1 id=ne.1h2v.s9.1511ac245c7a from=translated src=- shape=b53435b9 vocab=f72c8487
-/
theorem euclideanSimplexLinearForm_ne_zero_of_sum_pos
    {n : ℕ} {y : Fin n → ℝ} (hy : 0 < ∑ i, y i) :
    euclideanSimplexLinearForm y ≠ 0 := by
  intro hzero
  have hcoord : ∀ i, y i = 0 := by
    intro i
    have happ := congrArg
      (fun L : Grunbaum.SimplexE n →L[ℝ] ℝ ↦
        L (EuclideanSpace.single i 1)) hzero
    simpa [euclideanSimplexLinearForm, PiLp.single_apply] using happ
  have : (∑ i, y i) = 0 := by simp [hcoord]
  linarith

/-- The weighted form evaluated at the standard-simplex volume centroid.
@isnad1 id=eq.0h2v.s8.06692377c613 from=translated src=- shape=540bd38c vocab=4a21717f
-/
theorem euclideanSimplexLinearForm_centroid
    {n : ℕ} (y : Fin n → ℝ) :
    euclideanSimplexLinearForm y (Grunbaum.simplexCentroid n) =
      (∑ i, y i) / ((n : ℝ) + 1) := by
  rw [euclideanSimplexLinearForm_apply]
  simp_rw [Grunbaum.simplexCentroid_apply n]
  rw [div_eq_mul_inv, Finset.sum_mul]

/-- In dimension `d + 1`, the `δ = 1` large-sum hypothesis in §2.2 puts
the simplex centroid in the upper halfspace `1 ≤ L_y`.
@isnad1 id=le.1h2v.s9.4ab1360fd799 from=translated src=- shape=354225f4 vocab=6fb41455
-/
theorem one_le_euclideanSimplexLinearForm_centroid
    {d : ℕ} (y : Fin (d + 1) → ℝ)
    (hsum : ((d + 1 : ℕ) : ℝ) + 1 ≤ ∑ i, y i) :
    1 ≤ euclideanSimplexLinearForm y
      (Grunbaum.simplexFullBody d).centroid := by
  rw [Grunbaum.simplexFullBody_centroid,
    euclideanSimplexLinearForm_centroid]
  exact (le_div_iff₀ (by positivity :
    0 < (((d + 1 : ℕ) : ℝ) + 1))).2 (by simpa using hsum)

/--
@isnad1 id=eq.0h1v.s4.e20a30642eb1 from=translated src=- shape=b1bba7fd vocab=6b69f074
-/
theorem grunbaumConstant_eq_sharpConstant (d : ℕ) :
    Grunbaum.grunbaumConstant d = sharpConstant (d + 1) := by
  simp only [Grunbaum.grunbaumConstant, sharpConstant, Nat.cast_add,
    Nat.cast_one]
  congr 1
  ring

end

end Feige
