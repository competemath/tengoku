/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import Tengoku.LeanPool.LeanPool.Feige.SimplexGeometry
public import Tengoku.LeanPool.LeanPool.Feige.Grunbaum.Sharpness
public import Tengoku

/-!
# Basic interface to the Grünbaum formalization

This file registers the first, purely measure-theoretic part of the bridge
between the coordinate-function model used by `Feige` and Mathlib's
`EuclideanSpace` model used by `Grunbaum`.
-/

@[expose] public section

open Set MeasureTheory

namespace Feige

/-- The canonical passage from coordinate functions to Euclidean space. -/
def simplexToEuclidean (n : ℕ) :
    (Fin n → ℝ) → Grunbaum.SimplexE n :=
  WithLp.toLp 2

/--
@isnad1 id=measurab.0h1v.s5.f5c062078faf from=translated src=- shape=cae58d9e vocab=6d77bd3b
-/
theorem measurable_simplexToEuclidean (n : ℕ) :
    Measurable (simplexToEuclidean n) :=
  by
    simpa [simplexToEuclidean] using
      (PiLp.volume_preserving_toLp (Fin n)).measurable

/--
@isnad1 id=eq.0h3v.s5.3a98aca84ffc from=translated src=- shape=dbd2a47d vocab=f4e41968
-/
@[simp]
theorem simplexToEuclidean_apply
    (n : ℕ) (x : Fin n → ℝ) (i : Fin n) :
    simplexToEuclidean n x i = x i :=
  PiLp.toLp_apply 2 (fun _ : Fin n => ℝ) x i

/-- The two projects use exactly the same standard simplex, modulo the
canonical `PiLp.toLp` wrapper.
@isnad1 id=iff.0h2v.s5.3abccc5eb107 from=translated src=- shape=d2acfb7a vocab=7ccd89a1
-/
theorem simplexToEuclidean_mem_simplexSet_iff
    (n : ℕ) (x : Fin n → ℝ) :
    simplexToEuclidean n x ∈ Grunbaum.simplexSet n ↔
      x ∈ fullSimplex (Fin n) := by
  simp only [Grunbaum.mem_simplexSet, fullSimplex,
    Set.mem_ofPred_eq, Grunbaum.coordinateSum_apply,
    simplexToEuclidean_apply]

/--
@isnad1 id=eq.0h1v.s4.44412dc1aef5 from=translated src=- shape=3f7c3f8b vocab=e8110b85
-/
theorem simplexToEuclidean_preimage_simplexSet (n : ℕ) :
    simplexToEuclidean n ⁻¹' Grunbaum.simplexSet n =
      fullSimplex (Fin n) := by
  ext x
  exact simplexToEuclidean_mem_simplexSet_iff n x

/-- Lebesgue volume of the simplex is unchanged by the canonical
coordinate-function/Euclidean-space identification.
@isnad1 id=eq.0h1v.s8.a9bef2eca6da from=translated src=- shape=4407327c vocab=094e0542
-/
theorem volume_simplexSet_eq_volume_fullSimplex (n : ℕ) :
    volume (Grunbaum.simplexSet n) =
      volume (fullSimplex (Fin n)) := by
  rw [← (PiLp.volume_preserving_toLp (Fin n)).measure_preimage
    (Grunbaum.isClosed_simplexSet n).measurableSet.nullMeasurableSet]
  change volume (simplexToEuclidean n ⁻¹' Grunbaum.simplexSet n) =
    volume (fullSimplex (Fin n))
  rw [simplexToEuclidean_preimage_simplexSet]

/-- Transport of intersections with the standard simplex.  This is the
form needed to compare the two normalized halfspace-volume ratios.
@isnad1 id=eq.1h2v.s8.ba9a3473f97a from=translated src=- shape=acccf198 vocab=6350e8d9
-/
theorem volume_simplexSet_inter_eq_volume_fullSimplex_inter_preimage
    (n : ℕ) {A : Set (Grunbaum.SimplexE n)}
    (hA : MeasurableSet A) :
    volume (Grunbaum.simplexSet n ∩ A) =
      volume (fullSimplex (Fin n) ∩ simplexToEuclidean n ⁻¹' A) := by
  rw [← (PiLp.volume_preserving_toLp (Fin n)).measure_preimage
    ((Grunbaum.isClosed_simplexSet n).measurableSet.inter hA).nullMeasurableSet]
  change
    volume (simplexToEuclidean n ⁻¹'
      (Grunbaum.simplexSet n ∩ A)) =
      volume (fullSimplex (Fin n) ∩ simplexToEuclidean n ⁻¹' A)
  rw [preimage_inter, simplexToEuclidean_preimage_simplexSet]

end Feige
