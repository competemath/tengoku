/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Ambient.Euclidean
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Ball
public import Tengoku

/-!
# Cutoff

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open Set Filter
open scoped Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

private theorem vec3_norm_eq_native (v : Vec3) :
    vec3EuclideanNorm v = vecEuclideanNorm v := by
  simp [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]

/-- Fixed cutoff equal to one on the inner pressure ball and supported in the outer ball. -/
def fixedCutoff : Vec3 → ℝ :=
  canonicalBallCutoff (0 : Vec3) (13 / 20) (3 / 4)

private theorem vec3_norm_add_le (a b : Vec3) :
    vec3EuclideanNorm (a + b) ≤
      vec3EuclideanNorm a + vec3EuclideanNorm b := by
  rw [vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2,
    vec3EuclideanNorm_eq_l2, WithLp.toLp_add]
  exact norm_add_le _ _

private theorem native_norm_add_le (a b : Vec3) :
    vecEuclideanNorm (a + b) ≤
      vecEuclideanNorm a + vecEuclideanNorm b := by
  rw [← vec3_norm_eq_native, ← vec3_norm_eq_native,
    ← vec3_norm_eq_native]
  exact vec3_norm_add_le _ _

private theorem cutoff_geometry {ρ r : ℝ} (_ : 0 < ρ) (_ : 0 < r)
    (hhalf : r ≤ ρ / 2) (x₀ x y : Vec3)
    (hx : x ∈ vec3Ball x₀ r)
    (hy : y ∈ vec3Ball x₀ (3 * ρ / 4) \ vec3Ball x₀ (13 * ρ / 20)) :
    vec3EuclideanNorm (x - y) ≥ 3 * ρ / 20 := by
  have hxy : vec3EuclideanNorm (x - x₀) < r := mem_vec3Ball.mp hx
  have hyinner : ¬ vec3EuclideanNorm (y - x₀) < 13 * ρ / 20 := by
    simpa only [mem_vec3Ball] using hy.2
  have htri : vec3EuclideanNorm (y - x₀) ≤
      vec3EuclideanNorm (y - x) + vec3EuclideanNorm (x - x₀) := by
    calc
      vec3EuclideanNorm (y - x₀) = vecEuclideanNorm (y - x₀) :=
        vec3_norm_eq_native _
      _ = vecEuclideanNorm ((y - x) + (x - x₀)) := by
        congr 1
        abel
      _ ≤ vecEuclideanNorm (y - x) + vecEuclideanNorm (x - x₀) :=
        native_norm_add_le _ _
      _ = vec3EuclideanNorm (y - x) + vec3EuclideanNorm (x - x₀) := by
        rw [vec3_norm_eq_native, vec3_norm_eq_native]
  have hdist : 3 * ρ / 20 ≤ vec3EuclideanNorm (y - x) := by
    by_contra hn
    have hlt : vec3EuclideanNorm (y - x) < 3 * ρ / 20 := lt_of_not_ge hn
    have hsum := add_lt_add hlt hxy
    have : vec3EuclideanNorm (y - x) + vec3EuclideanNorm (x - x₀) <
        13 * ρ / 20 := by
      calc
        _ < 3 * ρ / 20 + r := hsum
        _ ≤ 3 * ρ / 20 + ρ / 2 := by gcongr
        _ = 13 * ρ / 20 := by ring
    exact hyinner (lt_of_le_of_lt htri this)
  have hdist' : 3 * ρ / 20 ≤ vecEuclideanNorm (y - x) := by
    simpa only [vec3_norm_eq_native] using hdist
  have hrev : vecEuclideanNorm (y - x) = vecEuclideanNorm (x - y) := by
    unfold vecEuclideanNorm vecNormSq vecDot
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Pi.sub_apply]
    ring
  rw [hrev] at hdist'
  simpa only [vec3_norm_eq_native] using hdist'

/--
@isnad1 id=le.5h5v.s7.8735b4ada0ce from=translated src=- shape=ef1533ea vocab=e90a1a2d
-/
theorem cutoff_annulus_separation
    {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (hhalf : r ≤ ρ / 2)
    {x₀ x y : Vec3} (hx : x ∈ vec3Ball x₀ r)
    (hy : y ∈ vec3Ball x₀ (3 * ρ / 4) \ vec3Ball x₀ (13 * ρ / 20)) :
    vec3EuclideanNorm (x - y) ≥ 3 * ρ / 20 :=
  cutoff_geometry hρ hr hhalf x₀ x y hx hy

end CKN
