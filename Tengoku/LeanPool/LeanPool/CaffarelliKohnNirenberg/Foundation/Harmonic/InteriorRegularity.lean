/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorRepresentative
public import Tengoku

/-!
# Interior Regularity

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology Convolution
open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Foundation.Heat

lemma approximation_scale_pos {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) :
    0 < ρ / (12 * ((n : ℝ) + 1)) := by
  positivity

lemma approximation_scale_le {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) :
    ρ / (12 * ((n : ℝ) + 1)) ≤ ρ / 12 := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith only [hn0]
  apply (div_le_div_iff₀ (by positivity : 0 < 12 * ((n : ℝ) + 1))
    (by positivity : 0 < (12 : ℝ))).2
  nlinarith only [hρ, hn]

lemma approximation_scale_tendsto {ρ : ℝ} (_ : 0 < ρ) :
    Tendsto (fun n : ℕ => ρ / (12 * ((n : ℝ) + 1))) atTop (nhds 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (b - 1)]
      with n hn
    linarith only [hn]
  have hden : Tendsto (fun n : ℕ => 12 * ((n : ℝ) + 1)) atTop atTop := by
    simpa [mul_comm] using
      hn.atTop_mul_const (show (0 : ℝ) < 12 by norm_num)
  exact tendsto_const_nhds.div_atTop hden

lemma closedBall_subset_euclideanBall
    {x₀ y : Vec3} {ρ ε : ℝ} (hρ : 0 < ρ) (_ : 0 < ε)
    (hy : y ∈ euclideanBall x₀ (3 * ρ / 4)) (hε_le : ε ≤ ρ / 12) :
    Metric.closedBall y ε ⊆ euclideanBall x₀ ρ := by
  intro z hz
  have hz' : ‖z - y‖ ≤ ε := by
    rw [← dist_eq_norm]
    exact (Metric.mem_closedBall.mp hz)
  have hy' : vec3EuclideanNorm (y - x₀) < 3 * ρ / 4 := by
    simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
      (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hy
  have htri : vec3EuclideanNorm (z - x₀) ≤
      vec3EuclideanNorm (z - y) + vec3EuclideanNorm (y - x₀) := by
    rw [vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2,
      vec3EuclideanNorm_eq_l2]
    calc
      ‖WithLp.toLp 2 (z - x₀)‖ =
          ‖WithLp.toLp 2 ((z - y) + (y - x₀))‖ := by
            congr 1
            ext i
            simp only [Pi.add_apply, Pi.sub_apply]
            ring
      _ ≤ ‖WithLp.toLp 2 (z - y)‖ +
          ‖WithLp.toLp 2 (y - x₀)‖ := norm_add_le _ _
  have hthree := CKN.euclideanNorm_le_three_mul_space_norm (z - y)
  have hthree' : vec3EuclideanNorm (z - y) ≤ 3 * ‖z - y‖ := by
    simpa only [CKN.spaceEuclideanNorm, vec3EuclideanNorm] using hthree
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).2
  have hfinal : vec3EuclideanNorm (z - x₀) < ρ := by
    nlinarith only [htri, hthree', hz', hy', hε_le, hρ]
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using hfinal

end CKN.Foundation.Heat
