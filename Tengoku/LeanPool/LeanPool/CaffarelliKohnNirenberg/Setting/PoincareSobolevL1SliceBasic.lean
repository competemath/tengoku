/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.PoincareSobolevL1Vec
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Tengoku
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpApproximation
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Transport
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.LpConvergence

/-!
# Poincare Sobolev L1 Slice Basic

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open Set MeasureTheory Filter Topology
open scoped BigOperators ENNReal Convolution Pointwise
open CKN.Foundation.Parabolic

namespace CKN

noncomputable section

/--
@isnad1 id=tendsto.4h4v.s8.29f331c8f492 from=translated src=- shape=3b7eee8d vocab=1ba82a47
-/
theorem lpNorm_tendsto_of_diff
    {μ : Measure Vec3} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f : Vec3 → ℝ} {g : ℕ → Vec3 → ℝ}
    (hf : MemLp f p μ) (hg : ∀ n, MemLp (g n) p μ)
    (hsub : Tendsto (fun n => lpNorm (fun x => g n x - f x) p μ)
      atTop (nhds 0)) :
    Tendsto (fun n => lpNorm (g n) p μ) atTop (nhds (lpNorm f p μ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsub
    (Eventually.of_forall (fun _ => norm_nonneg _))
  filter_upwards [] with n
  have h₁ := lpNorm_le_lpNorm_add_lpNorm_sub
    (f := f) (g := g n) (hg n) hp
  have h₂ := lpNorm_le_lpNorm_add_lpNorm_sub
    (f := g n) (g := f) hf hp
  have hcomm := lpNorm_sub_comm (g n) f p μ
  rw [← hcomm] at h₂
  have h₁' : lpNorm f p μ ≤ lpNorm (g n) p μ +
      lpNorm (fun x => g n x - f x) p μ := by
    change lpNorm f p μ ≤ lpNorm (g n) p μ +
      lpNorm (fun x => g n x - f x) p μ at h₁
    exact h₁
  have h₂' : lpNorm (g n) p μ ≤ lpNorm f p μ +
      lpNorm (fun x => g n x - f x) p μ := by
    change lpNorm (g n) p μ ≤ lpNorm f p μ +
      lpNorm (fun x => g n x - f x) p μ at h₂
    exact h₂
  exact (abs_le).2 ⟨
    (neg_le_sub_iff_le_add).2 (by simpa [add_comm] using h₁'),
    (sub_le_iff_le_add).2 (by simpa [add_comm] using h₂')⟩

/--
@isnad1 id=continuo.0h0v.s5.116624bf4c87 from=translated src=- shape=54c8eceb vocab=584236dd
-/
theorem continuous_vec3EuclideanNorm :
    Continuous (vec3EuclideanNorm : Vec3 → ℝ) := by
  change Continuous (fun z : Vec3 => Real.sqrt (∑ i : Fin 3, (z i) ^ 2))
  apply Continuous.sqrt
  apply continuous_finsetSum
  intro i hi
  exact ((continuous_apply i).pow 2)

/--
@isnad1 id=eq.1h2v.s4.ce3bb5ead899 from=translated src=- shape=715d6c2f vocab=5e284c63
-/
theorem vec3Ball_eq_euclideanBall' {x₀ : Vec3} {r : ℝ} (hr : 0 < r) :
    vec3Ball x₀ r = euclideanBall x₀ r := by
  ext x
  change vec3EuclideanNorm (x - x₀) < r ↔ x ∈ euclideanBall x₀ r
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
    using (mem_euclideanBall_iff_vecEuclideanNorm_lt (d := 3) hr).symm

private theorem native_vec3_norm_eq (x : Vec3) :
    vec3EuclideanNorm x = vecEuclideanNorm x := by
  simp [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]

/--
@isnad1 id=le.0h2v.s5.43043b2c1139 from=translated src=- shape=0438c7a3 vocab=4ea4a37e
-/
theorem native_euclidean_norm_add_le (x y : Vec3) :
    vec3EuclideanNorm (x + y) ≤ vec3EuclideanNorm x + vec3EuclideanNorm y := by
  rw [vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2,
    vec3EuclideanNorm_eq_l2, WithLp.toLp_add]
  exact norm_add_le _ _

/--
@isnad1 id=le.0h1v.s5.db4d40e3fe2a from=translated src=- shape=fcad3e9f vocab=a3ca6814
-/
theorem native_norm_le_euclidean_norm (x : Vec3) :
    ‖x‖ ≤ vec3EuclideanNorm x := by
  rw [Pi.norm_def]
  have hnn : Finset.univ.sup (fun i => ‖x i‖₊) ≤
      ⟨vec3EuclideanNorm x, vec3EuclideanNorm_nonneg x⟩ := by
    apply Finset.sup_le
    intro i hi
    have hi' : |x i| ≤ vec3EuclideanNorm x := by
      simpa [native_vec3_norm_eq] using abs_apply_le_vecEuclideanNorm x i
    exact_mod_cast hi'
  exact_mod_cast hnn

/--
@isnad1 id=le.0h1v.s5.aa6e4f1164e8 from=translated src=- shape=73f798ee vocab=695dce09
-/
theorem native_euclidean_norm_le_sqrt_three_norm (x : Vec3) :
    vec3EuclideanNorm x ≤ Real.sqrt 3 * ‖x‖ := by
  have hsq : vec3EuclideanNorm x ^ 2 ≤ (Real.sqrt 3 * ‖x‖) ^ 2 := by
    rw [vec3EuclideanNorm, Real.sq_sqrt
      (Finset.sum_nonneg (fun i _ => sq_nonneg (x i))),
      mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    calc
      (∑ i : Fin 3, x i ^ 2) = vecNormSq x := by
        rw [vecNormSq_eq_sum_sq]
      _ ≤ ∑ _i : Fin 3, ‖x‖ ^ 2 := by
        rw [vecNormSq_eq_sum_sq]
        apply Finset.sum_le_sum
        intro i _hi
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (norm_le_pi_norm x i) 2
      _ = 3 * ‖x‖ ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have h2 : |vec3EuclideanNorm x| ≤ |Real.sqrt 3 * ‖x‖| := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (vec3EuclideanNorm_nonneg x),
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg 3) (norm_nonneg x))] at h2

end
end CKN
