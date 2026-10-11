/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.ExtSobolevBallSupported
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.ProdSwap

/-!
# The time-Sobolev estimate on Euclidean balls

Clause (iv) of the external Sobolev input is used here in the Euclidean-ball
form.  The paper's equation (1446--1453) states, for `q = 10/3`,

`∫_{B_r} |v|^(10/3) ≤ C₆ ((∫_{B_r} |∇v|²)(∫_{B_r} |v|²)^(2/3)
  + r^(-2)(∫_{B_r} |v|²)^(5/3))`.

The text at lines 4649--4671 integrates this same-ball estimate in time to
obtain the `L∞_t L²_x ∩ L²_t H¹_x` to `L^(10/3)` embedding.  This theorem
formalizes that time estimate on Euclidean balls.  Clauses (i)--(iii) of the
external input are independent and are not changed here.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration

noncomputable section

namespace CKN

theorem euclideanBall_eq_vec3Ball_timeSobolev
    {x₀ : Vec3} {r : ℝ} (hr : 0 < r) :
    euclideanBall x₀ r = vec3Ball x₀ r := by
  ext x
  change x ∈ euclideanBall x₀ r ↔ vec3EuclideanNorm (x - x₀) < r
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
    (mem_euclideanBall_iff_vecEuclideanNorm_lt hr)

/-- Zero H¹ function on the whole spatial domain, used as a default slice. -/
noncomputable def zeroH1Whole : H1Function (Set.univ : Set Vec3) where
  toFun := fun _ => 0
  grad := fun _ => 0
  memL2 := by
    change MemLp (fun _ : Vec3 => (0 : ℝ)) 2 (volume.restrict Set.univ)
    simp
  gradMemL2 := by
    intro i
    change MemLp (fun _ : Vec3 => (0 : ℝ)) 2 (volume.restrict Set.univ)
    simp
  hasWeakGradient := by
    intro i
    have h := HasWeakGradientOn.of_contDiff (U := (Set.univ : Set Vec3))
      (f := fun _ : Vec3 => (0 : ℝ)) (contDiff_const (𝕜 := ℝ))
    simpa [HasWeakGradientOn] using h i

/-- Selected H¹ time slice when one exists, with zero as the default on exceptional times. -/
noncomputable def timeSobolevSlice
    (x₀ : Vec3) (r : ℝ) (hr : 0 < r)
    (g : Vec3 × ℝ → ℝ) (Dg : Vec3 × ℝ → Vec3) :
    ℝ → H1Function (euclideanBall x₀ r) := by
  classical
  let hball := euclideanBall_eq_vec3Ball_timeSobolev (x₀ := x₀) hr
  let zero := zeroH1Whole.restrict (isOpen_euclideanBall x₀ r) (Set.subset_univ _)
  exact fun s =>
    if hs : ∃ v : H1Function (vec3Ball x₀ r),
        (fun x => g (x, s)) =ᵐ[volume.restrict (vec3Ball x₀ r)] v.toFun ∧
        (fun x => Dg (x, s)) =ᵐ[volume.restrict (vec3Ball x₀ r)] v.grad then
      (Classical.choose hs).restrict (isOpen_euclideanBall x₀ r) (by rw [← hball])
    else zero

end CKN

end
