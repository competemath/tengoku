/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Ball

/-!
# Ball Basics

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open Set MeasureTheory

noncomputable section

namespace CKN.Foundation.Parabolic

/-- The explicit Euclidean ball `CKN.euclideanBall` coincides with `vec3Ball` for
positive radius.
@isnad1 id=eq.1h2v.s5.bc9f683b55ce from=translated src=- shape=8139cc40 vocab=c29d0dbd
-/
theorem euclideanBall_eq_vec3Ball {x₀ : Vec3} {r : ℝ} (hr : 0 < r) :
    CKN.euclideanBall x₀ r = vec3Ball x₀ r := by
  ext x
  rw [CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hr, mem_vec3Ball]
  simp [vec3EuclideanNorm, CKN.vecEuclideanNorm, CKN.vecNormSq, CKN.vecDot, pow_two]

/-- The closure of the Euclidean open ball of positive radius is compact.
@isnad1 id=iscompac.1h2v.s6.cfa7b810f0c3 from=translated src=- shape=b46f31a7 vocab=d6a5e226
-/
theorem isCompact_closure_vec3Ball {x : Vec3} {r : ℝ} (hr : 0 < r) :
    IsCompact (closure (vec3Ball x r)) := by
  rw [closure_vec3Ball hr]
  have h_eq : (vec3Homeomorph ⁻¹' Metric.closedBall (vec3Homeomorph x) r) =
      {y : Vec3 | vec3EuclideanNorm (y - x) ≤ r} := by
    ext y
    simp [mem_preimage, Metric.mem_closedBall, vec3Homeomorph_apply, dist_eq_norm,
      ← WithLp.toLp_sub, ← vec3EuclideanNorm_eq_l2]
  rw [← h_eq]
  exact vec3Homeomorph.isCompact_preimage.mpr (isCompact_closedBall (vec3Homeomorph x) r)

/-- The Lebesgue measure of the closure of a Euclidean open ball of positive radius
is finite.
@isnad1 id=lt.1h2v.s7.e11914b6c1c4 from=translated src=- shape=140802db vocab=dedfd242
-/
theorem measure_closure_vec3Ball_lt_top {x : Vec3} {r : ℝ} (hr : 0 < r) :
    volume (closure (vec3Ball x r)) < ⊤ :=
  (isCompact_closure_vec3Ball hr).measure_lt_top

end CKN.Foundation.Parabolic
