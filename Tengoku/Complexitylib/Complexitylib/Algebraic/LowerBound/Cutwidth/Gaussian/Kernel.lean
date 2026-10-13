/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Kernel.Defs
public import Tengoku
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Kernel.Internal

/-!
# Correlation of truncated distance kernels

This file bounds the truncated distance kernel of `Gaussian.Kernel.Defs` on a
graph of maximum degree three.

* `card_sphere_le` and `card_ball_le`: spheres and balls grow at most like
  `3 * 2 ^ d`, since a vertex at positive distance `d` has a neighbour at
  distance `d - 1` and hence at most two neighbours at distance `d + 1`.
* `sum_kernel_mul_ge`: for adjacent `u` and `v`, the kernel rows have inner
  product at least `κ = 2q / (1 + q²)` times the mean of their squared norms,
  up to `3 * (2 * q ^ 2) ^ R` contributed by the truncation spheres.
* `sum_unitKernel_mul_ge`: for `0 ≤ q`, the unit kernel rows of adjacent
  vertices have inner product at least `κ - 3 * (2 * q ^ 2) ^ R`.

The ball lemmas `ball_subset_ball_of_adj` and `mem_ball_of_not_disjoint` bound
the vertices on which a kernel row or a pair of adjacent rows depends.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian

section General

variable {W : Type} (H : SimpleGraph W)

/-- The kernel row of `v` takes the value `1` at `v`.
@isnad1 id=eq.0h5v.s4.2761be2e3b26 from=translated src=- shape=77383564 vocab=9cba6190
-/
theorem kernel_self (q : ℝ) (R : ℕ) (v : W) : kernel H q R v v = 1 :=
  Internal.kernel_self H q R v

/-- The kernel is nonnegative for a nonnegative ratio.
@isnad1 id=le.1h6v.s5.ff1a15e6c707 from=translated src=- shape=5bf33de9 vocab=289e6e34
-/
theorem kernel_nonneg {q : ℝ} (hq : 0 ≤ q) (R : ℕ) (v z : W) : 0 ≤ kernel H q R v z :=
  Internal.kernel_nonneg H hq R v z

/-- The kernel is symmetric.
@isnad1 id=eq.0h6v.s4.a41506e3a1d8 from=translated src=- shape=f8ea7b1a vocab=9cba6190
-/
theorem kernel_comm (q : ℝ) (R : ℕ) (v z : W) : kernel H q R v z = kernel H q R z v :=
  Internal.kernel_comm H q R v z

end General

section Finite

variable {W : Type} [Fintype W] (H : SimpleGraph W)

/--
@isnad1 id=iff.0h5v.s5.7452707057e3 from=translated src=- shape=0f11a645 vocab=09a78668
-/
@[simp]
theorem mem_sphere {v z : W} {d : ℕ} : z ∈ sphere H v d ↔ H.edist v z = d :=
  Internal.mem_sphere H

/--
@isnad1 id=iff.0h5v.s5.3c22d4b28c74 from=translated src=- shape=0f11a645 vocab=7a907953
-/
@[simp]
theorem mem_ball {v z : W} {r : ℕ} : z ∈ ball H v r ↔ H.edist v z ≤ r :=
  Internal.mem_ball H

/--
@isnad1 id=mem.0h4v.s4.119b9304ec1c from=translated src=- shape=e56637b0 vocab=3068180a
-/
theorem mem_ball_self (v : W) (r : ℕ) : v ∈ ball H v r :=
  Internal.mem_ball_self H v r

/--
@isnad1 id=iff.0h5v.s5.392c9b73bf5a from=translated src=- shape=14497550 vocab=3068180a
-/
theorem mem_ball_comm {v z : W} {r : ℕ} : z ∈ ball H v r ↔ v ∈ ball H z r :=
  Internal.mem_ball_comm H

/--
@isnad1 id=le.1h5v.s5.8a414c648d08 from=translated src=- shape=07309280 vocab=f628d3bb
-/
theorem ball_mono (v : W) {r r' : ℕ} (h : r ≤ r') : ball H v r ⊆ ball H v r' :=
  Internal.ball_mono H v h

/--
@isnad1 id=le.0h4v.s5.2dec8313a592 from=translated src=- shape=b3b486fc vocab=df93ad48
-/
theorem sphere_subset_ball (v : W) (r : ℕ) : sphere H v r ⊆ ball H v r :=
  Internal.sphere_subset_ball H v r

/--
@isnad1 id=eq.0h3v.s4.ac8043b2572e from=translated src=- shape=c42089ac vocab=d9e867b3
-/
theorem sphere_zero (v : W) : sphere H v 0 = {v} :=
  Internal.sphere_zero H v

/--
@isnad1 id=eq.0h3v.s4.eb8c2b8b8b56 from=translated src=- shape=c42089ac vocab=4e804c7a
-/
theorem ball_zero (v : W) : ball H v 0 = {v} :=
  Internal.ball_zero H v

/-- The ball around a neighbour lies in the ball of one larger radius.
@isnad1 id=le.1h5v.s5.f2226169d4ef from=translated src=- shape=9999352c vocab=026030b8
-/
theorem ball_subset_ball_of_adj {u v : W} (h : H.Adj u v) (R : ℕ) :
    ball H v R ⊆ ball H u (R + 1) :=
  Internal.ball_subset_ball_of_adj H h R

/-- Overlapping balls have centres within the sum of their radii.
@isnad1 id=mem.1h6v.s5.f00ab6c14517 from=translated src=- shape=cd11246e vocab=f086d7ac
-/
theorem mem_ball_of_not_disjoint {a b : W} {r r' : ℕ}
    (h : ¬ Disjoint (ball H a r) (ball H b r')) : b ∈ ball H a (r + r') :=
  Internal.mem_ball_of_not_disjoint H h

/-- The kernel row of `v` vanishes outside the ball of radius `R`.
@isnad1 id=eq.1h6v.s5.5d61f137d34b from=translated src=- shape=f7a06d1a vocab=c479ff3e
-/
theorem kernel_eq_zero_of_notMem_ball {q : ℝ} {R : ℕ} {v z : W} (h : z ∉ ball H v R) :
    kernel H q R v z = 0 :=
  Internal.kernel_eq_zero_of_notMem_ball H h

/--
@isnad1 id=eq.1h6v.s5.d39a94750186 from=translated src=- shape=0be26254 vocab=e92ac7a1
-/
theorem kernel_of_mem_ball {q : ℝ} {R : ℕ} {v z : W} (h : z ∈ ball H v R) :
    kernel H q R v z = q ^ H.dist v z :=
  Internal.kernel_of_mem_ball H h

/-- Every kernel row has squared norm at least one.
@isnad1 id=le.0h5v.s5.8393e305af9c from=translated src=- shape=ecb940cc vocab=a738210a
-/
theorem one_le_sum_kernel_sq {q : ℝ} (R : ℕ) (v : W) : 1 ≤ ∑ z, kernel H q R v z ^ 2 :=
  Internal.one_le_sum_kernel_sq H R v

/-- The unit kernel row has norm one.
@isnad1 id=eq.0h5v.s5.79559f99797a from=translated src=- shape=6b80f42b vocab=8db83249
-/
theorem sum_unitKernel_sq (q : ℝ) (R : ℕ) (v : W) : ∑ z, unitKernel H q R v z ^ 2 = 1 :=
  Internal.sum_unitKernel_sq H q R v

/--
@isnad1 id=eq.1h6v.s5.e884d9ef9f73 from=translated src=- shape=f7a06d1a vocab=4f5b9e00
-/
theorem unitKernel_eq_zero_of_notMem_ball {q : ℝ} {R : ℕ} {v z : W} (h : z ∉ ball H v R) :
    unitKernel H q R v z = 0 :=
  Internal.unitKernel_eq_zero_of_notMem_ball H h

/--
@isnad1 id=le.1h6v.s5.17bb003a1aa1 from=translated src=- shape=90c49730 vocab=d3107d0c
-/
theorem unitKernel_nonneg {q : ℝ} (hq : 0 ≤ q) (R : ℕ) (v z : W) :
    0 ≤ unitKernel H q R v z :=
  Internal.unitKernel_nonneg H hq R v z

variable [DecidableRel H.Adj]

/-- In a graph of maximum degree three, the sphere of radius `d + 1` has at most
`3 * 2 ^ d` vertices.
@isnad1 id=le.1h4v.s6.65800eec1f82 from=translated src=- shape=a8007ffc vocab=c85e04e2
-/
theorem card_sphere_succ_le (degree : ∀ v, H.degree v ≤ 3) (v : W) (d : ℕ) :
    (sphere H v (d + 1)).card ≤ 3 * 2 ^ d :=
  Internal.card_sphere_succ_le H degree v d

/-- In a graph of maximum degree three, the sphere of radius `d` has at most
`3 * 2 ^ d` vertices.
@isnad1 id=le.1h4v.s6.2711b45da073 from=translated src=- shape=c5a9260d vocab=442c0792
-/
theorem card_sphere_le (degree : ∀ v, H.degree v ≤ 3) (v : W) (d : ℕ) :
    (sphere H v d).card ≤ 3 * 2 ^ d :=
  Internal.card_sphere_le H degree v d

/-- In a graph of maximum degree three, the ball of radius `r` has at most
`3 * 2 ^ (r + 1)` vertices.
@isnad1 id=le.1h4v.s6.9558e5b01443 from=translated src=- shape=cdde4844 vocab=b056e60d
-/
theorem card_ball_le (degree : ∀ v, H.degree v ≤ 3) (v : W) (r : ℕ) :
    (ball H v r).card ≤ 3 * 2 ^ (r + 1) :=
  Internal.card_ball_le H degree v r

/-- **Pointwise correlation inequality, summed.** For adjacent vertices the kernel rows
have inner product at least `κ` times the mean of their squared norms, up to the
truncation boundary, where `κ = 2q/(1+q²)`.
@isnad1 id=le.2h6v.s8.58aa77d0dfd6 from=translated src=- shape=0866efa1 vocab=da40a0a2
-/
theorem sum_kernel_mul_ge (degree : ∀ v, H.degree v ≤ 3) (q : ℝ) (R : ℕ) {u v : W}
    (huv : H.Adj u v) :
    2 * q / (1 + q ^ 2) * ((∑ z, kernel H q R u z ^ 2) + ∑ z, kernel H q R v z ^ 2) / 2 -
        3 * (2 * q ^ 2) ^ R ≤ ∑ z, kernel H q R u z * kernel H q R v z :=
  Internal.sum_kernel_mul_ge H degree q R huv

/-- **Correlation of adjacent rows.** For a nonnegative ratio `q`, the unit kernel rows
of adjacent vertices have inner product at least `2q/(1+q²) - 3 (2q²)^R`.
@isnad1 id=le.3h6v.s7.7b4257f6a6b3 from=translated src=- shape=c51f6859 vocab=d2f21743
-/
theorem sum_unitKernel_mul_ge (degree : ∀ v, H.degree v ≤ 3) {q : ℝ} (hq0 : 0 ≤ q) (R : ℕ)
    {u v : W} (huv : H.Adj u v) :
    2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R ≤
      ∑ z, unitKernel H q R u z * unitKernel H q R v z :=
  Internal.sum_unitKernel_mul_ge H degree hq0 R huv

end Finite

end Algebraic.Cutwidth.Gaussian
