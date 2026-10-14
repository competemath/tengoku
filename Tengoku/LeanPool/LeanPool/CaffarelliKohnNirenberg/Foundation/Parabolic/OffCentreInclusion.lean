/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
# Off Centre Inclusion

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open Set

noncomputable section

namespace CKN.Foundation.Parabolic

/-- The Euclidean norm on `Vec3` satisfies the triangle inequality for three points:
`|x - z| ≤ |x - y| + |y - z|`.
@isnad1 id=le.0h3v.s6.45fa746dcf60 from=translated src=- shape=0b02ab07 vocab=06e74943
-/
theorem vec3EuclideanNorm_sub_le_add_sub (x y z : Vec3) :
    vec3EuclideanNorm (x - z) ≤ vec3EuclideanNorm (x - y) + vec3EuclideanNorm (y - z) := by
  have h : x - z = (x - y) + (y - z) := (sub_add_sub_cancel x y z).symm
  rw [h]
  exact vec3EuclideanNorm_add_le _ _

end CKN.Foundation.Parabolic
