/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Grassmannian.Rotations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The orthogonal action on the real Grassmannian

Conjugation of orthogonal projections proves continuity of the action in the
operator norm topology. This supplies measurability of the Haar orbit maps.
-/

@[expose] public section

namespace NKBesicovitch.Grassmannian

variable {n k : ℕ}

/-- The image of a direction under an orthogonal operator.-/
noncomputable def rotate (u : Rotations n) (V : Grassmannian n k) : Grassmannian n k :=
  ⟨V.val.map (Unitary.linearIsometryEquiv u).toLinearEquiv.toLinearMap,
    ((Unitary.linearIsometryEquiv u).toLinearEquiv.finrank_map_eq V.val).trans V.property⟩

/--
@isnad1 id=eq.0h3v.s12.43ac50201001 from=translated src=- shape=f173cd47 vocab=2d392d02
-/
theorem rotate_one (V : Grassmannian n k) : rotate 1 V = V := by
  apply Subtype.ext
  exact Submodule.map_id V.val

/--
@isnad1 id=eq.0h5v.s14.aabe66611769 from=translated src=- shape=48c08246 vocab=d20330df
-/
theorem rotate_mul (u v : Rotations n) (V : Grassmannian n k) :
    rotate (u * v) V = rotate u (rotate v V) := by
  apply Subtype.ext
  change V.val.map _ = (V.val.map _).map _
  rw [← Submodule.map_comp]
  rfl

/--
@isnad1 id=eq.0h4v.s14.6d6a48022f1f from=translated src=- shape=f6d5771f vocab=d841c8e2
-/
theorem projection_rotate (u : Rotations n) (V : Grassmannian n k) :
    (rotate u V).projection =
      (u : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) * V.projection *
        (star u : Rotations n) := by
  apply ContinuousLinearMap.ext
  intro x
  exact Submodule.starProjection_map_apply (Unitary.linearIsometryEquiv u) V.val x

/--
@isnad1 id=continuo.0h2v.s8.a8a2d7a2c8d3 from=translated src=- shape=e39008af vocab=45a4b922
-/
theorem continuous_projection : Continuous (projection (n := n) (k := k)) :=
  continuous_induced_dom

noncomputable instance : MulAction (Rotations n) (Grassmannian n k) where
  smul := rotate
  one_smul := rotate_one
  mul_smul := rotate_mul

end NKBesicovitch.Grassmannian
