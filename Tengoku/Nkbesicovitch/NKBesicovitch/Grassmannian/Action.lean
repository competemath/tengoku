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

theorem rotate_one (V : Grassmannian n k) : rotate 1 V = V := by
  apply Subtype.ext
  exact Submodule.map_id V.val

theorem rotate_mul (u v : Rotations n) (V : Grassmannian n k) :
    rotate (u * v) V = rotate u (rotate v V) := by
  apply Subtype.ext
  change V.val.map _ = (V.val.map _).map _
  rw [← Submodule.map_comp]
  rfl

theorem projection_rotate (u : Rotations n) (V : Grassmannian n k) :
    (rotate u V).projection =
      (u : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) * V.projection *
        (star u : Rotations n) := by
  apply ContinuousLinearMap.ext
  intro x
  exact Submodule.starProjection_map_apply (Unitary.linearIsometryEquiv u) V.val x

theorem continuous_projection : Continuous (projection (n := n) (k := k)) :=
  continuous_induced_dom

noncomputable instance : MulAction (Rotations n) (Grassmannian n k) where
  smul := rotate
  one_smul := rotate_one
  mul_smul := rotate_mul

end NKBesicovitch.Grassmannian
