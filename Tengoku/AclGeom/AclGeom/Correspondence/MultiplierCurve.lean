/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Correspondence.FunctionField
import Tengoku.Seed.Algebra.MvPolynomial.Monad

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The multiplier curve of the meet `F`

Raw field-theoretic inputs for the proposed linearity step of meet elimination in the corrected
blueprint Lemma `affine-grid-extraction` (#27).  In affine coordinates the meet `F` is a point
`f ∈ acl(a c, x)` outside `acl(a c)`; it is a point of the curve traced by `(a c, x)`.

* `idealOf_aeval_comp_eq_of_idealOf_eq`: equal vanishing ideals stay equal after applying the
  same polynomial map, the polynomial-image analogue of `idealOf_comp_eq_of_idealOf_eq`.
* `affine_multiplier_curve_of_joint_ideal`: a relocation with `p, y, δ, c, f` literally fixed
  and the same joint vanishing ideal (the output of `exists_affine_relocation`) keeps
  `(f, a' c, x')` on the same `k`-locus as `(f, a c, x)`.  The membership `f ∈ acl(a' c, x')`,
  the non-membership `f ∉ acl(a' c)` and the finite fibre `x' ∈ acl(a' c, f)` follow.
* `multiplier_projection_genericity`: for independent `A, B, M, X` and `f ∈ acl(M, X)` outside
  `acl(M)`, the fibre is finite, `M` is generic over `A, B, f`, and `f ∉ acl(A, B)`.

No component, curve action, stabilizer or linearity is assumed or proved.  The finite-component
and stabilizer argument, iterated fresh relocation, coordinate extraction and guarded completeness
remain open.

**Status:** polynomial-image and multiplier-curve/fibre prerequisites proved (#27, L2a).
Component/stabilizer linearity, iterated fresh relocation and guarded completeness remain open.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

open MvPolynomial

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **Polynomial images preserve equality of vanishing ideals**: if `a` and `b` have the same
vanishing ideal, so do their images under the same polynomial map `g`.-/
theorem idealOf_aeval_comp_eq_of_idealOf_eq {ι κ : Type*} {a b : ι → K}
    (h : idealOf k a = idealOf k b) (g : κ → MvPolynomial ι k) :
    idealOf k (fun j ↦ aeval a (g j)) = idealOf k (fun j ↦ aeval b (g j)) := by
  ext F
  rw [mem_idealOf_iff, mem_idealOf_iff]
  have ha : aeval (fun j ↦ aeval a (g j)) F = aeval a (bind₁ g F) := (aeval_bind₁ a g F).symm
  have hb : aeval (fun j ↦ aeval b (g j)) F = aeval b (bind₁ g F) := (aeval_bind₁ b g F).symm
  rw [ha, hb]
  constructor
  · intro hz
    have hm : bind₁ g F ∈ idealOf k a := (mem_idealOf_iff k).2 hz
    exact (mem_idealOf_iff k).1 (h ▸ hm)
  · intro hz
    have hm : bind₁ g F ∈ idealOf k b := (mem_idealOf_iff k).2 hz
    exact (mem_idealOf_iff k).1 (h.symm ▸ hm)

end

end AclGeom
