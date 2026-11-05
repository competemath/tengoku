/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Curves.RiemannRoch
import Tengoku.Seed.RingTheory.AlgebraTower

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The pole-order bound

The pole-side of Stichtenoth Theorem 1.4.11: the total pole order of `f`
over any finite set of poles is at most `[F : k(f)]`
(`sum_pole_orders_le_finrank`). The witnesses are prescribed-order
elements `u i j` with order `-j` at the `i`-th pole and order `1` at the
other listed poles; coefficients from `k(f)` shift orders at the `i`-th
pole by multiples of the pole order `e i` (the uniform order applied to
`f⁻¹`), so after normalizing the minimal coefficient order to zero, the
cross-place terms have positive order while the same-place terms have
distinct nonpositive orders by Euclidean uniqueness — a strictly dominant
term.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4b, issue #13, toward deg-div-zero).
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- Adjoining an element and its inverse give the same subfield.
@isnad1 id=eq.0h3v.s6.42f316087988 from=translated src=- shape=1bb7ae6c vocab=8b9df9c3
-/
theorem adjoin_inv_eq (f : F) :
    adjoin k ({f⁻¹} : Set F) = adjoin k ({f} : Set F) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [inv_zero]
  refine le_antisymm ?_ ?_
  · rw [adjoin_le_iff, Set.singleton_subset_iff]
    exact inv_mem (subset_adjoin k _ rfl)
  · rw [adjoin_le_iff, Set.singleton_subset_iff]
    have h1 : f⁻¹ ∈ adjoin k ({f⁻¹} : Set F) := subset_adjoin k _ rfl
    have h2 := inv_mem h1
    rwa [inv_inv] at h2

/-- Powers of a transcendental element are linearly independent.
@isnad1 id=linearin.1h4v.s6.cfd66fe614ef from=translated src=- shape=3f1f507d vocab=ceed4961
-/
theorem linearIndependent_pow_of_transcendental {f : F}
    (htr : Transcendental k f) (N : ℕ) :
    LinearIndependent k fun j : Fin N ↦ f ^ (j : ℕ) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have hp : (∑ j' : Fin N,
      Polynomial.C (g j') * Polynomial.X ^ (j' : ℕ)) = 0 := by
    rw [transcendental_iff] at htr
    refine htr _ ?_
    rw [map_sum]
    simpa [Algebra.smul_def] using hg
  have hcoeff := congrArg (fun p ↦ Polynomial.coeff p (j : ℕ)) hp
  simpa [Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow,
    Fin.val_inj] using hcoeff

variable [IsAlgClosed k] [IsFunctionFieldOneVar k F]

end

end AclGeom
