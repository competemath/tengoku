/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The center of a finite group algebra and conjugacy classes

For a finite group, central elements of its group monoid algebra have coefficients invariant
under conjugation. This identifies the center with functions on conjugacy classes and, over a
field, yields the center finrank formula in terms of the number of conjugacy classes.
-/

namespace RepresentationTheory.Algebra.MonoidAlgebra.Center

open scoped MonoidAlgebra

open _root_.MonoidAlgebra

section General

variable {k G : Type*} [CommRing k] [Group G]

/-- An element of a group monoid algebra is central exactly when its coefficients are invariant
under conjugation.
@isnad1 id=iff.0h3v.s8.e03d1518dc8f from=translated src=- shape=585e66b0 vocab=4c0f69c8
-/
theorem mem_center_iff_coeff_conj_invariant (x : MonoidAlgebra k G) :
    x ∈ Subalgebra.center k (MonoidAlgebra k G) ↔
      ∀ g h : G, x.coeff (g * h * g⁻¹) = x.coeff h := by
  rw [Subalgebra.mem_center_iff]
  constructor
  · -- centrality ⇒ conjugation-invariance of coefficients
    intro hx g h
    have hcomm := hx (single g (1 : k))
    have h1 : (single g (1 : k) * x).coeff (g * h) = x.coeff h := by
      simp
    have h2 : (x * single g (1 : k)).coeff (g * h) = x.coeff (g * h * g⁻¹) := by
      simp
    rw [hcomm] at h1
    rw [h2] at h1
    exact h1
  · -- conjugation-invariance ⇒ commutes with every element
    intro hcoeff y
    -- it suffices that `x` commutes with every `single g c`
    have hsingle : ∀ (g : G) (c : k), single g c * x = x * single g c := by
      intro g c
      ext h
      rw [coeff_single_mul_apply, coeff_mul_single_apply, mul_comm]
      congr 1
      -- `x (g⁻¹ * h) = x (h * g⁻¹)`, conjugate of one another
      have := hcoeff g (g⁻¹ * h)
      rw [← mul_assoc, mul_inv_cancel, one_mul] at this
      exact this.symm
    -- extend from generators to all of `y` by linearity
    conv_lhs => rw [← y.sum_coeff_single]
    conv_rhs => rw [← y.sum_coeff_single]
    simp only [Finsupp.sum]
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun g _ => hsingle g (y.coeff g)

variable [Fintype G]

end General

section FieldCase

variable (k G : Type*) [Field k] [Group G] [Fintype G]

end FieldCase

end RepresentationTheory.Algebra.MonoidAlgebra.Center
