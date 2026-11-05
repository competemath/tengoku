/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.Seed.Algebra.MvPolynomial.Nilpotent
import Tengoku.AclGeom.AclGeom.Correspondence.Additive
import Tengoku.AclGeom.AclGeom.Closure.Ambient
import Tengoku.AclGeom.AclGeom.Closure.FreshExtension
import Tengoku.AclGeom.AclGeom.Geometry.Points
import Tengoku.AclGeom.AclGeom.Geometry.Representatives
import Tengoku.AclGeom.AclGeom.Transfer.Transcendence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The additive correspondence theorem for three pairs

Blueprint Theorem `addcorr`: for algebraically independent `x₁, x₂, x₃` over an algebraically
closed `k ⊆ Ω` with `[xᵢ] = [yᵢ]`, `[x₁ + x₂] = [y₁ + y₂]` and `[x₁ + x₃] = [y₁ + y₃]`, there are
nonzero additive polynomials `P, Q` and constants `dᵢ ∈ k` with `Q(yᵢ) = P(xᵢ) + dᵢ` for all
three pairs, and `d₁ + d₂`, `d₁ + d₃` are the translation constants of the two sums (`addcorr`).

The two-pair core `AddCorrSetup.exists_delta_gen_data` gives, for each of the pairs `(1, 2)` and
`(1, 3)`, a prime generator `G = P(X₀) + Q(X₁)` taking constant values at both of its pairs.  The
two generators are compared on the first curve: its vanishing ideal is principal
(`exists_prime_span_idealOf`), and `G - e₁` is a translate of the prime `G`
(`prime_sub_C_of_split`), hence an associate of the curve's generator.  The two translated
generators therefore differ by a nonzero constant, so the first generator is constant on the
third pair too.  Additivity in every algebra (`IsAdditive.aeval_add`) gives the translation
constants of the sums.

The two-pair core needs elements fresh over the pairs; the blueprint has no such hypothesis.  The
theorem passes to the algebraically closed extension `FreshAmbient Ω` (`Closure.FreshExtension`)
and pulls the `k`-polynomial equations back along the injective embedding.  The independence of
`(y₁, y₂, y₃)` assumed by the blueprint follows from `[xᵢ] = [yᵢ]` and is not used.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** proved (#5).
-/

namespace AclGeom

open ClosedIF MvPolynomial

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- Over an infinite field, a pointwise additive polynomial is additive in every commutative
algebra.-/
theorem IsAdditive.aeval_add [Infinite k] {P : Polynomial k} (hP : IsAdditive P)
    {A : Type*} [CommRing A] [Algebra k A] (x y : A) :
    Polynomial.aeval (x + y) P = Polynomial.aeval x P + Polynomial.aeval y P := by
  have h : (Polynomial.aeval (X 0 + X 1) P : MvPolynomial (Fin 2) k) =
      Polynomial.aeval (X 0) P + Polynomial.aeval (X 1) P := by
    refine MvPolynomial.funext fun v ↦ ?_
    change MvPolynomial.aeval v _ = MvPolynomial.aeval v _
    simp only [map_add, ← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X]
    exact hP (v 0) (v 1)
  have h' := congrArg (MvPolynomial.aeval ![x, y]) h
  simpa only [map_add, ← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h'

end AclGeom
