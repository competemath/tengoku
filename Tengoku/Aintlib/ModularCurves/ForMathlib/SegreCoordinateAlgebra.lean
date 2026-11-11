/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex, AINTLIB ModularCurves project

Adapted from Clawristotle's `CoherentCohomologyFinite.SegreCoordinateAlgebra`.
-/
import Tengoku.Seed.LinearAlgebra.TensorProduct.RightExactness
import Tengoku.Seed.RingTheory.MvPolynomial.Homogeneous

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Coordinate algebra for the Segre embedding

The coordinate indexed by `(i, j)` maps to `X i ⊗ X j`. The standard quadratic
Segre relations lie in the kernel and are homogeneous.
-/

open scoped TensorProduct

noncomputable section

universe u

namespace MvPolynomial

/-- The coordinate-algebra map underlying the Segre embedding.-/
def segreCoordinateHom
    (R : Type u) [CommRing R] (m n : ℕ) :
    MvPolynomial (Fin (m + 1) × Fin (n + 1)) R →ₐ[R]
      MvPolynomial (Fin (m + 1)) R ⊗[R] MvPolynomial (Fin (n + 1)) R :=
  MvPolynomial.aeval fun p => X p.1 ⊗ₜ[R] X p.2

/--
@isnad1 id=eq.0h5v.s11.d1d4885f0792 from=translated src=- shape=8335599b vocab=c2897a21
-/
@[simp]
lemma segreCoordinateHom_X
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreCoordinateHom R m n (X (i, j)) = X i ⊗ₜ[R] X j := by
  simp only [segreCoordinateHom, aeval_X]

/-- The `2 × 2` minor relations vanish under the Segre coordinate map.
@isnad1 id=eq.0h7v.s11.ddfce9cafb60 from=translated src=- shape=8286e860 vocab=24801ba5
-/
lemma segreCoordinateHom_relation
    (R : Type u) [CommRing R] (m n : ℕ)
    (i i' : Fin (m + 1)) (j j' : Fin (n + 1)) :
    segreCoordinateHom R m n
      (X (i, j) * X (i', j') - X (i', j) * X (i, j')) = 0 := by
  simp only [map_sub, map_mul, segreCoordinateHom_X]
  simp only [Algebra.TensorProduct.tmul_mul_tmul]
  ring_nf

/-- Every defining `2 × 2` minor is homogeneous of degree two.
@isnad1 id=ishomoge.0h7v.s10.5e05b3aba23b from=translated src=- shape=7b6da074 vocab=8dc57368
-/
lemma segreRelation_isHomogeneous
    (R : Type u) [CommRing R] (m n : ℕ)
    (i i' : Fin (m + 1)) (j j' : Fin (n + 1)) :
    letI := @MvPolynomial.gradedAlgebra
      (Fin (m + 1) × Fin (n + 1)) R _
    (X (i, j) * X (i', j') - X (i', j) * X (i, j') :
      MvPolynomial (Fin (m + 1) × Fin (n + 1)) R).IsHomogeneous 2 := by
  letI := @MvPolynomial.gradedAlgebra
    (Fin (m + 1) × Fin (n + 1)) R _
  exact
    ((isHomogeneous_X R (i, j)).mul (isHomogeneous_X R (i', j'))).sub
      ((isHomogeneous_X R (i', j)).mul (isHomogeneous_X R (i, j')))

end MvPolynomial
