/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.Geometry.Convex.ConvexSpace.Barycenter
public import Tengoku.Tauceti.TauCeti.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# Barycentric subdivision of singular chains

The barycentric subdivision of the standard `n`-simplex `Δⁿ` has one `n`-simplex for each
permutation `π` of the vertices `{0, …, n}`: the affine simplex
`StdSimplex.continuousAffineMapMk (BarycentricSubdivision.vertex π)` whose `k`-th vertex is the
barycenter of the face of `Δⁿ` spanned by `π k, …, π n`. Its vertices are thus the barycenters
of a decreasing chain of faces, starting at the barycenter of `Δⁿ` itself.

The barycentric subdivision of a singular `n`-simplex `σ : Δⁿ → X` is the signed sum over `π` of
`sign π • σ ∘ StdSimplex.continuousAffineMapMk (vertex π)`. This is the closed form of Hatcher's
inductive definition `S σ = σ_♯ (b · S (∂ Δⁿ))`, where `b ·` is the cone from the barycenter `b`
of `Δⁿ`, placed as the first vertex. It is a morphism of singular chain complexes, natural in the
space.

## Main definitions and results

* `TauCeti.BarycentricSubdivision.sum_sign_boundary`: the boundary formula for the subdivision
  of the standard simplex. The faces of the subdivision simplices that meet the interior of `Δⁿ`
  cancel in pairs (exchanging two consecutive entries of `π`), and the remaining faces, which omit
  the barycenter of `Δⁿ`, are the subdivision simplices of the facets of `Δⁿ`, with the signs of
  the simplicial boundary (reindexing through Mathlib's `Equiv.Perm.decomposeFin'`).
* `TauCeti.singularSubdivisionX`: the subdivision of singular `n`-chains with coefficients in an
  object `R` of a preadditive category, computed on summands by
  `TauCeti.ιChainComplex_singularSubdivisionX`; it is the identity on `0`-chains
  (`TauCeti.singularSubdivisionX_zero`).
* `TauCeti.singularSubdivisionChainMap`: the subdivision is a chain map, `∂ S = S ∂`.
* `TauCeti.singularSubdivision`: the subdivision as a natural endomorphism of the singular chain
  complex functor `TopCat ⥤ ChainComplex C ℕ`.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, proof of Proposition 2.21, steps (2) and (3).
-/

public section

noncomputable section

open CategoryTheory Limits Convexity Simplicial Equiv AlgebraicTopology

universe w v u

namespace TauCeti

namespace BarycentricSubdivision

variable {n : ℕ}

variable {A : Type*} [AddCommGroup A]

end BarycentricSubdivision

open BarycentricSubdivision

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

variable (R : C) (X : TopCat.{w})

end TauCeti
