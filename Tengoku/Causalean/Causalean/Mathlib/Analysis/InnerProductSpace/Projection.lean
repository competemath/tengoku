/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Finite-dimensional normal-equation maps for semidefinite bilinear forms

This file isolates a Mathlib-style linear-algebra fact for degenerate normal
equations: a symmetric positive-semidefinite bilinear form on a
finite-dimensional real vector space admits a linear map into every linear
subspace whose residual satisfies the corresponding normal equations. The proof
works through the range of the induced map from the subspace to its dual and
uses a linear right inverse on that range.

Candidate for upstreaming to Mathlib.
-/

module
public import Tengoku

/-! # Semidefinite Normal-Equation Maps

This file proves `exists_orthogonalProjection_of_posSemidef`: every finite-dimensional
subspace of a vector space over a linearly ordered field admits a linear map into that
subspace whose residual is orthogonal, with respect to a symmetric positive-semidefinite
bilinear form, to every vector in the subspace. The result supplies the
linear-algebra substrate for weighted normal-equation arguments where the inner
product may be degenerate. -/

public section

namespace Causalean.Mathlib

open LinearMap

variable {K V : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup V] [Module K V]

end Causalean.Mathlib
