/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Nuisance subspace, weighted orthogonal projection, and residual maker

For `c : WeightedSupport R` and a linear subspace `H : Submodule ℝ (R → ℝ)`,
this file defines the `c.ip`-orthogonal projection `c.proj H : (R → ℝ) →ₗ[ℝ]
(R → ℝ)` onto `H` and the residual maker `c.residualize H = id - c.proj H`,
together with their basic algebraic properties.

This is the **WLS-projection** layer of the FWL substrate.  Its WLS-optimality
characterization (`proj_eq_argmin`, `residualize_orth_iff_argmin`) lives in
`Causalean/Stat/Weighted/WLS.lean`; the FWL coefficient layer
(`Q_XX`, `rhsVec`, `thetaHat`, `fwl_identity`) lives in
`Causalean/Stat/Weighted/FWL.lean`.

## Implementation note

The ambient space `R → ℝ` carries the weighted inner product `c.ip`, but
`c.ip` is only positive-semidefinite (definiteness fails off the observed
indices).  Mathlib's `Submodule.orthogonalProjection` is stated on a Hilbert
space, so we cannot reuse it off-the-shelf without quotienting / reweighting.

The projection lemma is proved by packaging `c.ip` as a positive-semidefinite
bilinear form and applying the generic helper
`Causalean.Mathlib.exists_orthogonalProjection_of_posSemidef`.
-/

module
public import Tengoku.Causalean.Causalean.Stat.Weighted.InnerProduct
public import Tengoku.Causalean.Causalean.Mathlib.Analysis.InnerProductSpace.Projection
public import Tengoku

/-! # Weighted projections and residual makers

This file defines the weighted orthogonal projection onto a nuisance subspace
and the corresponding residual maker.

The projection exists for the semidefinite weighted inner product because only
observed records matter. The resulting projection and residual maker are used by
the WLS optimality and finite-cell Frisch-Waugh-Lovell layers. -/

@[expose] public section

open scoped BigOperators

namespace Causalean
namespace Stat.Weighted
namespace WeightedSupport

variable {R : Type*}
variable [Fintype R] [DecidableEq R]

/-! ### Existence of the weighted orthogonal projection -/

/-! ### Idempotence of `c.proj H` -/

/-! ### Residual maker -/

/-! ### Vector-form residualization -/

end WeightedSupport
end Stat.Weighted
end Causalean
