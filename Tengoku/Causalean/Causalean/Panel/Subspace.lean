/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Panel nuisance subspace aliases

For `c : Cells I T` and a linear subspace `H : Submodule ℝ ((I × T) → ℝ)`,
the weighted inner product, orthogonal projection, residual maker, and
residualized regressor operations are provided by the generic weighted-support
substrate. This file exposes the panel-level `Cells` aliases used by downstream
panel APIs: `V`, `proj`, `residualize`, `tildeX`, `tildeXVec`, and the main
orthogonality and idempotence lemmas.
-/

module
public import Tengoku.Causalean.Causalean.Panel.InnerProduct
public import Tengoku.Causalean.Causalean.Stat.Weighted.Subspace

/-! # Panel Subspace Aliases

This file exposes panel-level names for weighted orthogonal projection,
residualization, and cell-array spaces. It keeps the panel regression API
connected to the generic weighted subspace construction used throughout the
library while preserving convenient `Cells.*` names for projection,
residual-maker, residualized-regressor, orthogonality, and idempotence facts. -/

@[expose] public section

namespace Causalean
namespace Panel
namespace Cells

/-- Cell-array space: scalar-valued arrays on `I × T`. -/
abbrev V (I T : Type*) : Type _ := (I × T) → ℝ

variable {I T : Type*}
variable [Fintype I] [Fintype T] [DecidableEq I] [DecidableEq T]

-- Most projection / residualization / tildeX declarations live under
-- `Causalean.Stat.Weighted.WeightedSupport.*` and are inherited through the
-- `Cells := WeightedSupport (I × T)` abbreviation.

-- Bare-name aliases under `Cells` namespace for downstream files that
-- reference these by fully-qualified name `Cells.proj`, `Cells.tildeX`,
-- etc. (rather than through dot-notation, which already resolves
-- transparently through the abbreviation).

variable {K : ℕ}

/-! ### Lemma aliases under the `Cells` namespace

These re-export the corresponding `WeightedSupport.*` lemmas under the
`Cells` namespace so that downstream files can reference them as
`Cells.tildeX_eq`, `Cells.residualize_in_orthogonal`, etc., either by
fully-qualified name (in `simp`-set hints, in proof scripts) or by
dot-notation. -/

end Cells
end Panel
end Causalean
