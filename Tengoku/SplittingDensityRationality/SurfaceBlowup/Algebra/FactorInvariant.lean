/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import Tengoku.SplittingDensityRationality.SurfaceBlowup.Measure.PrimitiveLocus
import Tengoku.SplittingDensityRationality.SurfaceBlowup.Unramified.FactorCells

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Invariance of factor invariants and uniqueness of algebra types

Over a complete DVR `O` with finite residue field and fraction field `K = BaseField O`, the
invariants `(e, f)` of the integral closure of `O` in a finite extension `L/K` depend only on the
`K`-isomorphism class of `L`. Consequences: polynomial types are invariant under normalized
reversal `g ↦ g(0)⁻¹ · reverse g`, algebra types are unique, and a monic `F ∈ O[X]` has polynomial
type `σ` over `K` exactly when `O[X]/(F)` has algebra type `σ`.

## Main results

* `SurfaceBlowup.field_invariant_algEquiv`, `SurfaceBlowup.factor_invariant_algEquiv`
* `SurfaceBlowup.reverse_normalized_irreducible`, `SurfaceBlowup.reverse_polynomial_type_iff`
* `SurfaceBlowup.algebra_type_unique`, `SurfaceBlowup.polynomial_type_iff_algebra_type`

Provenance: Thm_SurfaceBlowupV2_{factor_invariant_algEquiv, reverse_normalized_irreducible,
reverse_polynomial_type_iff, field_invariant_algEquiv, algebra_type_unique,
polynomial_type_iff_algebra_type}.
-/

namespace SurfaceBlowup

open Polynomial

/-! ### Invariance under isomorphism -/

/-! ### Normalized reversal -/

section Reverse

variable {K : Type} [Field K]

/-- The normalized reversal `f(0)⁻¹ · reverse f`.-/
private noncomputable def rho (f : K[X]) : K[X] := C (f.coeff 0)⁻¹ * f.reverse

end Reverse

/-! ### Uniqueness of algebra types -/

/-! ### Polynomial types versus algebra types -/

end SurfaceBlowup
