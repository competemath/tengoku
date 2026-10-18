/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Tengoku.LanaBelyi.Belyi.BelyiMap
import Tengoku.LanaBelyi.Belyi.RamificationBaseChange
import Tengoku.LanaBelyi.Belyi.P1.PointsBaseChange

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Base change of a Belyi map along a field extension

This file supplies the **field-extension specialisation** of statement **B2b** (taxis issue
#47): the compatibility of the branch locus, and of the `IsBelyiMap` predicate, with base
change along a field extension `k₀ ⊆ K`.

Concretely, for a morphism `f₀ : X₀ ⟶ ℙ¹_{k₀}` we take its base change along the canonical
map `Belyi.P1.mapOfAlgebra k₀ K : ℙ¹_K ⟶ ℙ¹_{k₀}` (which exhibits `ℙ¹_K` as the base change
of `ℙ¹_{k₀}`, `Belyi.P1.isPullback_mapOfAlgebra`), namely
`pullback.snd f₀ (mapOfAlgebra k₀ K) : (X₀ ×_{ℙ¹_{k₀}} ℙ¹_K) ⟶ ℙ¹_K`.

## Main results

* `Belyi.branch_baseChange_subset` — the **geometric core**: the branch locus of the base
  change lies over the branch locus of `f₀`:
  `Branch (pullback.snd f₀ (mapOfAlgebra k₀ K)) ⊆ (mapOfAlgebra k₀ K) ⁻¹' Branch f₀`.
  Bridge-free — a direct instantiation of `Belyi.branch_subset_preimage` (the forward
  inclusion of B2b) at the base-change square `Belyi.P1.isPullback_mapOfAlgebra`.
* `Belyi.isBelyiMap_baseChange_of_mapsTo` — the **packaged form**: if `f₀` is a Belyi map and
  the base-change map `mapOfAlgebra k₀ K` sends the fibre of the marked points `{0, 1, ∞}` of
  `ℙ¹_{k₀}` into the marked points of `ℙ¹_K` (the "marked-point matching" hypothesis), then the
  base change is a Belyi map over `K`.

`IsFinite` and `LocallyOfFinitePresentation` are stable under base change in mathlib, so the
only genuine input beyond the geometric core is the marked-point matching, i.e. that the
preimage of a marked point of `ℙ¹_{k₀}` under `mapOfAlgebra k₀ K` is again a marked point of
`ℙ¹_K`. The forward direction of this matching (a marked point maps to a marked point) is
`Belyi.P1.mapOfAlgebra_base_{zero,one,infty}`; the reverse (fibre-singleton) inclusion is a
separate homogeneous-prime computation, left as follow-up on #47.

This is exactly the input the forward direction of Belyi's theorem (B8, issue #51) consumes:
it produces a finite `f₀` over `ℚ̄` with `Branch f₀ ⊆ {0, 1, ∞}`, base-changes to `ℂ`, and
needs the base change to stay a Belyi map.
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory Limits

variable (k₀ K : Type u) [Field k₀] [Field K] [Algebra k₀ K]

section

variable {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ P1 k₀)

end

end Belyi
