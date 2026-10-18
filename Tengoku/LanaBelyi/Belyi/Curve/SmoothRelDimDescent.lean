/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Smooth
import Tengoku.Seed.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Tengoku.Seed.AlgebraicGeometry.Pullbacks
import Tengoku.Seed.RingTheory.Kaehler.TensorProduct
import Tengoku.Seed.RingTheory.Smooth.StandardSmoothCotangent
import Tengoku.Seed.RingTheory.RingHom.StandardSmooth
import Tengoku.Seed.RingTheory.LocalProperties.Projective
import Tengoku.Seed.RingTheory.Nilpotent.Lemmas
import Tengoku.LanaBelyi.Belyi.Definable

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Descent of `SmoothOfRelativeDimension 1` along a field extension

This file provides the smoothness-of-relative-dimension half of the descent step **B3c**
(taxis #205): if the base change `X₀ ×_{Spec k₀} Spec K` of a scheme `X₀ / k₀` along a field
extension `k₀ ⊆ K` is smooth of relative dimension `1` over `K`, then `X₀` is smooth of relative
dimension `1` over `k₀`.

The general `MorphismProperty.DescendsAlong (@SmoothOfRelativeDimension 1)` instance is a genuine
mathlib gap. Instead we prove the field-specific statement by the *forward* argument: `Smooth`
descends for free along the faithfully-flat cover, and on each affine chart of `X₀` the relative
dimension is pinned to `1` by a rank computation for Kähler differentials, transported across the
base change `A ↦ K ⊗[k₀] A`.

## Main results

* `Belyi.smoothOfRelativeDimension_of_baseChange`: the headline descent statement.
-/

universe u

open CategoryTheory Limits MorphismProperty AlgebraicGeometry TensorProduct

namespace Belyi

variable {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K]

end Belyi
