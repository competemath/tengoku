/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Tengoku.Hironaka.Hironaka.Algebra.RegularSmooth.Defs
public import Tengoku.Seed.AlgebraicGeometry.Morphisms.Smooth
import Tengoku.Hironaka.Hironaka.Algebra.RegularSmooth.Regular
import Tengoku.Hironaka.Hironaka.Algebra.RegularSmooth.RegularImpliesSmooth
import Tengoku.Hironaka.Hironaka.Algebra.RegularSmooth.SchemeForms

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Regular equals smooth over a perfect field

The scheme form of [Sta, Tag 00TV] with [Sta, Tag 00TT] (see also [Sta, Tag 038X]): for `X`
locally of finite type over a perfect field `k`, the smooth locus of `X → Spec k` is exactly the set
of regular points, and `X → Spec k` is smooth iff `X` is regular. Smooth implies regular is
`Scheme.isRegularAt_of_mem_smoothLocus` (`SchemeForms.lean`); regular implies smooth reduces,
through an affine open neighbourhood `U` of the point and the affine forms of `Regular.lean` and
`SmoothAt.lean` (`x ∈ f.smoothLocus` iff `Γ(X, U)` is smooth at the prime of `x`; `X` regular at
`x` iff that localization is a regular local ring), to the affine statement
`Algebra.IsSmoothAt.of_isRegularLocalRing_of_perfectField`.
The global statement is the pointwise one with Mathlib's `Scheme.Hom.smoothLocus_eq_top_iff`
(finite type over the Noetherian `Spec k` is finite presentation); see also `SingularLocus.lean`.
-/

public section

universe u

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}}

end AlgebraicGeometry
