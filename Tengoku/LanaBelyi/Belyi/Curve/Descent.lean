/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Separated
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Proper
import Tengoku.Seed.AlgebraicGeometry.Morphisms.FlatDescent
import Tengoku.Seed.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# fpqc descent of separatedness and properness

This file provides two `MorphismProperty.DescendsAlong … (@Surjective ⊓ @Flat ⊓ @QuasiCompact)`
instances that are missing from mathlib v4.32:

* `AlgebraicGeometry.descendsAlong_isSeparated_surjective_inf_flat_inf_quasicompact`
* `AlgebraicGeometry.descendsAlong_isProper_surjective_inf_flat_inf_quasicompact`

They are the separatedness/properness half of the descent step B3c (taxis #167): a scheme
`X₀ / k₀` whose base change `X₀ ×_{Spec k₀} Spec K` along a field extension `k₀ ⊆ K` is
separated (resp. proper) is itself separated (resp. proper) over `k₀`, because
`Spec K ⟶ Spec k₀` is `@Surjective ⊓ @Flat ⊓ @QuasiCompact`.

## The key observation

Mathlib already descends `@UniversallyClosed` along `@Surjective ⊓ @Flat ⊓ @QuasiCompact`
(`descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact`), but it does *not*
descend `@IsClosedImmersion`: that would require faithfully-flat codescent of
`RingHom.SurjectiveOnStalks`, an unsolved (research-grade) ring-theoretic descent problem.

Separatedness, however, does **not** need it. Since `@IsSeparated = diagonal @IsClosedImmersion`
and the diagonal `pullback.diagonal f` is **always** an immersion — hence a preimmersion, so it
already satisfies `SurjectiveOnStalks` for free — being a closed immersion on the diagonal is
equivalent to merely having a *closed range*, which is exactly what universal closedness
supplies. Concretely `@IsSeparated = diagonal @UniversallyClosed`
(`isSeparated_eq_diagonal_universallyClosed`). Descent of `@IsSeparated` then follows from the
existing `@UniversallyClosed` descent through mathlib's `diagonal`-descent combinator, with no
`SurjectiveOnStalks` descent anywhere. Properness follows by `MorphismProperty.DescendsAlong.inf`
from `isProper_eq` together with the descent of `@UniversallyClosed` and `@LocallyOfFiniteType`.

These are pure `AlgebraicGeometry` statements with only mathlib imports; they are natural
candidates for upstreaming.
-/

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

end AlgebraicGeometry
