/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.AlgebraicGeometry.AlgClosed.Basic
import Tengoku.LanaOka.Oka.AlgebraicGeometry.Morphisms.FormallyUnramified

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Morphisms into unramified schemes over an algebraically closed field

Let `K` be an algebraically closed field and `X` locally of finite type over `K`. Closed points of
`X` have residue field `K` (`AlgebraicGeometry.residueFieldIsoBase`), so a `K`-morphism out of
`Spec κ(x)` is determined by its image point. Combined with
`AlgebraicGeometry.ext_of_fromSpecResidueField_eq_of_formallyUnramified`, two morphisms into a
scheme which is unramified over some base are equal as soon as they agree on the closed points.
No reducedness of `X` and no separatedness is needed.

## Main results

- `AlgebraicGeometry.ext_of_apply_eq_of_formallyUnramified`: if `s : Y ⟶ Z` is formally
  unramified and locally of finite type, `Z` is locally of finite type over `K`, and `f g : X ⟶ Y`
  agree over `Z` and on all closed points of `X`, then `f = g`.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry

end AlgebraicGeometry
