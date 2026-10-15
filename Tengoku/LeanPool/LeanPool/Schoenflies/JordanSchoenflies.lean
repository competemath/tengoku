/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import Tengoku.LeanPool.LeanPool.Schoenflies.BoundaryAnchors

/-!
# The Jordan–Schönflies theorem

The quantitative stage recursion supplies the interior homeomorphism.  Its fresh target nets
give a dense source anchor set; radial mesh spokes supply the boundary germs, and finite-stage
nonboundary edge paths supply matched crosscuts. These data prove `HasLimitHomeomorphism`, then
`SquareExtension`, and finally the relative Jordan–Schönflies theorem.

## Blueprint

The declarations below close `thm:square-extension` and `thm:main`; the intervening square
reduction, closed-interior, pointed, and exterior extensions are supplied by `Endgame.lean`.
-/

@[expose] public section

open Set

namespace Schoenflies

/-- All four inputs to boundary continuity are supplied by the prescribed quantitative stage
sequence.
@isnad1 id=haslimit.0h0v.s0.555b9bfa25f6 from=translated src=- shape=45709ebd vocab=555b9bfa
-/
theorem hasLimitHomeomorphism : HasLimitHomeomorphism := by
  intro C u v hC hu
  let T := prescribedJordanStageSequence hC u v hu
  exact ⟨prescribedSourceAnchorSet hC hu, T.limitTower.F, T.limitTower.inv,
    prescribedSourceAnchorSet_subset hC hu,
    prescribedSourceAnchorSet_dense hC hu,
    T.isHomeoOn_F,
    prescribedSourceAnchorSet_hasAnchorCrosscuts hC hu,
    prescribedSourceAnchorSet_hasSpokes hC hu⟩

/-- **`thm:square-extension`.** Every homeomorphism from a Jordan curve to the boundary of the
model square extends over the corresponding closed domains.
@isnad1 id=squareex.0h0v.s0.57c405110fd2 from=translated src=- shape=45709ebd vocab=57c40511
-/
theorem squareExtension : SquareExtension :=
  squareExtension_of_hasLimitHomeomorphism hasLimitHomeomorphism

variable {C C' : Set Plane}

/-- **The relative Jordan–Schönflies theorem**, in the unbundled `IsHomeoOn` form.
@isnad1 id=ex.3h4v.s5.d8b9b8f45f09 from=translated src=- shape=b6622fbc vocab=b623ee19
-/
theorem jordan_schoenflies {f g : Plane → Plane}
    (hC : IsJordanCurve C) (hC' : IsJordanCurve C') (hfg : IsHomeoOn f g C C') :
    ∃ F G : Plane → Plane, IsHomeoOn F G univ univ ∧ EqOn F f C :=
  jordan_schoenflies_of_squareExtension squareExtension hC hC' hfg

/-- **The relative Jordan–Schönflies theorem**, packaged as a plane
self-homeomorphism.
@isnad1 id=ex.3h4v.s8.7b03463ed759 from=translated src=- shape=b87fcc09 vocab=ad6672d4
-/
theorem jordan_schoenflies_homeomorph {f g : Plane → Plane}
    (hC : IsJordanCurve C) (hC' : IsJordanCurve C') (hfg : IsHomeoOn f g C C') :
    ∃ F : Plane ≃ₜ Plane, EqOn F f C :=
  jordan_schoenflies_homeomorph_of_squareExtension squareExtension hC hC' hfg

/-- **The blueprint's bundled statement.** Every homeomorphism between two
Jordan curves extends to a self-homeomorphism of the plane.
@isnad1 id=ex.2h3v.s9.e0f57ec651e7 from=translated src=- shape=0dd5b5e8 vocab=4613aa4d
-/
theorem jordan_schoenflies_of_homeomorph
    (hC : IsJordanCurve C) (hC' : IsJordanCurve C') (e : ↥C ≃ₜ ↥C') :
    ∃ F : Plane ≃ₜ Plane, ∀ z : ↥C, F z = e z :=
  jordan_schoenflies_of_homeomorph_of_squareExtension squareExtension hC hC' e

end Schoenflies
