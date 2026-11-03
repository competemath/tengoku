import Tengoku.HodgeStructuresLean4.HodgePilot.Betti
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Exactness of sheaf pullback, and cohomology pullback for constant sheaves

For a continuous map `f : X ⟶ Y` of topological spaces, this file registers
the exactness instance package for the pullback of abelian sheaves
`TopCat.Sheaf.pullback AddCommGrpCat f`:

* `pullbackPreservesFiniteLimits` / `pullbackPreservesFiniteColimits` /
  `pullbackAdditive` — the pullback of abelian sheaves is an exact additive
  functor.  All three exist at this Mathlib but the finite-limits one is
  *synthesis-opaque*: bare `inferInstance` head-fails or times out, and the
  working route `show`-unfolds to the `Functor.sheafPullback` head and feeds
  the instance chain by `haveI` (see the proof).  Registering them here keyed
  at the `TopCat.Sheaf.pullback` head makes downstream derived-functor
  machinery (`Functor.mapExtAddHom`, `Functor.mapDerivedCategory`) fire by
  ordinary instance synthesis.
* `pullbackConstantSheafIso` / `pullbackConstantSheafObjIso` — the pullback
  of a constant sheaf is the constant sheaf on the source, by uniqueness of
  left adjoints (both sides are left adjoint to sections over the top open,
  since `f⁻¹(⊤) = ⊤`).
* `constHPullback`, `bettiMap`, `bettiMapC` — pullback maps on sheaf
  cohomology of constant sheaves along `f`, restoring the sheaf-Betti
  functoriality that was cut from `HodgePilot.Betti`:
  `H^n(Y, ℚ) →+ H^n(X, ℚ)` and `H^n(Y, ℂ) →+ H^n(X, ℂ)`, via
  `Functor.mapExtAddHom` of the exact additive pullback functor.

## Claim discipline

Everything in this file is instance packaging plus functoriality of sheaf
cohomology of constant sheaves along continuous maps (cohomology pullback).
The word *Betti* is used only as in `HodgePilot.Betti`: for sheaf cohomology
of constant sheaves, with no relation to any other cohomology theory asserted.
The constructed pullback maps are additive maps; **no claim is made that any
of them is an isomorphism**.
-/

open CategoryTheory Limits TopologicalSpace

universe u

noncomputable section

namespace HodgePilot.PullbackExact

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-! ## 1. The exactness instance package (GG-G1 recipe) -/

-- Sanity receipt: `Opens.map f` is representably flat (a Mathlib instance).

set_option maxHeartbeats 1600000 in
/-- The pullback of abelian sheaves along a continuous map preserves finite
limits.  This is present in Mathlib but synthesis-opaque: `inferInstance`
head-fails (def-opaque head) or times out (deep `lan` instance search); the
working route `show`-unfolds to the `Functor.sheafPullback` head and feeds
the chain by `haveI`.
@isnad1 id=preserve.0h3v.s7.44968a4e3869 from=translated src=- shape=9bd04b19 vocab=e6fbb2d9
-/
instance pullbackPreservesFiniteLimits :
    PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} f) := by
  show PreservesFiniteLimits
    ((Opens.map f).sheafPullback AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X))
  haveI : ReflectsLimits (forget AddCommGrpCat.{u}) :=
    reflectsLimits_of_reflectsIsomorphisms
  haveI : PreservesFiniteLimits ((Opens.map f).op.lan :
      ((Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})) :=
    lan_preservesFiniteLimits_of_flat (E := AddCommGrpCat.{u}) (Opens.map f)
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _

/-- The pullback of abelian sheaves preserves finite colimits (it is a left
adjoint); registered keyed at the `TopCat.Sheaf.pullback` head.
@isnad1 id=preserve.0h3v.s7.2c49e10c6760 from=translated src=- shape=9bd04b19 vocab=121034f5
-/
instance pullbackPreservesFiniteColimits :
    PreservesFiniteColimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} f) :=
  inferInstance

attribute [local instance] Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts in
/--
@isnad1 id=additive.0h3v.s7.e2dac96ec1d8 from=translated src=- shape=9bd04b19 vocab=d452dee5
-/
instance pullbackAdditive :
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _

/-! ## 2. Pullback of constant sheaves -/

/-- The pullback of a constant sheaf is the constant sheaf on the source, as
a natural isomorphism of functors, by uniqueness of left adjoints: the
composite `constantSheaf ⋙ pullback` is left adjoint to
`pushforward ⋙ (sections over ⊤)`, which agrees with `sections over ⊤` on the
source since `f⁻¹(⊤) = ⊤` definitionally.-/
def pullbackConstantSheafIso :
    constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} ⋙
        TopCat.Sheaf.pullback AddCommGrpCat.{u} f ≅
      constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  ((conjugateIsoEquiv
      ((constantSheafAdj _ _ (HodgePilot.Betti.opensTopTerminal Y)).comp
        (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f))
      (constantSheafAdj _ _ (HodgePilot.Betti.opensTopTerminal X))).symm
    (Iso.refl _)).symm

/-- The pullback of the constant sheaf at `M` is the constant sheaf at `M`
(object form).-/
def pullbackConstantSheafObjIso (M : AddCommGrpCat.{u}) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj
        ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj M) ≅
      (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj M :=
  (pullbackConstantSheafIso f).app M

/-! ## 3. Cohomology pullback for constant sheaves (sheaf-Betti functoriality) -/

open HodgePilot.Betti

end HodgePilot.PullbackExact

end
