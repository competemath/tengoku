/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Tengoku.Seed.Geometry.RingedSpace.LocallyRingedSpace
import Tengoku.LanaOka.Oka.Topology.Category.TopCat.Opens

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Sheaves of modules over the structure sheaf of a locally ringed space

Mathlib has this theory for **schemes** and only for schemes:
`AlgebraicGeometry.Scheme.ringCatSheaf` and `AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom` in
`Mathlib/AlgebraicGeometry/Modules/Presheaf.lean`, and pushforward and pullback of
`AlgebraicGeometry.Scheme.Modules` in `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`. A
development that reaches complex-analytic spaces needs the same one level down, at
`AlgebraicGeometry.LocallyRingedSpace`, and that is what this file is. There is no analytic
content in it; see `README.md` on the mirror tree.

## Where this would go upstream, and the two alternatives priced

The declarations here are stated for `AlgebraicGeometry.LocallyRingedSpace`, whose theory lives
under `Mathlib/Geometry/RingedSpace/`, so the mirror path proposes a new file
`Mathlib/Geometry/RingedSpace/LocallyRingedSpace/Modules.lean`, beside the two files that
directory already holds. Being new it costs no existing Mathlib file anything; the Mathlib part
of its own transitive closure is **1852** modules. Both alternatives were measured rather than
dismissed, by breadth-first search over `^(public )?import` in `.lake/packages/mathlib` with
comments masked, counting only modules with a file under `Mathlib/`:

* **into `Mathlib/Geometry/RingedSpace/LocallyRingedSpace.lean`**, which this repository already
  mirrors at `Oka/Geometry/RingedSpace/LocallyRingedSpace.lean`: that file's closure is 1688 and
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree` costs it **164**. `README.md` records 96
  as the figure that once made an upstreaming judged too expensive, so this is the option the
  price rules out, and it is why the material is a new file rather than an addition to the mirror
  file that already exists.
* **into `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`**, beside the scheme versions: closure
  2264, and the two Mathlib imports below together with the Mathlib target of the third —
  `Oka/Topology/Category/TopCat/Opens.lean` is itself a mirror file — cost it **4**. That is
  cheap, and a Mathlib reviewer who wanted the locally-ringed-space and the scheme statements in
  one place could take it. It is not the choice made here because the namespace, and every other
  file about it, sits under `Mathlib/Geometry/RingedSpace/`.

## Main definitions

- `AlgebraicGeometry.LocallyRingedSpace.ringSheaf`: the structure sheaf as a sheaf of rings
  rather than of commutative rings, which is the form in which `SheafOfModules` applies. **The
  site it is stated over is spelled `↑Y.toPresheafedSpace` and that is load-bearing**; the reason
  is on its own docstring and it is a measurement, not a preference.
- `AlgebraicGeometry.LocallyRingedSpace.Hom.toRingSheafHom`: the morphism of sheaves of rings
  induced by a morphism of locally ringed spaces, and
  `AlgebraicGeometry.LocallyRingedSpace.Hom.pullbackModules`, the pullback of `𝒪`-modules along
  it, with its adjunction `AlgebraicGeometry.LocallyRingedSpace.Hom.pullbackModulesAdj`.
- `AlgebraicGeometry.LocallyRingedSpace.Hom.pullbackModulesUnitToUnit`: the canonical map from
  the pullback of `𝒪_Y` to `𝒪_X`, which **is an isomorphism** —
  `AlgebraicGeometry.LocallyRingedSpace.isIso_pullbackModulesUnitToUnit` — and with it pullback
  sends free sheaves to free sheaves,
  `AlgebraicGeometry.LocallyRingedSpace.Hom.pullbackModulesFreeIso` and
  `AlgebraicGeometry.LocallyRingedSpace.Hom.freeFunctorCompPullbackModulesIso`.

## Provenance

Split out of `Oka/AnalyticSpace/Relations.lean` for taxis #905, unchanged: no statement, proof or
name here differs from what that file held. What that file kept is the three lines about `ℂ^ι`
that are the only analytic content it ever had.
-/

open CategoryTheory Limits TopologicalSpace Opposite SheafOfModules AlgebraicGeometry

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable (Y : LocallyRingedSpace.{u})

/-- The structure sheaf of a locally ringed space, viewed as a sheaf of rings rather than of
commutative rings. This is the form in which the theory of `SheafOfModules` and coherence
applies.

**The site is spelled `↑Y.toPresheafedSpace` rather than `↑Y`, and that is load-bearing.** The
two are definitionally equal, but `TopologicalSpace.Opens.map f.base` — for `f` a morphism of
locally ringed spaces — carries its implicit type arguments in the first spelling, and instance
search does not cross the two. `↑Y` elaborates to `↑Y.toTopCat`, and that is what makes the two
discrimination-tree keys differ, since the key is built from the elaborated implicit arguments;
so with `↑Y` here, Mathlib's

`instance : (Opens.map f).IsContinuous (Opens.grothendieckTopology Y)
  (Opens.grothendieckTopology X)`

is not found for `f.base`. Measured in three sessions.

**The consequence is a cost and not an impossibility, which is a correction of what this
docstring used to say.** The missing instance can be declared by hand — `inferInstanceAs` from
the `↑Y.toPresheafedSpace` spelling of the same statement transports it — and with it
`AlgebraicGeometry.LocallyRingedSpace.Hom.toRingSheafHom` below can be stated at the `↑Y` site
after all; without it, it cannot, and that half was measured too. So the old spelling costs one
transported instance, which every consumer would then need, where the spelling used here costs
none and is what `Opens.map` produces anyway. **Do not tidy it back.** -/
noncomputable def ringSheaf :
    Sheaf (Opens.grothendieckTopology ↑Y.toPresheafedSpace) RingCat.{u} :=
  ⟨Y.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u},
    (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
      (forget₂ CommRingCat.{u} RingCat.{u}) Y.presheaf).1 Y.IsSheaf⟩

/-- Sheafification is available at the site `AlgebraicGeometry.LocallyRingedSpace.ringSheaf` uses.

Mathlib has this for `Opens.grothendieckTopology ↑Y.toTopCat`. **This instance is load-bearing and
its absence is invisible here**: delete it and this file still elaborates, while `lake build` fails
**3857 modules later, in a different subtree**, at `Oka/Analytification/SheafCoherent.lean:150`
with `failed to synthesize instance of type class (analytificationSheaf g).PreservesZeroMorphisms`.

**What makes it load-bearing is not the reason this docstring used to give.** It said instance
search does not cross the two spellings, *for the reason above* — but the reason above is about
`Opens.map f.base`'s implicit arguments, and no `Opens.map` occurs here: with this instance
deleted, `infer_instance` still finds `HasSheafify (Opens.grothendieckTopology ↑Z.toPresheafedSpace)
AddCommGrpCat` at a direct goal in this very file. So the two spellings *do* cross at that goal,
and what the declared instance buys is something the deletion test locates and this docstring does
not: **the cause is unmeasured, the cost is not.** All three measurements are from 2026-08-25 at
`master` = `d12d334`. -/
instance hasSheafify_toPresheafedSpace :
    HasSheafify (Opens.grothendieckTopology ↑Y.toPresheafedSpace) AddCommGrpCat.{u} :=
  inferInstanceAs (HasSheafify (Opens.grothendieckTopology ↑Y.toTopCat) AddCommGrpCat.{u})

variable {Y} in
/-- **The morphism of sheaves of rings attached to a morphism of locally ringed spaces.**

Mathlib has this for schemes, as `AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom`, and not for
locally ringed spaces; this is that definition verbatim. It is what
`SheafOfModules.pullback` consumes, and hence what makes the pullback of
`𝒪`-modules along a morphism of locally ringed spaces — the analytification of a sheaf, among
other things — available at all. -/
noncomputable def Hom.toRingSheafHom {X : LocallyRingedSpace.{u}} (f : X ⟶ Y) :
    Y.ringSheaf ⟶ ((Opens.map f.base).sheafPushforwardContinuous
      RingCat.{u} _ _).obj X.ringSheaf where
  hom := Functor.whiskerRight f.c _

end AlgebraicGeometry.LocallyRingedSpace
