/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Finite
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Flat
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Affine
import Tengoku.Seed.AlgebraicGeometry.Morphisms.FlatDescent
import Tengoku.Seed.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Tengoku.Seed.AlgebraicGeometry.Morphisms.FinitePresentation
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Proper
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Smooth
import Tengoku.Seed.AlgebraicGeometry.Morphisms.ClosedImmersion
import Tengoku.Seed.AlgebraicGeometry.PullbackCarrier
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Etale
import Tengoku.Seed.AlgebraicGeometry.Morphisms.UnderlyingMap
import Tengoku.Seed.AlgebraicGeometry.Morphisms.QuasiCompact

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `IsStableUnderBaseChangeAlong` / `RespectsIso` for the standard morphism properties

**v4.33 bump compatibility.** Mathlib derives both

* `[P.IsStableUnderBaseChange] → P.IsStableUnderBaseChangeAlong f`
  (`CategoryTheory/MorphismProperty/Limits.lean`), and
* `[P.IsStableUnderBaseChange] → P.RespectsIso` (priority 900, same file),

but neither derivation fires by unification for the `AlgebraicGeometry` properties on this
pin, even with the relevant `IsStableUnderBaseChange` instance in scope — this was checked
in isolation for `@Surjective`. Supplying the instances at each concrete property makes them
fire; this file does that once so the ~20 affected call sites across `ModularCurves` need
only an import.

Delete this file when the derivations fire again upstream.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace ModularCurves.BumpCompat

/--
@isnad1 id=isstable.0h3v.s4.cce2f20885cd from=translated src=- shape=37c43956 vocab=f1368f25
-/
instance stableAlong_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@Surjective) f :=
  ⟨fun pb hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩

/--
@isnad1 id=isstable.0h3v.s4.5e961e2875a9 from=translated src=- shape=37c43956 vocab=83cffd0a
-/
instance stableAlong_flat {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@Flat) f :=
  ⟨fun pb hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩

/--
@isnad1 id=isstable.0h3v.s4.415a8764a496 from=translated src=- shape=37c43956 vocab=f31f160f
-/
instance stableAlong_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@IsFinite) f :=
  ⟨fun pb hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩

/--
@isnad1 id=isstable.0h3v.s4.64ae88e5fe66 from=translated src=- shape=37c43956 vocab=b4f6656f
-/
instance stableAlong_isProper {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@IsProper) f :=
  ⟨fun pb hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩

/--
@isnad1 id=isstable.0h3v.s4.0679ede323c5 from=translated src=- shape=37c43956 vocab=600da424
-/
instance stableAlong_isClosedImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@IsClosedImmersion) f :=
  ⟨fun pb hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩

/--
@isnad1 id=isstable.0h4v.s4.e23465a5a2a1 from=translated src=- shape=8f06bb0c vocab=00c1402d
-/
instance stableAlong_smoothOfRelativeDimension (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@SmoothOfRelativeDimension n) f :=
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange n
  ⟨fun pb hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩

/--
@isnad1 id=respects.0h0v.s2.6ff5fb252fa4 from=translated src=- shape=25b03439 vocab=3b89c278
-/
instance respectsIso_isFinite : MorphismProperty.RespectsIso (@IsFinite) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

/--
@isnad1 id=respects.0h0v.s2.5abf6af9effa from=translated src=- shape=25b03439 vocab=5e847331
-/
instance respectsIso_flat : MorphismProperty.RespectsIso (@Flat) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=iszarisk.0h0v.s1.1212a7033b92 from=translated src=- shape=49959d42 vocab=1fd353b0
-/
instance zariskiLocalAtTarget_isFinite : IsZariskiLocalAtTarget (@IsFinite) :=
  inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=hasaffin.0h0v.s10.e8f2d09dd046 from=translated src=- shape=e5782ca2 vocab=7a13cec1
-/
instance hasAffineProperty_isFinite : HasAffineProperty (@IsFinite)
    (fun X _ f _ ↦ IsAffine X ∧ RingHom.Finite (Scheme.Hom.appTop f).hom) :=
  inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=iszarisk.0h0v.s1.08b92d863a5b from=translated src=- shape=49959d42 vocab=f2bfcad3
-/
instance zariskiLocalAtTarget_etale : IsZariskiLocalAtTarget (@Etale) :=
  inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=respects.0h0v.s2.49d37709cc2c from=translated src=- shape=25b03439 vocab=01bcc068
-/
instance respectsIso_etale : MorphismProperty.RespectsIso (@Etale) :=
  inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=iszarisk.0h0v.s1.6eea9d28f03b from=translated src=- shape=49959d42 vocab=a24ed770
-/
instance zariskiLocalAtTarget_flat : IsZariskiLocalAtTarget (@Flat) :=
  inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=respects.0h0v.s2.d368daf8f18c from=translated src=- shape=25b03439 vocab=23b3cd91
-/
instance respectsIso_formallyUnramified :
    MorphismProperty.RespectsIso (@FormallyUnramified) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

/--
@isnad1 id=isstable.0h3v.s4.aa74fd2dc6ed from=translated src=- shape=37c43956 vocab=7231933b
-/
instance stableAlong_quasiCompact {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@QuasiCompact) f :=
  ⟨fun pb hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩

/--
@isnad1 id=isstable.0h3v.s4.e3649e62b94a from=translated src=- shape=37c43956 vocab=d204bfc3
-/
instance stableAlong_etale {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@Etale) f :=
  ⟨fun pb hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=iszarisk.0h0v.s1.7eb3be95d322 from=translated src=- shape=49959d42 vocab=f4ef4bf7
-/
instance zariskiLocalAtSource_locallyOfFinitePresentation :
    IsZariskiLocalAtSource (@LocallyOfFinitePresentation) :=
  inferInstance

end ModularCurves.BumpCompat
