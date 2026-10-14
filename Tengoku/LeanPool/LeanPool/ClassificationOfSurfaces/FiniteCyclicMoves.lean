/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.FiniteCyclicP2
public import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.FiniteCyclicRealization
import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.FiniteCyclicSignedRealization
public import Tengoku

/-!
# Finite cyclic move closures

This file combines signed presentation isomorphisms and the two primitive Gallier--Xu
subdivisions into stable closure APIs.

`Subdivides` is the directed reflexive-transitive closure. It preserves ordinary validity,
connectivity, and Gallier validity. `HasCommonSubdivision P Q` supplies a validity-safe common
target for topological comparison: starting with two ordinary-valid presentations, both forward
chains remain ordinary-valid. This is stronger operational data than an unrestricted symmetric
move chain, which may pass through the exceptional empty-word sphere where
`PolygonalRealization` is deliberately unavailable.

`MoveEquivalent` is also provided as the purely syntactic equivalence closure. A common
subdivision implies move equivalence, but no converse or confluence theorem is asserted here.
-/

@[expose] public section

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

/-- One directed presentation step: a signed isomorphism, P1 subdivision, or P2 subdivision. -/
def SubdivisionStep (P Q : FiniteCyclicPresentation) : Prop :=
  Nonempty (SignedPresentationIso P Q) ∨
    P1Subdivision P Q ∨ P2Subdivision P Q

namespace SubdivisionStep

/--
@isnad1 id=subdivis.0h3v.s3.4f956bc31f67 from=translated src=- shape=8584b719 vocab=ef773203
-/
theorem signedIso {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) :
    SubdivisionStep P Q :=
  Or.inl ⟨e⟩

/--
@isnad1 id=subdivis.1h2v.s3.6a1a7fb2c3c4 from=translated src=- shape=8584b719 vocab=12827b2d
-/
theorem p1 {P Q : FiniteCyclicPresentation}
    (h : P1Subdivision P Q) :
    SubdivisionStep P Q :=
  Or.inr (Or.inl h)

/--
@isnad1 id=subdivis.1h2v.s3.dbc922170b30 from=translated src=- shape=8584b719 vocab=f1e5b0f4
-/
theorem p2 {P Q : FiniteCyclicPresentation}
    (h : P2Subdivision P Q) :
    SubdivisionStep P Q :=
  Or.inr (Or.inr h)

/-- Every directed step preserves ordinary surface incidence validity.
@isnad1 id=issurfac.2h2v.s3.f4ba514b6aca from=translated src=- shape=a72c41e2 vocab=6bd705db
-/
theorem isSurfaceValid {P Q : FiniteCyclicPresentation}
    (hPQ : SubdivisionStep P Q) (validP : P.IsSurfaceValid) :
    Q.IsSurfaceValid := by
  rcases hPQ with hIso | hrest
  · rcases hIso with ⟨e⟩
    exact e.isSurfaceValid validP
  · rcases hrest with hP1 | hP2
    · exact hP1.isSurfaceValid validP
    · exact hP2.isSurfaceValid validP

/-- Every directed step preserves face-incidence connectivity.
@isnad1 id=isconnec.2h2v.s3.9158c3487855 from=translated src=- shape=a72c41e2 vocab=d5b796cc
-/
theorem isConnected {P Q : FiniteCyclicPresentation}
    (hPQ : SubdivisionStep P Q) (connectedP : P.IsConnected) :
    Q.IsConnected := by
  rcases hPQ with hIso | hrest
  · rcases hIso with ⟨e⟩
    exact e.isConnected connectedP
  · rcases hrest with hP1 | hP2
    · exact hP1.isConnected connectedP
    · exact hP2.isConnected connectedP

/-- Every directed step preserves the packed Gallier--Xu validity predicate.
@isnad1 id=isgallie.2h2v.s3.e7f84095ff63 from=translated src=- shape=a72c41e2 vocab=59cb7b39
-/
theorem isGallierValid {P Q : FiniteCyclicPresentation}
    (hPQ : SubdivisionStep P Q) (validP : P.IsGallierValid) :
    Q.IsGallierValid := by
  rcases hPQ with hIso | hrest
  · rcases hIso with ⟨e⟩
    exact e.isGallierValid validP
  · rcases hrest with hP1 | hP2
    · exact hP1.isGallierValid validP
    · exact hP2.isGallierValid validP

end SubdivisionStep

/-- Directed finite subdivision by signed isomorphisms, P1, and P2. -/
def Subdivides (P Q : FiniteCyclicPresentation) : Prop :=
  Relation.ReflTransGen SubdivisionStep P Q

namespace Subdivides

/--
@isnad1 id=subdivid.0h1v.s2.50988d294bca from=translated src=- shape=b3bac8d8 vocab=f178854a
-/
theorem refl (P : FiniteCyclicPresentation) : Subdivides P P :=
  Relation.ReflTransGen.refl

/--
@isnad1 id=subdivid.1h2v.s3.50d054460d18 from=translated src=- shape=8584b719 vocab=beb4d606
-/
theorem single {P Q : FiniteCyclicPresentation}
    (h : SubdivisionStep P Q) : Subdivides P Q :=
  Relation.ReflTransGen.single h

/--
@isnad1 id=subdivid.0h3v.s3.f40bf4bab0eb from=translated src=- shape=8584b719 vocab=57a4a55f
-/
theorem signedIso {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) : Subdivides P Q :=
  single (SubdivisionStep.signedIso e)

/--
@isnad1 id=subdivid.1h2v.s3.a4b589a7b11b from=translated src=- shape=8584b719 vocab=9a96b21a
-/
theorem p1 {P Q : FiniteCyclicPresentation}
    (h : P1Subdivision P Q) : Subdivides P Q :=
  single (SubdivisionStep.p1 h)

/--
@isnad1 id=subdivid.1h2v.s3.158fabc1e3fb from=translated src=- shape=8584b719 vocab=675f2ea8
-/
theorem p2 {P Q : FiniteCyclicPresentation}
    (h : P2Subdivision P Q) : Subdivides P Q :=
  single (SubdivisionStep.p2 h)

/--
@isnad1 id=subdivid.2h3v.s4.488b7fbca820 from=translated src=- shape=0bc0c4a6 vocab=f178854a
-/
theorem trans {P Q R : FiniteCyclicPresentation}
    (hPQ : Subdivides P Q) (hQR : Subdivides Q R) :
    Subdivides P R :=
  Relation.ReflTransGen.trans hPQ hQR

/-- Directed subdivision chains preserve ordinary surface incidence validity.
@isnad1 id=issurfac.2h2v.s3.c2d200b7eae0 from=translated src=- shape=a72c41e2 vocab=8670c005
-/
theorem isSurfaceValid {P Q : FiniteCyclicPresentation}
    (hPQ : Subdivides P Q) (validP : P.IsSurfaceValid) :
    Q.IsSurfaceValid := by
  induction hPQ with
  | refl =>
      exact validP
  | tail _ hstep ih =>
      exact hstep.isSurfaceValid ih

/-- Directed subdivision chains preserve face-incidence connectivity.
@isnad1 id=isconnec.2h2v.s3.aaa31441eb25 from=translated src=- shape=a72c41e2 vocab=83159d66
-/
theorem isConnected {P Q : FiniteCyclicPresentation}
    (hPQ : Subdivides P Q) (connectedP : P.IsConnected) :
    Q.IsConnected := by
  induction hPQ with
  | refl =>
      exact connectedP
  | tail _ hstep ih =>
      exact hstep.isConnected ih

/-- Directed subdivision chains preserve Gallier validity.
@isnad1 id=isgallie.2h2v.s3.19cbd141319b from=translated src=- shape=a72c41e2 vocab=432a71da
-/
theorem isGallierValid {P Q : FiniteCyclicPresentation}
    (hPQ : Subdivides P Q) (validP : P.IsGallierValid) :
    Q.IsGallierValid := by
  induction hPQ with
  | refl =>
      exact validP
  | tail _ hstep ih =>
      exact hstep.isGallierValid ih

end Subdivides

/-- Two presentations have a common directed subdivision. -/
def HasCommonSubdivision (P Q : FiniteCyclicPresentation) : Prop :=
  ∃ R : FiniteCyclicPresentation, Subdivides P R ∧ Subdivides Q R

namespace HasCommonSubdivision

/--
@isnad1 id=hascommo.0h1v.s2.816773e72145 from=translated src=- shape=b3bac8d8 vocab=6efa8b5b
-/
theorem refl (P : FiniteCyclicPresentation) : HasCommonSubdivision P P :=
  ⟨P, Subdivides.refl P, Subdivides.refl P⟩

/--
@isnad1 id=hascommo.1h2v.s3.7af51c52dab9 from=translated src=- shape=7e524d71 vocab=6efa8b5b
-/
theorem symm {P Q : FiniteCyclicPresentation}
    (h : HasCommonSubdivision P Q) :
    HasCommonSubdivision Q P := by
  rcases h with ⟨R, hPR, hQR⟩
  exact ⟨R, hQR, hPR⟩

end HasCommonSubdivision

/-- Purely syntactic equivalence generated by signed isomorphisms, P1, and P2. -/
def MoveEquivalent (P Q : FiniteCyclicPresentation) : Prop :=
  Relation.EqvGen SubdivisionStep P Q

namespace MoveEquivalent

/--
@isnad1 id=moveequi.0h1v.s2.337043fca987 from=translated src=- shape=b3bac8d8 vocab=8802753a
-/
theorem refl (P : FiniteCyclicPresentation) : MoveEquivalent P P :=
  Relation.EqvGen.refl P

/--
@isnad1 id=moveequi.1h2v.s3.905984fb31d7 from=translated src=- shape=8584b719 vocab=53d9cbec
-/
theorem ofStep {P Q : FiniteCyclicPresentation}
    (h : SubdivisionStep P Q) : MoveEquivalent P Q :=
  Relation.EqvGen.rel P Q h

/--
@isnad1 id=moveequi.1h2v.s3.6b5640541e6b from=translated src=- shape=7e524d71 vocab=8802753a
-/
theorem symm {P Q : FiniteCyclicPresentation}
    (h : MoveEquivalent P Q) : MoveEquivalent Q P :=
  Relation.EqvGen.symm P Q h

/--
@isnad1 id=moveequi.2h3v.s4.5f535cbb9667 from=translated src=- shape=0bc0c4a6 vocab=8802753a
-/
theorem trans {P Q R : FiniteCyclicPresentation}
    (hPQ : MoveEquivalent P Q) (hQR : MoveEquivalent Q R) :
    MoveEquivalent P R :=
  Relation.EqvGen.trans P Q R hPQ hQR

end MoveEquivalent

/-- Every directed subdivision chain is a syntactic move equivalence.
@isnad1 id=moveequi.1h2v.s3.64d16c289ae6 from=translated src=- shape=8584b719 vocab=055fa60c
-/
theorem Subdivides.moveEquivalent {P Q : FiniteCyclicPresentation}
    (hPQ : Subdivides P Q) :
    MoveEquivalent P Q := by
  induction hPQ with
  | refl =>
      exact MoveEquivalent.refl P
  | @tail Q R _ hstep ih =>
      exact ih.trans (MoveEquivalent.ofStep hstep)

/-- A common directed subdivision is in particular a syntactic move equivalence.
@isnad1 id=moveequi.1h2v.s3.c63db1a42c3f from=translated src=- shape=8584b719 vocab=75ec9158
-/
theorem HasCommonSubdivision.moveEquivalent
    {P Q : FiniteCyclicPresentation} (h : HasCommonSubdivision P Q) :
    MoveEquivalent P Q := by
  rcases h with ⟨R, hPR, hQR⟩
  exact hPR.moveEquivalent.trans hQR.moveEquivalent.symm

namespace PolygonallyEquivalent

/--
@isnad1 id=polygona.1h1v.s3.001cc9e27811 from=translated src=- shape=afaf5e02 vocab=e76bf322
-/
theorem refl (P : FiniteCyclicPresentation) (validP : P.IsSurfaceValid) :
    P.PolygonallyEquivalent P validP validP :=
  ⟨Homeomorph.refl _⟩

/--
@isnad1 id=polygona.3h2v.s4.079424965342 from=translated src=- shape=a4b3d380 vocab=e76bf322
-/
theorem symm {P Q : FiniteCyclicPresentation}
    {validP : P.IsSurfaceValid} {validQ : Q.IsSurfaceValid}
    (h : P.PolygonallyEquivalent Q validP validQ) :
    Q.PolygonallyEquivalent P validQ validP := by
  rcases h with ⟨e⟩
  exact ⟨e.symm⟩

/--
@isnad1 id=polygona.5h3v.s5.c053b03f2ccb from=translated src=- shape=f1fce897 vocab=e76bf322
-/
theorem trans {P Q R : FiniteCyclicPresentation}
    {validP : P.IsSurfaceValid} {validQ : Q.IsSurfaceValid}
    {validR : R.IsSurfaceValid}
    (hPQ : P.PolygonallyEquivalent Q validP validQ)
    (hQR : Q.PolygonallyEquivalent R validQ validR) :
    P.PolygonallyEquivalent R validP validR := by
  rcases hPQ with ⟨ePQ⟩
  rcases hQR with ⟨eQR⟩
  exact ⟨ePQ.trans eQR⟩

end PolygonallyEquivalent

/-- The stable proof obligation for primitive realization invariance.

The P1 and P2 realization files discharge the corresponding disjuncts; signed isomorphisms are
already implemented by `SignedPresentationIso.polygonallyEquivalent`. -/
def SubdivisionStep.PreservesPolygonalRealization : Prop :=
  ∀ {P Q : FiniteCyclicPresentation}, SubdivisionStep P Q →
    ∀ (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid),
      P.PolygonallyEquivalent Q validP validQ

/-- The realization-invariance obligation isolated to P1 subdivisions. -/
def P1Subdivision.PreservesPolygonalRealization : Prop :=
  ∀ {P Q : FiniteCyclicPresentation}, P1Subdivision P Q →
    ∀ (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid),
      P.PolygonallyEquivalent Q validP validQ

/-- The realization-invariance obligation isolated to P2 subdivisions. -/
def P2Subdivision.PreservesPolygonalRealization : Prop :=
  ∀ {P Q : FiniteCyclicPresentation}, P2Subdivision P Q →
    ∀ (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid),
      P.PolygonallyEquivalent Q validP validQ

/-- Signed-isomorphism invariance plus the two primitive geometric obligations supplies invariance
for every directed elementary step.
@isnad1 id=preserve.2h0v.s2.449d8932cd88 from=translated src=- shape=f443e7c7 vocab=951a907d
-/
theorem SubdivisionStep.preservesPolygonalRealization
    (hP1 : P1Subdivision.PreservesPolygonalRealization)
    (hP2 : P2Subdivision.PreservesPolygonalRealization) :
    SubdivisionStep.PreservesPolygonalRealization := by
  intro P Q hstep validP validQ
  rcases hstep with hIso | hrest
  · rcases hIso with ⟨e⟩
    exact e.polygonallyEquivalent validP validQ
  · rcases hrest with hP1Step | hP2Step
    · exact hP1 hP1Step validP validQ
    · exact hP2 hP2Step validP validQ

/-- If every primitive directed step preserves the faithful polygonal quotient, so does every
directed subdivision chain.
@isnad1 id=polygona.4h2v.s4.ee0cf65d7c1e from=translated src=- shape=9d24700d vocab=be0c29bf
-/
theorem Subdivides.polygonallyEquivalent
    (hprimitive : SubdivisionStep.PreservesPolygonalRealization)
    {P Q : FiniteCyclicPresentation} (hPQ : Subdivides P Q)
    (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid) :
    P.PolygonallyEquivalent Q validP validQ := by
  induction hPQ with
  | refl =>
      exact PolygonallyEquivalent.refl P validP
  | @tail R Q hPR hstep ih =>
      let validR : R.IsSurfaceValid :=
        Subdivides.isSurfaceValid hPR validP
      exact (ih validR).trans (hprimitive hstep validR validQ)

/-- Primitive realization invariance promotes a common-subdivision certificate to a
homeomorphism of faithful polygonal quotients.
@isnad1 id=polygona.4h2v.s4.9777b8b1448d from=translated src=- shape=9d24700d vocab=025cdc52
-/
theorem HasCommonSubdivision.polygonallyEquivalent
    (hprimitive : SubdivisionStep.PreservesPolygonalRealization)
    {P Q : FiniteCyclicPresentation} (h : HasCommonSubdivision P Q)
    (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid) :
    P.PolygonallyEquivalent Q validP validQ := by
  rcases h with ⟨R, hPR, hQR⟩
  let validR : R.IsSurfaceValid :=
    Subdivides.isSurfaceValid hPR validP
  exact
    (hPR.polygonallyEquivalent hprimitive validP validR).trans
      (hQR.polygonallyEquivalent hprimitive validQ validR).symm

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
