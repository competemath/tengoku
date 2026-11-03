import Tengoku.AlbertFrameTripleInvariants.AlbertLean.AutomorphismLaws
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.FrameLaws

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Full automorphism transport of ordered frames

This module supplies the elementary groupoid structure of the existing
`JordanAut` transport relation.  It also records that the literal ordered
projectors, frame laws, ledger, and trace-cube detector are natural under a
full unital product automorphism.  No transitivity assertion about arbitrary
frames is made: `FullRelated X Y` explicitly carries its automorphism witness.
-/

noncomputable section

namespace AlbertLean

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000

namespace JordanAut

/-- The identity unital product automorphism.-/
def id : JordanAut where
  toLinearEquiv := LinearEquiv.refl ℚ Coord
  map_one := rfl
  map_circle := by
    intro x y
    rfl

/-- Composition, with `comp g h` acting as `g` after `h`.-/
def comp (g h : JordanAut) : JordanAut where
  toLinearEquiv := h.toLinearEquiv.trans g.toLinearEquiv
  map_one := by
    change g.toLinearEquiv (h.toLinearEquiv one) = one
    rw [h.map_one, g.map_one]
  map_circle := by
    intro x y
    change g.toLinearEquiv (h.toLinearEquiv (structuredProduct x y)) =
      structuredProduct (g.toLinearEquiv (h.toLinearEquiv x))
        (g.toLinearEquiv (h.toLinearEquiv y))
    rw [h.map_circle, g.map_circle]

/-- The inverse unital product automorphism.-/
def inv (g : JordanAut) : JordanAut where
  toLinearEquiv := g.toLinearEquiv.symm
  map_one := by
    apply g.toLinearEquiv.injective
    rw [g.map_one]
    exact g.toLinearEquiv.apply_symm_apply one
  map_circle := by
    intro x y
    apply g.toLinearEquiv.injective
    rw [g.map_circle]
    simp

/--
@isnad1 id=eq.0h1v.s7.20add5e49613 from=translated src=- shape=72cd885a vocab=da393729
-/
@[simp] theorem id_apply (x : Coord) : id x = x := rfl

/--
@isnad1 id=eq.0h3v.s9.2d244a7e706c from=translated src=- shape=4451d468 vocab=2fe6ef2c
-/
@[simp] theorem comp_apply (g h : JordanAut) (x : Coord) :
    comp g h x = g (h x) := rfl

/--
@isnad1 id=eq.0h2v.s8.eb7a85af7b1d from=translated src=- shape=3d824fd6 vocab=dc63d206
-/
@[simp] theorem inv_apply (g : JordanAut) (x : Coord) :
    inv g x = g.toLinearEquiv.symm x := rfl

/--
@isnad1 id=eq.0h2v.s8.263cc89f5256 from=translated src=- shape=6efc61d7 vocab=7deb85ae
-/
@[simp] theorem inv_apply_apply (g : JordanAut) (x : Coord) :
    inv g (g x) = x := g.toLinearEquiv.symm_apply_apply x

/--
@isnad1 id=eq.0h2v.s8.56fea9b2c87a from=translated src=- shape=2732e55a vocab=7deb85ae
-/
@[simp] theorem apply_inv_apply (g : JordanAut) (x : Coord) :
    g (inv g x) = x := g.toLinearEquiv.apply_symm_apply x

/-- Every ordered spectral projector is natural under a full automorphism.
@isnad1 id=eq.0h3v.s8.700a89e179c6 from=translated src=- shape=34a4e799 vocab=93a806db
-/
theorem map_projector (g : JordanAut) (c : Coord) (i : Fin 3) :
    g (projector c i) = projector (g c) i := by
  fin_cases i
  · change g.toLinearEquiv ((2 : ℚ)⁻¹ •
        (structuredProduct c c - c)) =
      (2 : ℚ)⁻¹ •
        (structuredProduct (g.toLinearEquiv c) (g.toLinearEquiv c) -
          g.toLinearEquiv c)
    rw [map_smul, map_sub, g.map_circle]
  · change g.toLinearEquiv (one - structuredProduct c c) =
      one - structuredProduct (g.toLinearEquiv c) (g.toLinearEquiv c)
    rw [map_sub, g.map_one, g.map_circle]
  · change g.toLinearEquiv ((2 : ℚ)⁻¹ •
        (structuredProduct c c + c)) =
      (2 : ℚ)⁻¹ •
        (structuredProduct (g.toLinearEquiv c) (g.toLinearEquiv c) +
          g.toLinearEquiv c)
    rw [map_smul, map_add, g.map_circle]

end JordanAut

namespace Transports

/-- Identity transports every ordered triple to itself.
@isnad1 id=transpor.0h1v.s2.785a4929e49f from=translated src=- shape=9a349162 vocab=6710f877
-/
theorem refl (X : WitnessTriple) : Transports JordanAut.id X X := by
  exact ⟨rfl, rfl, rfl⟩

/-- Transporters compose in the same order as their actions.
@isnad1 id=transpor.2h5v.s4.4a2d2677aee0 from=translated src=- shape=b908fb11 vocab=865757ee
-/
theorem comp {g h : JordanAut} {X Y Z : WitnessTriple}
    (hXY : Transports h X Y) (hYZ : Transports g Y Z) :
    Transports (JordanAut.comp g h) X Z := by
  rcases hXY with ⟨hXE, hXF, hXK⟩
  rcases hYZ with ⟨hYE, hYF, hYK⟩
  refine ⟨?_, ?_, ?_⟩
  · change g (h X.cE) = Z.cE
    rw [hXE, hYE]
  · change g (h X.cF) = Z.cF
    rw [hXF, hYF]
  · change g (h X.cK) = Z.cK
    rw [hXK, hYK]

/-- Inverting an automorphism reverses an ordered transport.
@isnad1 id=transpor.1h3v.s4.b4d6b03ed4a8 from=translated src=- shape=ea419097 vocab=96052b74
-/
theorem inv {g : JordanAut} {X Y : WitnessTriple}
    (h : Transports g X Y) : Transports (JordanAut.inv g) Y X := by
  rcases h with ⟨hE, hF, hK⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [← hE]
    exact JordanAut.inv_apply_apply g X.cE
  · rw [← hF]
    exact JordanAut.inv_apply_apply g X.cF
  · rw [← hK]
    exact JordanAut.inv_apply_apply g X.cK

end Transports

/-- Two ordered triples are fully related when an actual `JordanAut`
transports all three encoders in their frozen order.-/
def FullRelated (X Y : WitnessTriple) : Prop :=
  ∃ g : JordanAut, Transports g X Y

namespace FullRelated

/--
@isnad1 id=fullrela.0h1v.s2.14f99e88dfe0 from=translated src=- shape=b3bac8d8 vocab=082e4bb6
-/
theorem refl (X : WitnessTriple) : FullRelated X X :=
  ⟨JordanAut.id, Transports.refl X⟩

/--
@isnad1 id=fullrela.1h2v.s3.8f75df41b5e0 from=translated src=- shape=7e524d71 vocab=082e4bb6
-/
theorem symm {X Y : WitnessTriple} (h : FullRelated X Y) :
    FullRelated Y X := by
  rcases h with ⟨g, hg⟩
  exact ⟨JordanAut.inv g, hg.inv⟩

/--
@isnad1 id=fullrela.2h3v.s4.4fe4e9819ca5 from=translated src=- shape=0bc0c4a6 vocab=082e4bb6
-/
theorem trans {X Y Z : WitnessTriple}
    (hXY : FullRelated X Y) (hYZ : FullRelated Y Z) :
    FullRelated X Z := by
  rcases hXY with ⟨h, hh⟩
  rcases hYZ with ⟨g, hg⟩
  exact ⟨JordanAut.comp g h, hh.comp hg⟩

end FullRelated

/-- Full automorphism transport is an equivalence relation on the literal
ordered witness triples.
@isnad1 id=equivale.0h0v.s1.9989d05526c6 from=translated src=- shape=25b03439 vocab=e01f01b7
-/
theorem fullRelated_equivalence : Equivalence FullRelated :=
  ⟨FullRelated.refl, FullRelated.symm, FullRelated.trans⟩

/-- A transporter acts naturally on the encoder selected by any frozen row.
@isnad1 id=eq.1h4v.s7.3df9dc417e42 from=translated src=- shape=05bd0ed1 vocab=a95a49e4
-/
theorem map_encoder_of_transports (g : JordanAut) (X Y : WitnessTriple)
    (h : Transports g X Y) (r : Fin 3) :
    g (encoder X r) = encoder Y r := by
  rcases h with ⟨hE, hF, hK⟩
  fin_cases r
  · change g.toLinearEquiv X.cE = Y.cE
    exact hE
  · change g.toLinearEquiv X.cF = Y.cF
    exact hF
  · change g.toLinearEquiv X.cK = Y.cK
    exact hK

/-- A transporter acts naturally on all nine ordered projectors.
@isnad1 id=eq.1h5v.s7.7f7ae946d689 from=translated src=- shape=cff58ec3 vocab=7cd1b92b
-/
theorem map_projector_of_transports (g : JordanAut) (X Y : WitnessTriple)
    (h : Transports g X Y) (r i : Fin 3) :
    g (projector (encoder X r) i) = projector (encoder Y r) i := by
  rw [JordanAut.map_projector, map_encoder_of_transports g X Y h r]

/-- The printed product trace is invariant under every full automorphism.
@isnad1 id=eq.0h2v.s7.be98827491a6 from=translated src=- shape=2c1368b9 vocab=da374df9
-/
theorem productTrace_invariant (g : JordanAut) (x : Coord) :
    productTrace (g x) = productTrace x := by
  simpa only [productTrace_eq_traceN] using traceN_invariant g x

/-- The printed quadratic coefficient, hence the source `spurN`, is invariant.
@isnad1 id=eq.0h2v.s7.ce8310c92e51 from=translated src=- shape=2c1368b9 vocab=aaa6e64b
-/
theorem spurN_invariant (g : JordanAut) (x : Coord) :
    spurN (g x) = spurN x := by
  rw [← productSpur_eq_spurN, ← productSpur_eq_spurN]
  simp only [productSpur, ← g.map_circle, productTrace_invariant]

/-- The printed cubic coefficient, hence the source cubic norm, is invariant.
@isnad1 id=eq.0h2v.s7.88af07ca98cc from=translated src=- shape=2c1368b9 vocab=a350e0ce
-/
theorem cubicNorm_invariant (g : JordanAut) (x : Coord) :
    cubicNorm (g x) = cubicNorm x := by
  rw [← productNorm_eq_cubicNorm, ← productNorm_eq_cubicNorm]
  simp only [productNorm, ← g.map_circle, productTrace_invariant]

/-- The three printed encoder invariants are preserved in both directions.
@isnad1 id=iff.0h2v.s7.7d38c09016ef from=translated src=- shape=3594e6c6 vocab=ab52f1b7
-/
theorem lawfulEncoder_iff (g : JordanAut) (c : Coord) :
    LawfulEncoder (g c) ↔ LawfulEncoder c := by
  simp only [LawfulEncoder, traceN_invariant, spurN_invariant,
    cubicNorm_invariant]

/-- Full frame lawfulness is preserved in both directions.  `FrameLaws`
reduces this to the three printed encoder invariants.
@isnad1 id=iff.0h2v.s7.6799abad156d from=translated src=- shape=3594e6c6 vocab=6ba8b382
-/
theorem lawfulFrame_iff (g : JordanAut) (c : Coord) :
    LawfulFrame (g c) ↔ LawfulFrame c := by
  constructor
  · intro h
    exact lawfulFrame_of_lawfulEncoder c ((lawfulEncoder_iff g c).mp h.1)
  · intro h
    exact lawfulFrame_of_lawfulEncoder (g c)
      ((lawfulEncoder_iff g c).mpr h.1)

/-- A transported ordered triple is lawful exactly when its source is.
@isnad1 id=iff.1h3v.s4.bb294e43dc55 from=translated src=- shape=8584964e vocab=37f136c1
-/
theorem lawfulFrameTriple_iff_of_transports
    (g : JordanAut) (X Y : WitnessTriple) (h : Transports g X Y) :
    LawfulFrameTriple Y ↔ LawfulFrameTriple X := by
  constructor
  · intro hY r
    have hr : LawfulFrame (g (encoder X r)) := by
      rw [map_encoder_of_transports g X Y h r]
      exact hY r
    exact (lawfulFrame_iff g (encoder X r)).mp hr
  · intro hX r
    have hr := (lawfulFrame_iff g (encoder X r)).mpr (hX r)
    rwa [map_encoder_of_transports g X Y h r] at hr

/-- Pair moments of ordered projectors are invariant.
@isnad1 id=eq.0h5v.s8.2b09feaa6f11 from=translated src=- shape=5bb8d6ac vocab=389fa5ad
-/
theorem projectorPairing_invariant (g : JordanAut)
    (c d : Coord) (i j : Fin 3) :
    traceForm (projector (g c) i) (projector (g d) j) =
      traceForm (projector c i) (projector d j) := by
  rw [← JordanAut.map_projector, ← JordanAut.map_projector,
    traceForm_invariant]

/-- Joint moments of three ordered projectors are invariant.
@isnad1 id=eq.0h7v.s9.9702b9291e87 from=translated src=- shape=c7a9e05d vocab=c43d63c3
-/
theorem projectorJoint_invariant (g : JordanAut)
    (a b c : Coord) (i j l : Fin 3) :
    traceForm (projector (g a) i)
        (structuredProduct (projector (g b) j) (projector (g c) l)) =
      traceForm (projector a i)
        (structuredProduct (projector b j) (projector c l)) := by
  rw [← JordanAut.map_projector, ← JordanAut.map_projector,
    ← JordanAut.map_projector, ← g.map_circle, traceForm_invariant]

/-- The entire frozen pair-and-centered ledger is preserved by transport.
@isnad1 id=eq.1h3v.s4.317605af81e9 from=translated src=- shape=7dc06ae2 vocab=b940b1d1
-/
theorem ledger_invariant (g : JordanAut) (X Y : WitnessTriple)
    (h : Transports g X Y) : ledger Y = ledger X := by
  rcases h with ⟨hE, hF, hK⟩
  simp only [ledger]
  rw [Ledger.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext i j
    change traceForm (projector Y.cE i) (projector Y.cF j) =
      traceForm (projector X.cE i) (projector X.cF j)
    rw [← hE, ← hF]
    exact projectorPairing_invariant g X.cE X.cF i j
  · funext j l
    change traceForm (projector Y.cF j) (projector Y.cK l) =
      traceForm (projector X.cF j) (projector X.cK l)
    rw [← hF, ← hK]
    exact projectorPairing_invariant g X.cF X.cK j l
  · funext l i
    change traceForm (projector Y.cK l) (projector Y.cE i) =
      traceForm (projector X.cK l) (projector X.cE i)
    rw [← hK, ← hE]
    exact projectorPairing_invariant g X.cK X.cE l i
  · funext i j l
    change
      traceForm (projector Y.cE i)
          (structuredProduct (projector Y.cF j) (projector Y.cK l)) -
            (traceForm (projector Y.cE i) (projector Y.cF j) +
              traceForm (projector Y.cF j) (projector Y.cK l) +
              traceForm (projector Y.cK l) (projector Y.cE i)) / 3 + 2 / 9 =
        traceForm (projector X.cE i)
          (structuredProduct (projector X.cF j) (projector X.cK l)) -
            (traceForm (projector X.cE i) (projector X.cF j) +
              traceForm (projector X.cF j) (projector X.cK l) +
              traceForm (projector X.cK l) (projector X.cE i)) / 3 + 2 / 9
    rw [← hE, ← hF, ← hK, projectorJoint_invariant,
      projectorPairing_invariant, projectorPairing_invariant,
      projectorPairing_invariant]

namespace FullRelated

/--
@isnad1 id=eq.1h2v.s3.5ad108abd529 from=translated src=- shape=52d409ee vocab=778acd6f
-/
theorem ledger_eq {X Y : WitnessTriple} (h : FullRelated X Y) :
    ledger X = ledger Y := by
  rcases h with ⟨g, hg⟩
  exact (ledger_invariant g X Y hg).symm

/--
@isnad1 id=eq.1h2v.s3.fd7047d279a2 from=translated src=- shape=52d409ee vocab=504c94e9
-/
theorem traceCubeDetector_eq {X Y : WitnessTriple} (h : FullRelated X Y) :
    traceCubeDetector X = traceCubeDetector Y := by
  rcases h with ⟨g, hg⟩
  exact (traceCubeDetector_invariant g X Y hg).symm

end FullRelated

/-- Different detector values rule out every full ordered transporter.
@isnad1 id=not.1h2v.s3.863f2923423f from=translated src=- shape=c4457ff1 vocab=504c94e9
-/
theorem not_fullRelated_of_traceCubeDetector_ne {X Y : WitnessTriple}
    (h : traceCubeDetector X ≠ traceCubeDetector Y) :
    ¬ FullRelated X Y := by
  intro hXY
  exact h hXY.traceCubeDetector_eq

/-- Existential form of detector separation, convenient at chart endpoints.
@isnad1 id=not.1h2v.s4.399f414c21e1 from=translated src=- shape=69954d72 vocab=836b48f7
-/
theorem no_full_transporter_of_traceCubeDetector_ne {X Y : WitnessTriple}
    (h : traceCubeDetector X ≠ traceCubeDetector Y) :
    ¬ ∃ g : JordanAut, Transports g X Y :=
  not_fullRelated_of_traceCubeDetector_ne h

end AlbertLean
