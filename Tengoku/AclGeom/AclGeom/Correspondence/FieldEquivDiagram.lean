/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Tengoku.Seed.Algebra.Category.Ring.Constructions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Faithful four-arrow diagrams of field equivalences

The presented correspondence-family groupoid records formal composition
relations, but equality in that quotient is not by itself equality of
function-field maps.  This file supplies the semantic target needed for
that comparison.  Its arrows are literal field equivalences, so equality is
faithful by definition.

Equivalences between three varying field charts can be conjugated to three
fixed reference fields.  Conjugation preserves composition, inverse, and
equality.  Four commuting composition triangles on those reference fields
then satisfy the exact right-arrow cancellation formula

`c = a ≫ e⁻¹ ≫ b`.

The construction is deliberately independent of how the field
equivalences arise.  In the group-chunk application they are restrictions
of semilinear algebraic-closure transports to one common finite normal
curve cover.
-/

namespace AclGeom

noncomputable section

universe u

namespace FieldEquiv

variable {X Y Z X' Y' Z' : Type u}
  [Field X] [Field Y] [Field Z]
  [Field X'] [Field Y'] [Field Z']

/-- Conjugate a field equivalence by equivalences of its source and target
charts.  The result is oriented from the new source to the new target.-/
def conjugate (eX : X ≃+* X') (eY : Y ≃+* Y')
    (f : X ≃+* Y) : X' ≃+* Y' :=
  eX.symm.trans (f.trans eY)

/-- Pointwise formula for conjugation.
@isnad1 id=eq.0h8v.s9.0b2f486f45af from=translated src=- shape=18d5ed5c vocab=c8defdf5
-/
@[simp] theorem conjugate_apply (eX : X ≃+* X') (eY : Y ≃+* Y')
    (f : X ≃+* Y) (x : X') :
    conjugate eX eY f x = eY (f (eX.symm x)) :=
  rfl

/-- Conjugation carries an identity equivalence to an identity
equivalence.
@isnad1 id=eq.0h3v.s7.136fffdb7255 from=translated src=- shape=8d0f511c vocab=4b489403
-/
@[simp] theorem conjugate_refl (eX : X ≃+* X') :
    conjugate eX eX (RingEquiv.refl X) = RingEquiv.refl X' := by
  ext x
  simp [conjugate]

/-- Conjugation preserves composition of field equivalences exactly.
@isnad1 id=eq.0h11v.s8.7e1b00d895bb from=translated src=- shape=cf0824eb vocab=9523b382
-/
theorem conjugate_trans (eX : X ≃+* X') (eY : Y ≃+* Y')
    (eZ : Z ≃+* Z') (f : X ≃+* Y) (g : Y ≃+* Z) :
    (conjugate eX eY f).trans (conjugate eY eZ g) =
      conjugate eX eZ (f.trans g) := by
  ext x
  simp [conjugate]

/-- Conjugation preserves inverse equivalences exactly.
@isnad1 id=eq.0h7v.s8.3649de63af78 from=translated src=- shape=581bef52 vocab=166ea6ee
-/
@[simp] theorem conjugate_symm (eX : X ≃+* X') (eY : Y ≃+* Y')
    (f : X ≃+* Y) :
    (conjugate eX eY f).symm = conjugate eY eX f.symm := by
  ext y
  simp [conjugate]

/-- Conjugation by fixed chart equivalences is faithful.
@isnad1 id=injectiv.0h6v.s7.faa08be989ad from=translated src=- shape=2aa15d34 vocab=60e3f369
-/
theorem conjugate_injective (eX : X ≃+* X') (eY : Y ≃+* Y') :
    Function.Injective (conjugate eX eY : (X ≃+* Y) → (X' ≃+* Y')) := by
  intro f g h
  ext x
  have hx := congrArg (fun F : X' ≃+* Y' ↦ eY.symm (F (eX x))) h
  simpa [conjugate] using hx

/-- Equality can be checked after conjugating both equivalences to fixed
reference charts.
@isnad1 id=iff.0h8v.s8.78abfab756fe from=translated src=- shape=5ce0b4ba vocab=cbe025f2
-/
theorem conjugate_eq_iff (eX : X ≃+* X') (eY : Y ≃+* Y')
    (f g : X ≃+* Y) :
    conjugate eX eY f = conjugate eX eY g ↔ f = g :=
  ⟨fun h ↦ conjugate_injective eX eY h,
    congrArg (conjugate eX eY)⟩

/-- Cancel a target automorphism from an equality of field equivalences.
This small algebraic lemma keeps deck-correction proofs independent of the
implementation of the finite normal covers on which they are applied.-/
theorem eq_trans_symm_of_trans_eq (f g : X ≃+* Y) (d : Y ≃+* Y)
    (h : f.trans d = g) : f = g.trans d.symm := by
  ext x
  have hx := congrArg (fun e : X ≃+* Y ↦ e x) h
  change d (f x) = g x at hx
  change f x = d.symm (g x)
  rw [← hx]
  simp

/-- One literal composition triangle of field equivalences.-/
structure CompositionTriangle (X Y Z : Type u)
    [Field X] [Field Y] [Field Z] where
  /-- The left arrow.-/
  left : X ≃+* Y
  /-- The right arrow.-/
  right : Y ≃+* Z
  /-- The direct composite arrow.-/
  direct : X ≃+* Z
  /-- Literal composition of the two successive arrows.-/
  composition : left.trans right = direct

namespace CompositionTriangle

variable (T : CompositionTriangle X Y Z)

/-- Conjugate an entire composition triangle to three reference fields.-/
def conjugate (eX : X ≃+* X') (eY : Y ≃+* Y')
    (eZ : Z ≃+* Z') : CompositionTriangle X' Y' Z' where
  left := FieldEquiv.conjugate eX eY T.left
  right := FieldEquiv.conjugate eY eZ T.right
  direct := FieldEquiv.conjugate eX eZ T.direct
  composition := by
    rw [FieldEquiv.conjugate_trans, T.composition]

/-- A source chart canonically induces a middle chart by transporting
backwards through the left arrow.-/
def inducedMiddleChart (eX : X ≃+* X') : Y ≃+* X' :=
  T.left.symm.trans eX

/-- A source chart canonically induces a target chart by transporting
backwards through the direct arrow.-/
def inducedTargetChart (eX : X ≃+* X') : Z ≃+* X' :=
  T.direct.symm.trans eX

/-- The middle chart induced from a source chart returns the source-chart
value on every point transported through the left arrow.  This is the
restriction formula used to retain a distinguished branch while changing
the ambient normal-cover chart.
@isnad1 id=eq.0h7v.s9.819da27f5dfa from=translated src=- shape=e0ed752e vocab=a413ed49
-/
@[simp] theorem inducedMiddleChart_left_apply (eX : X ≃+* X') (x : X) :
    T.inducedMiddleChart eX (T.left x) = eX x := by
  simp [inducedMiddleChart]

/-- The target chart induced from a source chart returns the source-chart
value on every point transported through the direct arrow.
@isnad1 id=eq.0h7v.s9.38ade969178f from=translated src=- shape=b8739348 vocab=b8c07273
-/
@[simp] theorem inducedTargetChart_direct_apply (eX : X ≃+* X') (x : X) :
    T.inducedTargetChart eX (T.direct x) = eX x := by
  simp [inducedTargetChart]

/-- If the source chart and left arrow fix a coefficient field, then the
middle chart induced from them fixes that coefficient field as well.
@isnad1 id=eq.2h8v.s9.6a6878095b90 from=translated src=- shape=16346b42 vocab=8f53fe21
-/
theorem inducedMiddleChart_algebraMap
    {F : Type u} [Field F] [Algebra F X] [Algebra F Y] [Algebra F X']
    (eX : X ≃+* X')
    (heX : ∀ c : F, eX (algebraMap F X c) = algebraMap F X' c)
    (hleft : ∀ c : F, T.left (algebraMap F X c) = algebraMap F Y c)
    (c : F) :
    T.inducedMiddleChart eX (algebraMap F Y c) =
      algebraMap F X' c := by
  have hs : T.left.symm (algebraMap F Y c) = algebraMap F X c := by
    apply T.left.injective
    rw [T.left.apply_symm_apply, hleft]
  rw [inducedMiddleChart, RingEquiv.trans_apply, hs, heX]

/-- If the source chart and direct arrow fix a coefficient field, then the
target chart induced from them fixes that coefficient field as well.
@isnad1 id=eq.2h8v.s9.628cdca81cca from=translated src=- shape=58ae2f76 vocab=6322eac9
-/
theorem inducedTargetChart_algebraMap
    {F : Type u} [Field F] [Algebra F X] [Algebra F Z] [Algebra F X']
    (eX : X ≃+* X')
    (heX : ∀ c : F, eX (algebraMap F X c) = algebraMap F X' c)
    (hdirect : ∀ c : F, T.direct (algebraMap F X c) = algebraMap F Z c)
    (c : F) :
    T.inducedTargetChart eX (algebraMap F Z c) =
      algebraMap F X' c := by
  have hs : T.direct.symm (algebraMap F Z c) = algebraMap F X c := by
    apply T.direct.injective
    rw [T.direct.apply_symm_apply, hdirect]
  rw [inducedTargetChart, RingEquiv.trans_apply, hs, heX]

/-- With the induced middle chart, the conjugated left arrow is the
identity on the reference source.
@isnad1 id=eq.0h6v.s7.ba5916fbe080 from=translated src=- shape=dc47ea80 vocab=1afb05ac
-/
@[simp] theorem conjugate_induced_left (eX : X ≃+* X') :
    (T.conjugate eX (T.inducedMiddleChart eX)
      (T.inducedTargetChart eX)).left = RingEquiv.refl X' := by
  ext x
  simp [conjugate, inducedMiddleChart]

/-- With the induced target chart, the conjugated direct arrow is the
identity on the reference source.
@isnad1 id=eq.0h6v.s7.3595291f568e from=translated src=- shape=dc47ea80 vocab=f31ff1bd
-/
@[simp] theorem conjugate_induced_direct (eX : X ≃+* X') :
    (T.conjugate eX (T.inducedMiddleChart eX)
      (T.inducedTargetChart eX)).direct = RingEquiv.refl X' := by
  ext x
  simp [conjugate, inducedTargetChart]

/-- With both induced charts, the conjugated right arrow is also the
identity.  Thus a reference assembled solely from source charts is a
gauge-normalized organizational diagram; a nontrivial family action still
requires independently fixed middle/target charts or selected graph data.
@isnad1 id=eq.0h6v.s7.f77fd0a8b043 from=translated src=- shape=dc47ea80 vocab=b4c6104f
-/
@[simp] theorem conjugate_induced_right (eX : X ≃+* X') :
    (T.conjugate eX (T.inducedMiddleChart eX)
      (T.inducedTargetChart eX)).right = RingEquiv.refl X' := by
  ext x
  change eX (T.direct.symm (T.right (T.left (eX.symm x)))) = x
  calc
    _ = eX (T.direct.symm
        ((T.left.trans T.right) (eX.symm x))) := rfl
    _ = eX (T.direct.symm (T.direct (eX.symm x))) := by
      rw [T.composition]
    _ = x := by simp

/-- Postcomposing an induced middle chart by an independently chosen
common left arrow makes that arrow the literal conjugated left edge.
@isnad1 id=eq.0h10v.s8.70e6403c27c5 from=translated src=- shape=7fde299b vocab=f060fafe
-/
@[simp] theorem conjugate_inducedMiddle_trans_left
    (eX : X ≃+* X') (left' : X' ≃+* Y') (direct' : X' ≃+* Z') :
    (T.conjugate eX ((T.inducedMiddleChart eX).trans left')
      ((T.inducedTargetChart eX).trans direct')).left = left' := by
  ext x
  simp [conjugate, inducedMiddleChart]

/-- Postcomposing an induced target chart by an independently chosen
common direct arrow makes that arrow the literal conjugated direct edge.
@isnad1 id=eq.0h10v.s8.f410768f2d5c from=translated src=- shape=e33c1852 vocab=4a05a9e0
-/
@[simp] theorem conjugate_inducedTarget_trans_direct
    (eX : X ≃+* X') (left' : X' ≃+* Y') (direct' : X' ≃+* Z') :
    (T.conjugate eX ((T.inducedMiddleChart eX).trans left')
      ((T.inducedTargetChart eX).trans direct')).direct = direct' := by
  ext x
  simp [conjugate, inducedTargetChart]

/-- With independently prescribed common left and direct arrows, the
conjugated right edge is their quotient rather than an identity.
@isnad1 id=eq.0h10v.s9.927ccc9bc233 from=translated src=- shape=03bc78b1 vocab=f7fe5680
-/
@[simp] theorem conjugate_induced_trans_right
    (eX : X ≃+* X') (left' : X' ≃+* Y') (direct' : X' ≃+* Z') :
    (T.conjugate eX ((T.inducedMiddleChart eX).trans left')
      ((T.inducedTargetChart eX).trans direct')).right =
        left'.symm.trans direct' := by
  ext y
  change direct' (eX (T.direct.symm
      (T.right (T.left (eX.symm (left'.symm y)))))) =
    direct' (left'.symm y)
  have hcomp := DFunLike.congr_fun T.composition
    (eX.symm (left'.symm y))
  change T.right (T.left (eX.symm (left'.symm y))) =
    T.direct (eX.symm (left'.symm y)) at hcomp
  rw [hcomp]
  simp

/-- A restriction square for the left arrow followed by one for the right
arrow gives the corresponding restriction square for the strict direct
arrow.  Keeping this argument generic prevents concrete finite-cover types
from being unfolded merely to reassociate the triangle identity.
@isnad1 id=eq.2h8v.s8.113f7b6a3cd7 from=translated src=- shape=0c28d62c vocab=e6f92778
-/
theorem direct_comp_of_left_right
    {F : Type u} [Semiring F]
    (source : F →+* X) (middle : F →+* Y) (target : F →+* Z)
    (hleft : T.left.toRingHom.comp source = middle)
    (hright : T.right.toRingHom.comp middle = target) :
    T.direct.toRingHom.comp source = target := by
  apply RingHom.ext
  intro x
  have hcomp := DFunLike.congr_fun T.composition (source x)
  have hl := DFunLike.congr_fun hleft x
  have hr := DFunLike.congr_fun hright x
  change T.right (T.left (source x)) = T.direct (source x) at hcomp
  change T.left (source x) = middle x at hl
  change T.right (middle x) = target x at hr
  exact hcomp.symm.trans ((congrArg T.right hl).trans hr)

end CompositionTriangle

/-- Four composition triangles together with compatible identifications of
all their source, middle, and target fields with three reference fields.
The four compatibility equations say exactly that repeated edge labels
remain the same after conjugation.-/
structure FourTriangleReference
    (X Y Z Xse Yse Zse Xsa Ysa Zsa Xsb Ysb Zsb Xsc Ysc Zsc : Type u)
    [Field X] [Field Y] [Field Z]
    [Field Xse] [Field Yse] [Field Zse]
    [Field Xsa] [Field Ysa] [Field Zsa]
    [Field Xsb] [Field Ysb] [Field Zsb]
    [Field Xsc] [Field Ysc] [Field Zsc] where
  /-- The `s·e=u` triangle.-/
  se : CompositionTriangle Xse Yse Zse
  /-- The `sA·a=u` triangle.-/
  sAa : CompositionTriangle Xsa Ysa Zsa
  /-- The `s·b=uB` triangle.-/
  sb : CompositionTriangle Xsb Ysb Zsb
  /-- The `sA·c=uB` triangle.-/
  sAc : CompositionTriangle Xsc Ysc Zsc
  /-- Reference chart for the first source field.-/
  seX : Xse ≃+* X
  /-- Reference chart for the first middle field.-/
  seY : Yse ≃+* Y
  /-- Reference chart for the first target field.-/
  seZ : Zse ≃+* Z
  /-- Reference chart for the second source field.-/
  sAaX : Xsa ≃+* X
  /-- Reference chart for the second middle field.-/
  sAaY : Ysa ≃+* Y
  /-- Reference chart for the second target field.-/
  sAaZ : Zsa ≃+* Z
  /-- Reference chart for the third source field.-/
  sbX : Xsb ≃+* X
  /-- Reference chart for the third middle field.-/
  sbY : Ysb ≃+* Y
  /-- Reference chart for the third target field.-/
  sbZ : Zsb ≃+* Z
  /-- Reference chart for the fourth source field.-/
  sAcX : Xsc ≃+* X
  /-- Reference chart for the fourth middle field.-/
  sAcY : Ysc ≃+* Y
  /-- Reference chart for the fourth target field.-/
  sAcZ : Zsc ≃+* Z
  /-- The repeated `s` arrow agrees after reference conjugation.-/
  leftS :
    (sb.conjugate sbX sbY sbZ).left =
      (se.conjugate seX seY seZ).left
  /-- The repeated `sA` arrow agrees after reference conjugation.-/
  leftSA :
    (sAc.conjugate sAcX sAcY sAcZ).left =
      (sAa.conjugate sAaX sAaY sAaZ).left
  /-- The repeated `u` composite agrees after reference conjugation.-/
  compositeU :
    (sAa.conjugate sAaX sAaY sAaZ).direct =
      (se.conjugate seX seY seZ).direct
  /-- The repeated `uB` composite agrees after reference conjugation.-/
  compositeUB :
    (sAc.conjugate sAcX sAcY sAcZ).direct =
      (sb.conjugate sbX sbY sbZ).direct

/-- A semantic four-arrow diagram on three fixed field charts.  Its four
faces are literal equalities of field equivalences rather than relations
in a formal quotient groupoid.-/
structure FourArrowDiagram (X Y Z : Type u)
    [Field X] [Field Y] [Field Z] where
  /-- The repeated left-family arrow labelled by `s`.-/
  leftS : X ≃+* Y
  /-- The repeated left-family arrow labelled by `sA`.-/
  leftSA : X ≃+* Y
  /-- The first based right-family arrow labelled by `e`.-/
  rightE : Y ≃+* Z
  /-- The inverse-input right-family arrow labelled by `a`.-/
  rightA : Y ≃+* Z
  /-- The second based right-family arrow labelled by `b`.-/
  rightB : Y ≃+* Z
  /-- The output right-family arrow labelled by `c`.-/
  rightC : Y ≃+* Z
  /-- The repeated composite arrow labelled by `u`.-/
  compositeU : X ≃+* Z
  /-- The repeated composite arrow labelled by `uB`.-/
  compositeUB : X ≃+* Z
  /-- The semantic face `s ≫ e = u`.-/
  se_u : leftS.trans rightE = compositeU
  /-- The semantic face `sA ≫ a = u`.-/
  sA_a_u : leftSA.trans rightA = compositeU
  /-- The semantic face `s ≫ b = uB`.-/
  s_b_uB : leftS.trans rightB = compositeUB
  /-- The semantic face `sA ≫ c = uB`.-/
  sA_c_uB : leftSA.trans rightC = compositeUB

namespace FourTriangleReference

variable {Xse Yse Zse Xsa Ysa Zsa Xsb Ysb Zsb Xsc Ysc Zsc : Type u}
  [Field Xse] [Field Yse] [Field Zse]
  [Field Xsa] [Field Ysa] [Field Zsa]
  [Field Xsb] [Field Ysb] [Field Zsb]
  [Field Xsc] [Field Ysc] [Field Zsc]

/-- Build compatible middle and target charts from independently chosen
common left and direct arrows.  Unlike `ofSourceCharts`, this construction
does not identify the three reference fields and does not force the right
arrows to be identities.  The chart on each middle (respectively target)
field first returns to its source chart and then follows the prescribed
common left (respectively direct) arrow.-/
def ofCommonLeftDirect
    (se : CompositionTriangle Xse Yse Zse)
    (sAa : CompositionTriangle Xsa Ysa Zsa)
    (sb : CompositionTriangle Xsb Ysb Zsb)
    (sAc : CompositionTriangle Xsc Ysc Zsc)
    (seX : Xse ≃+* X) (sAaX : Xsa ≃+* X)
    (sbX : Xsb ≃+* X) (sAcX : Xsc ≃+* X)
    (leftS leftSA : X ≃+* Y)
    (directU directUB : X ≃+* Z) :
    FourTriangleReference X Y Z
      Xse Yse Zse Xsa Ysa Zsa Xsb Ysb Zsb Xsc Ysc Zsc where
  se := se
  sAa := sAa
  sb := sb
  sAc := sAc
  seX := seX
  seY := (se.inducedMiddleChart seX).trans leftS
  seZ := (se.inducedTargetChart seX).trans directU
  sAaX := sAaX
  sAaY := (sAa.inducedMiddleChart sAaX).trans leftSA
  sAaZ := (sAa.inducedTargetChart sAaX).trans directU
  sbX := sbX
  sbY := (sb.inducedMiddleChart sbX).trans leftS
  sbZ := (sb.inducedTargetChart sbX).trans directUB
  sAcX := sAcX
  sAcY := (sAc.inducedMiddleChart sAcX).trans leftSA
  sAcZ := (sAc.inducedTargetChart sAcX).trans directUB
  leftS := by
    ext x
    simp [CompositionTriangle.conjugate,
      CompositionTriangle.inducedMiddleChart, FieldEquiv.conjugate]
  leftSA := by
    ext x
    simp [CompositionTriangle.conjugate,
      CompositionTriangle.inducedMiddleChart, FieldEquiv.conjugate]
  compositeU := by
    ext x
    simp [CompositionTriangle.conjugate,
      CompositionTriangle.inducedTargetChart, FieldEquiv.conjugate]
  compositeUB := by
    ext x
    simp [CompositionTriangle.conjugate,
      CompositionTriangle.inducedTargetChart, FieldEquiv.conjugate]

/-- Four composition triangles with chosen charts to one reference source
acquire canonical gauge-normalized middle and target charts.  Every
conjugated arrow is an identity, so the result organizes four selected
graphs in one field but does not by itself retain a nontrivial action on
that field.-/
def ofSourceCharts
    (se : CompositionTriangle Xse Yse Zse)
    (sAa : CompositionTriangle Xsa Ysa Zsa)
    (sb : CompositionTriangle Xsb Ysb Zsb)
    (sAc : CompositionTriangle Xsc Ysc Zsc)
    (seX : Xse ≃+* X) (sAaX : Xsa ≃+* X)
    (sbX : Xsb ≃+* X) (sAcX : Xsc ≃+* X) :
    FourTriangleReference X X X
      Xse Yse Zse Xsa Ysa Zsa Xsb Ysb Zsb Xsc Ysc Zsc where
  se := se
  sAa := sAa
  sb := sb
  sAc := sAc
  seX := seX
  seY := se.inducedMiddleChart seX
  seZ := se.inducedTargetChart seX
  sAaX := sAaX
  sAaY := sAa.inducedMiddleChart sAaX
  sAaZ := sAa.inducedTargetChart sAaX
  sbX := sbX
  sbY := sb.inducedMiddleChart sbX
  sbZ := sb.inducedTargetChart sbX
  sAcX := sAcX
  sAcY := sAc.inducedMiddleChart sAcX
  sAcZ := sAc.inducedTargetChart sAcX
  leftS := by simp
  leftSA := by simp
  compositeU := by simp
  compositeUB := by simp

variable {Xse Yse Zse Xsa Ysa Zsa Xsb Ysb Zsb Xsc Ysc Zsc : Type u}
  [Field Xse] [Field Yse] [Field Zse]
  [Field Xsa] [Field Ysa] [Field Zsa]
  [Field Xsb] [Field Ysb] [Field Zsb]
  [Field Xsc] [Field Ysc] [Field Zsc]
  (R : FourTriangleReference
    X Y Z Xse Yse Zse Xsa Ysa Zsa Xsb Ysb Zsb Xsc Ysc Zsc)

/-- Compatible reference charts turn four independently typed composition
triangles into one semantic four-arrow diagram.-/
def toFourArrowDiagram : FourArrowDiagram X Y Z where
  leftS := (R.se.conjugate R.seX R.seY R.seZ).left
  leftSA := (R.sAa.conjugate R.sAaX R.sAaY R.sAaZ).left
  rightE := (R.se.conjugate R.seX R.seY R.seZ).right
  rightA := (R.sAa.conjugate R.sAaX R.sAaY R.sAaZ).right
  rightB := (R.sb.conjugate R.sbX R.sbY R.sbZ).right
  rightC := (R.sAc.conjugate R.sAcX R.sAcY R.sAcZ).right
  compositeU := (R.se.conjugate R.seX R.seY R.seZ).direct
  compositeUB := (R.sb.conjugate R.sbX R.sbY R.sbZ).direct
  se_u := (R.se.conjugate R.seX R.seY R.seZ).composition
  sA_a_u := by
    rw [(R.sAa.conjugate R.sAaX R.sAaY R.sAaZ).composition,
      R.compositeU]
  s_b_uB := by
    rw [← R.leftS,
      (R.sb.conjugate R.sbX R.sbY R.sbZ).composition]
  sA_c_uB := by
    rw [← R.leftSA,
      (R.sAc.conjugate R.sAcX R.sAcY R.sAcZ).composition,
      R.compositeUB]

/-- The semantic diagram obtained from independently prescribed common
left and direct arrows retains those arrows literally, and its four right
arrows are the corresponding nontrivial quotients.
@isnad1 id=other.0h27v.s10.d85182848be5 from=translated src=- shape=3a7f9814 vocab=8a652508
-/
theorem ofCommonLeftDirect_toFourArrowDiagram
    (se : CompositionTriangle Xse Yse Zse)
    (sAa : CompositionTriangle Xsa Ysa Zsa)
    (sb : CompositionTriangle Xsb Ysb Zsb)
    (sAc : CompositionTriangle Xsc Ysc Zsc)
    (seX : Xse ≃+* X) (sAaX : Xsa ≃+* X)
    (sbX : Xsb ≃+* X) (sAcX : Xsc ≃+* X)
    (leftS leftSA : X ≃+* Y)
    (directU directUB : X ≃+* Z) :
    let A := ofCommonLeftDirect se sAa sb sAc
      seX sAaX sbX sAcX leftS leftSA directU directUB
    A.toFourArrowDiagram.leftS = leftS ∧
      A.toFourArrowDiagram.leftSA = leftSA ∧
      A.toFourArrowDiagram.rightE = leftS.symm.trans directU ∧
      A.toFourArrowDiagram.rightA = leftSA.symm.trans directU ∧
      A.toFourArrowDiagram.rightB = leftS.symm.trans directUB ∧
      A.toFourArrowDiagram.rightC = leftSA.symm.trans directUB ∧
      A.toFourArrowDiagram.compositeU = directU ∧
      A.toFourArrowDiagram.compositeUB = directUB := by
  dsimp only [toFourArrowDiagram]
  simp [ofCommonLeftDirect]

/-- The four right arrows of a source-induced reference are all identities.
This exposes the exact boundary of `ofSourceCharts`: parameter-dependent
information must be recovered from selected graph embeddings, or from a
reference with independently specified middle and target charts.
@isnad1 id=other.0h21v.s9.1e6488f80ce6 from=translated src=- shape=1daef3ce vocab=31ce082c
-/
theorem ofSourceCharts_right_arrows_eq_refl
    (se : CompositionTriangle Xse Yse Zse)
    (sAa : CompositionTriangle Xsa Ysa Zsa)
    (sb : CompositionTriangle Xsb Ysb Zsb)
    (sAc : CompositionTriangle Xsc Ysc Zsc)
    (seX : Xse ≃+* X) (sAaX : Xsa ≃+* X)
    (sbX : Xsb ≃+* X) (sAcX : Xsc ≃+* X) :
    let A := FourTriangleReference.ofSourceCharts
      se sAa sb sAc seX sAaX sbX sAcX
    A.toFourArrowDiagram.rightE = RingEquiv.refl X ∧
      A.toFourArrowDiagram.rightA = RingEquiv.refl X ∧
      A.toFourArrowDiagram.rightB = RingEquiv.refl X ∧
      A.toFourArrowDiagram.rightC = RingEquiv.refl X := by
  dsimp only [toFourArrowDiagram]
  exact ⟨se.conjugate_induced_right seX,
    sAa.conjugate_induced_right sAaX,
    sb.conjugate_induced_right sbX,
    sAc.conjugate_induced_right sAcX⟩

/-- The first semantic right arrow acts on an element expressed in its
original middle chart by the original right arrow followed by the target
chart.
@isnad1 id=eq.0h17v.s9.444448040407 from=translated src=- shape=857bfbda vocab=7fe54eaa
-/
@[simp] theorem toFourArrowDiagram_rightE_apply (y : Yse) :
    R.toFourArrowDiagram.rightE (R.seY y) =
      R.seZ (R.se.right y) := by
  simp [toFourArrowDiagram, CompositionTriangle.conjugate,
    FieldEquiv.conjugate]

/-- Pointwise chart formula for the inverse-input semantic right arrow.
@isnad1 id=eq.0h17v.s9.f9d324230d5a from=translated src=- shape=7815c97d vocab=c37db84a
-/
@[simp] theorem toFourArrowDiagram_rightA_apply (y : Ysa) :
    R.toFourArrowDiagram.rightA (R.sAaY y) =
      R.sAaZ (R.sAa.right y) := by
  simp [toFourArrowDiagram, CompositionTriangle.conjugate,
    FieldEquiv.conjugate]

/-- Pointwise chart formula for the second-input semantic right arrow.
@isnad1 id=eq.0h17v.s9.53f4541eb19a from=translated src=- shape=cfdddd2c vocab=037383a3
-/
@[simp] theorem toFourArrowDiagram_rightB_apply (y : Ysb) :
    R.toFourArrowDiagram.rightB (R.sbY y) =
      R.sbZ (R.sb.right y) := by
  simp [toFourArrowDiagram, CompositionTriangle.conjugate,
    FieldEquiv.conjugate]

/-- Pointwise chart formula for the output semantic right arrow.
@isnad1 id=eq.0h17v.s9.b89e58ae6075 from=translated src=- shape=6400d216 vocab=66868dbe
-/
@[simp] theorem toFourArrowDiagram_rightC_apply (y : Ysc) :
    R.toFourArrowDiagram.rightC (R.sAcY y) =
      R.sAcZ (R.sAc.right y) := by
  simp [toFourArrowDiagram, CompositionTriangle.conjugate,
    FieldEquiv.conjugate]

end FourTriangleReference

namespace FourArrowDiagram

variable (D : FourArrowDiagram X Y Z)

/-- Transport a semantic four-arrow diagram to three reference fields by
conjugating every arrow.-/
def conjugate (eX : X ≃+* X') (eY : Y ≃+* Y')
    (eZ : Z ≃+* Z') : FourArrowDiagram X' Y' Z' where
  leftS := FieldEquiv.conjugate eX eY D.leftS
  leftSA := FieldEquiv.conjugate eX eY D.leftSA
  rightE := FieldEquiv.conjugate eY eZ D.rightE
  rightA := FieldEquiv.conjugate eY eZ D.rightA
  rightB := FieldEquiv.conjugate eY eZ D.rightB
  rightC := FieldEquiv.conjugate eY eZ D.rightC
  compositeU := FieldEquiv.conjugate eX eZ D.compositeU
  compositeUB := FieldEquiv.conjugate eX eZ D.compositeUB
  se_u := by
    rw [FieldEquiv.conjugate_trans, D.se_u]
  sA_a_u := by
    rw [FieldEquiv.conjugate_trans, D.sA_a_u]
  s_b_uB := by
    rw [FieldEquiv.conjugate_trans, D.s_b_uB]
  sA_c_uB := by
    rw [FieldEquiv.conjugate_trans, D.sA_c_uB]

/-- The transported diagram has the pointwise conjugated output arrow.
@isnad1 id=eq.0h10v.s8.188fc2541708 from=translated src=- shape=38575ff4 vocab=da3c6934
-/
@[simp] theorem conjugate_rightC
    (eX : X ≃+* X') (eY : Y ≃+* Y') (eZ : Z ≃+* Z') :
    (D.conjugate eX eY eZ).rightC =
      FieldEquiv.conjugate eY eZ D.rightC :=
  rfl

/-- **Faithful semantic four-arrow cancellation.**  Four literal
composition identities between field equivalences force the output
right-family map to be the based difference product of the other three.
@isnad1 id=eq.0h4v.s8.e317448aeb61 from=translated src=- shape=2237d77a vocab=11936212
-/
theorem right_cancellation :
    D.rightC = (D.rightA.trans D.rightE.symm).trans D.rightB := by
  ext y
  let x := D.leftSA.symm y
  have hsc := congrArg (fun f : X ≃+* Z ↦ f x) D.sA_c_uB
  have hsb := congrArg (fun f : X ≃+* Z ↦ f x) D.s_b_uB
  have hsa := congrArg (fun f : X ≃+* Z ↦ f x) D.sA_a_u
  have hse := congrArg (fun f : X ≃+* Z ↦ f x) D.se_u
  change D.rightC (D.leftSA x) = D.compositeUB x at hsc
  change D.rightB (D.leftS x) = D.compositeUB x at hsb
  change D.rightA (D.leftSA x) = D.compositeU x at hsa
  change D.rightE (D.leftS x) = D.compositeU x at hse
  change D.rightC y = D.rightB (D.rightE.symm (D.rightA y))
  calc
    D.rightC y = D.rightC (D.leftSA x) := by simp [x]
    _ = D.compositeUB x := hsc
    _ = D.rightB (D.leftS x) := hsb.symm
    _ = D.rightB (D.rightE.symm (D.rightE (D.leftS x))) := by simp
    _ = D.rightB (D.rightE.symm (D.compositeU x)) := by rw [hse]
    _ = D.rightB (D.rightE.symm (D.rightA (D.leftSA x))) := by rw [hsa]
    _ = D.rightB (D.rightE.symm (D.rightA y)) := by simp [x]

/-- A common coefficient-field embedding in the middle chart together with
its four images under the semantic right arrows.  Recording all five maps
in one structure prevents a family of unrelated parameter embeddings from
being mistaken for a restriction of the four-arrow diagram.-/
structure RightRestriction (F : Type u) [Field F] where
  /-- The one coefficient embedding shared by all four right arrows.-/
  middle : F →+* Y
  /-- Its image under the right arrow labelled by `e`.-/
  mapE : F →+* Z
  /-- Its image under the right arrow labelled by `a`.-/
  mapA : F →+* Z
  /-- Its image under the right arrow labelled by `b`.-/
  mapB : F →+* Z
  /-- Its image under the right arrow labelled by `c`.-/
  mapC : F →+* Z
  /-- The `e` map is the restriction of the semantic `e` arrow.-/
  rightE : D.rightE.toRingHom.comp middle = mapE
  /-- The `a` map is the restriction of the semantic `a` arrow.-/
  rightA : D.rightA.toRingHom.comp middle = mapA
  /-- The `b` map is the restriction of the semantic `b` arrow.-/
  rightB : D.rightB.toRingHom.comp middle = mapB
  /-- The `c` map is the restriction of the semantic `c` arrow.-/
  rightC : D.rightC.toRingHom.comp middle = mapC

namespace RightRestriction

variable {F : Type u} [Field F] (C : D.RightRestriction F)

/-- Build a common right-arrow restriction from two coefficient embeddings in
the source chart.  The first source embedding is used by the repeated `s`
faces and the second by the repeated `sA` faces.  Requiring both left images
to be the same `middle` map is exactly the compatibility needed for all four
right-arrow restrictions to have one literal domain in the middle chart.-/
def ofSourceRestrictions
    (middle : F →+* Y)
    (sourceS sourceSA : F →+* X)
    (mapE mapA mapB mapC : F →+* Z)
    (leftS : D.leftS.toRingHom.comp sourceS = middle)
    (leftSA : D.leftSA.toRingHom.comp sourceSA = middle)
    (directUE : D.compositeU.toRingHom.comp sourceS = mapE)
    (directUA : D.compositeU.toRingHom.comp sourceSA = mapA)
    (directUBB : D.compositeUB.toRingHom.comp sourceS = mapB)
    (directUBC : D.compositeUB.toRingHom.comp sourceSA = mapC) :
    D.RightRestriction F where
  middle := middle
  mapE := mapE
  mapA := mapA
  mapB := mapB
  mapC := mapC
  rightE := by
    apply RingHom.ext
    intro z
    have hleft := DFunLike.congr_fun leftS z
    have hdirect := DFunLike.congr_fun directUE z
    have hface := DFunLike.congr_fun D.se_u (sourceS z)
    change D.leftS (sourceS z) = middle z at hleft
    change D.compositeU (sourceS z) = mapE z at hdirect
    change D.rightE (D.leftS (sourceS z)) =
      D.compositeU (sourceS z) at hface
    change D.rightE (middle z) = mapE z
    rw [← hleft, hface, hdirect]
  rightA := by
    apply RingHom.ext
    intro z
    have hleft := DFunLike.congr_fun leftSA z
    have hdirect := DFunLike.congr_fun directUA z
    have hface := DFunLike.congr_fun D.sA_a_u (sourceSA z)
    change D.leftSA (sourceSA z) = middle z at hleft
    change D.compositeU (sourceSA z) = mapA z at hdirect
    change D.rightA (D.leftSA (sourceSA z)) =
      D.compositeU (sourceSA z) at hface
    change D.rightA (middle z) = mapA z
    rw [← hleft, hface, hdirect]
  rightB := by
    apply RingHom.ext
    intro z
    have hleft := DFunLike.congr_fun leftS z
    have hdirect := DFunLike.congr_fun directUBB z
    have hface := DFunLike.congr_fun D.s_b_uB (sourceS z)
    change D.leftS (sourceS z) = middle z at hleft
    change D.compositeUB (sourceS z) = mapB z at hdirect
    change D.rightB (D.leftS (sourceS z)) =
      D.compositeUB (sourceS z) at hface
    change D.rightB (middle z) = mapB z
    rw [← hleft, hface, hdirect]
  rightC := by
    apply RingHom.ext
    intro z
    have hleft := DFunLike.congr_fun leftSA z
    have hdirect := DFunLike.congr_fun directUBC z
    have hface := DFunLike.congr_fun D.sA_c_uB (sourceSA z)
    change D.leftSA (sourceSA z) = middle z at hleft
    change D.compositeUB (sourceSA z) = mapC z at hdirect
    change D.rightC (D.leftSA (sourceSA z)) =
      D.compositeUB (sourceSA z) at hface
    change D.rightC (middle z) = mapC z
    rw [← hleft, hface, hdirect]

/-- Faithful four-arrow cancellation restricted to one common coefficient
field.  The formula retains the inverse `e` arrow in the middle chart; it is
therefore the exact field-map factorization that must later be spread to the
intrinsic germ chart.
@isnad1 id=eq.0h6v.s7.f40d517e5abf from=translated src=- shape=56f993f0 vocab=dd72c62b
-/
theorem mapC_factorization :
    C.mapC = D.rightB.toRingHom.comp
      (D.rightE.symm.toRingHom.comp C.mapA) := by
  apply RingHom.ext
  intro z
  calc
    C.mapC z = D.rightC (C.middle z) :=
      (DFunLike.congr_fun C.rightC z).symm
    _ = D.rightB (D.rightE.symm (D.rightA (C.middle z))) :=
      DFunLike.congr_fun D.right_cancellation (C.middle z)
    _ = D.rightB (D.rightE.symm (C.mapA z)) := by
      have hz := DFunLike.congr_fun C.rightA z
      change D.rightA (C.middle z) = C.mapA z at hz
      rw [hz]

end RightRestriction

/-- Pointwise form of semantic four-arrow cancellation.
@isnad1 id=eq.0h5v.s9.30c5bde3b3b9 from=translated src=- shape=eaf8b22b vocab=88ec629e
-/
theorem right_cancellation_apply (y : Y) :
    D.rightC y = D.rightB (D.rightE.symm (D.rightA y)) := by
  exact DFunLike.congr_fun D.right_cancellation y

/-- Cancellation is invariant under simultaneous conjugation to any three
reference field charts.
@isnad1 id=eq.0h10v.s9.b10d9fb0c9ad from=translated src=- shape=f1aca7f5 vocab=4c5cef92
-/
theorem conjugate_right_cancellation
    (eX : X ≃+* X') (eY : Y ≃+* Y') (eZ : Z ≃+* Z') :
    (D.conjugate eX eY eZ).rightC =
      (((D.conjugate eX eY eZ).rightA.trans
        (D.conjugate eX eY eZ).rightE.symm).trans
          (D.conjugate eX eY eZ).rightB) :=
  (D.conjugate eX eY eZ).right_cancellation

end FourArrowDiagram

end FieldEquiv

end

end AclGeom
