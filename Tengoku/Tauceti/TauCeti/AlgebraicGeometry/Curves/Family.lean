/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.AlgebraicGeometry.Morphisms.RelativeDimension

/-!
# Families of curves

A morphism of schemes `f : X ⟶ S` is a *family of curves* if it is proper, flat, of finite
presentation, and of relative dimension at most one, following the Stacks Project's notion of a
family of curves over a scheme base. Nodal, prestable, semistable, and stable families of curves
are families of curves satisfying further conditions. Geometric connectedness of the fibres and
the genus are deliberately not part of the definition.

Finite presentation is recorded as `LocallyOfFinitePresentation`: a proper morphism is already
quasi-compact and separated, hence quasi-separated.

The notion is invariant under isomorphisms, local on the target, and stable under arbitrary base
change. Over a field, it says that a proper scheme has dimension at most one. Finite flat
morphisms of finite presentation are families of curves.

## Main declarations

* `TauCeti.AlgebraicGeometry.FamilyOfCurves f`: `f` is a family of curves.
* `TauCeti.AlgebraicGeometry.FamilyOfCurves.isZariskiLocalAtTarget`: locality on the target.
* `TauCeti.AlgebraicGeometry.FamilyOfCurves.of_isPullback`: stability under base change.
* `TauCeti.AlgebraicGeometry.familyOfCurves_iff_of_field`: families of curves over a field.

## References

* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- A morphism of schemes `f : X ⟶ S` is a family of curves if it is proper, flat, locally of
finite presentation, and of relative dimension at most one. Being proper, such a morphism is
quasi-compact and quasi-separated, hence of finite presentation. -/
@[mk_iff]
class FamilyOfCurves {X S : Scheme.{u}} (f : X ⟶ S) : Prop
    extends IsProper f, Flat f, LocallyOfFinitePresentation f, RelativeDimensionLE 1 f

variable {X Y Z S : Scheme.{u}}

namespace FamilyOfCurves

/-- Being a family of curves is invariant under isomorphisms of arrows. -/
instance respectsIso : MorphismProperty.RespectsIso @FamilyOfCurves.{u} :=
  .mk _ (fun e f (_ : FamilyOfCurves f) ↦
      have : RelativeDimensionLE 1 (e.hom ≫ f) := inferInstance
      ⟨⟩)
    fun e f (_ : FamilyOfCurves f) ↦
      have : RelativeDimensionLE 1 (f ≫ e.hom) := inferInstance
      ⟨⟩

/-- The restriction of a family of curves to an open subscheme of the base is a family of
curves. -/
instance morphismRestrict (f : X ⟶ Y) (U : Y.Opens) [FamilyOfCurves f] :
    FamilyOfCurves (f ∣_ U) :=
  have : RelativeDimensionLE 1 (f ∣_ U) :=
    IsZariskiLocalAtTarget.restrict (P := @RelativeDimensionLE 1) inferInstance U
  ⟨⟩

/-- Being a family of curves is local on the target. -/
instance isZariskiLocalAtTarget : IsZariskiLocalAtTarget @FamilyOfCurves.{u} :=
  .mk' (fun f _ (_ : FamilyOfCurves f) ↦ inferInstance) fun f _ U hU hf ↦
    -- Instance search does not find these instances through `HasRingHomProperty` on its own.
    have := HasRingHomProperty.instIsZariskiLocalAtTarget @Flat
    have := HasRingHomProperty.instIsZariskiLocalAtTarget @LocallyOfFinitePresentation
    have : IsProper f :=
      IsZariskiLocalAtTarget.of_iSup_eq_top U hU fun i ↦ (hf i).toIsProper
    have : Flat f := IsZariskiLocalAtTarget.of_iSup_eq_top U hU fun i ↦ (hf i).toFlat
    have : LocallyOfFinitePresentation f :=
      IsZariskiLocalAtTarget.of_iSup_eq_top U hU fun i ↦ (hf i).toLocallyOfFinitePresentation
    have : RelativeDimensionLE 1 f :=
      IsZariskiLocalAtTarget.of_iSup_eq_top U hU fun i ↦ (hf i).toRelativeDimensionLE
    ⟨⟩

/-- Being a family of curves is stable under arbitrary base change. -/
theorem of_isPullback {P : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) [FamilyOfCurves f] : FamilyOfCurves snd :=
  have : IsProper snd := MorphismProperty.of_isPullback (P := @IsProper) h inferInstance
  have : Flat snd := MorphismProperty.of_isPullback (P := @Flat) h inferInstance
  have : LocallyOfFinitePresentation snd :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) h
      inferInstance
  have : RelativeDimensionLE 1 snd := .of_isPullback h
  ⟨⟩

end FamilyOfCurves

end AlgebraicGeometry

end TauCeti
