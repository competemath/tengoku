/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.AlgebraicGeometry.Morphisms.FormallyUnramified
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Separated
import Tengoku.Seed.AlgebraicGeometry.Morphisms.IsIso
import Tengoku.LanaOka.Oka.Topology.JacobsonSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Equalisers of morphisms into unramified schemes

The diagonal of a morphism `Y ⟶ Z` which is formally unramified and locally of finite type is an
open immersion (`AlgebraicGeometry.FormallyUnramified.isOpenImmersion_diagonal`). Consequently the
equaliser of two morphisms `f g : X ⟶ Y` over `Z` is an open subscheme of `X`. If `X` is a
Jacobson scheme and `f`, `g` agree on the residue fields of all closed points, this open subscheme
contains every closed point, hence is all of `X`, and `f = g`.

## Main results

- `AlgebraicGeometry.isOpenImmersion_equalizer_ι_left`: the equaliser of two morphisms into a
  formally unramified scheme of finite type is an open immersion.
- `AlgebraicGeometry.ext_of_fromSpecResidueField_eq_of_formallyUnramified`: two morphisms from a
  Jacobson scheme into a formally unramified scheme of finite type over `Z` which agree over `Z`
  and on the residue fields of the closed points are equal.
-/

open CategoryTheory Limits MorphismProperty

universe u

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- **The equaliser of two morphisms into a formally unramified scheme of finite type is an open
immersion**: it is the pullback of the diagonal, which is an open immersion. -/
instance isOpenImmersion_equalizer_ι_left {S : Scheme.{u}} {X Y : Over S}
    [FormallyUnramified Y.hom] [LocallyOfFiniteType Y.hom] (f g : X ⟶ Y) :
    IsOpenImmersion (equalizer.ι f g).left := by
  refine MorphismProperty.of_isPullback
    ((Limits.isPullback_equalizer_prod f g).map (Over.forget _)).flip ?_
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsOpenImmersion _
    (Over.prodLeftIsoPullback Y Y).hom]
  convert! (inferInstance : IsOpenImmersion (pullback.diagonal Y.hom))
  ext1 <;> simp [← Over.comp_left]

set_option backward.isDefEq.respectTransparency false in
/-- **Morphisms into an unramified scheme are determined on closed points**: let `X` be a Jacobson
scheme and `s : Y ⟶ Z` formally unramified and locally of finite type. If `f g : X ⟶ Y` agree over
`Z` and `Spec κ(x) ⟶ X ⟶ Y` agree for every closed point `x`, then `f = g`. -/
theorem ext_of_fromSpecResidueField_eq_of_formallyUnramified {X Y Z : Scheme.{u}}
    [JacobsonSpace X] {f g : X ⟶ Y} (s : Y ⟶ Z) [FormallyUnramified s] [LocallyOfFiniteType s]
    (h : f ≫ s = g ≫ s)
    (H : ∀ x ∈ closedPoints X, X.fromSpecResidueField x ≫ f = X.fromSpecResidueField x ≫ g) :
    f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g h.symm
  have : FormallyUnramified Y'.hom := ‹_›
  have : LocallyOfFiniteType Y'.hom := ‹_›
  have hsurj : Surjective (equalizer.ι f' g').left := by
    refine ⟨fun x ↦ ?_⟩
    have hr := JacobsonSpace.eq_univ_of_isOpen_of_closedPoints_subset (X := X)
      (equalizer.ι f' g').left.isOpenEmbedding.isOpen_range (fun x hx ↦ ?_)
    · exact Set.eq_univ_iff_forall.1 hr x
    let ι' : Over.mk (X.fromSpecResidueField x ≫ f ≫ s) ⟶ X' :=
      Over.homMk (X.fromSpecResidueField x)
    refine ⟨(equalizer.lift ι' ?_).left (IsLocalRing.closedPoint _), ?_⟩
    · ext1
      exact H x hx
    · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, equalizer.lift_ι]
      exact Scheme.fromSpecResidueField_apply x _
  have := (isIso_iff_isOpenImmersion_and_surjective (equalizer.ι f' g').left).2
    ⟨inferInstance, hsurj⟩
  rw [← cancel_epi (equalizer.ι f' g').left]
  exact congr($(equalizer.condition f' g').left)

end AlgebraicGeometry
