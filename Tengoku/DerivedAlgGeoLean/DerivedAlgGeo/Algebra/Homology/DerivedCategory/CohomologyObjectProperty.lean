/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.CategoryTheory.Abelian.SerreClass.Weak
import Tengoku.Seed.Algebra.Homology.DerivedCategory.HomologySequence
import Tengoku.Seed.CategoryTheory.Triangulated.Subcategory

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cohomology in a weak Serre subcategory cuts out a triangulated subcategory

Let `A` be an abelian category and `P : ObjectProperty A` a **weak Serre
subcategory** — closed under kernels, cokernels and extensions, and containing
the zero object. This file proves that

`cohomologyIn P := fun E ↦ ∀ n, P (Hⁿ E)`

is a triangulated subcategory of `DerivedCategory A`, so that
`(cohomologyIn P).FullSubcategory` inherits a pretriangulated structure from
Mathlib's `ObjectProperty.instPretriangulatedFullSubcategory`, with the
inclusion triangulated.

## The one mathematical input

Closure under cones is the only field with content, and it is exactly the
five-term statement of `Abelian/WeakSerre.lean` applied to the long exact homology
sequence. For a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` the sequence

`Hⁿ⁻¹X₃ ⟶ HⁿX₁ ⟶ HⁿX₂ ⟶ HⁿX₃ ⟶ Hⁿ⁺¹X₁`

is exact at its three inner spots, and if `X₁` and `X₃` have all cohomology in
`P` then the four outer terms are in `P`. This is why a *weak* Serre
subcategory suffices and no closure under subobjects or quotients is needed:
the two extra terms of the five-term sequence pay for exactly that gap.

## Why this is not in Mathlib

Mathlib has the three closure classes and the long exact sequence, and it has
`ObjectProperty.IsTriangulated`, but nothing connects them. The `t`-structure
route (`DerivedCategory.TStructure`) answers a different question — boundedness,
not cohomological support in a subcategory.

## Main results

* `DerivedCategory.cohomologyIn` — the object property.
* `DerivedCategory.cohomologyIn_isTriangulated` — it is a triangulated
  subcategory, hence `Pretriangulated` on the full subcategory and the
  inclusion is triangulated.
-/

universe t w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A] {n : ℤ}

/-- The objects of `DerivedCategory A` all of whose cohomology objects satisfy
`P`. For `P` quasi-coherence on a scheme this is the honest `Dqc(X)`.-/
def cohomologyIn (P : ObjectProperty A) : ObjectProperty (DerivedCategory A) :=
  fun E ↦ ∀ n : ℤ, P ((homologyFunctor A n).obj E)

/--
@isnad1 id=iff.0h3v.s5.12e195eb4584 from=translated src=- shape=f2ae98fc vocab=5dcb39ca
-/
lemma mem_cohomologyIn_iff (P : ObjectProperty A) (E : DerivedCategory A) :
    cohomologyIn P E ↔ ∀ n : ℤ, P ((homologyFunctor A n).obj E) :=
  Iff.rfl

variable (P : ObjectProperty A)

instance [P.IsClosedUnderIsomorphisms] :
    (cohomologyIn P).IsClosedUnderIsomorphisms where
  of_iso e hE n := P.prop_of_iso ((homologyFunctor A n).mapIso e) (hE n)

instance [P.ContainsZero] [P.IsClosedUnderIsomorphisms] :
    (cohomologyIn P).ContainsZero where
  exists_zero := by
    obtain ⟨Z, hZ⟩ := (inferInstance : HasZeroObject (DerivedCategory A)).zero
    exact ⟨Z, hZ, fun n ↦ P.prop_of_isZero (Functor.map_isZero (homologyFunctor A n) hZ)⟩

instance [P.IsClosedUnderIsomorphisms] :
    (cohomologyIn P).IsStableUnderShift ℤ where
  isStableUnderShiftBy m :=
    { le_shift := by
        intro E hE n
        exact P.prop_of_iso
          (((homologyFunctor A 0).shiftIso m n (m + n) rfl).app E).symm (hE (m + n)) }

section WeakSerre

variable [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels]
  [P.IsClosedUnderExtensions] [P.IsClosedUnderIsomorphisms]

/-- **Closure under cones**: the only field of `IsTriangulated` with content.

The long exact homology sequence of the distinguished triangle supplies the
three exactness hypotheses of `ObjectProperty.prop_X₃_of_exact₅`, and the four
outer terms come from `X₁` and `X₃` in adjacent degrees.
@isnad1 id=istriang.0h2v.s6.21c7f9db886d from=translated src=- shape=9295130f vocab=141ff5f9
-/
instance cohomologyIn_isTriangulatedClosed₂ :
    (cohomologyIn P).IsTriangulatedClosed₂ :=
  .mk' (by
    intro T hT h₁ h₃ n
    exact P.prop_X₃_of_exact₅
      (HomologySequence.exact₁ T hT (n - 1) n (by lia))
      (HomologySequence.exact₂ T hT n)
      (HomologySequence.exact₃ T hT n (n + 1) rfl)
      (h₃ (n - 1)) (h₁ n) (h₃ n) (h₁ (n + 1)))

/-- **`cohomologyIn P` is a triangulated subcategory** when `P` is a weak Serre
subcategory containing zero.

Two consequences come for free from Mathlib: `(cohomologyIn P).FullSubcategory`
is `Pretriangulated` (and `IsTriangulated` when `DerivedCategory A` is), and
`(cohomologyIn P).ι` is a triangulated functor.
@isnad1 id=istriang.0h2v.s6.ede32a400f1d from=translated src=- shape=8a455c20 vocab=1ebe3ac3
-/
instance cohomologyIn_isTriangulated [P.ContainsZero] :
    (cohomologyIn P).IsTriangulated where

end WeakSerre

section Coproducts

/-- **Closure under a coproduct that cohomology preserves.**

The two hypotheses are stated for the one indexing type at hand rather than as
instances on `A`: they hold by instance search when `A` has exact coproducts of
that shape (`DerivedCategory.hasCoproductsOfShape` and
`DerivedCategory.homologyFunctor_preservesCoproductsOfShape` in
`DerivedCategory/Coproducts.lean`), and a consumer with a different source for
them passes it here.

Given them, the argument is one step: `Hⁿ(∐ Eᵢ)` *is* a colimit of the `Hⁿ(Eᵢ)`,
each of which is in `P`, so `P`'s own closure under `ι`-indexed colimits applies.
@isnad1 id=var.1h6v.s6.0a7c147e0573 from=translated src=- shape=23586bbb vocab=2489111c
-/
lemma cohomologyIn_coproduct {ι : Type t} [P.IsClosedUnderColimitsOfShape (Discrete ι)]
    (E : ι → DerivedCategory A) [HasCoproduct E]
    (hpres : PreservesColimitsOfShape (Discrete ι) (homologyFunctor A n))
    (hE : ∀ i, cohomologyIn P (E i)) : P ((homologyFunctor A n).obj (∐ E)) := by
  haveI := hpres
  refine ObjectProperty.colimitsOfShape_le P (Discrete ι) _ ⟨?_⟩
  exact
    { diag := Discrete.functor E ⋙ homologyFunctor A n
      ι := ((homologyFunctor A n).mapCocone (colimit.cocone (Discrete.functor E))).ι
      isColimit := isColimitOfPreserves _ (colimit.isColimit (Discrete.functor E))
      prop_diag_obj := fun j ↦ hE j.as n }

/-- **`cohomologyIn P` is closed under a coproduct preserved by every `Hⁿ`.**
@isnad1 id=cohomolo.1h5v.s6.0e82a9a49daf from=translated src=- shape=c32b44e8 vocab=a0e32414
-/
lemma cohomologyIn_prop_coproduct {ι : Type t}
    [P.IsClosedUnderColimitsOfShape (Discrete ι)]
    (E : ι → DerivedCategory A) [HasCoproduct E]
    (hpres : ∀ n : ℤ, PreservesColimitsOfShape (Discrete ι) (homologyFunctor A n))
    (hE : ∀ i, cohomologyIn P (E i)) : cohomologyIn P (∐ E) :=
  fun n ↦ cohomologyIn_coproduct P (n := n) E (hpres n) hE

/-- **`cohomologyIn P` is closed under coproducts of shape `ι` as an `ObjectProperty`**, so that
Mathlib's full-subcategory machinery applies: `(cohomologyIn P).FullSubcategory` has coproducts
of shape `ι` and `(cohomologyIn P).ι` creates and preserves them
(`Limits.hasColimitsOfShape_of_closedUnderColimits`,
`Limits.createsColimitsOfShapeFullSubcategoryInclusion`).

The hypothesis `hpres` is stated rather than assumed as an instance for the same reason as in
`cohomologyIn_prop_coproduct`.  A colimit of shape `Discrete ι` of a diagram `p.diag` is a
coproduct of the family `i ↦ p.diag.obj ⟨i⟩` up to the isomorphism `Discrete.natIsoFunctor`, and
`cohomologyIn_prop_coproduct` applies degreewise.
@isnad1 id=isclosed.1h3v.s6.744f14bf8ec6 from=translated src=- shape=4ccd3e67 vocab=c21f47a5
-/
lemma cohomologyIn_isClosedUnderColimitsOfShape_discrete {ι : Type t}
    [P.IsClosedUnderColimitsOfShape (Discrete ι)] [P.IsClosedUnderIsomorphisms]
    [HasCoproductsOfShape ι (DerivedCategory A)]
    (hpres : ∀ n : ℤ, PreservesColimitsOfShape (Discrete ι) (homologyFunctor A n)) :
    (cohomologyIn P).IsClosedUnderColimitsOfShape (Discrete ι) where
  colimitsOfShape_le := by
    rintro Y ⟨p⟩
    have e : Y ≅ ∐ (fun i => p.diag.obj ⟨i⟩) :=
      p.isColimit.coconePointUniqueUpToIso (colimit.isColimit p.diag) ≪≫
        HasColimit.isoOfNatIso Discrete.natIsoFunctor
    intro n
    exact P.prop_of_iso ((homologyFunctor A n).mapIso e.symm)
      (cohomologyIn_prop_coproduct P _ hpres (fun i => p.prop_diag_obj ⟨i⟩) n)

end Coproducts

end DerivedCategory
