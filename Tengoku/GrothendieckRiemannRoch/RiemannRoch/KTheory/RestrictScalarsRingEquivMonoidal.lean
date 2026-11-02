/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.Seed.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Tengoku.Seed.Algebra.Category.ModuleCat.ChangeOfRings
import Tengoku.Seed.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
import Tengoku.Seed.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The tensor comparison for restriction of scalars along a ring isomorphism is an isomorphism

`ModuleCat.restrictScalars f` is lax monoidal for every ring homomorphism `f`, via the doctrinal
adjunction `extendScalars f ⊣ restrictScalars f`. When `f` is (the underlying map of) a ring
isomorphism `e`, `extendScalars e.toRingHom` and `restrictScalars e.toRingHom` become mutually
inverse equivalences, so the lax tensor comparison `μ` of `restrictScalars e.toRingHom` is an
isomorphism. This is the algebraic input needed to show that the canonical pullback tensor
comparison for scheme module sheaves is an isomorphism along an open immersion, where the
relevant restriction-of-scalars maps are levelwise ring isomorphisms.

The second half of the file lifts this pointwise, from `ModuleCat.restrictScalars` to
`PresheafOfModules.restrictScalars`, whose action on objects is exactly `ModuleCat.restrictScalars`
applied section by section: this is the algebraic input needed to show that
`PresheafOfModules.pushforward` along a levelwise ring isomorphism (as arises from
`Scheme.Modules.overEquiv`, `SheafOfModules.pushforwardPushforwardEquivalence`) has an isomorphic
tensor comparison — see `docs/PR_LEDGER.md`'s "`overEquivMonoidal`" discussion.
-/

noncomputable section

open CategoryTheory ModuleCat Functor MonoidalCategory

universe u

variable {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)

/-- The lax tensor comparison for restriction of scalars along a ring isomorphism is an
isomorphism.-/
theorem ModuleCat.restrictScalars_isIso_μ_of_ringEquiv (M N : ModuleCat S) :
    IsIso (Functor.LaxMonoidal.μ (ModuleCat.restrictScalars e.toRingHom) M N) := by
  haveI hu : IsIso (extendRestrictScalarsAdj e.toRingHom).unit :=
    Adjunction.instIsIsoFunctorUnitOfIsEquivalence (extendRestrictScalarsAdj e.toRingHom)
  haveI hc : IsIso (extendRestrictScalarsAdj e.toRingHom).counit := by infer_instance
  haveI hcM : IsIso ((extendRestrictScalarsAdj e.toRingHom).counit.app M) :=
    NatIso.isIso_app_of_isIso _ M
  haveI hcN : IsIso ((extendRestrictScalarsAdj e.toRingHom).counit.app N) :=
    NatIso.isIso_app_of_isIso _ N
  haveI hunit : IsIso ((extendRestrictScalarsAdj e.toRingHom).unit.app
      (MonoidalCategoryStruct.tensorObj ((restrictScalars e.toRingHom).obj M)
        ((restrictScalars e.toRingHom).obj N) : ModuleCat R)) :=
    NatIso.isIso_app_of_isIso _ _
  haveI ht : IsIso (MonoidalCategoryStruct.tensorHom
      ((extendRestrictScalarsAdj e.toRingHom).counit.app M)
      ((extendRestrictScalarsAdj e.toRingHom).counit.app N)) :=
    tensor_isIso ((extendRestrictScalarsAdj e.toRingHom).counit.app M)
      ((extendRestrictScalarsAdj e.toRingHom).counit.app N)
  haveI hd : IsIso (Functor.OplaxMonoidal.δ (extendScalars e.toRingHom)
      ((restrictScalars e.toRingHom).obj M) ((restrictScalars e.toRingHom).obj N)) := by
    infer_instance
  haveI hdt : IsIso (Functor.OplaxMonoidal.δ (extendScalars e.toRingHom)
      ((restrictScalars e.toRingHom).obj M) ((restrictScalars e.toRingHom).obj N) ≫
      MonoidalCategoryStruct.tensorHom
        ((extendRestrictScalarsAdj e.toRingHom).counit.app M)
        ((extendRestrictScalarsAdj e.toRingHom).counit.app N)) :=
    IsIso.comp_isIso' hd ht
  haveI hmap : IsIso ((restrictScalars e.toRingHom).map
      (Functor.OplaxMonoidal.δ (extendScalars e.toRingHom)
          ((restrictScalars e.toRingHom).obj M) ((restrictScalars e.toRingHom).obj N) ≫
        MonoidalCategoryStruct.tensorHom
          ((extendRestrictScalarsAdj e.toRingHom).counit.app M)
          ((extendRestrictScalarsAdj e.toRingHom).counit.app N))) :=
    Functor.map_isIso (restrictScalars e.toRingHom) _
  simp only [Adjunction.rightAdjointLaxMonoidal_μ, Adjunction.homEquiv_unit]
  exact IsIso.comp_isIso' hunit hmap

variable {C : Type u} [Category.{u} C] {P Q : Cᵒᵖ ⥤ CommRingCat.{u}}
  (α : P ⋙ forget₂ CommRingCat RingCat ⟶ Q ⋙ forget₂ CommRingCat RingCat)

variable (hα : ∀ X, IsIso (α.app X)) (M N : PresheafOfModules.{u} (Q ⋙ forget₂ CommRingCat RingCat))

end
