/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.Seed.CategoryTheory.Localization.SmallShiftedHom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Composition of degree-zero shifted morphisms in a localization

Two composition lemmas for `SmallShiftedHom` that Mathlib's `SmallShiftedHom.mk₀` API lacks
at the pin: composing two degree-zero shifted morphisms, and composing a shifted morphism
with a degree-zero one. Both are stated for an arbitrary morphism property compatible with
the shift; their use for the injective-resolution presentation of `Ext` is in
`Algebra/Homology/DerivedCategory/Ext/InjectiveResolutionNaturality.lean`.
-/

universe w v u

open CategoryTheory Category Localization

namespace CategoryTheory.Localization.SmallShiftedHom

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {M : Type*} [AddMonoid M]
  [HasShift C M] [W.IsCompatibleWithShift M] {X Y Z : C}

/-- Composing two degree-zero shifted morphisms is the degree-zero shifted composition.
@isnad1 id=eq.1h9v.s7.613cac1fb876 from=translated src=- shape=c546ec24 vocab=feca070e
-/
lemma mk₀_comp_mk₀' [HasSmallLocalizedShiftedHom.{w} W M X Y]
    [HasSmallLocalizedShiftedHom.{w} W M Y Z] [HasSmallLocalizedShiftedHom.{w} W M X Z]
    [HasSmallLocalizedShiftedHom.{w} W M Z Z]
    (m₀ : M) (hm₀ : m₀ = 0) (f : X ⟶ Y) (g : Y ⟶ Z) :
    (SmallShiftedHom.mk₀ W m₀ hm₀ f).comp (SmallShiftedHom.mk₀ W m₀ hm₀ g)
        (by rw [hm₀, zero_add]) =
      SmallShiftedHom.mk₀ W m₀ hm₀ (f ≫ g) :=
  (SmallShiftedHom.equiv W W.Q).injective (by
    rw [SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk₀, SmallShiftedHom.equiv_mk₀,
      SmallShiftedHom.equiv_mk₀, Functor.map_comp, ShiftedHom.mk₀_comp_mk₀])

/-- Composing a shifted morphism with a degree-zero one is the shifted composition.
@isnad1 id=eq.1h10v.s7.96e8f423c6c0 from=translated src=- shape=a81032fa vocab=9a386f2f
-/
lemma mk_comp_mk₀ [HasSmallLocalizedShiftedHom.{w} W M X Y]
    [HasSmallLocalizedShiftedHom.{w} W M Y Z] [HasSmallLocalizedShiftedHom.{w} W M X Z]
    [HasSmallLocalizedShiftedHom.{w} W M Z Z]
    {m : M} (f : ShiftedHom X Y m) (m₀ : M) (hm₀ : m₀ = 0) (g : Y ⟶ Z) :
    (SmallShiftedHom.mk W f).comp (SmallShiftedHom.mk₀ W m₀ hm₀ g)
        (by rw [hm₀, zero_add]) =
      SmallShiftedHom.mk W (f ≫ g⟦m⟧') :=
  (SmallShiftedHom.equiv W W.Q).injective (by
    rw [SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk, SmallShiftedHom.equiv_mk,
      SmallShiftedHom.equiv_mk₀, ShiftedHom.comp_mk₀]
    simp [ShiftedHom.map])

end CategoryTheory.Localization.SmallShiftedHom
