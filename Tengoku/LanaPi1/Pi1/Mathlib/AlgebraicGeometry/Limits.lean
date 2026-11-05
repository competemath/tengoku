module

public import Tengoku.Seed.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

universe u w

open CategoryTheory Limits

namespace AlgebraicGeometry

section General

lemma isClosedImmersion_of_isPreimmersion_of_isClosed
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsPreimmersion f] (hf : IsClosed (Set.range f.base)) :
    IsClosedImmersion f where
  isClosedEmbedding := ⟨Scheme.Hom.isEmbedding f, hf⟩

lemma isClosedImmersion_iff_isClosed_range_of_isPreimmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsPreimmersion f] :
    IsClosedImmersion f ↔ IsClosed (Set.range f.base) :=
  ⟨fun _ ↦ f.isClosedEmbedding.isClosed_range,
    fun h ↦ isClosedImmersion_of_isPreimmersion_of_isClosed f h⟩

end General
