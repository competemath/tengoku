module

public import Tengoku.Seed.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

universe u w

open CategoryTheory Limits

namespace AlgebraicGeometry

section General

/--
@isnad1 id=isclosed.1h3v.s7.f2dccdc7d195 from=translated src=- shape=6aaa75a0 vocab=6dabc086
-/
lemma isClosedImmersion_of_isPreimmersion_of_isClosed
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsPreimmersion f] (hf : IsClosed (Set.range f.base)) :
    IsClosedImmersion f where
  isClosedEmbedding := ⟨Scheme.Hom.isEmbedding f, hf⟩

/--
@isnad1 id=iff.0h3v.s7.982cd7626d82 from=translated src=- shape=03aa9df0 vocab=6dabc086
-/
lemma isClosedImmersion_iff_isClosed_range_of_isPreimmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsPreimmersion f] :
    IsClosedImmersion f ↔ IsClosed (Set.range f.base) :=
  ⟨fun _ ↦ f.isClosedEmbedding.isClosed_range,
    fun h ↦ isClosedImmersion_of_isPreimmersion_of_isClosed f h⟩

end General
