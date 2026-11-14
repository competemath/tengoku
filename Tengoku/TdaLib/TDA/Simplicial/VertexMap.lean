import Tengoku.Seed.AlgebraicTopology.SimplicialComplex.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Noninjective simplicial vertex maps

A vertex map between preabstract simplicial complexes is a total function on the
ambient vertex types whose finite images preserve faces.  The definition does
not require injectivity, order, or preservation of face cardinality.
-/

universe u v w z

namespace TDA.Simplicial

open Finset

noncomputable section

variable {I : Type u} {J : Type v} {P : Type w} {Q : Type z}

local instance (α : Type*) : DecidableEq α := Classical.decEq α

/-- A simplicial vertex map between preabstract simplicial complexes.-/
structure VertexMap (K : PreAbstractSimplicialComplex I)
    (L : PreAbstractSimplicialComplex J) where
  /-- The total map on ambient vertices.-/
  toFun : I → J
  /-- The image of every source face is a target face.-/
  map_face : ∀ s, s ∈ K →
    @Finset.image I J (Classical.decEq J) toFun s ∈ L

instance (K : PreAbstractSimplicialComplex I) (L : PreAbstractSimplicialComplex J) :
    CoeFun (VertexMap K L) (fun _ => I → J) := ⟨VertexMap.toFun⟩

/-- Two vertex maps are equal when their ambient functions are pointwise equal.
@isnad1 id=eq.1h6v.s5.6f5450677bb6 from=translated src=- shape=c29487d5 vocab=4926fcb2
-/
@[ext] theorem VertexMap.ext {K : PreAbstractSimplicialComplex I}
    {L : PreAbstractSimplicialComplex J} {f g : VertexMap K L}
    (h : ∀ i, f i = g i) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      cases funext h
      rfl

/-- The identity vertex map.-/
def VertexMap.id (K : PreAbstractSimplicialComplex I) : VertexMap K K :=
  { toFun := fun i => i
    map_face := by
      intro s hs
      simpa using hs }

/-- Vertex maps compose by composing their ambient functions.-/
def VertexMap.comp {K : PreAbstractSimplicialComplex I}
    {L : PreAbstractSimplicialComplex J} {M : PreAbstractSimplicialComplex P}
    (f : VertexMap K L) (g : VertexMap L M) : VertexMap K M :=
  { toFun := g.toFun ∘ f.toFun
    map_face := by
      intro s hs
      have hf : @Finset.image I J (Classical.decEq J) f.toFun s ∈ L :=
        f.map_face s hs
      have hg := g.map_face (@Finset.image I J (Classical.decEq J) f.toFun s) hf
      simpa only [Finset.image_image, Function.comp_apply] using hg }

/--
@isnad1 id=eq.0h9v.s5.bb46ab5df1c9 from=translated src=- shape=79a9e27d vocab=e820f0f4
-/
@[simp] theorem VertexMap.comp_apply {K : PreAbstractSimplicialComplex I}
    {L : PreAbstractSimplicialComplex J} {M : PreAbstractSimplicialComplex P}
    (f : VertexMap K L) (g : VertexMap L M) (i : I) : VertexMap.comp f g i = g (f i) := rfl

/--
@isnad1 id=eq.0h3v.s4.8b4e52cfa3d8 from=translated src=- shape=7f1a4b83 vocab=d72be005
-/
@[simp] theorem VertexMap.id_apply (K : PreAbstractSimplicialComplex I) (i : I) :
    VertexMap.id K i = i := rfl

/-! Extensional identity and associativity laws. -/

/--
@isnad1 id=eq.0h5v.s5.68cda6fe3b44 from=translated src=- shape=b2d8c2d9 vocab=46da3cc1
-/
theorem VertexMap.id_comp {K : PreAbstractSimplicialComplex I}
    {L : PreAbstractSimplicialComplex J} (f : VertexMap K L) :
    VertexMap.comp (VertexMap.id K) f = f := by
  apply VertexMap.ext
  intro i
  simp [VertexMap.comp, VertexMap.id]

/--
@isnad1 id=eq.0h5v.s5.da6a1eeb29f1 from=translated src=- shape=26774166 vocab=46da3cc1
-/
theorem VertexMap.comp_id {K : PreAbstractSimplicialComplex I}
    {L : PreAbstractSimplicialComplex J} (f : VertexMap K L) :
    VertexMap.comp f (VertexMap.id L) = f := by
  apply VertexMap.ext
  intro i
  simp [VertexMap.comp, VertexMap.id]

/--
@isnad1 id=eq.0h11v.s6.17ed377a12ba from=translated src=- shape=27e22358 vocab=bba81ace
-/
theorem VertexMap.comp_assoc {K : PreAbstractSimplicialComplex I}
    {L : PreAbstractSimplicialComplex J} {M : PreAbstractSimplicialComplex P}
    {N : PreAbstractSimplicialComplex Q} (f : VertexMap K L) (g : VertexMap L M)
    (h : VertexMap M N) :
    VertexMap.comp (VertexMap.comp f g) h = VertexMap.comp f (VertexMap.comp g h) := by
  apply VertexMap.ext
  intro i
  rfl

/-- The pointwise face condition is equivalent to image-complex containment.

The local classical equality decision is used only by the finite-image
operation in the pinned mathlib definition of `PreAbstractSimplicialComplex.map`.
@isnad1 id=iff.0h5v.s6.f785bb8098f8 from=translated src=- shape=ab3beb3e vocab=132c2c9c
-/
theorem map_le_iff {K : PreAbstractSimplicialComplex I}
    {L : PreAbstractSimplicialComplex J} (r : I → J) :
    PreAbstractSimplicialComplex.map K r ≤ L ↔ ∀ s ∈ K, s.image r ∈ L := by
  constructor
  · intro h s hs
    exact h (by
      change s.image r ∈ PreAbstractSimplicialComplex.map K r
      exact ⟨s, hs, rfl⟩)
  · intro h s hs
    change s ∈ K.faces.image (fun t => t.image r) at hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact h t ht

/-- A vertex map's field is exactly the image-complex containment condition.
@isnad1 id=iff.0h5v.s6.750ac5a78d7b from=translated src=- shape=8c2f8aaa vocab=4c81fa5c
-/
theorem VertexMap.map_le_iff {K : PreAbstractSimplicialComplex I}
    {L : PreAbstractSimplicialComplex J} (f : VertexMap K L) :
    PreAbstractSimplicialComplex.map K f ≤ L ↔ ∀ s ∈ K, s.image f ∈ L := by
  exact TDA.Simplicial.map_le_iff f

end
end TDA.Simplicial
