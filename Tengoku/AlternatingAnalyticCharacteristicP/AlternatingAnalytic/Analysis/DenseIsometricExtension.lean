import Tengoku.Seed.Analysis.Normed.Group.Hom
import Tengoku.Seed.Analysis.Normed.Ring.Lemmas
import Tengoku.Seed.Topology.Algebra.UniformRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Extending isometric ring homomorphisms

An isometric ring homomorphism from a dense subring into a complete normed ring
extends isometrically to the whole ring. This is used for the Laurent subfield
in Lemma D.2.
-/

namespace AlternatingAnalytic

variable {A B C : Type*} [NormedRing A] [NormedRing B] [NormedRing C] [CompleteSpace C]

/-- Extend an isometric ring map across a dense isometric inclusion.
@isnad1 id=ex.3h5v.s8.38b35d8128a4 from=translated src=- shape=9d1bbb50 vocab=2cd67728
-/
theorem exists_isometric_ringHom_extension (i : A →+* B) (f : A →+* C)
    (hi : Isometry i) (hd : DenseRange i) (hf : Isometry f) :
    ∃ g : B →+* C, Isometry g ∧ ∀ a : A, g (i a) = f a := by
  let g : B →+* C := IsDenseInducing.extendRingHom hi.isUniformInducing hd hf.uniformContinuous
  have hc : Continuous g :=
    (uniformContinuous_uniformly_extend hi.isUniformInducing hd hf.uniformContinuous).continuous
  have hfix (a : A) : g (i a) = f a :=
    IsDenseInducing.extend_eq (hi.isUniformInducing.isDenseInducing hd) hf.continuous a
  refine ⟨g, AddMonoidHomClass.isometry_of_norm g ?_, hfix⟩
  intro b
  apply DenseRange.induction_on hd b (p := fun b => ‖g b‖ = ‖b‖)
    (isClosed_eq hc.norm continuous_norm) ?_
  intro a
  rw [hfix, (AddMonoidHomClass.isometry_iff_norm f).mp hf,
    (AddMonoidHomClass.isometry_iff_norm i).mp hi]

omit [CompleteSpace C] in
/-- The image of a complete ring under an isometry is the closure of the image of any
dense subring.
@isnad1 id=eq.2h5v.s8.8a86279693dd from=translated src=- shape=762597b7 vocab=06c1b3ce
-/
theorem closure_range_comp_eq_range [CompleteSpace B] (i : A →+* B) (g : B →+* C)
    (hd : DenseRange i) (hg : Isometry g) :
    closure (Set.range (g.comp i)) = Set.range g := by
  apply le_antisymm
  · apply closure_minimal _ hg.isClosedEmbedding.isClosed_range
    rintro _ ⟨a, rfl⟩
    exact ⟨i a, rfl⟩
  · rintro _ ⟨b, rfl⟩
    apply DenseRange.induction_on hd b (p := fun b => g b ∈ closure (Set.range (g.comp i)))
      (isClosed_closure.preimage hg.continuous) ?_
    intro a
    exact subset_closure ⟨a, rfl⟩

end AlternatingAnalytic
