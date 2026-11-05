module

public import Tengoku.Seed.RingTheory.Finiteness.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

universe u

lemma RingHom.finite_algebraMap_iff {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] : (algebraMap R S).Finite ↔ Module.Finite R S := by
  simp only [RingHom.Finite]
  congr!
  exact Algebra.algebra_ext _ _ fun _ ↦ rfl
