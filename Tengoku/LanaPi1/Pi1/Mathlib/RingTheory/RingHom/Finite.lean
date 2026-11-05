module

public import Tengoku.Seed.RingTheory.Finiteness.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

universe u

/--
@isnad1 id=iff.0h2v.s6.edc04efd8814 from=translated src=- shape=0b1c07de vocab=b7306f2a
-/
lemma RingHom.finite_algebraMap_iff {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] : (algebraMap R S).Finite ↔ Module.Finite R S := by
  simp only [RingHom.Finite]
  congr!
  exact Algebra.algebra_ext _ _ fun _ ↦ rfl
