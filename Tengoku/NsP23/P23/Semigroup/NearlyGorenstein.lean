import Tengoku.NsP23.P23.Semigroup.PseudoFrobenius

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The numerical-semigroup PF NG-vector interface

This is exactly the pseudo-Frobenius NG-vector characterization used by the
P23 human authority.  This module does not claim a separate proof of its
equivalence with the trace definition for the one-dimensional local
semigroup ring.
-/

namespace P23.Semigroup

noncomputable section

open FourGeneratedNumericalSemigroup

/-- A pseudo-Frobenius integer witnessing the standard NG-vector condition at
one of the four minimal generators.-/
def NGWitnessForGenerator (D : FourGeneratedNumericalSemigroup)
    (j : Fin 4) (f : D.PseudoFrobeniusIndex) : Prop :=
  ∀ g : D.PseudoFrobeniusIndex,
    IntInGamma D ((D.n j : ℤ) + f.1 - g.1)

/-- The project-level numerical-semigroup nearly-Gorenstein predicate: the
standard PF NG-vector criterion used by the human proof.-/
def SemigroupNearlyGorenstein (D : FourGeneratedNumericalSemigroup) : Prop :=
  ∀ j : Fin 4, ∃ f : D.PseudoFrobeniusIndex,
    NGWitnessForGenerator D j f

/-- Stable semantic interface exposing the exact NG-vector criterion.
@isnad1 id=iff.0h1v.s5.8a57d6487f74 from=translated src=- shape=8f85a152 vocab=8efa0c44
-/
theorem semigroupNearlyGorenstein_iff_ngVector
    (D : FourGeneratedNumericalSemigroup) :
    SemigroupNearlyGorenstein D ↔
      ∀ j : Fin 4, ∃ f : D.PseudoFrobeniusIndex,
        ∀ g : D.PseudoFrobeniusIndex,
          IntInGamma D ((D.n j : ℤ) + f.1 - g.1) := by
  rfl

/--
@isnad1 id=ex.1h2v.s4.51068fb4bc90 from=translated src=- shape=94a10c7c vocab=300ab894
-/
theorem exists_ngWitness (D : FourGeneratedNumericalSemigroup)
    (hng : SemigroupNearlyGorenstein D) (j : Fin 4) :
    ∃ f : D.PseudoFrobeniusIndex, NGWitnessForGenerator D j f :=
  hng j

/-- The witness at the selected base generator, retained for the later source
lemma although it is not needed by the Run22 trace proof.
@isnad1 id=ex.1h2v.s4.51068fb4bc90 from=translated src=- shape=94a10c7c vocab=300ab894
-/
theorem exists_base_ngWitness (D : FourGeneratedNumericalSemigroup)
    (hng : SemigroupNearlyGorenstein D) (i : Fin 4) :
    ∃ f : D.PseudoFrobeniusIndex, NGWitnessForGenerator D i f :=
  exists_ngWitness D hng i

/-- The witness at a chosen tail, with the original generator index preserved
by `tailIndex`.
@isnad1 id=ex.1h3v.s6.cf6b95898959 from=translated src=- shape=325bcc49 vocab=683bee7a
-/
theorem exists_tail_ngWitness (D : FourGeneratedNumericalSemigroup)
    (hng : SemigroupNearlyGorenstein D) (i : Fin 4) (j : Fin 3) :
    ∃ f : D.PseudoFrobeniusIndex,
      NGWitnessForGenerator D (D.tailIndex i j) f :=
  exists_ngWitness D hng (D.tailIndex i j)

end

end P23.Semigroup
