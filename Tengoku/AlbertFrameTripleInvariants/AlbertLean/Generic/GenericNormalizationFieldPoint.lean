import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FieldPointOpenWitness
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.GenericBaseLocalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms exists_generic_normalization_field_point` (it only prints; the queue checks the axioms of every declaration). -/

/-! A torsion-free parameter algebra with one legal witness has a legal field
point over an injective copy of the base fraction field.  This theorem does not
construct the parameter algebra or discharge its torsion-freeness. -/

noncomputable section
namespace AlbertLean.Generic.GenericNormalizationFieldPoint

open GenericBaseLocalization FieldPointOpenWitness

universe u v
variable {A B : Type u} [CommRing A] [CommRing B] [IsDomain A] [Nontrivial B]
  [Algebra A B] [Module.IsTorsionFree A B]
variable {L : Type v} [Field L]

theorem exists_generic_normalization_field_point
    (w : B →+* L) (D : B) (hD : w D ≠ 0) :
    ∃ (E : Type u) (_ : Field E) (j : FractionRing A →+* E),
      Function.Injective j ∧
      ∃ f : B →+* E, f D ≠ 0 ∧ ∀ a : A,
        f (algebraMap A B a) = j (algebraMap A (FractionRing A) a) := by
  obtain ⟨E, hE, g, hg⟩ := exists_field_point_of_injective_witness
    (algebraMap B (GenericBaseRing A B)) (algebraMap_injective A B) w D hD
  letI : Field E := hE
  let j : FractionRing A →+* E := g.comp (fractionMap A B)
  let f : B →+* E := g.comp (algebraMap B (GenericBaseRing A B))
  refine ⟨E, hE, j, RingHom.injective j, f, ?_, ?_⟩
  · exact hg
  · intro a
    simp [f, j, coefficientMap, fractionMap_algebraMap]

end AlbertLean.Generic.GenericNormalizationFieldPoint
