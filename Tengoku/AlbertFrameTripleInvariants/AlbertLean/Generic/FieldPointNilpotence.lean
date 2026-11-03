import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.TensorDifferenceDescent
import Tengoku.Seed.RingTheory.Ideal.Quotient.Operations
import Tengoku.Seed.RingTheory.Localization.FractionRing
import Tengoku.Seed.RingTheory.Nilpotent.Lemmas
import Tengoku.Seed.RingTheory.TensorProduct.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms exists_base_of_field_embedding_agreement` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms isNilpotent_of_forall_field_maps_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms tensorDifference_isNilpotent_of_field_embedding_agreement` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Field-valued points detect nilpotence.  The quantifier ranges over fields in
the ring's universe, which includes every fraction field of a prime quotient.
-/

noncomputable section
open scoped TensorProduct
namespace AlbertLean.Generic.FieldPointNilpotence

universe u v

/-- If every field-valued point kills an element, that element belongs to every
prime ideal and is therefore nilpotent.
@isnad1 id=isnilpot.1h2v.s6.4cc35bee83b5 from=translated src=- shape=c46eaa54 vocab=db32e066
-/
theorem isNilpotent_of_forall_field_maps_zero
    {R : Type u} [CommRing R] (r : R)
    (hfield : ∀ (L : Type u) (_ : Field L) (f : R →+* L), f r = 0) :
    IsNilpotent r := by
  rw [nilpotent_iff_mem_prime]
  intro p hp
  letI : p.IsPrime := hp
  let Q := R ⧸ p
  let L := FractionRing Q
  let j : Q →+* L := algebraMap Q L
  let f : R →+* L := j.comp (Ideal.Quotient.mk p)
  have hz : f r = 0 := hfield L inferInstance f
  have hq : Ideal.Quotient.mk p r = 0 := by
    apply (IsFractionRing.injective Q L)
    simpa [f, j] using hz
  exact Ideal.Quotient.eq_zero_iff_mem.mp hq

section TensorAdapter

variable (H : Type u) (K : Type v) [Field H] [Field K] [Algebra H K]

/-- Agreement of the two induced copies of `K` at `a`, for every field-valued
point of the tensor product, implies nilpotence of `a ⊗ 1 - 1 ⊗ a`.

The hypothesis asks only that two ring maps agree on the displayed copy of
`H`; it does not assume `K/H` algebraic.
@isnad1 id=isnilpot.1h3v.s10.41069143b431 from=translated src=- shape=c18ef8f5 vocab=6c505822
-/
theorem tensorDifference_isNilpotent_of_field_embedding_agreement
    (a : K)
    (hagree : ∀ (L : Type v) (_ : Field L)
      (left right : K →+* L),
      (∀ x : H, left (algebraMap H K x) = right (algebraMap H K x)) →
      left a = right a) :
    IsNilpotent
      (a ⊗ₜ[H] (1 : K) - (1 : K) ⊗ₜ[H] a : K ⊗[H] K) := by
  apply isNilpotent_of_forall_field_maps_zero
  intro L instL f
  let left : K →+* L := f.comp
    (Algebra.TensorProduct.includeLeft (R := H) (S := H) (A := K) (B := K)).toRingHom
  let right : K →+* L := f.comp
    (Algebra.TensorProduct.includeRight (R := H) (A := K) (B := K)).toRingHom
  have hbase : ∀ x : H,
      left (algebraMap H K x) = right (algebraMap H K x) := by
    intro x
    simp [left, right, Algebra.TensorProduct.algebraMap_apply']
  have ha : left a = right a := hagree L instL left right hbase
  simpa [left, right, sub_eq_zero] using ha

end TensorAdapter

/-- Field-valued comparisons detect precisely the base field in characteristic
zero. The extension itself may have positive transcendence degree.
@isnad1 id=ex.1h3v.s8.a3e1991a3928 from=translated src=- shape=27d8e4e3 vocab=f5e020c8
-/
theorem exists_base_of_field_embedding_agreement
    (H : Type u) (K : Type v) [Field H] [CharZero H] [Field K] [Algebra H K]
    (a : K)
    (hagree : ∀ (L : Type v) (_ : Field L) (left right : K →+* L),
      (∀ x : H, left (algebraMap H K x) = right (algebraMap H K x)) →
      left a = right a) :
    ∃ h : H, algebraMap H K h = a := by
  apply TensorDifferenceDescent.exists_base_of_difference_isNilpotent H K a
  exact tensorDifference_isNilpotent_of_field_embedding_agreement H K a hagree

end AlbertLean.Generic.FieldPointNilpotence
