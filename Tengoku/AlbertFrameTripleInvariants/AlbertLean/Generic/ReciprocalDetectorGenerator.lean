import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ReciprocalFixedField

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms moved_generates` (it only prints; the queue checks the axioms of every declaration). -/

/-! Any element moved by the reciprocal involution generates its quadratic
extension over the fixed field. This uses the checked two-coefficient form. -/
noncomputable section
namespace AlbertLean.Generic.ReciprocalDetectorGenerator

open NestedReciprocalField

variable (B : Type*) [Field B] [CharZero B] (m : B) (hm : m ≠ 0)

/-- A moved detector recovers the original determinant root over the fixed field.
@isnad1 id=eq.2h3v.s11.2fc50f404a38 from=translated src=- shape=87750976 vocab=b4d8a3ce
-/
theorem moved_generates (d : Omega B) (hd : σ B m hm d ≠ d) :
    Subfield.closure ((invariantField B m : Set (Omega B)) ∪ {d}) = ⊤ := by
  let D := Subfield.closure ((invariantField B m : Set (Omega B)) ∪ {d})
  have base_mem (x : invariantField B m) : (x : Omega B) ∈ D :=
    Subfield.subset_closure (Or.inl x.property)
  have dmem : d ∈ D := Subfield.subset_closure (Or.inr rfl)
  obtain ⟨a,b,h⟩ := exists_two_coefficients B m hm d
  have hb : (b : Omega B) ≠ 0 := by
    intro hb
    have ha : d = (a : Omega B) := by simpa only [hb, zero_mul, add_zero] using h
    apply hd
    rw [ha]
    exact invariantField_fixed B m hm _ a.property
  have ht : T B = (d - (a : Omega B)) / (b : Omega B) := by
    rw [h]
    field_simp [hb] <;> ring
  have tmem : T B ∈ D := by
    rw [ht]
    exact D.div_mem (D.sub_mem dmem (base_mem a)) (base_mem b)
  apply top_unique
  intro z _
  obtain ⟨a,b,hz⟩ := exists_two_coefficients B m hm z
  change z ∈ D
  rw [hz]
  exact D.add_mem (base_mem a) (D.mul_mem (base_mem b) tmem)

end AlbertLean.Generic.ReciprocalDetectorGenerator
