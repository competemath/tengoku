import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FieldPointNilpotence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms not_isNilpotent_of_injective_witness` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_field_point_of_injective_witness` (it only prints; the queue checks the axioms of every declaration). -/

/-! A field-valued witness nonzero at `d` remains detectable after an
injective ring map: the image of `d` is not nilpotent, and some field-valued
point of the target ring is nonzero there. -/
noncomputable section
namespace AlbertLean.Generic.FieldPointOpenWitness

universe u v
variable {B C : Type u} [CommRing B] [CommRing C]
variable {L : Type v} [Field L]

theorem not_isNilpotent_of_injective_witness
    (i : B →+* C) (hi : Function.Injective i)
    (w : B →+* L) (d : B) (hd : w d ≠ 0) :
    ¬ IsNilpotent (i d) := by
  rintro ⟨n, hn⟩
  have hb : d ^ n = 0 := hi (by simpa only [map_pow, map_zero] using hn)
  have hw : (w d) ^ n = 0 := by
    simpa only [map_pow, map_zero] using congrArg w hb
  exact hd (show IsNilpotent (w d) from ⟨n, hw⟩).eq_zero

theorem exists_field_point_of_injective_witness
    (i : B →+* C) (hi : Function.Injective i)
    (w : B →+* L) (d : B) (hd : w d ≠ 0) :
    ∃ (E : Type u) (_ : Field E) (f : C →+* E), f (i d) ≠ 0 := by
  classical
  by_contra h
  apply not_isNilpotent_of_injective_witness i hi w d hd
  apply FieldPointNilpotence.isNilpotent_of_forall_field_maps_zero
  intro E hE f
  by_contra hf
  exact h ⟨E, hE, f, hf⟩

end AlbertLean.Generic.FieldPointOpenWitness
