import Tengoku.Seed.Algebra.Field.Subfield.Basic
import Tengoku.Seed.Algebra.GroupWithZero.Units.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms agreement_of_mem_generated_field` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms not_mem_generated_field_of_companion` (it only prints; the queue checks the axioms of every declaration). -/

/-! A companion need only define a map of the raw ring. Agreement on the
measurement generators forces agreement on every raw element whose image is
in their generated field. No map of the whole fraction field is assigned to
the companion. Intended consumer: the actual Albert generic companion. -/

namespace AlbertLean.Generic.RawCompanionSeparation

variable {R F K : Type*} [CommRing R] [Field F] [Field K]

theorem agreement_of_mem_generated_field
    (i : R →+* F) (hi : Function.Injective i)
    (phi : F →+* K) (e : R →+* K) (S : Set R)
    (hS : ∀ x ∈ S, e x = phi (i x))
    (d : R) (hd : i d ∈ Subfield.closure (i '' S)) :
    e d = phi (i d) := by
  have hc : ∀ x ∈ Subring.closure S, e x = phi (i x) :=
    RingHom.eqOn_set_closure (f := e) (g := phi.comp i) hS
  obtain ⟨a, ha, b, hb, hab⟩ := Subfield.mem_closure_iff.mp hd
  rw [← i.map_closure] at ha hb
  obtain ⟨ar, har, rfl⟩ := Subring.mem_map.mp ha
  obtain ⟨br, hbr, rfl⟩ := Subring.mem_map.mp hb
  by_cases hb0 : i br = 0
  · have hid : i d = 0 := by simpa only [hb0, div_zero] using hab.symm
    have hd0 : d = 0 := hi (by simpa only [map_zero] using hid)
    simp only [hd0, map_zero]
  · have hmul : i ar = i d * i br := (div_eq_iff hb0).mp hab
    have hraw : ar = d * br := hi (by simpa only [map_mul] using hmul)
    have hphi : phi (i br) ≠ 0 := by
      simpa only [map_zero] using phi.injective.ne hb0
    apply mul_right_cancel₀ hphi
    calc
      e d * phi (i br) = e (d * br) := by rw [map_mul, hc br hbr]
      _ = e ar := congrArg e hraw.symm
      _ = phi (i ar) := hc ar har
      _ = phi (i d) * phi (i br) := by rw [hmul, map_mul]

/-- Separation at an actual ring-valued companion rules out membership in
the original measurement field. Neither injectivity of the companion map
nor a dominant chart is a hypothesis.-/
theorem not_mem_generated_field_of_companion
    (i : R →+* F) (hi : Function.Injective i)
    (phi : F →+* K) (e : R →+* K) (S : Set R)
    (hS : ∀ x ∈ S, e x = phi (i x))
    (d : R) (hsep : e d ≠ phi (i d)) :
    i d ∉ Subfield.closure (i '' S) := by
  intro hd
  exact hsep (agreement_of_mem_generated_field i hi phi e S hS d hd)

end AlbertLean.Generic.RawCompanionSeparation
