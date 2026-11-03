import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuadraticCharacterField

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms subfield_eq_of_deck_moved` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms detector_generates` (it only prints; the queue checks the axioms of every declaration). -/

/-! A detector moved by the deck map generates the quadratic fixed field.
The actual chart, its common fixed field, and a legitimate restriction of
global invariants remain explicit application obligations. -/

noncomputable section
namespace AlbertLean.Generic.DetectorFieldSandwich

open QuadraticCharacterDescent

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [CharZero Ω]

/-- Any intermediate subfield containing a deck-separated detector is the
whole tau-fixed field. No classification of all chart symmetries is needed.
@isnad1 id=eq.4h5v.s8.14335df32222 from=translated src=- shape=9f482220 vocab=5b9302a1
-/
theorem subfield_eq_of_deck_moved (D : Data (k := k) (Ω := Ω))
    (R : Subfield Ω) (hbase : ∀ a : k, algebraMap k Ω a ∈ R)
    (hfixed : R ≤ D.fixedField) (w : Ω) (hw : w ∈ R)
    (hsep : D.delta w ≠ w) : R = D.fixedField := by
  obtain ⟨a, b, hab⟩ := (D.tau_fixed_iff w).mp (hfixed hw)
  have hb : algebraMap k Ω b ≠ 0 := by
    intro h
    apply hsep
    rw [hab, h, zero_mul, add_zero]
    exact D.delta.commutes a
  have hu : D.u = (w - algebraMap k Ω a) / algebraMap k Ω b := by
    apply (eq_div_iff hb).2
    rw [hab]
    ring
  have huR : D.u ∈ R := by
    rw [hu]
    exact R.div_mem (R.sub_mem hw (hbase a)) (hbase b)
  apply le_antisymm hfixed
  intro x hx
  obtain ⟨c, d, hcd⟩ := (D.tau_fixed_iff x).mp hx
  rw [hcd]
  exact R.add_mem (hbase c) (R.mul_mem (hbase d) huR)

/-- The original scalar field and one separated detector generate the field.
@isnad1 id=eq.2h4v.s8.f4cebdbb8c5f from=translated src=- shape=d3ab7217 vocab=623681e3
-/
theorem detector_generates (D : Data (k := k) (Ω := Ω))
    (w : Ω) (hw : D.tau w = w) (hsep : D.delta w ≠ w) :
    Subfield.closure (Set.range (algebraMap k Ω) ∪ {w}) = D.fixedField := by
  apply subfield_eq_of_deck_moved D _
  · intro a
    exact Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
  · apply Subfield.closure_le.mpr
    intro x hx
    rcases hx with ⟨a, rfl⟩ | hx
    · exact D.tau.commutes a
    · rw [Set.mem_singleton_iff.mp hx]
      exact hw
  · exact Subfield.subset_closure (Or.inr (Set.mem_singleton w))
  · exact hsep

end AlbertLean.Generic.DetectorFieldSandwich
