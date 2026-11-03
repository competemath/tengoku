import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ResidualOrientationField
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.GenericLedgerFixedField

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms generic_z1_ne` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms ledger_gauge_eq_orientation` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms orientationLedgerField_degree_two` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section

namespace AlbertLean.Generic.GenericOrientationAttachment

open AlbertLean.Residual.FrameIdeal
open AlbertLean.Generic.GenericDeterminantOpen
open AlbertLean.Generic.GenericFieldChart
open AlbertLean.Generic.GenericLedgerFixedField
open AlbertLean.Generic.NestedReciprocalField
open AlbertLean.Generic.ResidualLedgerMomentField
open AlbertLean.Generic.ResidualOrientationField

universe u
variable (k : Type u) [Field k] [CharZero k]

def groundBase : Subfield (FunctionField k) :=
  Subfield.closure (Set.range (algebraMap k (FunctionField k)))

/--
@isnad1 id=le.0h1v.s10.748d5f6a469f from=translated src=- shape=6746b013 vocab=08b9ddd2
-/
theorem ground_le_gauge : groundBase k ≤ gaugeBase k := by
  apply Subfield.closure_le.2
  rintro _ ⟨a,rfl⟩
  exact Subfield.subset_closure (Or.inl ⟨a,rfl⟩)

/--
@isnad1 id=ne.0h1v.s9.304a56664440 from=translated src=- shape=805f1cc7 vocab=6586004b
-/
theorem generic_z1_ne : (genericChart k).z1 ≠ 0 := by
  change includeBase k (ι k (GenericDeterminantOpen.a k)) ≠ 0
  apply (map_ne_zero (includeBase k)).mpr
  intro hι
  have h : GenericDeterminantOpen.a k = 0 := by
    apply iota_injective k
    simpa using hι
  have hh := congrArg (witnessEval k) h
  simpa [GenericDeterminantOpen.a, gaugeX, GenericDeterminantOpen.x,
    witnessEval, witnessValue] using hh

/--
@isnad1 id=eq.0h1v.s9.3609717657c2 from=translated src=- shape=805f1cc7 vocab=36660c53
-/
theorem generic_r1 : (genericChart k).r1 = 1 := by
  rfl

/-- Adjoining the three normalized gauge variables to the ledger base is
the same generated field as adjoining all four gauge coordinates after
forming the ground-base ledger.
@isnad1 id=eq.0h1v.s9.4db5cf29e46b from=translated src=- shape=d620cab6 vocab=1d9f863b
-/
theorem ledger_gauge_eq_gaugeAugmented :
    ledgerField (gaugeBase k) (encoderA (genericChart k))
        (encoderB (genericChart k)) =
      gaugeAugmentedLedgerField (groundBase k) (genericChart k) := by
  let L := ledgerField (groundBase k) (encoderA (genericChart k)) (encoderB (genericChart k))
  let C := ledgerField (gaugeBase k) (encoderA (genericChart k)) (encoderB (genericChart k))
  let G := gaugeAugmentedLedgerField (groundBase k) (genericChart k)
  have hbase : gaugeBase k ≤ G := by
    apply Subfield.closure_le.2
    change gaugeGenerators k ⊆ G
    rintro z (⟨a,rfl⟩ | hz)
    · exact Subfield.subset_closure (Or.inl
        (Subfield.subset_closure (Or.inl (Subfield.subset_closure ⟨a,rfl⟩))))
    · rcases hz with rfl | rfl | rfl
      · exact Subfield.subset_closure (Or.inr (Or.inr (Or.inl rfl)))
      · exact Subfield.subset_closure (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact Subfield.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  have hLC : L ≤ C := by
    apply Subfield.closure_le.2
    change (groundBase k : Set (FunctionField k)) ∪
      ledgerCells (encoderA (genericChart k)) (encoderB (genericChart k)) ⊆ C
    rintro z (hz | hz)
    · exact Subfield.subset_closure (Or.inl (ground_le_gauge k hz))
    · exact Subfield.subset_closure (Or.inr hz)
  apply le_antisymm
  · apply Subfield.closure_le.2
    change (gaugeBase k : Set (FunctionField k)) ∪
      ledgerCells (encoderA (genericChart k)) (encoderB (genericChart k)) ⊆ G
    rintro z (hz | hz)
    · exact hbase hz
    · exact Subfield.subset_closure (Or.inl (Subfield.subset_closure (Or.inr hz)))
  · apply Subfield.closure_le.2
    change (L : Set (FunctionField k)) ∪
      {(genericChart k).r1, (genericChart k).z1,
        (genericChart k).r2, (genericChart k).z2} ⊆ C
    rintro z (hz | hz)
    · exact hLC hz
    · rcases hz with rfl | rfl | rfl | rfl
      · rw [generic_r1]; exact C.one_mem
      · exact Subfield.subset_closure (Or.inl (gauge_mem_a k))
      · exact Subfield.subset_closure (Or.inl (gauge_mem_b k))
      · exact Subfield.subset_closure (Or.inl (gauge_mem_c k))

/--
@isnad1 id=eq.0h1v.s9.3068e38272dc from=translated src=- shape=d620cab6 vocab=bf798552
-/
theorem ledger_gauge_eq_orientation :
    ledgerField (gaugeBase k) (encoderA (genericChart k))
        (encoderB (genericChart k)) =
      orientationLedgerField (groundBase k) (genericChart k) := by
  rw [ledger_gauge_eq_gaugeAugmented]
  exact gaugeAugmentedLedgerField_eq_orientationLedgerField
    (groundBase k) (genericChart k) (generic_r1 k) (generic_z1_ne k)

/--
@isnad1 id=eq.0h1v.s8.48e6e100e791 from=translated src=- shape=8d6d4749 vocab=9288410c
-/
theorem orientation_eq_invariantField :
    orientationLedgerField (groundBase k) (genericChart k) =
      invariantField (Base k) (Matrix.det (rationalM k)) := by
  rw [← ledger_gauge_eq_orientation]
  exact generic_ledgerField_eq_invariantField k

/-- Exact degree two over the literal ledger field with only orientation
adjoined.  This makes no assertion that orientation itself has degree two
over the ground ledger field.
@isnad1 id=eq.0h1v.s12.552d4db399be from=translated src=- shape=b7fa0b4f vocab=c2462f57
-/
theorem orientationLedgerField_degree_two :
    Module.finrank (orientationLedgerField (groundBase k) (genericChart k))
      (FunctionField k) = 2 := by
  rw [orientation_eq_invariantField]
  exact invariantField_degree_two (Base k) (Matrix.det (rationalM k))
    (det_rationalM_ne_zero k)

end AlbertLean.Generic.GenericOrientationAttachment
