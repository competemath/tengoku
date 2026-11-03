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

theorem ground_le_gauge : groundBase k ≤ gaugeBase k := by
  apply Subfield.closure_le.2
  rintro _ ⟨a,rfl⟩
  exact Subfield.subset_closure (Or.inl ⟨a,rfl⟩)

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

theorem generic_r1 : (genericChart k).r1 = 1 := by
  rfl

/-- Adjoining the three normalized gauge variables to the ledger base is
the same generated field as adjoining all four gauge coordinates after
forming the ground-base ledger.-/
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

theorem ledger_gauge_eq_orientation :
    ledgerField (gaugeBase k) (encoderA (genericChart k))
        (encoderB (genericChart k)) =
      orientationLedgerField (groundBase k) (genericChart k) := by
  rw [ledger_gauge_eq_gaugeAugmented]
  exact gaugeAugmentedLedgerField_eq_orientationLedgerField
    (groundBase k) (genericChart k) (generic_r1 k) (generic_z1_ne k)

theorem orientation_eq_invariantField :
    orientationLedgerField (groundBase k) (genericChart k) =
      invariantField (Base k) (Matrix.det (rationalM k)) := by
  rw [← ledger_gauge_eq_orientation]
  exact generic_ledgerField_eq_invariantField k

/-- Exact degree two over the literal ledger field with only orientation
adjoined.  This makes no assertion that orientation itself has degree two
over the ground ledger field.-/
theorem orientationLedgerField_degree_two :
    Module.finrank (orientationLedgerField (groundBase k) (genericChart k))
      (FunctionField k) = 2 := by
  rw [orientation_eq_invariantField]
  exact invariantField_degree_two (Base k) (Matrix.det (rationalM k))
    (det_rationalM_ne_zero k)

end AlbertLean.Generic.GenericOrientationAttachment
