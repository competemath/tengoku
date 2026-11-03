import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.GenericLedgerInvariance
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SignRootAdjoin
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuadraticCharacterField

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms kappa_square_mem_H` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms joint_fixed_iff` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms descentData` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms fixedField_degree_two` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms fixedField_generated_by_product` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms product_not_mem_H` (it only prints; the queue checks the axioms of every declaration). -/

/-! Concrete common fixed-field identification for the literal generic ledger.
This discharges the two-involution package on the actual parameter field.
Attachment to a global full-automorphism invariant field remains separate. -/

noncomputable section
namespace AlbertLean.Generic.GenericCommonFixedField

open AlbertLean.Triality.ExteriorSix
open AlbertLean.Triality.CoordinateTensor
open AlbertLean.Triality.StructuredCubic
open AlbertLean.Residual.FrameIdeal
open AlbertLean.Generic.ResidualLedgerPower
open AlbertLean.Generic.ResidualPowerMeasurements
open AlbertLean.Generic.ResidualLedgerMomentField
open AlbertLean.Generic.ResidualOrientationField
open AlbertLean.Generic.GenericDeterminantOpen
open AlbertLean.Generic.GenericFieldChart
open AlbertLean.Generic.GenericOrientationAttachment
open AlbertLean.Generic.GenericFieldSymmetries
open AlbertLean.Generic.GenericLedgerInvariance
open AlbertLean.Generic.NestedReciprocalField

universe u
variable (k : Type u) [Field k] [CharZero k]

theorem kappa_square_mem_H : kappa k ^ 2 ∈ H k := by
  let x := genericChart k
  have hl : LedgerIn (H k) (sourceLedger (encoderA x) (encoderB x)) :=
    ledgerIn_ledgerField (groundBase k) _ _
  have hd := powers_diag_mem (H k) _ _ hl
  have ha := norms_mem (H k) (encoderA x) (hd.1 1) (hd.1 2)
  have hb := norms_mem (H k) (encoderB x) (hd.2 1) (hd.2 2)
  have hg : BV (vectorA x) (vectorB x) ∈ H k :=
    (power_sectors_mem (H k) _ _ hl 1 1).1
  have he : kappa k ^ 2 = BV (vectorA x) (vectorB x) ^ 2 -
      4 * nV (vectorA x) * nV (vectorB x) := by
    rw [kappa_eq_orientation]
    change orientation x ^ 2 = _
    simp [orientation, BV, BW, vectorA, vectorB, nV, Pf]
    ring
  rw [he]
  exact (H k).sub_mem ((H k).pow_mem hg 2)
    ((H k).mul_mem ((H k).mul_mem (natCast_mem (H k) 4) ha.1) hb.1)

theorem orientation_adjoin_eq_invariant :
    Subfield.closure (((H k : Subfield (FunctionField k)) : Set (FunctionField k)) ∪
      {kappa k}) = invariantField (Base k) (Matrix.det (rationalM k)) := by
  rw [kappa_eq_orientation]
  exact orientation_eq_invariantField k

/-- Both concrete symmetries fix exactly the original ledger field in common.-/
theorem joint_fixed_iff (z : FunctionField k) :
    (tau k z = z ∧ deck k z = z) ↔ z ∈ H k := by
  constructor
  · rintro ⟨ht,hd⟩
    have hz : z ∈ Subfield.closure ((H k : Set (FunctionField k)) ∪ {kappa k}) := by
      rw [orientation_adjoin_eq_invariant]
      exact (fixed_iff_mem_invariantField (Base k) (Matrix.det (rationalM k))
        (det_rationalM_ne_zero k) z).1 hd
    have hn : nu k z = z := by
      apply (deck k).injective
      change tau k z = deck k z
      rw [ht,hd]
    exact (SignRootAdjoin.fixed_iff_mem_base (H k) (nu k)
      (fun _ h => H_le_nuFixed k h) (kappa k) (kappa_square_mem_H k)
      (nu_kappa k) (kappa_ne_zero k) hz).1 hn
  · intro hz
    exact ⟨tau_fixed_of_mem_H k hz,deck_fixed_of_mem_H k hz⟩

def tauOverH : FunctionField k ≃ₐ[H k] FunctionField k where
  toRingEquiv := tau k
  commutes' a := tau_fixed_of_mem_H k a.property

def deckOverH : FunctionField k ≃ₐ[H k] FunctionField k where
  toRingEquiv := deck k
  commutes' a := deck_fixed_of_mem_H k a.property

/-- Every hypothesis is supplied by the actual field, not a manuscript premise.-/
def descentData : QuadraticCharacterDescent.Data (k := H k) (Ω := FunctionField k) where
  tau := tauOverH k
  delta := deckOverH k
  tau_involutive := tau_twice k
  delta_involutive := deck_twice k
  commute := tau_commutes_deck k
  kappa := kappa k
  eta := eta k
  kappa_ne := kappa_ne_zero k
  eta_ne := eta_ne_zero k
  tau_kappa := tau_kappa k
  delta_kappa := deck_kappa k
  tau_eta := tau_eta k
  delta_eta := deck_eta k
  joint_fixed z := by
    change (tau k z = z ∧ deck k z = z) ↔
      ∃ a : H k, algebraMap (H k) (FunctionField k) a = z
    rw [joint_fixed_iff]
    exact ⟨fun hz => ⟨⟨z,hz⟩,rfl⟩,fun ⟨a,ha⟩ => ha ▸ a.property⟩

/-- Exact quadratic degree for the concrete tau-fixed field over the ledger.-/
theorem fixedField_degree_two :
    Module.finrank (H k) (descentData k).fixedField = 2 :=
  (descentData k).fixedField_finrank

theorem fixedField_generated_by_product :
    Subfield.closure ((H k : Set (FunctionField k)) ∪ {kappa k * eta k}) =
      (descentData k).fixedField := by
  have hr : Set.range (algebraMap (H k) (FunctionField k)) =
      (H k : Set (FunctionField k)) := by
    ext z
    exact ⟨fun ⟨a,ha⟩ => ha ▸ a.property,fun hz => ⟨⟨z,hz⟩,rfl⟩⟩
  have hu : (descentData k).u = kappa k * eta k := rfl
  simpa only [hr, hu] using (descentData k).fixedField_generated_by_u

theorem product_not_mem_H : kappa k * eta k ∉ H k := by
  intro h
  exact (descentData k).u_not_base ⟨⟨kappa k * eta k,h⟩,rfl⟩

end AlbertLean.Generic.GenericCommonFixedField
