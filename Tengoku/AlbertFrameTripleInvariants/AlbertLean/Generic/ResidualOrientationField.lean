import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ResidualLedgerMomentField

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms normalized_gauge_formulas` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms gaugeAugmentedLedgerField_eq_orientationLedgerField` (it only prints; the queue checks the axioms of every declaration). -/

/-! The normalized gauge is recovered after adjoining only its orientation. -/

noncomputable section
namespace AlbertLean.Generic.ResidualOrientationField

open AlbertLean.Triality.ExteriorSix
open AlbertLean.Triality.CoordinateTensor
open AlbertLean.Triality.StructuredCubic
open AlbertLean.Residual.FrameIdeal
open AlbertLean.Generic.ResidualLedgerPower
open AlbertLean.Generic.ResidualPowerMeasurements
open AlbertLean.Generic.ResidualLedgerMomentField

variable {K : Type*} [Field K] [CharZero K]

def orientationLedgerField (base : Subfield K) (x : ExplicitFrameChart K) : Subfield K :=
  Subfield.closure (((ledgerField base (encoderA x) (encoderB x) : Subfield K) : Set K) ∪
    {orientation x})

def gaugeAugmentedLedgerField (base : Subfield K) (x : ExplicitFrameChart K) : Subfield K :=
  Subfield.closure (((ledgerField base (encoderA x) (encoderB x) : Subfield K) : Set K) ∪
    {x.r1, x.z1, x.r2, x.z2})

/-- Here `g` is the full polar Gram.  The paper's `p` is `g/2`.
@isnad1 id=other.2h2v.s7.2c8f3f220c7a from=translated src=- shape=57d977ef vocab=7714ccb8
-/
theorem normalized_gauge_formulas (x : ExplicitFrameChart K) (hr1 : x.r1 = 1)
    (hz1 : x.z1 ≠ 0) :
    let g := BV (vectorA x) (vectorB x)
    x.z1 = nV (vectorA x) ∧
      x.r2 = (g - orientation x) / (2 * x.z1) ∧
      x.z2 = (g + orientation x) / 2 := by
  dsimp
  constructor
  · simp [nV, vectorA, Pf, BW, hr1]
  constructor
  · apply (eq_div_iff (mul_ne_zero (by norm_num) hz1)).2
    simp [BV, BW, vectorA, vectorB, orientation, hr1]
    ring
  · simp [BV, BW, vectorA, vectorB, orientation, hr1]
    ring

/--
@isnad1 id=eq.2h3v.s6.f0f03b5e8070 from=translated src=- shape=b1c5a93d vocab=02afe295
-/
theorem gaugeAugmentedLedgerField_eq_orientationLedgerField
    (base : Subfield K) (x : ExplicitFrameChart K)
    (hr1 : x.r1 = 1) (hz1 : x.z1 ≠ 0) :
    gaugeAugmentedLedgerField base x = orientationLedgerField base x := by
  let L := ledgerField base (encoderA x) (encoderB x)
  let O := orientationLedgerField base x
  have hLO : L ≤ O := fun _ ht => Subfield.subset_closure (Or.inl ht)
  have hk : orientation x ∈ O := Subfield.subset_closure (Or.inr (by rfl))
  have hLedgerO : LedgerIn O (sourceLedger (encoderA x) (encoderB x)) := by
    rcases ledgerIn_ledgerField base (encoderA x) (encoderB x) with ⟨hP,hQ,hR,hC⟩
    exact ⟨fun i j => hLO (hP i j), fun j l => hLO (hQ j l),
      fun l i => hLO (hR l i), fun i j l => hLO (hC i j l)⟩
  have hd := powers_diag_mem O (encoderA x) (encoderB x) hLedgerO
  have hnA := norms_mem O (encoderA x) (hd.1 1) (hd.1 2)
  have hz : x.z1 ∈ O := by
    rw [(normalized_gauge_formulas x hr1 hz1).1]
    simpa only [encoderA] using hnA.1
  have hg : BV (vectorA x) (vectorB x) ∈ O := by
    simpa only [power, Matrix.cons_val_one, Matrix.cons_val_zero, encoderA, encoderB] using
      (power_sectors_mem O (encoderA x) (encoderB x) hLedgerO 1 1).1
  have hr2 : x.r2 ∈ O := by
    rw [(normalized_gauge_formulas x hr1 hz1).2.1]
    exact O.div_mem (O.sub_mem hg hk) (O.mul_mem (natCast_mem O 2) hz)
  have hz2 : x.z2 ∈ O := by
    rw [(normalized_gauge_formulas x hr1 hz1).2.2]
    exact O.div_mem (O.add_mem hg hk) (natCast_mem O 2)
  apply le_antisymm
  · apply Subfield.closure_le.2
    rintro t (ht | ht)
    · exact hLO ht
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · rw [hr1]; exact O.one_mem
      · exact hz
      · exact hr2
      · exact hz2
  · apply Subfield.closure_le.2
    rintro t (ht | rfl)
    · exact Subfield.subset_closure (Or.inl ht)
    · rw [orientation]
      exact (gaugeAugmentedLedgerField base x).sub_mem
        ((gaugeAugmentedLedgerField base x).mul_mem
          (Subfield.subset_closure (Or.inr (by simp)))
          (Subfield.subset_closure (Or.inr (by simp))))
        ((gaugeAugmentedLedgerField base x).mul_mem
          (Subfield.subset_closure (Or.inr (by simp)))
          (Subfield.subset_closure (Or.inr (by simp))))

end AlbertLean.Generic.ResidualOrientationField
