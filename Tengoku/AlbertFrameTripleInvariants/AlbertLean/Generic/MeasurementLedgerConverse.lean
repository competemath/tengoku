import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ResidualLedgerMomentField

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms square_sectors_mem` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms ledgerIn_of_measurements` (it only prints; the queue checks the axioms of every declaration). -/

/-! Reconstruct the literal ledger from a small set of power measurements.
This converse uses only scalar field closure and the three already proved
centering identities. No chart gauge or frame equation is assumed. -/

noncomputable section
namespace AlbertLean.Generic.MeasurementLedgerConverse

open AlbertLean.Triality.ExteriorSix
open AlbertLean.Triality.CoordinateTensor
open AlbertLean.Triality.StructuredCubic
open AlbertLean.Triality.StructuredAdjoint
open AlbertLean.Triality.StructuredProduct
open AlbertLean.Residual.TrialitySquares
open AlbertLean.Generic.ProductDiagonal
open AlbertLean.Generic.ResidualLedgerPower
open AlbertLean.Generic.ResidualPowerMeasurements
open AlbertLean.Generic.ResidualLedgerMomentField

variable {K : Type*} [Field K] [CharZero K]

theorem power_diagonals_of_norms (F : Subfield K) (a : JCoord K)
    (ha : DiagIn F a) (hv : nV a.v ∈ F) (hs : nS a.s ∈ F) (hc : nC a.c ∈ F) :
    ∀ p, DiagIn F (power a p) := by
  intro p
  fin_cases p
  · intro i
    fin_cases i <;> simp [power, sourceOne, diagLinear]
  · exact ha
  · intro i
    fin_cases i
    · change (sourceSquare a).d1 ∈ F
      rw [sourceSquare_d1]
      exact F.add_mem (F.add_mem (F.pow_mem (ha 0) 2) hs) hc
    · change (sourceSquare a).d2 ∈ F
      rw [sourceSquare_d2]
      exact F.add_mem (F.add_mem (F.pow_mem (ha 1) 2) hc) hv
    · change (sourceSquare a).d3 ∈ F
      rw [sourceSquare_d3]
      exact F.add_mem (F.add_mem (F.pow_mem (ha 2) 2) hv) hs

theorem uncentered_mem (F : Subfield K) (la lb g11 g12 g21 g22 : K)
    (hla : la ∈ F) (hlb : lb ∈ F) (h11 : g11 ∈ F)
    (h12 : g12 ∈ F) (h21 : g21 ∈ F)
    (hU : g22 - la * g12 - lb * g21 + la * lb * g11 ∈ F) : g22 ∈ F := by
  have h := F.sub_mem
    (F.add_mem (F.add_mem hU (F.mul_mem hla h12)) (F.mul_mem hlb h21))
    (F.mul_mem (F.mul_mem hla hlb) h11)
  convert h using 1 <;> ring

theorem square_sectors_mem (F : Subfield K) (a b : JCoord K)
    (ha : DiagIn F a) (hb : DiagIn F b)
    (h11 : SectorIn F a b)
    (h12 : SectorIn F a (sourceSquare b))
    (h21 : SectorIn F (sourceSquare a) b)
    (hUV : normalizedUV a.s b.s a.c b.c ∈ F)
    (hUS : BS (sourceMuS a.c a.v) (sourceMuS b.c b.v) ∈ F)
    (hUC : BC (sourceMuC a.v a.s) (sourceMuC b.v b.s) ∈ F) :
    SectorIn F (sourceSquare a) (sourceSquare b) := by
  rw [uV_centered] at hUV
  rw [uS_centered] at hUS
  rw [uC_centered] at hUC
  refine ⟨?_, ?_, ?_⟩
  · exact uncentered_mem F _ _ _ _ _ _ (F.add_mem (ha 1) (ha 2))
      (F.add_mem (hb 1) (hb 2)) h11.1 h12.1 h21.1 hUV
  · exact uncentered_mem F _ _ _ _ _ _ (F.add_mem (ha 0) (ha 2))
      (F.add_mem (hb 0) (hb 2)) h11.2.1 h12.2.1 h21.2.1 hUS
  · exact uncentered_mem F _ _ _ _ _ _ (F.add_mem (ha 0) (ha 1))
      (F.add_mem (hb 0) (hb 1)) h11.2.2 h12.2.2 h21.2.2 hUC

/-- The three nontrivial sector pairs and their U correction recover every
power pair, and hence every original centered ledger cell.-/
theorem ledgerIn_of_measurements (F : Subfield K) (a b : JCoord K)
    (ha : ∀ p, DiagIn F (power a p)) (hb : ∀ p, DiagIn F (power b p))
    (h11 : SectorIn F a b)
    (h12 : SectorIn F a (sourceSquare b))
    (h21 : SectorIn F (sourceSquare a) b)
    (hUV : normalizedUV a.s b.s a.c b.c ∈ F)
    (hUS : BS (sourceMuS a.c a.v) (sourceMuS b.c b.v) ∈ F)
    (hUC : BC (sourceMuC a.v a.s) (sourceMuC b.v b.s) ∈ F) :
    LedgerIn F (sourceLedger a b) := by
  have h22 := square_sectors_mem F a b (ha 1) (hb 1) h11 h12 h21 hUV hUS hUC
  have hs : ∀ p q, SectorIn F (power a p) (power b q) := by
    intro p q
    fin_cases p <;> fin_cases q
    all_goals first
      | exact h11 | exact h12 | exact h21 | exact h22
      | simp [SectorIn, power, sourceOne, BV, BS, BC, BW, evalU]
  apply ledgerIn_of_power_diagonal_mem
  intro i p q
  have hpair := hs p q
  fin_cases i
  · change (sourceProduct (power a p) (power b q)).d1 ∈ F
    rw [sourceProduct_d1]
    exact F.add_mem (F.mul_mem (ha p 0) (hb q 0))
      (F.div_mem (F.add_mem hpair.2.1 hpair.2.2) (natCast_mem F 2))
  · change (sourceProduct (power a p) (power b q)).d2 ∈ F
    rw [sourceProduct_d2]
    exact F.add_mem (F.mul_mem (ha p 1) (hb q 1))
      (F.div_mem (F.add_mem hpair.2.2 hpair.1) (natCast_mem F 2))
  · change (sourceProduct (power a p) (power b q)).d3 ∈ F
    rw [sourceProduct_d3]
    exact F.add_mem (F.mul_mem (ha p 2) (hb q 2))
      (F.div_mem (F.add_mem hpair.1 hpair.2.1) (natCast_mem F 2))

end AlbertLean.Generic.MeasurementLedgerConverse
