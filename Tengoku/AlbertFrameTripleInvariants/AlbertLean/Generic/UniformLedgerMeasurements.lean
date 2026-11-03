import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ResidualPowerMeasurements

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms H_sourceLedger` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms recovered_measurements` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Polynomial measurements of a pair of source encoders, written directly in
the literal 54-cell ledger.  The equalities below are pointwise identities;
no conclusion is inferred from two subfield-membership statements.
-/

noncomputable section
namespace AlbertLean.Generic.UniformLedgerMeasurements

open AlbertLean.Triality.ExteriorSix
open AlbertLean.Triality.CoordinateTensor
open AlbertLean.Triality.StructuredCubic
open AlbertLean.Triality.StructuredAdjoint
open AlbertLean.Triality.StructuredProduct
open AlbertLean.Residual.TrialitySquares
open AlbertLean.Generic.ProductDiagonal
open AlbertLean.Generic.ResidualLedgerPower
open AlbertLean.Generic.ResidualPowerMeasurements

variable {K : Type*} [CommRing K] [Algebra ℚ K]

def ledgerWeight : Fin 3 → Fin 3 → K := ![![1, 1, 1], ![-1, 0, 1], ![1, 0, 1]]

/-- The uncentred joint cell, recovered polynomially from the public cell.-/
def rawJoint (L : SourceLedger K) (i j l : Fin 3) : K :=
  L.C0 i j l + (L.P i j + L.Q j l + L.R l i) * algebraMap ℚ K (1/3) -
    algebraMap ℚ K (2/9)

/-- The diagonal power-product table obtained by the fixed tensor change of basis.-/
def H (L : SourceLedger K) (i p q : Fin 3) : K :=
  ∑ j, ∑ l, ledgerWeight p j * ledgerWeight q l * rawJoint L i j l

def D (L : SourceLedger K) (i p : Fin 3) : K := H L i p 0
def E (L : SourceLedger K) (i q : Fin 3) : K := H L i 0 q
def J (L : SourceLedger K) (i p q : Fin 3) : K := H L i p q - D L i p * E L i q

def gV (L : SourceLedger K) (p q : Fin 3) : K := J L 1 p q + J L 2 p q - J L 0 p q
def gS (L : SourceLedger K) (p q : Fin 3) : K := J L 0 p q + J L 2 p q - J L 1 p q
def gC (L : SourceLedger K) (p q : Fin 3) : K := J L 0 p q + J L 1 p q - J L 2 p q

def half (x : K) : K := x * algebraMap ℚ K (1/2)
def nVx (L : SourceLedger K) : K := half (H L 1 2 0 - D L 1 1 ^ 2 + H L 2 2 0 - D L 2 1 ^ 2 - (H L 0 2 0 - D L 0 1 ^ 2))
def nSx (L : SourceLedger K) : K := half (H L 0 2 0 - D L 0 1 ^ 2 + H L 2 2 0 - D L 2 1 ^ 2 - (H L 1 2 0 - D L 1 1 ^ 2))
def nCx (L : SourceLedger K) : K := half (H L 0 2 0 - D L 0 1 ^ 2 + H L 1 2 0 - D L 1 1 ^ 2 - (H L 2 2 0 - D L 2 1 ^ 2))
def nVy (L : SourceLedger K) : K := half (H L 1 0 2 - E L 1 1 ^ 2 + H L 2 0 2 - E L 2 1 ^ 2 - (H L 0 0 2 - E L 0 1 ^ 2))
def nSy (L : SourceLedger K) : K := half (H L 0 0 2 - E L 0 1 ^ 2 + H L 2 0 2 - E L 2 1 ^ 2 - (H L 1 0 2 - E L 1 1 ^ 2))
def nCy (L : SourceLedger K) : K := half (H L 0 0 2 - E L 0 1 ^ 2 + H L 1 0 2 - E L 1 1 ^ 2 - (H L 2 0 2 - E L 2 1 ^ 2))

def lVx (L : SourceLedger K) := D L 1 1 + D L 2 1
def lSx (L : SourceLedger K) := D L 0 1 + D L 2 1
def lCx (L : SourceLedger K) := D L 0 1 + D L 1 1
def lVy (L : SourceLedger K) := E L 1 1 + E L 2 1
def lSy (L : SourceLedger K) := E L 0 1 + E L 2 1
def lCy (L : SourceLedger K) := E L 0 1 + E L 1 1

def t211 (L : SourceLedger K) := gV L 2 1 - lVx L * gV L 1 1
def t121 (L : SourceLedger K) := gS L 2 1 - lSx L * gS L 1 1
def t112 (L : SourceLedger K) := gC L 2 1 - lCx L * gC L 1 1
def t122 (L : SourceLedger K) := gV L 1 2 - lVy L * gV L 1 1
def t212 (L : SourceLedger K) := gS L 1 2 - lSy L * gS L 1 1
def t221 (L : SourceLedger K) := gC L 1 2 - lCy L * gC L 1 1
def t111 (L : SourceLedger K) := D L 0 1 * nVx L + D L 1 1 * nSx L + D L 2 1 * nCx L - D L 0 1 * D L 1 1 * D L 2 1
def t222 (L : SourceLedger K) := E L 0 1 * nVy L + E L 1 1 * nSy L + E L 2 1 * nCy L - E L 0 1 * E L 1 1 * E L 2 1

def uV (L : SourceLedger K) := gV L 2 2 - lVx L * gV L 1 2 - lVy L * gV L 2 1 + lVx L * lVy L * gV L 1 1
def uS (L : SourceLedger K) := gS L 2 2 - lSx L * gS L 1 2 - lSy L * gS L 2 1 + lSx L * lSy L * gS L 1 1
def uC (L : SourceLedger K) := gC L 2 2 - lCx L * gC L 1 2 - lCy L * gC L 2 1 + lCx L * lCy L * gC L 1 1

section Field
variable {K : Type*} [Field K] [CharZero K]

/--
@isnad1 id=eq.0h3v.s5.399b2e26612e from=translated src=- shape=a8546a93 vocab=ba6e40f4
-/
@[simp] theorem ledgerWeight_eq_powerWeight (p j : Fin 3) :
    ledgerWeight (K := K) p j = powerWeight p j := by
  fin_cases p <;> fin_cases j <;> rfl

/--
@isnad1 id=eq.0h6v.s10.07d0ae8ce947 from=translated src=- shape=ddf69da3 vocab=95a60d0f
-/
theorem rawJoint_sourceLedger (a b : JCoord K) (i j l : Fin 3) :
    rawJoint (sourceLedger a b) i j l =
      diagonalProduct i (spectralProjector a j) (spectralProjector b l) := by
  rw [diagonalProduct_apply, ← diagonal_trace]
  simp [rawJoint, sourceLedger]
  ring

/--
@isnad1 id=eq.0h6v.s8.fbe272b1a929 from=translated src=- shape=5db15303 vocab=85a43023
-/
theorem H_sourceLedger (a b : JCoord K) (i p q : Fin 3) :
    H (sourceLedger a b) i p q =
      diagLinear i (sourceProduct (power a p) (power b q)) := by
  rw [power_eq_weighted_projectors a p, power_eq_weighted_projectors b q]
  simp only [H]
  simp_rw [rawJoint_sourceLedger]
  simp only [ledgerWeight_eq_powerWeight]
  change (∑ j, ∑ l, powerWeight p j * powerWeight q l *
      diagonalProduct i (spectralProjector a j) (spectralProjector b l)) =
    diagonalProduct i (∑ j, powerWeight p j • spectralProjector a j)
      (∑ l, powerWeight q l • spectralProjector b l)
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  ring

/--
@isnad1 id=and.2h3v.s9.103e65c9ac47 from=translated src=- shape=943ece30 vocab=6aee998b
-/
theorem recovered_measurements (a b : JCoord K)
    (hNa : sourceNorm a = 0) (hNb : sourceNorm b = 0) :
    nVx (sourceLedger a b) = nV a.v ∧ nSx (sourceLedger a b) = nS a.s ∧
    nCx (sourceLedger a b) = nC a.c ∧ nVy (sourceLedger a b) = nV b.v ∧
    nSy (sourceLedger a b) = nS b.s ∧ nCy (sourceLedger a b) = nC b.c ∧
    gV (sourceLedger a b) 1 1 = BV a.v b.v ∧
    gS (sourceLedger a b) 1 1 = BS a.s b.s ∧
    gC (sourceLedger a b) 1 1 = BC a.c b.c ∧
    t111 (sourceLedger a b) = triality a.v a.s a.c ∧
    t211 (sourceLedger a b) = triality b.v a.s a.c ∧
    t121 (sourceLedger a b) = triality a.v b.s a.c ∧
    t112 (sourceLedger a b) = triality a.v a.s b.c ∧
    t122 (sourceLedger a b) = triality a.v b.s b.c ∧
    t212 (sourceLedger a b) = triality b.v a.s b.c ∧
    t221 (sourceLedger a b) = triality b.v b.s a.c ∧
    t222 (sourceLedger a b) = triality b.v b.s b.c ∧
    uV (sourceLedger a b) = normalizedUV a.s b.s a.c b.c ∧
    uS (sourceLedger a b) = BS (sourceMuS a.c a.v) (sourceMuS b.c b.v) ∧
    uC (sourceLedger a b) = BC (sourceMuC a.v a.s) (sourceMuC b.v b.s) := by
  repeat' apply And.intro
  all_goals simp [nVx, nSx, nCx, nVy, nSy, nCy, half, gV, gS, gC, J, D, E,
    lVx, lSx, lCx, lVy, lSy, lCy, t111, t211, t121, t112, t122, t212,
    t221, t222, uV, uS, uC, H_sourceLedger, power, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, sourceProduct_one_left,
    sourceProduct_one_right, diagLinear_zero, diagLinear_one, diagLinear_two,
    sourceSquare_d1, sourceSquare_d2, sourceSquare_d3,
    sourceSquare_v, sourceSquare_s, sourceSquare_c, sourceProduct_d1,
    sourceProduct_d2, sourceProduct_d3, uV_centered, uS_centered, uC_centered,
    lV, lS, lC]
  all_goals try (solve | ring)
  · rw [sourceNorm_formula] at hNa
    linear_combination -hNa
  · rw [BV_add_left, BV_smul_left, muV_triality]
    ring
  · rw [BS_add_left, BS_smul_left, muS_triality]
    ring
  · rw [BC_add_left, BC_smul_left, muC_triality]
    ring
  · rw [BV_add_right, BV_smul_right,
      BV_symmetric a.v (normalizedMuV b.s b.c), muV_triality]
    ring
  · rw [BS_add_right, BS_smul_right,
      BS_symmetric a.s (sourceMuS b.c b.v), muS_triality]
    ring
  · rw [BC_add_right, BC_smul_right,
      BC_symmetric a.c (sourceMuC b.v b.s), muC_triality]
    ring
  · rw [sourceNorm_formula] at hNb
    linear_combination -hNb

end Field

end AlbertLean.Generic.UniformLedgerMeasurements
