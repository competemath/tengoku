import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ResidualSourceMeasurements
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.UniformLedgerMeasurements

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms matrixM_eq_uniform_inverse` (it only prints; the queue checks the axioms of every declaration). -/

/-! The actual normalized-source uniform moment reconstruction. -/

noncomputable section
namespace AlbertLean.Generic.UniformMomentReconstruction

open AlbertLean.Triality.ExteriorSix
open AlbertLean.Triality.CoordinateTensor
open AlbertLean.Triality.StructuredCubic
open AlbertLean.Triality.StructuredAdjoint
open AlbertLean.Residual.TrialitySquares
open AlbertLean.Residual.FrameIdeal
open AlbertLean.Generic.ResidualLedgerPower
open AlbertLean.Generic.ResidualSourceMeasurements
open AlbertLean.Generic.UniformLedgerMeasurements

variable {K : Type*} [CommRing K] [Algebra ℚ K]

def uniformN (L : SourceLedger K) (a h sigma : K) : Matrix (Fin 4) (Fin 4) K := fun i j =>
  if i = 0 ∧ j = 0 then 2*a*sigma*nSx L else
  if i = 1 ∧ j = 1 then 2*a*sigma*nSy L else
  if i = 2 ∧ j = 2 then 2*a*sigma*nCx L else
  if i = 3 ∧ j = 3 then 2*a*sigma*nCy L else
  if i = 0 ∧ j = 1 then 2*a*uC L-a*(h-sigma)*gS L 1 1 else
  if i = 1 ∧ j = 0 then a*(h+sigma)*gS L 1 1-2*a*uC L else
  if i = 2 ∧ j = 3 then a*(h+sigma)*gC L 1 1-2*a*uS L else
  if i = 3 ∧ j = 2 then 2*a*uS L-a*(h-sigma)*gC L 1 1 else
  if i = 0 ∧ j = 2 then a*(h+sigma)*t111 L-2*a^2*t211 L else
  if i = 2 ∧ j = 0 then 2*a*t211 L-(h-sigma)*t111 L else
  if i = 0 ∧ j = 3 then a*(h+sigma)*t112 L-2*a^2*t212 L else
  if i = 3 ∧ j = 0 then 2*a*t212 L-(h-sigma)*t112 L else
  if i = 1 ∧ j = 2 then a*(h+sigma)*t121 L-2*a^2*t221 L else
  if i = 2 ∧ j = 1 then 2*a*t221 L-(h-sigma)*t121 L else
  if i = 1 ∧ j = 3 then a*(h+sigma)*t122 L-2*a^2*t222 L else
  2*a*t222 L-(h-sigma)*t122 L

/-- Polynomial reconstruction over an abstract matrix. Literal Fin cases are
reduced before scalar algebra; no concrete chart is unfolded here.-/
private theorem uniformN_eq_smul_of_measurements
    (L : SourceLedger K) (m : Matrix (Fin 4) (Fin 4) K)
    (a b c sigma h : K)
    (h00 : nSx L = m 0 0) (h11 : nSy L = m 1 1)
    (h22 : nCx L = m 2 2) (h33 : nCy L = m 3 3)
    (hS : gS L 1 1 = m 0 1 + m 1 0)
    (hC : gC L 1 1 = m 2 3 + m 3 2)
    (hUC : uC L = c * m 0 1 + a*b * m 1 0)
    (hUS : uS L = a*b * m 2 3 + c * m 3 2)
    (hT111 : t111 L = m 0 2 + a * m 2 0)
    (hT211 : t211 L = b * m 0 2 + c * m 2 0)
    (hT112 : t112 L = m 0 3 + a * m 3 0)
    (hT212 : t212 L = b * m 0 3 + c * m 3 0)
    (hT121 : t121 L = m 1 2 + a * m 2 1)
    (hT221 : t221 L = b * m 1 2 + c * m 2 1)
    (hT122 : t122 L = m 1 3 + a * m 3 1)
    (hT222 : t222 L = b * m 1 3 + c * m 3 1)
    (hsum : h = c + a*b) (hc : c = sigma + a*b) :
    uniformN L a h sigma = (2*a*sigma) • m := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · change 2*a*sigma*nSx L = (2*a*sigma) * m 0 0
    simp only [h00, h11, h22, h33, hS, hC, hUC, hUS,
      hT111, hT211, hT112, hT212, hT121, hT221, hT122, hT222, hsum, hc] <;> ring
  · change 2*a*uC L-a*(h-sigma)*gS L 1 1 = (2*a*sigma) * m 0 1
    simp only [h00, h11, h22, h33, hS, hC, hUC, hUS,
      hT111, hT211, hT112, hT212, hT121, hT221, hT122, hT222, hsum, hc] <;> ring
  · change a*(h+sigma)*t111 L-2*a^2*t211 L = (2*a*sigma) * m 0 2
    simp only [h00, h11, h22, h33, hS, hC, hUC, hUS,
      hT111, hT211, hT112, hT212, hT121, hT221, hT122, hT222, hsum, hc] <;> ring
  · change a*(h+sigma)*t112 L-2*a^2*t212 L = (2*a*sigma) * m 0 3
    simp only [h00, h11, h22, h33, hS, hC, hUC, hUS,
      hT111, hT211, hT112, hT212, hT121, hT221, hT122, hT222, hsum, hc] <;> ring
  · change a*(h+sigma)*gS L 1 1-2*a*uC L = (2*a*sigma) * m 1 0
    simp only [h00, h11, h22, h33, hS, hC, hUC, hUS,
      hT111, hT211, hT112, hT212, hT121, hT221, hT122, hT222, hsum, hc] <;> ring
  · change 2*a*sigma*nSy L = (2*a*sigma) * m 1 1
    simp only [h00, h11, h22, h33, hS, hC, hUC, hUS,
      hT111, hT211, hT112, hT212, hT121, hT221, hT122, hT222, hsum, hc] <;> ring
  · change a*(h+sigma)*t121 L-2*a^2*t221 L = (2*a*sigma) * m 1 2
    simp only [h00, h11, h22, h33, hS, hC, hUC, hUS,
      hT111, hT211, hT112, hT212, hT121, hT221, hT122, hT222, hsum, hc] <;> ring
  · change a*(h+sigma)*t122 L-2*a^2*t222 L = (2*a*sigma) * m 1 3
    simp only [h00, h11, h22, h33, hS, hC, hUC, hUS,
      hT111, hT211, hT112, hT212, hT121, hT221, hT122, hT222, hsum, hc] <;> ring
  · change 2*a*t211 L-(h-sigma)*t111 L = (2*a*sigma) * m 2 0
    simp only [h00, h11, h22, h33, hS, hC, hUC, hUS,
      hT111, hT211, hT112, hT212, hT121, hT221, hT122, hT222, hsum, hc] <;> ring
  · change 2*a*t221 L-(h-sigma)*t121 L = (2*a*sigma) * m 2 1
    simp only [h00, h11, h22, h33, hS, hC, hUC, hUS,
      hT111, hT211, hT112, hT212, hT121, hT221, hT122, hT222, hsum, hc] <;> ring
  · change 2*a*sigma*nCx L = (2*a*sigma) * m 2 2
    simp only [h00, h11, h22, h33, hS, hC, hUC, hUS,
      hT111, hT211, hT112, hT212, hT121, hT221, hT122, hT222, hsum, hc] <;> ring
  · change a*(h+sigma)*gC L 1 1-2*a*uS L = (2*a*sigma) * m 2 3
    simp only [h00, h11, h22, h33, hS, hC, hUC, hUS,
      hT111, hT211, hT112, hT212, hT121, hT221, hT122, hT222, hsum, hc] <;> ring
  · change 2*a*t212 L-(h-sigma)*t112 L = (2*a*sigma) * m 3 0
    simp only [h00, h11, h22, h33, hS, hC, hUC, hUS,
      hT111, hT211, hT112, hT212, hT121, hT221, hT122, hT222, hsum, hc] <;> ring
  · change 2*a*t222 L-(h-sigma)*t122 L = (2*a*sigma) * m 3 1
    simp only [h00, h11, h22, h33, hS, hC, hUC, hUS,
      hT111, hT211, hT112, hT212, hT121, hT221, hT122, hT222, hsum, hc] <;> ring
  · change 2*a*uS L-a*(h-sigma)*gC L 1 1 = (2*a*sigma) * m 3 2
    simp only [h00, h11, h22, h33, hS, hC, hUC, hUS,
      hT111, hT211, hT112, hT212, hT121, hT221, hT122, hT222, hsum, hc] <;> ring
  · change 2*a*sigma*nCy L = (2*a*sigma) * m 3 3
    simp only [h00, h11, h22, h33, hS, hC, hUC, hUS,
      hT111, hT211, hT112, hT212, hT121, hT221, hT122, hT222, hsum, hc] <;> ring

section Field
variable {K : Type*} [Field K] [CharZero K]

/-- Cancel the common scalar once, with both matrices still abstract.-/
private theorem inverse_of_cleared
    (m n : Matrix (Fin 4) (Fin 4) K) (z : K) (hz : z ≠ 0)
    (hn : n = z • m) : m = z⁻¹ • n := by
  rw [hn, ← mul_smul, inv_mul_cancel₀ hz, one_smul]

/-- Every one of the sixteen entries is recovered from the actual source pair.
The only inverse is the common vector determinant `2*a*sigma`.
@isnad1 id=eq.9h6v.s8.019df7aed119 from=translated src=- shape=46df64fa vocab=79389f4d
-/
theorem matrixM_eq_uniform_inverse (q : ExplicitFrameChart K) (a b c sigma : K)
    (hq : EquationsVanish (explicitFrameEquationValues q))
    (hr1 : q.r1 = 1) (hz1 : q.z1 = a) (hr2 : q.r2 = b) (hz2 : q.z2 = c)
    (hb : b = (gramV12 q - sigma) / (2*a))
    (hc : c = (gramV12 q + sigma) / 2)
    (hsigma : sigma ≠ 0) (ha : 2*a ≠ 0) :
    matrixM q = (2*a*sigma)⁻¹ •
      uniformN (sourceLedger (encoderA q) (encoderB q)) a (gramV12 q) sigma := by
  have hfixed := (equationsVanish_iff_source_fixedSpectrum q).1 hq
  have hm := recovered_measurements (encoderA q) (encoderB q) hfixed.2.2.1 hfixed.2.2.2.2.2
  rcases hm with ⟨hnVx, hnSx, hnCx, hnVy, hnSy, hnCy, hgV, hgS, hgC,
    ht111, ht211, ht121, ht112, ht122, ht212, ht221, ht222, huV, huS, huC⟩
  have ha0 : a ≠ 0 := by
    intro hz
    exact ha (by rw [hz, mul_zero])
  have hab : a * b = (gramV12 q - sigma) / 2 := by
    rw [hb]
    field_simp [ha0] <;> ring
  have hdet : c - a*b = sigma := by rw [hc, hab]; ring
  have hc' : c = sigma + a*b := by linear_combination hdet
  have hsum : gramV12 q = c + a*b := by
    simp only [gramV12, hr1, hz1, hr2, hz2, one_mul]
    ring
  let L := sourceLedger (encoderA q) (encoderB q)
  have h00 : nSx L = matrixM q 0 0 := by simpa [L, encoderA, matrixM, momentMatrix, nS, nC] using hnSx
  have h11 : nSy L = matrixM q 1 1 := by simpa [L, encoderB, matrixM, momentMatrix, nS, nC] using hnSy
  have h22 : nCx L = matrixM q 2 2 := by simpa [L, encoderA, matrixM, momentMatrix, nS, nC] using hnCx
  have h33 : nCy L = matrixM q 3 3 := by simpa [L, encoderB, matrixM, momentMatrix, nS, nC] using hnCy
  have hS : gS L 1 1 = matrixM q 0 1 + matrixM q 1 0 := by
    simpa [L, encoderA, encoderB, matrixM, momentMatrix, BS, BC] using hgS
  have hC : gC L 1 1 = matrixM q 2 3 + matrixM q 3 2 := by
    simpa [L, encoderA, encoderB, matrixM, momentMatrix, BS, BC] using hgC
  have hVA : (encoderA q).v = planeVector 1 a := by
    apply VCoord.ext <;> simp [encoderA, vectorA, planeVector, hr1, hz1]
  have hVB : (encoderB q).v = planeVector b c := by
    apply VCoord.ext <;> simp [encoderB, vectorB, planeVector, hr2, hz2]
  have hUC : uC L = c * matrixM q 0 1 + a*b * matrixM q 1 0 := by
    change uC (sourceLedger (encoderA q) (encoderB q)) = _
    rw [huC, hVA, hVB, plane_muC_pairing]
    simp [encoderA, encoderB, matrixM, momentMatrix, one_mul,
      mul_assoc, mul_comm, mul_left_comm]
  have hUS : uS L = a*b * matrixM q 2 3 + c * matrixM q 3 2 := by
    change uS (sourceLedger (encoderA q) (encoderB q)) = _
    rw [huS, hVA, hVB, plane_muS_pairing]
    simp [encoderA, encoderB, matrixM, momentMatrix, one_mul,
      mul_assoc, mul_comm, mul_left_comm]
  have hT111 : t111 L = matrixM q 0 2 + a * matrixM q 2 0 := by
    change t111 (sourceLedger (encoderA q) (encoderB q)) = _
    rw [ht111, hVA, plane_triality]
    simp [encoderA, encoderB, matrixM, momentMatrix]
  have hT211 : t211 L = b * matrixM q 0 2 + c * matrixM q 2 0 := by
    change t211 (sourceLedger (encoderA q) (encoderB q)) = _
    rw [ht211, hVB, plane_triality]
    simp [encoderA, encoderB, matrixM, momentMatrix]
  have hT112 : t112 L = matrixM q 0 3 + a * matrixM q 3 0 := by
    change t112 (sourceLedger (encoderA q) (encoderB q)) = _
    rw [ht112, hVA, plane_triality]
    simp [encoderA, encoderB, matrixM, momentMatrix]
  have hT212 : t212 L = b * matrixM q 0 3 + c * matrixM q 3 0 := by
    change t212 (sourceLedger (encoderA q) (encoderB q)) = _
    rw [ht212, hVB, plane_triality]
    simp [encoderA, encoderB, matrixM, momentMatrix]
  have hT121 : t121 L = matrixM q 1 2 + a * matrixM q 2 1 := by
    change t121 (sourceLedger (encoderA q) (encoderB q)) = _
    rw [ht121, hVA, plane_triality]
    simp [encoderA, encoderB, matrixM, momentMatrix]
  have hT221 : t221 L = b * matrixM q 1 2 + c * matrixM q 2 1 := by
    change t221 (sourceLedger (encoderA q) (encoderB q)) = _
    rw [ht221, hVB, plane_triality]
    simp [encoderA, encoderB, matrixM, momentMatrix]
  have hT122 : t122 L = matrixM q 1 3 + a * matrixM q 3 1 := by
    change t122 (sourceLedger (encoderA q) (encoderB q)) = _
    rw [ht122, hVA, plane_triality]
    simp [encoderA, encoderB, matrixM, momentMatrix]
  have hT222 : t222 L = b * matrixM q 1 3 + c * matrixM q 3 1 := by
    change t222 (sourceLedger (encoderA q) (encoderB q)) = _
    rw [ht222, hVB, plane_triality]
    simp [encoderA, encoderB, matrixM, momentMatrix]
  have hcleared := uniformN_eq_smul_of_measurements L (matrixM q)
    a b c sigma (gramV12 q) h00 h11 h22 h33 hS hC hUC hUS
    hT111 hT211 hT112 hT212 hT121 hT221 hT122 hT222 hsum hc'
  exact inverse_of_cleared (matrixM q)
    (uniformN L a (gramV12 q) sigma) (2*a*sigma)
    (mul_ne_zero ha hsigma) hcleared

end Field

end AlbertLean.Generic.UniformMomentReconstruction
