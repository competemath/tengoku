import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FourRowComponents
import Tengoku.Seed.Tactic.Abel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms anchor_properties` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms anchor_unique` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms inverse_after_right_change` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms cslotSum_right_change` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms normalized_second_components` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms componentSolution_of_raw` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Determinant-one normalization of ordinary matrix components

The right multiplier `b0⁻¹ * a0` sends the first second-component to `a0`.
Its inverse acts on the third components. All sum and determinant equations
are transported here without assuming a matrix quadratic or an Albert model.
-/

noncomputable section
namespace AlbertLean.Generic.FourRowNormalization

open FourRowFrameReduction FourRowComponents
open FourRowUniqueness (reconstructionDenominator)

variable {K : Type*} [Field K]

/-- The unique right multiplier anchoring the first second-component.-/
def anchor (a0 b0 : Mat3 K) : Mat3 K := b0⁻¹ * a0

/-- The coordinate recovered after anchoring.-/
def normalizedX (a0 b0 b1 : Mat3 K) : Mat3 K :=
  (b1 * anchor a0 b0) * a0⁻¹

theorem anchor_properties (a0 b0 : Mat3 K)
    (ha0 : a0.det ≠ 0) (hb0 : b0.det = a0.det) :
    (anchor a0 b0).det = 1 ∧ b0 * anchor a0 b0 = a0 ∧
      (a0⁻¹ * b0) * anchor a0 b0 = 1 ∧
      anchor a0 b0 * (a0⁻¹ * b0) = 1 := by
  have hb : IsUnit b0.det := isUnit_iff_ne_zero.mpr (hb0 ▸ ha0)
  have ha : IsUnit a0.det := isUnit_iff_ne_zero.mpr ha0
  dsimp only [anchor]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, ← hb0]
    exact Matrix.det_nonsing_inv_mul_det b0 hb
  · rw [← mul_assoc, Matrix.mul_nonsing_inv b0 hb, one_mul]
  · rw [mul_assoc, ← mul_assoc b0, Matrix.mul_nonsing_inv b0 hb,
      one_mul, Matrix.nonsing_inv_mul a0 ha]
  · rw [mul_assoc, ← mul_assoc a0, Matrix.mul_nonsing_inv a0 ha,
      one_mul, Matrix.nonsing_inv_mul b0 hb]

theorem anchor_unique (a0 b0 h : Mat3 K) (hb0 : b0.det ≠ 0)
    (hh : b0 * h = a0) : h = anchor a0 b0 := by
  have hm := congrArg (fun Z : Mat3 K => b0⁻¹ * Z) hh
  simpa only [anchor, ← mul_assoc,
    Matrix.nonsing_inv_mul b0 (isUnit_iff_ne_zero.mpr hb0), one_mul] using hm

/-- An explicit left inverse suffices for square matrices over a field.-/
theorem inverse_after_right_change (b g h : Mat3 K)
    (hb : b.det ≠ 0) (hgh : g * h = 1) :
    (b * h)⁻¹ = g * b⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [mul_assoc, ← mul_assoc b⁻¹,
    Matrix.nonsing_inv_mul b (isUnit_iff_ne_zero.mpr hb), one_mul, hgh]

/-- The inverse-adjugate sum transforms by left multiplication.-/
theorem cslotSum_right_change
    (b0 b1 b2 A0 A1 A2 g h : Mat3 K)
    (hb0 : b0.det ≠ 0) (hb1 : b1.det ≠ 0) (hb2 : b2.det ≠ 0)
    (hgh : g * h = 1) :
    cslotSum (b0 * h) (b1 * h) (b2 * h) A0 A1 A2 =
      g * cslotSum b0 b1 b2 A0 A1 A2 := by
  simp only [cslotSum, inverse_after_right_change b0 g h hb0 hgh,
    inverse_after_right_change b1 g h hb1 hgh,
    inverse_after_right_change b2 g h hb2 hgh, mul_add, mul_assoc]

/-- A zero second-component sum gives the complete normalized parameterization.-/
theorem normalized_second_components
    (a0 b0 b1 b2 : Mat3 K) (ha0 : a0.det ≠ 0)
    (hb0 : b0.det = a0.det) (hsum : b0 + b1 + b2 = 0) :
    b0 * anchor a0 b0 = a0 ∧
      b1 * anchor a0 b0 = normalizedX a0 b0 b1 * a0 ∧
      b2 * anchor a0 b0 = -(1 + normalizedX a0 b0 b1) * a0 := by
  have h0 := (anchor_properties a0 b0 ha0 hb0).2.1
  have h1 : b1 * anchor a0 b0 = normalizedX a0 b0 b1 * a0 := by
    dsimp only [normalizedX]
    rw [mul_assoc, Matrix.nonsing_inv_mul a0 (isUnit_iff_ne_zero.mpr ha0), mul_one]
  refine ⟨h0, h1, ?_⟩
  have hs := congrArg (fun Z : Mat3 K => Z * anchor a0 b0) hsum
  simp only [add_mul, zero_mul, h0, h1] at hs
  have ht : b2 * anchor a0 b0 = -(a0 + normalizedX a0 b0 b1 * a0) := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [add_comm] using hs
  simpa only [neg_mul, add_mul, one_mul] using ht

/-- Every invertible raw component system can be anchored before applying the
existing reconstruction theorem. The reconstruction denominator remains explicit.-/
theorem componentSolution_of_raw
    (a0 a1 a2 b0 b1 b2 : Mat3 K)
    (ha0 : a0.det ≠ 0) (ha1 : a1.det ≠ 0) (ha2 : a2.det ≠ 0)
    (hb0 : b0.det = a0.det) (hb1 : b1.det = a1.det) (hb2 : b2.det = a2.det)
    (hbsum : b0 + b1 + b2 = 0)
    (hcsum : cslotSum b0 b1 b2 a0.adjugate a1.adjugate a2.adjugate = 0)
    (hden : (reconstructionDenominator (componentU a0 a1 a2) (componentV a0 a1)
      (a1.det / a0.det) (a2.det / a0.det) (Matrix.trace (normalizedX a0 b0 b1))).det ≠ 0) :
    ComponentSolution a0 a1 a2 (normalizedX a0 b0 b1) := by
  obtain ⟨hd, _, hgh, _⟩ := anchor_properties a0 b0 ha0 hb0
  obtain ⟨h0, h1, h2⟩ := normalized_second_components a0 b0 b1 b2 ha0 hb0 hbsum
  refine ⟨?_, ?_, ?_, hden⟩
  · rw [← h1, Matrix.det_mul, hd, mul_one, hb1]
  · rw [← h2, Matrix.det_mul, hd, mul_one, hb2]
  · have ht := cslotSum_right_change b0 b1 b2 a0.adjugate a1.adjugate a2.adjugate
      (a0⁻¹ * b0) (anchor a0 b0) (hb0 ▸ ha0) (hb1 ▸ ha1) (hb2 ▸ ha2) hgh
    rw [h0, h1, h2, hcsum, mul_zero] at ht
    exact ht

end AlbertLean.Generic.FourRowNormalization
