import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FourRowAdjugateSystem
import Tengoku.Seed.Tactic.FinCases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms normalizedX_eq_ratio` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms gaugeRelated_iff_ratio_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms gaugeRelated_equivalence` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms gauge_transporter_unique` (it only prints; the queue checks the axioms of every declaration). -/

/-! # Gauge classification of raw ordinary matrix systems

No Albert carrier or product is defined here.
-/

noncomputable section
namespace AlbertLean.Generic.FourRowGauge

open AlbertLean.Generic.FourRowFrameReduction
open AlbertLean.Generic.FourRowAdjoint (parametrized_iff_adjugate_equations)
open AlbertLean.Generic.FourRowNormalization

variable {K : Type*} [Field K]

/-- Raw cyclic adjugate system over fixed first components.-/
structure RawSystem (a : Fin 3 → Mat3 K) where
  b : Fin 3 → Mat3 K
  c : Fin 3 → Mat3 K
  b_ne : ∀ i, (b i).det ≠ 0
  equations : ∀ i, (a i).adjugate = b i * c i ∧
    (c i).adjugate = a i * b i ∧ (b i).adjugate = c i * a i
  b_sum : b 0 + b 1 + b 2 = 0
  c_sum : c 0 + c 1 + c 2 = 0

def ratio {a : Fin 3 → Mat3 K} (S : RawSystem a) : Mat3 K :=
  S.b 1 * (S.b 0)⁻¹

/-- The anchored coordinate used by the existing normalization module reduces
to the raw right ratio.
@isnad1 id=eq.1h4v.s7.c8f2b13788d9 from=translated src=- shape=c018ecd8 vocab=35ef924e
-/
theorem normalizedX_eq_ratio (a0 b0 b1 : Mat3 K) (ha0 : a0.det ≠ 0) :
    normalizedX a0 b0 b1 = b1 * b0⁻¹ := by
  simp only [normalizedX, anchor, mul_assoc]
  rw [Matrix.mul_nonsing_inv a0 (isUnit_iff_ne_zero.mpr ha0), mul_one]

def GaugeRelated {a : Fin 3 → Mat3 K} (S T : RawSystem a) : Prop :=
  ∃ h : Mat3 K, h.det = 1 ∧
    (∀ i, T.b i = S.b i * h) ∧ (∀ i, T.c i = h⁻¹ * S.c i)

/--
@isnad1 id=eq.0h4v.s6.a73e1b5e9432 from=translated src=- shape=99764a39 vocab=554f64e3
-/
theorem det_b_eq {a : Fin 3 → Mat3 K} (S : RawSystem a) (i : Fin 3) :
    (S.b i).det = (a i).det :=
  (parametrized_iff_adjugate_equations (a i) (S.b i) (S.c i) (S.b_ne i)).mpr
    (S.equations i) |>.1

/--
@isnad1 id=eq.0h4v.s7.3aad3d8febca from=translated src=- shape=69c29398 vocab=197f1258
-/
theorem c_eq_inverse_adjugate {a : Fin 3 → Mat3 K}
    (S : RawSystem a) (i : Fin 3) :
    S.c i = (S.b i)⁻¹ * (a i).adjugate :=
  (parametrized_iff_adjugate_equations (a i) (S.b i) (S.c i) (S.b_ne i)).mpr
    (S.equations i) |>.2

/--
@isnad1 id=eq.1h4v.s5.90d08ee4ace4 from=translated src=- shape=2571d701 vocab=e5d69672
-/
theorem ratio_eq_of_gaugeRelated {a : Fin 3 → Mat3 K}
    {S T : RawSystem a} (hg : GaugeRelated S T) : ratio S = ratio T := by
  rcases hg with ⟨h, hdet, hb, _⟩
  have hh : h.det ≠ 0 := by rw [hdet]; exact one_ne_zero
  have hhinv : h⁻¹ * h = 1 := Matrix.nonsing_inv_mul h (isUnit_iff_ne_zero.mpr hh)
  have hinv := inverse_after_right_change (S.b 0) h⁻¹ h (S.b_ne 0) hhinv
  rw [ratio, ratio, hb 1, hb 0, hinv]
  symm
  rw [mul_assoc, ← mul_assoc h h⁻¹,
    Matrix.mul_nonsing_inv h (isUnit_iff_ne_zero.mpr hh), one_mul]

/-- Equality of normalized ratios constructs the unique determinant-one gauge.
@isnad1 id=gaugerel.1h4v.s5.17594da3fb41 from=translated src=- shape=958433b8 vocab=e5d69672
-/
theorem gaugeRelated_of_ratio_eq {a : Fin 3 → Mat3 K}
    {S T : RawSystem a} (hratio : ratio S = ratio T) : GaugeRelated S T := by
  let h : Mat3 K := (S.b 0)⁻¹ * T.b 0
  have hs0 := S.b_ne 0
  have ht0 := T.b_ne 0
  have hb0 : S.b 0 * h = T.b 0 := by
    dsimp only [h]
    rw [← mul_assoc,
      Matrix.mul_nonsing_inv (S.b 0) (isUnit_iff_ne_zero.mpr hs0), one_mul]
  have hdet : h.det = 1 := by
    dsimp only [h]
    rw [Matrix.det_mul, det_b_eq T 0, ← det_b_eq S 0]
    exact Matrix.det_nonsing_inv_mul_det (S.b 0) (isUnit_iff_ne_zero.mpr hs0)
  have hh : h.det ≠ 0 := by rw [hdet]; exact one_ne_zero
  have hb1 : S.b 1 * h = T.b 1 := by
    have hm := congrArg (fun Z : Mat3 K => Z * T.b 0) hratio
    simp only [ratio, mul_assoc,
      Matrix.nonsing_inv_mul (T.b 0) (isUnit_iff_ne_zero.mpr ht0), mul_one] at hm
    simpa only [h, mul_assoc] using hm
  have hb2 : S.b 2 * h = T.b 2 := by
    have hs := congrArg (fun Z : Mat3 K => Z * h) S.b_sum
    simp only [add_mul, zero_mul, hb0, hb1] at hs
    exact add_left_cancel (hs.trans T.b_sum.symm)
  have hb : ∀ i, T.b i = S.b i * h := by
    intro i
    fin_cases i
    · exact hb0.symm
    · exact hb1.symm
    · exact hb2.symm
  have hhinv : h⁻¹ * h = 1 := Matrix.nonsing_inv_mul h (isUnit_iff_ne_zero.mpr hh)
  have hc : ∀ i, T.c i = h⁻¹ * S.c i := by
    intro i
    rw [c_eq_inverse_adjugate T i, c_eq_inverse_adjugate S i, hb i,
      inverse_after_right_change (S.b i) h⁻¹ h (S.b_ne i) hhinv,
      mul_assoc]
  exact ⟨h, hdet, hb, hc⟩

/--
@isnad1 id=iff.0h4v.s5.97d0b3c28aef from=translated src=- shape=cc43120b vocab=e5d69672
-/
theorem gaugeRelated_iff_ratio_eq {a : Fin 3 → Mat3 K} (S T : RawSystem a) :
    GaugeRelated S T ↔ ratio S = ratio T :=
  ⟨ratio_eq_of_gaugeRelated, gaugeRelated_of_ratio_eq⟩

/-- The displayed transporter relation is an equivalence relation on raw systems.
@isnad1 id=equivale.0h2v.s4.3ae66d151023 from=translated src=- shape=15cb83f1 vocab=9da988f6
-/
theorem gaugeRelated_equivalence (a : Fin 3 → Mat3 K) :
    Equivalence (GaugeRelated (a := a)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro S
    exact (gaugeRelated_iff_ratio_eq S S).mpr rfl
  · intro S T h
    exact (gaugeRelated_iff_ratio_eq T S).mpr ((gaugeRelated_iff_ratio_eq S T).mp h).symm
  · intro S T W hST hTW
    exact (gaugeRelated_iff_ratio_eq S W).mpr
      (((gaugeRelated_iff_ratio_eq S T).mp hST).trans
        ((gaugeRelated_iff_ratio_eq T W).mp hTW))

/-- The right transporter is forced by its action on the nonsingular zeroth component.
@isnad1 id=eq.1h5v.s8.9d7dfccfb9ab from=translated src=- shape=43fbd063 vocab=eb9330a6
-/
theorem gauge_transporter_unique {a : Fin 3 → Mat3 K} (S T : RawSystem a)
    (h : Mat3 K) (hb0 : T.b 0 = S.b 0 * h) :
    h = (S.b 0)⁻¹ * T.b 0 := by
  calc
    h = 1 * h := (one_mul h).symm
    _ = ((S.b 0)⁻¹ * S.b 0) * h := by
      rw [Matrix.nonsing_inv_mul (S.b 0) (isUnit_iff_ne_zero.mpr (S.b_ne 0))]
    _ = (S.b 0)⁻¹ * (S.b 0 * h) := by rw [mul_assoc]
    _ = (S.b 0)⁻¹ * T.b 0 := by rw [← hb0]

end AlbertLean.Generic.FourRowGauge
