import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FourRowComponents
import Tengoku.Seed.LinearAlgebra.Matrix.NonsingularInverse

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowAdjoint.det_nonsing_inv_mul_adjugate` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowAdjoint.parametrized_adjugate_equations` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowAdjoint.det_eq_of_adjugate_equations` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowAdjoint.parametrized_iff_adjugate_equations` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Ordinary three-by-three adjugate parametrization

This module isolates the associative matrix algebra behind one proposed
component chart.  It defines no Albert algebra and makes no rank-one, primitive,
idempotent, or frame claim.
-/

noncomputable section
namespace AlbertLean.Generic.FourRowAdjoint

variable {K : Type*} [Field K]
abbrev Mat3 (K : Type*) := Matrix (Fin 3) (Fin 3) K

/-- Left cancellation by an explicitly nonsingular square matrix.-/
theorem eq_of_mul_eq_mul_left
    (M X Y : Mat3 K) (hM : M.det ≠ 0) (h : M * X = M * Y) : X = Y := by
  calc
    X = M⁻¹ * (M * X) := by
      rw [← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM), Matrix.one_mul]
    _ = M⁻¹ * (M * Y) := by rw [h]
    _ = Y := by
      rw [← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM), Matrix.one_mul]

/-- The determinant of the parametrized third matrix equals the common
determinant.  This is the only scalar calculation needed below.
@isnad1 id=eq.2h3v.s8.3739f4a1e2c6 from=translated src=- shape=9105fc1f vocab=df1ed370
-/
theorem det_nonsing_inv_mul_adjugate
    (a b : Mat3 K) (hb : b.det ≠ 0) (hdet : b.det = a.det) :
    (b⁻¹ * a.adjugate).det = a.det := by
  rw [Matrix.det_mul, Matrix.det_nonsing_inv, Matrix.det_adjugate]
  rw [← hdet]
  simp only [Ring.inverse_eq_inv]
  field_simp [hb]
  norm_num

/-- The first adjugate equation is immediate from the definition of `c`.
@isnad1 id=eq.1h3v.s8.5f2d22a16315 from=translated src=- shape=8d7bfb3b vocab=df1ed370
-/
theorem adjugate_eq_mul_parametrized
    (a b : Mat3 K) (hb : b.det ≠ 0) :
    a.adjugate = b * (b⁻¹ * a.adjugate) := by
  rw [← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv b (isUnit_iff_ne_zero.mpr hb), Matrix.one_mul]

/-- The third adjugate equation follows by comparing after multiplication by
`b`; no commutation or adjugate-of-product formula is used.
@isnad1 id=eq.2h3v.s8.02a6412bd62e from=translated src=- shape=bef497c7 vocab=df1ed370
-/
theorem adjugate_b_eq_parametrized_mul_a
    (a b : Mat3 K) (hb : b.det ≠ 0) (hdet : b.det = a.det) :
    b.adjugate = (b⁻¹ * a.adjugate) * a := by
  apply eq_of_mul_eq_mul_left b _ _ hb
  calc
    b * b.adjugate = b.det • (1 : Mat3 K) := Matrix.mul_adjugate b
    _ = a.det • (1 : Mat3 K) := by rw [hdet]
    _ = a.adjugate * a := (Matrix.adjugate_mul a).symm
    _ = b * ((b⁻¹ * a.adjugate) * a) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv b (isUnit_iff_ne_zero.mpr hb), Matrix.one_mul]

/-- The middle adjugate equation follows from its defining determinant
identity and cancellation by the now-proved nonsingular matrix `c`.
@isnad1 id=eq.2h3v.s8.01659509df78 from=translated src=- shape=acc04326 vocab=df1ed370
-/
theorem adjugate_parametrized_eq_mul
    (a b : Mat3 K) (hb : b.det ≠ 0) (hdet : b.det = a.det) :
    (b⁻¹ * a.adjugate).adjugate = a * b := by
  let c : Mat3 K := b⁻¹ * a.adjugate
  have hdetc : c.det = a.det := by
    exact det_nonsing_inv_mul_adjugate a b hb hdet
  have ha : a.det ≠ 0 := by rw [← hdet]; exact hb
  have hc : c.det ≠ 0 := by rw [hdetc]; exact ha
  apply eq_of_mul_eq_mul_left c _ _ hc
  calc
    c * c.adjugate = c.det • (1 : Mat3 K) := Matrix.mul_adjugate c
    _ = a.det • (1 : Mat3 K) := by rw [hdetc]
    _ = b.det • (1 : Mat3 K) := by rw [hdet]
    _ = b.adjugate * b := (Matrix.adjugate_mul b).symm
    _ = (c * a) * b := by
      rw [← adjugate_b_eq_parametrized_mul_a a b hb hdet]
    _ = c * (a * b) := by rw [Matrix.mul_assoc]

/-- Complete forward package for `c=b⁻¹ adj(a)`.  The single nonsingularity
hypothesis on `b`, together with equal determinants, is sufficient.
@isnad1 id=other.2h3v.s9.648207545ca5 from=translated src=- shape=16ed74a4 vocab=df1ed370
-/
theorem parametrized_adjugate_equations
    (a b : Mat3 K) (hb : b.det ≠ 0) (hdet : b.det = a.det) :
    let c := b⁻¹ * a.adjugate
    a.adjugate = b * c ∧ c.adjugate = a * b ∧ b.adjugate = c * a := by
  dsimp only
  exact ⟨adjugate_eq_mul_parametrized a b hb,
    adjugate_parametrized_eq_mul a b hb hdet,
    adjugate_b_eq_parametrized_mul_a a b hb hdet⟩

/-- Conversely, the first adjugate equation recovers the parameter `c`
whenever `b` is nonsingular.-/
theorem eq_nonsing_inv_mul_adjugate_of_adjugate_eq_mul
    (a b c : Mat3 K) (hb : b.det ≠ 0) (h : a.adjugate = b * c) :
    c = b⁻¹ * a.adjugate := by
  calc
    c = b⁻¹ * (b * c) := by
      rw [← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul b (isUnit_iff_ne_zero.mpr hb), Matrix.one_mul]
    _ = b⁻¹ * a.adjugate := by rw [← h]

/-- The first and third raw adjugate equations already force equality of the
two determinants.  Reading one diagonal entry avoids scalar-matrix extensionality.
@isnad1 id=eq.2h4v.s8.09a41b6ace0b from=translated src=- shape=9315b5aa vocab=b2dc626f
-/
theorem det_eq_of_adjugate_equations
    (a b c : Mat3 K) (ha : a.adjugate = b * c)
    (hb : b.adjugate = c * a) : b.det = a.det := by
  have hm : a.det • (1 : Mat3 K) = b.det • (1 : Mat3 K) := by
    calc
      a.det • (1 : Mat3 K) = a.adjugate * a := (Matrix.adjugate_mul a).symm
      _ = (b * c) * a := by rw [ha]
      _ = b * (c * a) := by rw [Matrix.mul_assoc]
      _ = b * b.adjugate := by rw [← hb]
      _ = b.det • (1 : Mat3 K) := Matrix.mul_adjugate b
  have hentry := congrFun (congrFun hm 0) 0
  simpa using hentry.symm

/-- Exact characterization without a redundant determinant hypothesis on the
raw-equation side.  The first and third equations recover equal determinants;
then nonsingularity of `b` recovers the displayed parameter `c`.
@isnad1 id=iff.1h4v.s9.f426e662f22f from=translated src=- shape=f07d718e vocab=df1ed370
-/
theorem parametrized_iff_adjugate_equations
    (a b c : Mat3 K) (hb : b.det ≠ 0) :
    (b.det = a.det ∧ c = b⁻¹ * a.adjugate) ↔
      (a.adjugate = b * c ∧ c.adjugate = a * b ∧ b.adjugate = c * a) := by
  constructor
  · rintro ⟨hdet, rfl⟩
    exact parametrized_adjugate_equations a b hb hdet
  · rintro ⟨ha, hc, hbAdj⟩
    have hdet := det_eq_of_adjugate_equations a b c ha hbAdj
    exact ⟨hdet, eq_nonsing_inv_mul_adjugate_of_adjugate_eq_mul a b c hb ha⟩

end AlbertLean.Generic.FourRowAdjoint
