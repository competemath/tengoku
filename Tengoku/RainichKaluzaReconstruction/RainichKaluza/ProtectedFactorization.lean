import Tengoku.RainichKaluzaReconstruction.RainichKaluza.CharacteristicData
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Characteristic factorization from a protected opposite root pair

The earlier coefficient development encoded the proposed quadratic
factorization and deduced its two protected roots.  This file proves the
converse needed by the geometric argument: a monic quartic with nonzero roots
`+q` and `-q` necessarily contains the factor `x²-q²`, with the complementary
quadratic fixed by its first two characteristic coefficients.
-/

namespace RainichKaluza

/-- The odd characteristic coefficient is forced by a nonzero opposite root
pair.
@isnad1 id=eq.3h2v.s6.e2b852e2325c from=translated src=- shape=2d76a5d3 vocab=6bcc4ebf
-/
theorem e3_eq_neg_e1_mul_sq_of_opposite_roots
    (d : CharacteristicData) (q : ℝ) (hq : q ≠ 0)
    (hplus : monicQuartic d q = 0)
    (hminus : monicQuartic d (-q) = 0) :
    d.e3 = -(d.e1 * q ^ 2) := by
  have hproduct : q * (d.e1 * q ^ 2 + d.e3) = 0 := by
    simp [monicQuartic] at hplus hminus
    nlinarith
  have hsum : d.e1 * q ^ 2 + d.e3 = 0 :=
    (mul_eq_zero.mp hproduct).resolve_left hq
  linarith

/-- The constant characteristic coefficient is forced by the same opposite
root pair.
@isnad1 id=eq.2h2v.s6.d81b271ab08f from=translated src=- shape=b572ca0a vocab=eeb8faee
-/
theorem e4_eq_neg_sq_mul_add_of_opposite_roots
    (d : CharacteristicData) (q : ℝ)
    (hplus : monicQuartic d q = 0)
    (hminus : monicQuartic d (-q) = 0) :
    d.e4 = -(q ^ 2 * (d.e2 + q ^ 2)) := by
  simp [monicQuartic] at hplus hminus
  nlinarith

/-- **Protected-pair factorization theorem.** A nonzero opposite root pair
forces the proposed quadratic characteristic factorization.
@isnad1 id=eq.3h3v.s7.97bb9da1c59a from=translated src=- shape=77436d97 vocab=0a0683bb
-/
theorem monicQuartic_factorization_of_opposite_roots
    (d : CharacteristicData) (q x : ℝ) (hq : q ≠ 0)
    (hplus : monicQuartic d q = 0)
    (hminus : monicQuartic d (-q) = 0) :
    monicQuartic d x =
      (x ^ 2 - q ^ 2) *
        (x ^ 2 - d.e1 * x + d.e2 + q ^ 2) := by
  rw [monicQuartic]
  rw [e3_eq_neg_e1_mul_sq_of_opposite_roots d q hq hplus hminus]
  rw [e4_eq_neg_sq_mul_add_of_opposite_roots d q hplus hminus]
  ring

/-- The characteristic data themselves are exactly those produced by the
factorization parameters determined from the protected pair.
@isnad1 id=eq.3h2v.s6.9eb254bf17ce from=translated src=- shape=3d379bad vocab=fad4109a
-/
theorem characteristicData_eq_fromFactorization_of_opposite_roots
    (d : CharacteristicData) (q : ℝ) (hq : q ≠ 0)
    (hplus : monicQuartic d q = 0)
    (hminus : monicQuartic d (-q) = 0) :
    d = CharacteristicData.fromFactorization
      { ricciTrace := d.e1
        qSq := q ^ 2
        residualConstant := -(d.e2 + q ^ 2) } := by
  have he3 := e3_eq_neg_e1_mul_sq_of_opposite_roots d q hq hplus hminus
  have he4 := e4_eq_neg_sq_mul_add_of_opposite_roots d q hplus hminus
  cases d
  simp_all [CharacteristicData.fromFactorization]
  ring

end RainichKaluza
