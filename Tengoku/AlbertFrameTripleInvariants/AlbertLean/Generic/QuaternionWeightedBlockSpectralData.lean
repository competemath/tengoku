import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionWeightedBlockEquations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms mul_adj` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms weighted_product` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms pivot_trace_relation` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms pivot_determinant_relation` (it only prints; the queue checks the axioms of every declaration). -/

/-! Scalar spectral data of the one remaining weighted block. The self-adjoint
and projector equations are exactly the equations transported by the Q1 gauge. -/
noncomputable section
namespace AlbertLean.Generic.QuaternionRow.WeightedBlockEquations
open AlbertLean.Generic.QuaternionRow.BlockEigenbasis
variable {K : Type*} [Field K] [CharZero K]

def adj (X : Mat2 K) : Mat2 K := matrix (X 1 1) (-X 0 1) (-X 1 0) (X 0 0)

/--
@isnad1 id=eq.0h2v.s7.b8b2f891902d from=translated src=- shape=08f4a857 vocab=895306ea
-/
theorem mul_adj (X : Mat2 K) : X * adj X = determinant X • (1 : Mat2 K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adj, matrix, Matrix.mul_apply, Fin.sum_univ_two, determinant] <;> ring

/--
@isnad1 id=eq.1h5v.s8.264b6eb18efd from=translated src=- shape=06a0c439 vocab=895306ea
-/
theorem weighted_product (p q : K) (X Y : Mat2 K)
    (h : p • Y = q • adj X) :
    p • (X * Y) = (q * determinant X) • (1 : Mat2 K) := by
  calc
    p • (X * Y) = X * (p • Y) := (mul_smul_comm p X Y).symm
    _ = X * (q • adj X) := by rw [h]
    _ = q • (X * adj X) := mul_smul_comm q X (adj X)
    _ = (q * determinant X) • (1 : Mat2 K) := by rw [mul_adj, smul_smul]

/-- The weighted adjoint relation recovers the trace from the overlap data.
@isnad1 id=eq.4h4v.s10.487707a22bfa from=translated src=- shape=7141fbf5 vocab=67d6b702
-/
theorem pivot_trace_relation (B : Fin 3 → Fin 3 → Mat2 K) (p q : Fin 3 → K)
    (hd : ∀ i, B i i = q i • (1 : Mat2 K))
    (hr : ∀ i, B i 0 + B i 1 + B i 2 = 0)
    (hc : ∀ j, p 0 • B 0 j + p 1 • B 1 j + p 2 • B 2 j = 0)
    (hs : p 1 • B 1 0 = p 0 • adj (B 0 1)) :
    p 0 * trace2 (B 0 1) = -p 0 * q 0 - p 1 * q 1 + p 2 * q 2 := by
  have hb := (scaled_block_equations B p q hd hr hc).2.2.2.1
  have hb00 := congrArg (fun X : Mat2 K => X 0 0) hb
  have hs00 := congrArg (fun X : Mat2 K => X 0 0) hs
  simp [adj, matrix, Matrix.one_apply, smul_eq_mul] at hb00 hs00
  dsimp [trace2]
  linear_combination hb00 - hs00

/-- The first diagonal projector equation determines the determinant of the
remaining block once its trace and the overlaps are known.
@isnad1 id=eq.6h4v.s11.c100ad1d3818 from=translated src=- shape=1015cbe7 vocab=8a73af4d
-/
theorem pivot_determinant_relation (B : Fin 3 → Fin 3 → Mat2 K) (p q : Fin 3 → K)
    (hd : ∀ i, B i i = q i • (1 : Mat2 K))
    (hr : ∀ i, B i 0 + B i 1 + B i 2 = 0)
    (hc : ∀ j, p 0 • B 0 j + p 1 • B 1 j + p 2 • B 2 j = 0)
    (hs1 : p 1 • B 1 0 = p 0 • adj (B 0 1))
    (hs2 : p 2 • B 2 0 = p 0 • adj (B 0 2))
    (hi : B 0 0 * B 0 0 + B 0 1 * B 1 0 + B 0 2 * B 2 0 = B 0 0) :
    p 0 * (p 1 + p 2) * determinant (B 0 1) =
      p 1 * p 2 * (q 0 - q 0 ^ 2) -
        p 0 * p 1 * (q 0 ^ 2 + q 0 * trace2 (B 0 1)) := by
  have hw1 := weighted_product (p 1) (p 0) (B 0 1) (B 1 0) hs1
  have hw2 := weighted_product (p 2) (p 0) (B 0 2) (B 2 0) hs2
  have h01 : B 0 2 = affine (-q 0) (-1) (B 0 1) := by
    rw [(scaled_block_equations B p q hd hr hc).1]
    simp [affine, sub_eq_add_neg]
  have hdet : determinant (B 0 2) =
      q 0 ^ 2 + q 0 * trace2 (B 0 1) + determinant (B 0 1) := by
    rw [h01, determinant_affine]
    ring
  have hm := congrArg (fun X : Mat2 K => X 0 0) hi
  have h1 := congrArg (fun X : Mat2 K => X 0 0) hw1
  have h2 := congrArg (fun X : Mat2 K => X 0 0) hw2
  rw [hd 0] at hm
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    ite_true, smul_eq_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    one_mul, smul_smul] at hm h1 h2
  rw [hdet] at h2
  linear_combination p 1 * p 2 * hm - p 2 * h1 - p 1 * h2

end AlbertLean.Generic.QuaternionRow.WeightedBlockEquations
