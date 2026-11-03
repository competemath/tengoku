import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionSymplecticConjugation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms left_form` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms scaled_right_form` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms inverse_form` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms conjugate_mem` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms conjugateLinearEquiv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms jordanAut` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.SimilitudeConjugation

open AlbertLean.Generic.QuaternionRow.GroupedBridge
open AlbertLean.Generic.QuaternionRow.SelfAdjointCarrier
open AlbertLean.Generic.QuaternionRow.ScalarJordanAut

universe u
variable {K : Type u} [Field K] [CharZero K]

variable (M N : Mat6 K) (c : K)

/-- The first useful form of the multiplier identity, with the explicit
inverse on the right.-/
theorem left_form (hMN : M * N = 1)
    (hform : M.transpose * symplecticJ * M = c • symplecticJ) :
    M.transpose * symplecticJ = c • (symplecticJ * N) := by
  calc
    M.transpose * symplecticJ = M.transpose * symplecticJ * (M * N) := by
      rw [hMN, Matrix.mul_one]
    _ = (M.transpose * symplecticJ * M) * N := by
      simp only [Matrix.mul_assoc]
    _ = (c • symplecticJ) * N := by rw [hform]
    _ = c • (symplecticJ * N) := by rw [Matrix.smul_mul]

/-- The companion identity.  Keeping the multiplier on the left avoids any
choice of a square root of `c`.-/
theorem scaled_right_form (hMN : M * N = 1)
    (hform : M.transpose * symplecticJ * M = c • symplecticJ) :
    c • (N.transpose * symplecticJ) = symplecticJ * M := by
  calc
    c • (N.transpose * symplecticJ) = N.transpose * (c • symplecticJ) := by
      rw [Matrix.mul_smul]
    _ = N.transpose * (M.transpose * symplecticJ * M) := by rw [hform]
    _ = (M * N).transpose * symplecticJ * M := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = symplecticJ * M := by rw [hMN, Matrix.transpose_one, Matrix.one_mul]

/-- The explicit inverse is a similitude of inverse multiplier.-/
theorem inverse_form (hMN : M * N = 1) (hc : c ≠ 0)
    (hform : M.transpose * symplecticJ * M = c • symplecticJ) :
    N.transpose * symplecticJ * N = c⁻¹ • symplecticJ := by
  have hr := congrArg (fun A : Mat6 K => A * N)
    (scaled_right_form M N c hMN hform)
  have hscaled : c • (N.transpose * symplecticJ * N) = symplecticJ := by
    simpa only [Matrix.smul_mul, Matrix.mul_assoc, hMN, Matrix.mul_one] using hr
  calc
    N.transpose * symplecticJ * N = (1 : K) • (N.transpose * symplecticJ * N) := by simp
    _ = (c⁻¹ * c) • (N.transpose * symplecticJ * N) := by rw [inv_mul_cancel₀ hc]
    _ = c⁻¹ • (c • (N.transpose * symplecticJ * N)) := by rw [smul_smul]
    _ = c⁻¹ • symplecticJ := by rw [hscaled]

/-- Conjugation by an invertible symplectic similitude preserves the actual
`PᵀJ=JP` carrier.-/
theorem conjugate_mem (hMN : M * N = 1)
    (hform : M.transpose * symplecticJ * M = c • symplecticJ)
    (P : Carrier K) : IsSelfAdjoint (M * (P : Mat6 K) * N) := by
  have hl := left_form M N c hMN hform
  have hr := scaled_right_form M N c hMN hform
  change (M * (P : Mat6 K) * N).transpose * symplecticJ =
    symplecticJ * (M * (P : Mat6 K) * N)
  rw [Matrix.transpose_mul, Matrix.transpose_mul]
  calc
    N.transpose * ((P : Mat6 K).transpose * M.transpose) * symplecticJ =
        N.transpose * (P : Mat6 K).transpose *
          (M.transpose * symplecticJ) := by simp only [Matrix.mul_assoc]
    _ = N.transpose * (P : Mat6 K).transpose *
          (c • (symplecticJ * N)) := by rw [hl]
    _ = c • (N.transpose * ((P : Mat6 K).transpose * symplecticJ) * N) := by
      simp only [Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul]
    _ = c • (N.transpose * (symplecticJ * (P : Mat6 K)) * N) := by
      rw [carrier_property P]
    _ = (c • (N.transpose * symplecticJ)) * (P : Mat6 K) * N := by
      simp only [Matrix.mul_assoc, Matrix.smul_mul]
    _ = symplecticJ * M * (P : Mat6 K) * N := by rw [hr]
    _ = symplecticJ * (M * (P : Mat6 K) * N) := by
      simp only [Matrix.mul_assoc]

def conjugateLinear (hMN : M * N = 1)
    (hform : M.transpose * symplecticJ * M = c • symplecticJ) :
    Carrier K →ₗ[K] Carrier K where
  toFun P := ⟨M * (P : Mat6 K) * N, conjugate_mem M N c hMN hform P⟩
  map_add' A B := by
    apply Subtype.ext
    simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' t A := by
    apply Subtype.ext
    simp [Matrix.mul_smul, Matrix.smul_mul]

@[simp] theorem conjugateLinear_coe (hMN : M * N = 1)
    (hform : M.transpose * symplecticJ * M = c • symplecticJ) (P : Carrier K) :
    ((conjugateLinear M N c hMN hform P : Carrier K) : Mat6 K) = M * P * N := rfl

def conjugateLinearEquiv (hMN : M * N = 1) (hNM : N * M = 1) (hc : c ≠ 0)
    (hform : M.transpose * symplecticJ * M = c • symplecticJ) :
    Carrier K ≃ₗ[K] Carrier K where
  toLinearMap := conjugateLinear M N c hMN hform
  invFun := conjugateLinear N M c⁻¹ hNM (inverse_form M N c hMN hc hform)
  left_inv P := by
    apply Subtype.ext
    change N * (M * (P : Mat6 K) * N) * M = (P : Mat6 K)
    calc
      N * (M * (P : Mat6 K) * N) * M =
          (N * M) * (P : Mat6 K) * (N * M) := by
            simp only [Matrix.mul_assoc]
      _ = 1 * (P : Mat6 K) * 1 := by rw [hNM]
      _ = (P : Mat6 K) := by simp
  right_inv P := by
    apply Subtype.ext
    change M * (N * (P : Mat6 K) * M) * N = (P : Mat6 K)
    calc
      M * (N * (P : Mat6 K) * M) * N =
          (M * N) * (P : Mat6 K) * (M * N) := by
            simp only [Matrix.mul_assoc]
      _ = 1 * (P : Mat6 K) * 1 := by rw [hMN]
      _ = (P : Mat6 K) := by simp

/-- Every explicitly invertible symplectic similitude acts by a genuine
unital Jordan automorphism of the quaternion carrier.-/
def jordanAut (hMN : M * N = 1) (hNM : N * M = 1) (hc : c ≠ 0)
    (hform : M.transpose * symplecticJ * M = c • symplecticJ) : Aut (K := K) where
  linear := conjugateLinearEquiv M N c hMN hNM hc hform
  map_one := by
    apply Subtype.ext
    exact SymplecticConjugation.conjugate_map_one M N hMN
  map_jordan A B := by
    apply Subtype.ext
    exact SymplecticConjugation.conjugate_map_jordan M N hNM A B

end AlbertLean.Generic.QuaternionRow.SimilitudeConjugation
