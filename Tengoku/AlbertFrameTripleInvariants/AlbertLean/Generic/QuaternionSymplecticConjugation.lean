import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionScalarJordanAut

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms conjugate_mem` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms conjugateLinearEquiv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms conjugate_map_jordan` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms jordanAut` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.SymplecticConjugation

open AlbertLean.Generic.QuaternionRow.GroupedBridge
open AlbertLean.Generic.QuaternionRow.SelfAdjointCarrier
open AlbertLean.Generic.QuaternionRow.ScalarJordanAut

universe u
variable {K : Type u} [Field K] [CharZero K]

/--
@isnad1 id=eq.2h3v.s8.372611365209 from=translated src=- shape=dc4faf3e vocab=e74ad03e
-/
theorem left_form_of_symplectic_inverse
    (M N : Mat6 K) (hMN : M * N = 1)
    (hform : M.transpose * symplecticJ * M = symplecticJ) :
    M.transpose * symplecticJ = symplecticJ * N := by
  calc
    M.transpose * symplecticJ =
        M.transpose * symplecticJ * (M * N) := by rw [hMN, Matrix.mul_one]
    _ = (M.transpose * symplecticJ * M) * N := by
      simp only [Matrix.mul_assoc]
    _ = symplecticJ * N := by rw [hform]

/--
@isnad1 id=eq.2h3v.s8.b02d97db003f from=translated src=- shape=b856f9b8 vocab=e74ad03e
-/
theorem right_form_of_symplectic_inverse
    (M N : Mat6 K) (hMN : M * N = 1)
    (hform : M.transpose * symplecticJ * M = symplecticJ) :
    N.transpose * symplecticJ = symplecticJ * M := by
  calc
    N.transpose * symplecticJ =
        N.transpose * (M.transpose * symplecticJ * M) := by rw [hform]
    _ = (M * N).transpose * symplecticJ * M := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = symplecticJ * M := by rw [hMN, Matrix.transpose_one, Matrix.one_mul]

/--
@isnad1 id=eq.3h3v.s9.2d1ad740aca9 from=translated src=- shape=0610cbca vocab=e74ad03e
-/
theorem inverse_is_symplectic
    (M N : Mat6 K) (hMN : M * N = 1) (hNM : N * M = 1)
    (hform : M.transpose * symplecticJ * M = symplecticJ) :
    N.transpose * symplecticJ * N = symplecticJ := by
  rw [right_form_of_symplectic_inverse M N hMN hform, Matrix.mul_assoc, hMN,
    Matrix.mul_one]

/-- Conjugation by an explicitly invertible symplectic matrix preserves the
actual `PᵀJ=JP` carrier.
@isnad1 id=isselfad.2h4v.s9.10fa02bd506c from=translated src=- shape=00e12f78 vocab=429bf580
-/
theorem conjugate_mem
    (M N : Mat6 K) (hMN : M * N = 1)
    (hform : M.transpose * symplecticJ * M = symplecticJ)
    (P : Carrier K) : IsSelfAdjoint (M * (P : Mat6 K) * N) := by
  have hleft := left_form_of_symplectic_inverse M N hMN hform
  have hright := right_form_of_symplectic_inverse M N hMN hform
  change (M * (P : Mat6 K) * N).transpose * symplecticJ =
    symplecticJ * (M * (P : Mat6 K) * N)
  rw [Matrix.transpose_mul, Matrix.transpose_mul]
  calc
    N.transpose * ((P : Mat6 K).transpose * M.transpose) * symplecticJ =
        N.transpose * (P : Mat6 K).transpose *
          (M.transpose * symplecticJ) := by
      simp only [Matrix.mul_assoc]
    _ = N.transpose * (P : Mat6 K).transpose * (symplecticJ * N) := by
      rw [hleft]
    _ = N.transpose * ((P : Mat6 K).transpose * symplecticJ) * N := by
      simp only [Matrix.mul_assoc]
    _ = N.transpose * (symplecticJ * (P : Mat6 K)) * N := by
      rw [carrier_property P]
    _ = (N.transpose * symplecticJ) * (P : Mat6 K) * N := by
      simp only [Matrix.mul_assoc]
    _ = symplecticJ * M * (P : Mat6 K) * N := by rw [hright]
    _ = symplecticJ * (M * (P : Mat6 K) * N) := by
      simp only [Matrix.mul_assoc]

def conjugateLinear
    (M N : Mat6 K) (hMN : M * N = 1)
    (hform : M.transpose * symplecticJ * M = symplecticJ) :
    Carrier K →ₗ[K] Carrier K where
  toFun P := ⟨M * (P : Mat6 K) * N, conjugate_mem M N hMN hform P⟩
  map_add' A B := by
    apply Subtype.ext
    simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' t A := by
    apply Subtype.ext
    simp [Matrix.mul_smul, Matrix.smul_mul]

/--
@isnad1 id=eq.2h4v.s11.31c4d180df96 from=translated src=- shape=4b8191b4 vocab=63f7305d
-/
@[simp] theorem conjugateLinear_coe
    (M N : Mat6 K) (hMN : M * N = 1)
    (hform : M.transpose * symplecticJ * M = symplecticJ) (P : Carrier K) :
    ((conjugateLinear M N hMN hform P : Carrier K) : Mat6 K) = M * P * N := rfl

def conjugateLinearEquiv
    (M N : Mat6 K) (hMN : M * N = 1) (hNM : N * M = 1)
    (hform : M.transpose * symplecticJ * M = symplecticJ) :
    Carrier K ≃ₗ[K] Carrier K where
  toLinearMap := conjugateLinear M N hMN hform
  invFun := conjugateLinear N M hNM (inverse_is_symplectic M N hMN hNM hform)
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

/--
@isnad1 id=eq.1h3v.s8.2d9df70d11ff from=translated src=- shape=16edc93d vocab=9d330ec2
-/
theorem conjugate_map_one
    (M N : Mat6 K) (hMN : M * N = 1) : M * (1 : Mat6 K) * N = 1 := by
  simpa using hMN

/--
@isnad1 id=eq.1h5v.s9.8541950071b5 from=translated src=- shape=35be6d12 vocab=64e318e3
-/
theorem conjugate_map_jordan
    (M N : Mat6 K) (hNM : N * M = 1) (A B : Mat6 K) :
    M * matrixJordan A B * N =
      matrixJordan (M * A * N) (M * B * N) := by
  have hmul (X Y : Mat6 K) :
      M * (X * Y) * N = (M * X * N) * (M * Y * N) := by
    symm
    calc
      (M * X * N) * (M * Y * N) = M * X * (N * M) * Y * N := by
        simp only [Matrix.mul_assoc]
      _ = M * X * 1 * Y * N := by rw [hNM]
      _ = M * (X * Y) * N := by simp [Matrix.mul_assoc]
  simp only [matrixJordan, Matrix.mul_smul, Matrix.smul_mul]
  rw [Matrix.mul_add, Matrix.add_mul, hmul A B, hmul B A]

/-- A generic symplectic conjugation is a genuine unital linear Jordan
automorphism of the actual quaternion carrier.-/
def jordanAut
    (M N : Mat6 K) (hMN : M * N = 1) (hNM : N * M = 1)
    (hform : M.transpose * symplecticJ * M = symplecticJ) : Aut (K := K) where
  linear := conjugateLinearEquiv M N hMN hNM hform
  map_one := by
    apply Subtype.ext
    exact conjugate_map_one M N hMN
  map_jordan A B := by
    apply Subtype.ext
    exact conjugate_map_jordan M N hNM A B

end AlbertLean.Generic.QuaternionRow.SymplecticConjugation
