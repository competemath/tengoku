module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.QWeylModule
public import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# Genuine graded pieces and cyclic cubic actions

The cyclic operators act on the actual binary homogeneous components with
their prescribed generator shifts. Their coefficients have exactly the
degrees required by those shifts, including the transposed dual action.
-/

noncomputable section
namespace ChoppedPlane.QWeyl
open MvPolynomial Module
variable {K : Type*} [Field K]

/-- The degrees of the three literal cyclic coefficients.-/
def profileFactorDegrees : CubicProfile → Fin 3 → ℕ
  | .degreeThree => ![1, 1, 1]
  | .degreeTwo => ![1, 0, 2]
  | .degreeOne => ![0, 1, 2]

theorem cubicLinearFactors_homogeneous (q : K) (i : Fin 3) :
    (cubicLinearFactors q i).IsHomogeneous 1 := by
  fin_cases i
  · exact (isHomogeneous_X K 0).add (isHomogeneous_X K 1)
  · exact (isHomogeneous_X K 0).add ((isHomogeneous_X K 1).C_mul q)
  · exact (isHomogeneous_X K 0).add ((isHomogeneous_X K 1).C_mul (q ^ 2))

theorem profileFactors_homogeneous (q : K) (s : CubicProfile) (i : Fin 3) :
    (profileFactors q s i).IsHomogeneous (profileFactorDegrees s i) := by
  cases s <;> fin_cases i
  · exact cubicLinearFactors_homogeneous q 0
  · exact cubicLinearFactors_homogeneous q 1
  · exact cubicLinearFactors_homogeneous q 2
  · exact cubicLinearFactors_homogeneous q 0
  · exact isHomogeneous_one (Fin 2) K
  · exact (cubicLinearFactors_homogeneous q 1).mul (cubicLinearFactors_homogeneous q 2)
  · exact isHomogeneous_one (Fin 2) K
  · exact cubicLinearFactors_homogeneous q 1
  · exact (cubicLinearFactors_homogeneous q 0).mul (cubicLinearFactors_homogeneous q 2)

/-- Homogeneous multiplication preserves the signed-degree convention,
including negative source degrees.-/
theorem homogeneous_mul_mem_signedForms {d : ℕ} {t : ℤ} {p q : BinaryRing K}
    (hp : p.IsHomogeneous d) (hq : q ∈ signedForms K 2 t) :
    p * q ∈ signedForms K 2 (t + d) := by
  apply (mem_signedForms_iff_component_self (t + d) (p * q)).mpr
  rw [signedComponent_mul_form t p q hp, signedComponent_self t ⟨q, hq⟩]

/-- A coefficient of the required shifted degree raises the actual weighted
component by `k`.-/
theorem weighted_mul_mem_signedForms {d wsrc wtarget k : ℕ} {t : ℤ}
    {p q : BinaryRing K} (hp : p.IsHomogeneous d)
    (hq : q ∈ signedForms K 2 (t - wsrc))
    (hdegree : (d : ℤ) + wtarget = (k : ℤ) + wsrc) :
    p * q ∈ signedForms K 2 (t + k - wtarget) := by
  have hshift : t - wsrc + d = t + k - wtarget := by omega
  rw [← hshift]
  exact homogeneous_mul_mem_signedForms hp hq

/-- The literal homogeneous binary space has one monomial for each possible
exponent of the first variable.-/
theorem finrank_binaryForms (n : ℕ) : finrank K (Forms K 2 n) = n + 1 := by
  rw [finrank_forms, show 2 + n - 1 = n + 1 by omega,
    ← Nat.choose_symm (by omega : n ≤ n + 1)]
  simp

/-- Signed binary pieces have the positive-part dimension in every degree.-/
theorem finrank_signedBinaryForms (t : ℤ) :
    finrank K (signedForms K 2 t) = (t + 1).toNat := by
  by_cases ht : 0 ≤ t
  · rw [signedForms, ite_eq_left ht, finrank_binaryForms]
    omega
  · rw [signedForms, ite_eq_right ht]
    simp only [finrank_bot]
    omega

/-- Dimension of the actual free binary module with arbitrary generator shifts.-/
theorem finrank_gradedBinaryVector (w : Fin 3 → ℕ) (t : ℤ) :
    finrank K (GradedBinaryVector (K := K) w t) =
      ∑ i, (t - w i + 1).toNat := by
  rw [Module.finrank_pi_fintype]
  simp only [finrank_signedBinaryForms]

/-- The same dimension formula expressed without truncated integer-to-natural
conversion.-/
theorem finrank_gradedBinaryVector_int (w : Fin 3 → ℕ) (t : ℤ) :
    (finrank K (GradedBinaryVector (K := K) w t) : ℤ) =
      ∑ i, max (t - w i + 1) 0 := by
  rw [finrank_gradedBinaryVector, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  omega

/-- The integer profile parameter records the number of generators shifted
from degree zero to degree one.-/
def profileIndex : CubicProfile → ℕ
  | .degreeThree => 0
  | .degreeTwo => 1
  | .degreeOne => 2

/-- The original module has dimension `3t+3-s` in nonnegative degrees.-/
theorem finrank_gradedProfile (s : CubicProfile) (t : ℤ) (ht : 0 ≤ t) :
    (finrank K (GradedBinaryVector (K := K) (generatorWeights s) t) : ℤ) =
      3 * t + 3 - profileIndex s := by
  rw [finrank_gradedBinaryVector_int]
  cases s <;> simp [generatorWeights, profileIndex, Fin.sum_univ_succ] <;> omega

/-- The transposed module has dimension `3t-3+s` in degrees at least one.-/
theorem finrank_gradedProfileDual (s : CubicProfile) (t : ℤ) (ht : 1 ≤ t) :
    (finrank K (GradedBinaryVector (K := K) (dualGeneratorWeights s) t) : ℤ) =
      3 * t - 3 + profileIndex s := by
  rw [finrank_gradedBinaryVector_int]
  cases s <;> simp [dualGeneratorWeights, generatorWeights, profileIndex,
    Fin.sum_univ_succ] <;> omega

theorem finrank_gradedProfile_nat (s : CubicProfile) (t : ℕ) :
    finrank K (GradedBinaryVector (K := K) (generatorWeights s) (t : ℤ)) =
      3 * t + 3 - profileIndex s := by
  have hi : profileIndex s ≤ 2 := by cases s <;> decide
  have h := finrank_gradedProfile (K := K) s (t : ℤ) (by omega)
  omega

theorem finrank_gradedProfileDual_succ (s : CubicProfile) (t : ℕ) :
    finrank K (GradedBinaryVector (K := K) (dualGeneratorWeights s) ((t + 1 : ℕ) : ℤ)) =
      3 * t + profileIndex s := by
  have h := finrank_gradedProfileDual (K := K) s ((t + 1 : ℕ) : ℤ) (by omega)
  omega

end ChoppedPlane.QWeyl
