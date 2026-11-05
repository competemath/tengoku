module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.ProfileCrossing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-! The three actual graded coefficient operators for cubic matrix witnesses. -/
noncomputable section
namespace ChoppedPlane.QWeyl
open MvPolynomial Module
variable {K : Type*} [Field K]

/-- Multiplication by a binary linear form on a genuinely shifted component.-/
def gradedBinaryMultiply (f : Forms K 2 1) (w : Fin 3 → ℕ) (t : ℤ) :
    GradedBinaryVector (K := K) w t →ₗ[K]
      GradedBinaryVector (K := K) w (t+1) where
  toFun m i := ⟨f.val * (m i).val, by
    exact weighted_mul_mem_signedForms f.property (m i).property (by norm_num)⟩
  map_add' m n := by
    ext i
    simp [mul_add]
  map_smul' a m := by
    ext i
    simp

/--
@isnad1 id=eq.0h5v.s12.47b73c46d45a from=translated src=- shape=75141acb vocab=7455e0a0
-/
@[simp] theorem gradedBinaryMultiply_val (f : Forms K 2 1) (w : Fin 3 → ℕ)
    (t : ℤ) (m : GradedBinaryVector (K := K) w t) :
    gradedBinaryVectorVal w (t+1) (gradedBinaryMultiply f w t m) =
      f.val • gradedBinaryVectorVal w t m := rfl

/-- Multiplication by one binary coordinate on the genuine shifted pieces.-/
def gradedBinaryCoordinate (j : Fin 2) (w : Fin 3 → ℕ) (t : ℤ) :
    GradedBinaryVector (K := K) w t →ₗ[K]
      GradedBinaryVector (K := K) w (t+1) :=
  gradedBinaryMultiply ⟨X j, isHomogeneous_X K j⟩ w t

/--
@isnad1 id=eq.0h5v.s12.a709c933d100 from=translated src=- shape=b651b68c vocab=887aa6f6
-/
@[simp] theorem gradedBinaryCoordinate_val (j : Fin 2) (w : Fin 3 → ℕ)
    (t : ℤ) (m : GradedBinaryVector (K := K) w t) :
    gradedBinaryVectorVal w (t+1) (gradedBinaryCoordinate j w t m) =
      (X j : BinaryRing K) • gradedBinaryVectorVal w t m := rfl

/-- A concrete finite basis with exactly the advertised number of rows.-/
def profileSourceBasis (s : CubicProfile) (r : ℕ) :
    Basis (Fin (profileRows s r)) K
      (GradedBinaryVector (K := K) (generatorWeights s) (r : ℤ)) :=
  finBasisOfFinrankEq K _ (finrank_gradedProfile_eq_rows s r)

/-- The next graded component has exactly three additional basis vectors.-/
def profileTargetBasis (s : CubicProfile) (r : ℕ) :
    Basis (Fin (profileRows s r+3)) K
      (GradedBinaryVector (K := K) (generatorWeights s) ((r : ℤ)+1)) :=
  finBasisOfFinrankEq K _ (by
    rw [show (r : ℤ)+1 = ((r+1 : ℕ) : ℤ) by omega,
      finrank_gradedProfile_eq_rows, profileRows_succ])

end ChoppedPlane.QWeyl
