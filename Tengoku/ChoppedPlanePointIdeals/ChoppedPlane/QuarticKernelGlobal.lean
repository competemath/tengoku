module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.QuarticKernelCoordinates
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.QWeylModule

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-! Global polynomial coefficients for the quartic directional kernel.
The two scalar minors clear coordinates to exactly the auxiliary degree;
relative primality then descends every coordinate in the binary free module. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace ChoppedPlane.QWeyl
open MvPolynomial Module
open ChoppedPlane.SymmetricDerivative
open scoped TensorProduct

variable {B F K : Type*} [CommRing B] [IsDomain B] [UniqueFactorizationMonoid B]
  [Field F] [Algebra B F] [IsFractionRing B F]
  [Field K] [CharZero K] [Algebra K F]

/-- The two chart matrices use the same symmetric kernel basis.-/
theorem quarticKernelSynthesis_charts {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    (u v z a b : R) (n : ℕ) (c : Fin (n + 1) → M) :
    kernelSynthesis (quarticKernelMatrixU u v z a) n c =
      kernelSynthesis (quarticKernelMatrixV u v z b) n c := by
  simp only [kernelSynthesis, quarticKernelMatrixU, quarticKernelMatrixV,
    Matrix.cons_val_one, Matrix.cons_val_two]

/-- The row-zero lift has no influence on the symmetric kernel expression.-/
theorem quarticKernelSynthesis_lift {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    (u v z a b : R) (n : ℕ) (c : Fin (n + 1) → M) :
    kernelSynthesis (quarticKernelMatrixU u v z a) n c =
      kernelSynthesis (quarticKernelMatrixU u v z b) n c := by
  simp only [kernelSynthesis, quarticKernelMatrixU,
    Matrix.cons_val_one, Matrix.cons_val_two]

/-- Both cleared substitutions are integral and commute with coefficient maps.-/
theorem quarticClearU_map {R S : Type*} [CommRing R] [CommRing S]
    (θ : R →+* S) (u v z : R) :
    (fun i => MvPolynomial.map θ (quarticClearU u v z i)) =
      quarticClearU (θ u) (θ v) (θ z) := by
  funext i
  fin_cases i <;> simp [quarticClearU]

theorem quarticClearV_map {R S : Type*} [CommRing R] [CommRing S]
    (θ : R →+* S) (u v z : R) :
    (fun i => MvPolynomial.map θ (quarticClearV u v z i)) =
      quarticClearV (θ u) (θ v) (θ z) := by
  funext i
  fin_cases i <;> simp [quarticClearV]

include K

end ChoppedPlane.QWeyl
