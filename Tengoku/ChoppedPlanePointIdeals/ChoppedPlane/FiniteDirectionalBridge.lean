module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.PolynomialOperatorDuality
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.HomogeneousTensorCoordinates

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-! The finite coefficient differential and the actual cubic tensor
directional derivative agree coefficient by coefficient. -/
noncomputable section
namespace ChoppedPlane
open MvPolynomial
open SymmetricDerivative
variable {K : Type*} [Field K]
variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M] [Module K M]
variable {V W : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- Finite graded coefficients are synthesized as genuine auxiliary
polynomials with coefficients in the cubic module.-/
def finiteDirectionalSynthesis (ν : V →ₗ[K] M) (n : ℕ)
    (c : Sym (Fin 3) n → V) : AuxTensor (R := R) (M := M) :=
  homogeneousTensorSynthesis n (fun s => ν (c s))

@[simp] theorem finiteDirectionalSynthesis_coefficient (ν : V →ₗ[K] M) (n : ℕ)
    (c : Sym (Fin 3) n → V) (s : Sym (Fin 3) n) :
    tensorCoefficients (finiteDirectionalSynthesis (R := R) ν n c)
      (homogeneousTensorExponent n s) = ν (c s) :=
  congrFun (homogeneousTensorCoefficientVector_synthesis n (fun s => ν (c s))) s

theorem finiteDirectionalSynthesis_injective (ν : V →ₗ[K] M)
    (hν : Function.Injective ν) (n : ℕ) :
    Function.Injective (finiteDirectionalSynthesis (R := R) ν n) := by
  intro c d h
  funext s
  apply hν
  simpa using congrArg (fun P => tensorCoefficients P (homogeneousTensorExponent n s)) h

@[simp] theorem finiteDirectionalSynthesis_zero (ν : V →ₗ[K] M) (n : ℕ) :
    finiteDirectionalSynthesis (R := R) ν n 0 = 0 := by
  simp [finiteDirectionalSynthesis, homogeneousTensorSynthesis]

end ChoppedPlane
