module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.PolynomialOperatorDuality
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.HomogeneousTensorCoordinates

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# Actual tensor polynomial differential operators

Three coefficient-module maps act after the corresponding three partial
derivatives on genuine auxiliary polynomial tensors. Homogeneous coefficient
coordinates identify this map with the finite operator differential.
-/

noncomputable section
namespace ChoppedPlane
open Module MvPolynomial SymmetricDerivative
open scoped TensorProduct

variable {K : Type*} [Field K]
variable {V W : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- Apply each coefficient operator after its actual auxiliary derivative.-/
def operatorTensorDifferential (T : Fin 3 → V →ₗ[K] W) :
    AuxTensor (R := K) (M := V) →ₗ[K] AuxTensor (R := K) (M := W) :=
  ∑ i : Fin 3, TensorProduct.map (pderiv i).toLinearMap (T i)

/--
@isnad1 id=eq.0h6v.s10.44734730d424 from=translated src=- shape=1872cbae vocab=9f5c45ea
-/
@[simp] theorem operatorTensorDifferential_tmul
    (T : Fin 3 → V →ₗ[K] W) (f : Aux K) (v : V) :
    operatorTensorDifferential T (f ⊗ₜ[K] v) =
      ∑ i : Fin 3, pderiv i f ⊗ₜ[K] T i v := by
  simp [operatorTensorDifferential]

/-- Differentiating the synthesized monomials gives exactly the finite
coefficient operator, without assuming any freeness of the modules.
@isnad1 id=eq.0h6v.s10.9bcdadc77cc3 from=translated src=- shape=aee9e883 vocab=7cc2a219
-/
theorem operatorTensorDifferential_synthesis_coefficients
    (T : Fin 3 → V →ₗ[K] W) (t : ℕ) (x : Sym (Fin 3) (t + 1) → V) :
    homogeneousTensorCoefficientVector t
        (operatorTensorDifferential T (homogeneousTensorSynthesis (t + 1) x)) =
      operatorDifferential T t x := by
  funext s
  simp only [homogeneousTensorCoefficientVector, homogeneousTensorSynthesis,
    map_sum, operatorTensorDifferential_tmul, Finsupp.finsetSum_apply,
    tensorCoefficients_tmul, operatorDifferential_coeff]

end ChoppedPlane
