import Tengoku.OpenaiMath.OAI.Combinatorics.EuclideanRamsey.TensorNecessity

namespace OAI

universe uIndex

noncomputable section

open scoped TensorProduct RealInnerProductSpace

namespace EuclideanRamsey

section Descent
variable (F : IntermediateField ℚ ℝ) {ι : Type uIndex} (b : Module.Basis ι F ℝ)

def tensorCoordinates : (ℝ ⊗[ℚ] ℝ) ≃ₗ[ℚ] (ι × ι →₀ (F ⊗[ℚ] F)) :=
  (TensorProduct.congr (b.repr.restrictScalars ℚ) (b.repr.restrictScalars ℚ)).trans
    (finsuppTensorFinsupp ℚ ℚ F F ι ι)

variable (φ : ℝ →ₗ[F] F)

local instance tensorRing : CommRing (F ⊗[ℚ] F) := inferInstance

def coefficientTrace : (ι × ι →₀ (F ⊗[ℚ] F)) →ₗ[(F ⊗[ℚ] F)] (F ⊗[ℚ] F) :=
  Finsupp.linearCombination (F ⊗[ℚ] F) (fun k => φ (b k.1 * b k.2) ⊗ₜ[ℚ] (1 : F))

def tensorDescent : (ℝ ⊗[ℚ] ℝ) →ₗ[ℚ] (F ⊗[ℚ] F) :=
  ((coefficientTrace F b φ).restrictScalars ℚ).comp (tensorCoordinates F b).toLinearMap

end Descent

end EuclideanRamsey

namespace EuclideanRamsey
open scoped TensorProduct BigOperators

end EuclideanRamsey

end

end OAI
