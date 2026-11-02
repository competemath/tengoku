import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tier 1: real-linear conjugation on the complexification `ℂ ⊗[ℝ] V`. -/

open scoped TensorProduct

noncomputable section

namespace HodgePilot

variable (V : Type*) [AddCommGroup V] [Module ℝ V]

/-- Conjugation `σ = conj ⊗ id` on the complexification, as an `ℝ`-linear map.-/
def sigmaR : ℂ ⊗[ℝ] V →ₗ[ℝ] ℂ ⊗[ℝ] V :=
  TensorProduct.map Complex.conjAe.toLinearMap LinearMap.id

@[simp] theorem sigmaR_tmul (c : ℂ) (v : V) :
    sigmaR V (c ⊗ₜ[ℝ] v) = (starRingEnd ℂ) c ⊗ₜ[ℝ] v := by
  simp [sigmaR, TensorProduct.map_tmul, Complex.conjAe_coe]

end HodgePilot
