import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Mathlib_RightActionInstances

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_TensorProduct_bijective_productMap_pi_comp_of_isGalois.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Algebra_TensorProduct_bijective_productMap_pi_comp_of_isGalois

set_option autoImplicit false

open scoped TensorProduct

noncomputable section

namespace Split

open scoped TensorProduct.RightActions

variable (K L F : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [Field F] [Algebra K F] (σ₀ : L →ₐ[K] F)

theorem injective_comp : Function.Injective (fun τ : L ≃ₐ[K] L => σ₀.comp (τ : L →ₐ[K] L)) := by
  intro τ τ' h
  apply AlgEquiv.ext
  intro x
  have hx := congrArg (fun φ : L →ₐ[K] F => φ x) h
  exact σ₀.toRingHom.injective hx

end Split

end
