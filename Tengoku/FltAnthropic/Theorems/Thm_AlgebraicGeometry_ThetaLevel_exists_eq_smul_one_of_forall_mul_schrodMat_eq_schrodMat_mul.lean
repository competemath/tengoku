import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_ThetaLevelGroup
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_ThetaLevel_exists_eq_smul_one_of_forall_mul_schrodMat_eq_schrodMat_mul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_ThetaLevel_exists_eq_smul_one_of_forall_mul_schrodMat_eq_schrodMat_mul.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped BigOperators
open AlgebraicGeometry AlgebraicGeometry.ThetaLevel

theorem AlgebraicGeometry.ThetaLevel.exists_eq_smul_one_of_forall_mul_schrodMat_eq_schrodMat_mul
    {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] (hδd : ∏ i, δ i = d)
    (B : Type) [CommRing B] (ζ ω : B) (hζ : ζ ^ d = 1) (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j))
    (hω : ω ^ 2 = ζ) {n : ℕ} (e : Fin n ≃ HH δ)
    (T : Matrix (Fin n) (Fin n) B) (hT : ∀ z : Heis δ d, T * schrodMat δ d B ω e z = schrodMat δ d B ω e z * T) :
    ∃ c : B, T = c • (1 : Matrix (Fin n) (Fin n) B) := by exact @_root_.P2MW.S_AlgebraicGeometry_ThetaLevel_exists_eq_smul_one_of_forall_mul_schrodMat_eq_schrodMat_mul.solution g δ _ d _ hδd B _ ζ ω hζ hζu hω n e T hT
