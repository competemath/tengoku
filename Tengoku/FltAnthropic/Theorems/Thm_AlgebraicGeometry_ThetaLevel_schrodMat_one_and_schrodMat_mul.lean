import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_ThetaLevelGroup
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_ThetaLevel_schrodMat_one_and_schrodMat_mul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_ThetaLevel_schrodMat_one_and_schrodMat_mul.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped BigOperators
open AlgebraicGeometry AlgebraicGeometry.ThetaLevel

/--
@isnad1 id=and.1h7v.s8.d239377a20c7 from=translated src=- shape=5fff70de vocab=ebd282e7
-/
theorem AlgebraicGeometry.ThetaLevel.schrodMat_one_and_schrodMat_mul
    {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] (B : Type) [CommRing B] (ω : B) (hω : ω ^ (2 * d) = 1)
    {n : ℕ} (e : Fin n ≃ HH δ) :
    schrodMat δ d B ω e 1 = 1 ∧
      ∀ z z' : Heis δ d, schrodMat δ d B ω e (z * z') = schrodMat δ d B ω e z * schrodMat δ d B ω e z' := by exact @_root_.P2MW.S_AlgebraicGeometry_ThetaLevel_schrodMat_one_and_schrodMat_mul.solution g δ _ d _ B _ ω hω n e
