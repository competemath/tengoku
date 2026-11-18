import Tengoku.Seed.NumberTheory.Height.NumberField
import Tengoku.Seed.FieldTheory.IsAlgClosed.AlgebraicClosure
import Tengoku.FltAnthropic.P2M.Sol.S_Height_inv_finrank_mul_logHeight_inclusion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Height_inv_finrank_mul_logHeight_inclusion.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=eq.1h4v.s11.9e9063e59670 from=translated src=- shape=e57af944 vocab=bd1cfe7e
-/
theorem Height.inv_finrank_mul_logHeight_inclusion
    {K L : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥K] [NumberField ↥L]
    (h : K ≤ L) {ι : Type*} [Finite ι] (x : ι → ↥K) :
    (Module.finrank ℚ ↥L : ℝ)⁻¹ * logHeight (fun i => IntermediateField.inclusion h (x i))
      = (Module.finrank ℚ ↥K : ℝ)⁻¹ * logHeight x := by exact @_root_.P2MW.S_Height_inv_finrank_mul_logHeight_inclusion.solution K L _ _ h ι _ x
