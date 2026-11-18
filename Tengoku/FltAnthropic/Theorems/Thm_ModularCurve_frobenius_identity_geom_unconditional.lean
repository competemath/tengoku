import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_JqCoeff
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_frobenius_identity_geom_unconditional

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_frobenius_identity_geom_unconditional.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open ModularCurve
theorem ModularCurve.frobenius_identity_geom_unconditional (K : Type*) [CommRing K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] :
    jqNModC K ℓ = (jqModC K) ^ ℓ := by exact @_root_.P2MW.S_ModularCurve_frobenius_identity_geom_unconditional.solution K _ ℓ _ _
