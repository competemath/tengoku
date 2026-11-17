import Tengoku.FltAnthropic.Definitions.Def_FrobeniusDensity_PrimeSums
import Tengoku.Seed.NumberTheory.NumberField.DedekindZeta
import Tengoku.FltAnthropic.P2M.Sol.S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open NumberField
theorem FrobeniusDensity.tendsto_sub_one_mul_idealSum_test
    (K : Type*) [Field K] [NumberField K] :
    Filter.Tendsto (fun s : ℝ => (s - 1) * (FrobeniusDensity.idealSum K s).toReal)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (dedekindZeta_residue K)) := by exact @_root_.P2MW.S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.solution K _ _
