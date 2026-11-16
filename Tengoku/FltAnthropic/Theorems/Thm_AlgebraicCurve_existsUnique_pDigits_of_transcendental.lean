import Tengoku.Seed.FieldTheory.IntermediateField.Adjoin.Basic
import Tengoku.Seed.FieldTheory.Perfect
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicCurve_existsUnique_pDigits_of_transcendental

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicCurve_existsUnique_pDigits_of_transcendental.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem AlgebraicCurve.existsUnique_pDigits_of_transcendental {K M : Type*} [Field K] [Field M] [Algebra K M]
    [PerfectField K] (p : ℕ) [hp : Fact p.Prime] [CharP K p] (t : M) (htr : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set M)) M] (htp : ∀ a : M, a ^ p ≠ t) (g : M) :
    ∃! a : Fin p → M, g = ∑ i : Fin p, a i ^ p * t ^ (i : ℕ) := by exact @_root_.P2MW.S_AlgebraicCurve_existsUnique_pDigits_of_transcendental.solution K M _ _ _ _ p hp _ t htr _ htp g
