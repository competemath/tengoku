import Tengoku.Seed.GroupTheory.OrderOfElement
import Tengoku.FltAnthropic.Definitions.Def_SchurMultiplierTrivial
import Tengoku.FltAnthropic.P2M.Sol.S_Ihara_hasTrivialSchurMultiplier_of_dicyclic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Ihara_hasTrivialSchurMultiplier_of_dicyclic.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem Ihara.hasTrivialSchurMultiplier_of_dicyclic
    {G : Type*} [Group G] (x y : G) (m : ℕ)
    (hx : orderOf x = 2 * m) (hy : y ^ 2 = x ^ m) (hconj : y * x * y⁻¹ = x⁻¹)
    (hgen : Subgroup.closure {x, y} = ⊤) :
    Ihara.HasTrivialSchurMultiplier G := by exact @_root_.P2MW.S_Ihara_hasTrivialSchurMultiplier_of_dicyclic.solution G _ x y m hx hy hconj hgen
