import Tengoku.FltAnthropic.Definitions.Def_LocalLanglands_HeckeCosetSystem
import Tengoku.FltAnthropic.P2M.Sol.S_HeckeIntegralSeam_heckeCosetSum_eq_of_isHeckeCosetSystem

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HeckeIntegralSeam_heckeCosetSum_eq_of_isHeckeCosetSystem.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=eq.3h8v.s7.2774bf009939 from=translated src=- shape=8708ce77 vocab=46acc293
-/
theorem HeckeIntegralSeam.heckeCosetSum_eq_of_isHeckeCosetSystem
    {G : Type*} [Group G] {n : ℕ} {U : Subgroup G} {gv : G}
    {reps reps' : Fin n → G}
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U gv reps)
    (hsys' : HeckeIntegralSeam.IsHeckeCosetSystem U gv reps')
    {φ : G → ℂ} (hinv : ∀ g : G, ∀ u ∈ U, φ (g * u) = φ g) (g : G) :
    ∑ i, φ (g * reps' i) = ∑ i, φ (g * reps i) := by exact @_root_.P2MW.S_HeckeIntegralSeam_heckeCosetSum_eq_of_isHeckeCosetSystem.solution G _ n U gv reps reps' hsys hsys' φ hinv g
