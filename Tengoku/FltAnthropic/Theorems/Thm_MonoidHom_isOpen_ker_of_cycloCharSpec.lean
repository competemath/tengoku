import Tengoku.Seed.FieldTheory.KrullTopology
import Tengoku.Seed.FieldTheory.IsAlgClosed.Basic
import Tengoku.FltAnthropic.Definitions.Def_FieldTheory_RatAlgClosureGalois
import Tengoku.FltAnthropic.P2M.Sol.S_MonoidHom_isOpen_ker_of_cycloCharSpec

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MonoidHom_isOpen_ker_of_cycloCharSpec.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=isopen.1h2v.s11.891cafda1448 from=translated src=- shape=5a806d28 vocab=5ca8ad67
-/
theorem MonoidHom.isOpen_ker_of_cycloCharSpec (m : ℕ) [NeZero m]
    (cyc : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod m)ˣ)
    (hcyc : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ),
      μ ^ m = 1 → σ μ = μ ^ ((cyc σ : ZMod m)).val) :
    IsOpen ((cyc.ker : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
      Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) := by exact @_root_.P2MW.S_MonoidHom_isOpen_ker_of_cycloCharSpec.solution m _ cyc hcyc
