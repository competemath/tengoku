import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_CompletionBridge
import Tengoku.FltAnthropic.P2M.Sol.S_exists_finiteDimensional_comap_localGaloisToGlobal_iff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_exists_finiteDimensional_comap_localGaloisToGlobal_iff.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false
open scoped IntermediateField
theorem _root_.Tengoku.FltAnthropic.exists_finiteDimensional_comap_localGaloisToGlobal_iff
    (q : ℕ) [Fact q.Prime]
    (P : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) → Prop)
    (hP : ∀ U V, V ≤ U → P U → P V) :
    (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        P (F.fixingSubgroup.comap (localGaloisToGlobal q))) ↔
      ∃ K : IntermediateField ℚ_[q] (PadicAlgCl q), FiniteDimensional ℚ_[q] K ∧
        P K.fixingSubgroup := by exact @_root_.P2MW.S_exists_finiteDimensional_comap_localGaloisToGlobal_iff.solution q _ P hP
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
