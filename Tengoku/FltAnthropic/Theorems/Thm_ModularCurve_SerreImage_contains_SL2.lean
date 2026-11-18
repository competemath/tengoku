import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_SL2Elementary
import Tengoku.Seed.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Tengoku.Seed.FieldTheory.Finite.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_SerreImage_contains_SL2

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_SerreImage_contains_SL2.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open Matrix MatrixGroups Subgroup
/--
@isnad1 id=le.2h2v.s11.551e523c2bd0 from=translated src=- shape=ee8a08a7 vocab=f7fdcf27
-/
theorem ModularCurve.SerreImage.contains_SL2 {p : ℕ} [Fact p.Prime]
    (H : Subgroup (GL (Fin 2) (ZMod p)))
    (hirr : ∀ v : Fin 2 → ZMod p, v ≠ 0 → ∃ g ∈ H, ∀ c : ZMod p,
      ((g : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)).mulVec v ≠ c • v)
    (hunip : ∃ u ∈ H, ((u : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1) ^ 2 = 0 ∧ u ≠ 1) :
    (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := ZMod p)).range ≤ H := by exact @_root_.P2MW.S_ModularCurve_SerreImage_contains_SL2.solution p _ H hirr hunip
