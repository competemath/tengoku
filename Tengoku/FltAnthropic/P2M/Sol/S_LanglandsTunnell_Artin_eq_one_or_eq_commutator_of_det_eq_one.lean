import Tengoku.Seed.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Tengoku.Seed.Data.ZMod.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_Artin_eq_one_or_eq_commutator_of_det_eq_one.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_Artin_eq_one_or_eq_commutator_of_det_eq_one

set_option autoImplicit false

theorem solution :
    ∀ g : GL (Fin 2) (ZMod 3), (g : Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1 →
      (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) = 1 ∨
        ∃ x : GL (Fin 2) (ZMod 3), ∃ y : GL (Fin 2) (ZMod 3), g = x * y * x⁻¹ * y⁻¹ := by
  decide +kernel
