import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_QuaternionAlgebra_Order

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_QuaternionAlgebra_IsOrder_finrank_eq_four.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_QuaternionAlgebra_IsOrder_finrank_eq_four

set_option autoImplicit false

open scoped Quaternion

theorem solution {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : QuaternionAlgebra.IsOrder Λ) : Module.finrank ℤ Λ = 4 := by
  haveI : Submodule.IsLattice ℚ Λ := ⟨hΛ.fg, hΛ.spanTop⟩
  have hr : Module.rank ℤ Λ = Module.rank ℚ ℍ[ℚ, a, b] := Submodule.IsLattice.rank' ℚ Λ
  rw [QuaternionAlgebra.rank_eq_four] at hr
  exact Module.finrank_eq_of_rank_eq hr
