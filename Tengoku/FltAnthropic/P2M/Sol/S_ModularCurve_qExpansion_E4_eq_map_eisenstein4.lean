import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0
import Tengoku.Seed.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_qExpansion_E4_eq_map_eisenstein4.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_qExpansion_E4_eq_map_eisenstein4

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Complex Filter Topology
open scoped MatrixGroups PowerSeries.WithPiTopology

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve
export _root_.ModularCurve (eisenstein4)
open _root_.ModularCurve

end ModularCurve

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_qExpansion_E4_eq_map_eisenstein4.ModularCurve in
/--
@isnad1 id=eq.0h0v.s8.73bb88346be2 from=translated src=- shape=f6c39c8f vocab=b86b4137
-/
theorem solution : UpperHalfPlane.qExpansion 1 ⇑ModularForm.E₄ = PowerSeries.map (Int.castRingHom ℂ) ModularCurve.eisenstein4 := by
  ext m
  rw [EisensteinSeries.E_qExpansion_coeff _ ⟨2, rfl⟩ m, PowerSeries.coeff_map, eisenstein4,
    PowerSeries.coeff_mk]
  split_ifs with hm
  · simp
  · rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four,
      ArithmeticFunction.sigma_apply]
    simp only [eq_intCast, Int.cast_mul, Int.cast_ofNat, Int.cast_sum, Int.cast_pow,
      Int.cast_natCast]
    push_cast
    ring
end
