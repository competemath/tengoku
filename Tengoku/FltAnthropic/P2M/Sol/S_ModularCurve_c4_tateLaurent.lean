import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_TateFormal
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_c4_tateLaurent.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_c4_tateLaurent

set_option autoImplicit false

open _root_.PowerSeries open _root_.HahnSeries open _root_.ModularCurve

namespace ModularCurve
export _root_.ModularCurve (tateA4 coeff_tateA4 tatePowerSeries tatePowerSeries_a₁ tatePowerSeries_a₂ tatePowerSeries_a₃ tatePowerSeries_a₄ laurentOfInt_apply tateLaurent eisenstein4)
namespace TD1
open _root_.ModularCurve

theorem c₄_tatePowerSeries : tatePowerSeries.c₄ = 1 - 48 * tateA4 := by
  rw [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, tatePowerSeries_a₁, tatePowerSeries_a₂,
    tatePowerSeries_a₃, tatePowerSeries_a₄]
  ring

theorem one_sub_48_tateA4 : (1 - 48 * tateA4 : PowerSeries ℤ) = eisenstein4 := by
  ext n
  have h48 : (48 : PowerSeries ℤ) * tateA4 = (48 : ℕ) • tateA4 := by
    rw [nsmul_eq_mul, Nat.cast_ofNat]
  rw [map_sub, PowerSeries.coeff_one, eisenstein4, PowerSeries.coeff_mk, h48, map_nsmul, coeff_tateA4,
    nsmul_eq_mul, Nat.cast_ofNat]
  split_ifs with h
  · subst h; simp
  · simp only [zero_sub, mul_neg, neg_neg, Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring

theorem main (K : Type*) [CommRing K] :
    (tateLaurent K).c₄ = HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) eisenstein4) := by
  rw [tateLaurent, WeierstrassCurve.map_c₄, c₄_tatePowerSeries, one_sub_48_tateA4, laurentOfInt_apply]

end ModularCurve.TD1

open PowerSeries HahnSeries in
theorem solution (K : Type*) [CommRing K] :
    (tateLaurent K).c₄ = HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) eisenstein4) :=
  ModularCurve.TD1.main K
