import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CuspForm_ModPForms
import Tengoku.FltAnthropic.Definitions.Def_PowerSeries_FormalHeckeOperators

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModPForms_heckeT_apply_eq_heckePS.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModPForms_heckeT_apply_eq_heckePS

set_option autoImplicit false

/--
@isnad1 id=eq.1h4v.s8.3d934e2fa19d from=translated src=- shape=cbf96b62 vocab=8cf35334
-/
theorem solution (F : Type) [Field F] (k : ℕ) (hk : 1 ≤ k) (ℓ : ℕ) (φ : PowerSeries F) :
    PowerSeries.heckeT ℓ k φ = ModPForms.heckePS (k : ℤ) ℓ φ := by
  ext n
  unfold ModPForms.heckePS
  rw [PowerSeries.coeff_heckeT, PowerSeries.coeff_mk, mul_comm ℓ n, mul_ite, mul_zero,
    show ((k : ℤ) - 1) = ((k - 1 : ℕ) : ℤ) by omega, zpow_natCast]
