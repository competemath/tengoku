import Tengoku.Seed.RingTheory.PowerSeries.Ideal
import Tengoku.Seed.RingTheory.MvPowerSeries.Rename
import Tengoku.Seed.Data.Finsupp.Option

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvPowerSeries_isNoetherianRing_of_finite.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvPowerSeries_isNoetherianRing_of_finite

universe u v w

noncomputable section

namespace M4cP1PS

open Finsupp Finset

section Equiv

variable {σ : Type*} {R : Type*} [CommSemiring R]

def optFun (φ : MvPowerSeries (Option σ) R) : PowerSeries (MvPowerSeries σ R) :=
  PowerSeries.mk fun n => fun d => MvPowerSeries.coeff (d.optionElim n) φ

def optInv (ψ : PowerSeries (MvPowerSeries σ R)) : MvPowerSeries (Option σ) R :=
  fun m => MvPowerSeries.coeff m.some (PowerSeries.coeff (m none) ψ)

end Equiv

section Noetherian

variable (R : Type*) [CommRing R] [IsNoetherianRing R]

end Noetherian

end M4cP1PS
open scoped _root_.P2MW.S_MvPowerSeries_isNoetherianRing_of_finite.M4cP1PS

end
open scoped _root_.P2MW.S_MvPowerSeries_isNoetherianRing_of_finite.M4cP1PS
