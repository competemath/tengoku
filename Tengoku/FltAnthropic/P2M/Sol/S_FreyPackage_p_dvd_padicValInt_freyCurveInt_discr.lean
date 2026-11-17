import Tengoku.Seed.NumberTheory.Padics.PadicVal.Basic
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_FreyPackage
import Tengoku.FltAnthropic.Theorems.Thm_FreyPackage_padicValInt_freyCurveInt_discr

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_FreyPackage_p_dvd_padicValInt_freyCurveInt_discr.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_FreyPackage_p_dvd_padicValInt_freyCurveInt_discr

theorem solution (P : FreyPackage) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) : P.p ∣ padicValInt ℓ P.freyCurveInt.Δ :=
  ⟨2 * padicValInt ℓ (P.a * P.b * P.c), by rw [P.padicValInt_freyCurveInt_discr hℓ hℓ2]; ring⟩
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
