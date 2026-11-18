import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_LaurentSeries_HeckeU
import Tengoku.FltAnthropic.Definitions.Def_LaurentSeries_HeckeV
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LaurentCoeff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LaurentSeries_commute_heckeU_heckeV.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LaurentSeries_commute_heckeU_heckeV

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

set_option autoImplicit false

open ModularCurve LaurentSeries

/--
@isnad1 id=commute.3h3v.s7.fdc05428d6ec from=translated src=- shape=10d393b7 vocab=7ffc67d6
-/
theorem solution (R : Type*) [CommRing R] (p ℓ : ℕ) (hp : 0 < p) (hℓ : 0 < ℓ)
    (hpl : Nat.Coprime p ℓ) :
    Commute (heckeU R p hp) (heckeV R ℓ hℓ)  := by
  have cop : IsCoprime (ℓ : ℤ) (p : ℤ) := Nat.isCoprime_iff_coprime.mpr hpl.symm
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne'
  ext f n
  simp only [Module.End.mul_apply, coeff_heckeU, coeff_heckeV]
  by_cases h : (ℓ : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    rw [ite_eq_left ⟨p * m, by ring⟩, ite_eq_left ⟨m, rfl⟩, show (p : ℤ) * (ℓ * m) = ℓ * (p * m) by ring,
      Int.mul_ediv_cancel_left _ hℓ0, Int.mul_ediv_cancel_left _ hℓ0]
  · rw [ite_eq_right h, ite_eq_right]
    intro h'
    exact h (cop.dvd_of_dvd_mul_left h')
