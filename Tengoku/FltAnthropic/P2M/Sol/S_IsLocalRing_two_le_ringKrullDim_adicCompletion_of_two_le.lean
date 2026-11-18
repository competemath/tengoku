import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_IsLocalRing_faithfullyFlat_adicCompletion_maximalIdeal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsLocalRing_two_le_ringKrullDim_adicCompletion_of_two_le.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsLocalRing_two_le_ringKrullDim_adicCompletion_of_two_le
set_option autoImplicit false

theorem solution
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (h : 2 ≤ ringKrullDim R) :
    2 ≤ ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal R) R) := by
  haveI : Module.FaithfullyFlat R (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
    IsLocalRing.faithfullyFlat_adicCompletion_maximalIdeal R
  have h2 : (2 : ℕ) ≤ Order.krullDim (PrimeSpectrum R) := by
    show ((2 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim R
    exact h
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp h2
  obtain ⟨Q, hQ⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat
    (A := R) (B := AdicCompletion (IsLocalRing.maximalIdeal R) R) l.last
  haveI : Q.asIdeal.LiesOver l.last.asIdeal := ⟨by rw [← hQ]; rfl⟩
  obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l Q.asIdeal
  have := Order.le_krullDim_iff.mpr ⟨L, hL.trans hl⟩
  exact this
