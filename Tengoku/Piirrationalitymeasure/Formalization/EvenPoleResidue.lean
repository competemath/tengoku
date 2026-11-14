import Tengoku.Piirrationalitymeasure.Formalization.EvenPolePartialFractions
import Tengoku.Piirrationalitymeasure.Formalization.CoefficientResidue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Mobius residue preservation for the general even rational function. -/

namespace PiIrrationality.EvenPole

open HahnSeries Polynomial

local instance : CharZero (LaurentSeries ℚ) := algebraRat.charZero _
noncomputable local instance : Algebra ℚ (LaurentSeries ℚ) := HahnSeries.powerSeriesAlgebra ℤ ℚ
noncomputable local instance : Algebra ℤ (LaurentSeries ℚ) := Ring.toIntAlgebra _

/--
@isnad1 id=eq.1h2v.s9.ab5b35164a15 from=translated src=- shape=ab7a4d3a vocab=9da0d71c
-/
theorem mobius_residue (F : Polynomial ℤ) {m : ℕ} (hm : 0 < m) :
    laurentResidue (density F m mobiusLaurent * laurentDerivation ℚ mobiusLaurent) =
      laurentCoeff F m 0 := by
  have hp : 5 + mobiusLaurent ≠ 0 := by
    simpa only [add_comm] using mobiusLaurent_add_five_ne_zero
  have hm' : mobiusLaurent - 5 ≠ 0 :=
    sub_ne_zero.mpr (sub_ne_zero.mp five_sub_mobiusLaurent_ne_zero).symm
  rw [partialFractions F hm _ mobiusLaurent_add_five_ne_zero hm',
    add_mul, map_add, laurentResidue_polynomial_mul_derivation, zero_add,
    Finset.sum_mul, map_sum]
  rw [Finset.sum_eq_single (⟨0, hm⟩ : Fin m)]
  · simp only [Fin.val_zero, Nat.cast_zero, zero_add, pow_one, mul_assoc,
      laurentResidue_const_mul, mobiusLaurent_logarithmic_pair]
    simp [laurentResidue]
  · intro j hj hj0
    rw [mul_assoc, laurentResidue_const_mul,
      laurentResidue_polePair_mul_derivation _ _ (by
        have h : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
        omega) hp five_sub_mobiusLaurent_ne_zero, mul_zero]
  · simp

end PiIrrationality.EvenPole
