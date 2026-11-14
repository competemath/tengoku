import Tengoku.Twinprime.TwinPrime.Analytic.CharacterConductor
import Tengoku.Twinprime.TwinPrime.Analytic.TotientReciprocal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Maximal progression errors reduced to weighted primitive conductors

The exact conductor regrouping and the elementary reciprocal-totient bound
combine here. The output retains centered errors at conductor one and all
endpoint maxima. The remaining primitive mean-value estimate is not assumed
or proved in this finite reduction.
-/

noncomputable section

open Finset Filter

namespace TwinPrime.Analytic

theorem sum_primitiveCharacter_errors_le_weighted_conductor_sum (T Q : ℕ) :
    (∑ q ∈ Icc 1 Q,
      (∑ χ : DirichletCharacter ℂ q, characterMaxError T χ.primitiveCharacter) /
        Nat.totient q) ≤
      totientReciprocalConstant * (1 + Real.log Q) *
        ∑ r ∈ Icc 1 Q, primitiveCharacterMass T r / Nat.totient r := by
  rw [sum_primitiveCharacter_errors_eq_conductor_sum, mul_sum]
  apply sum_le_sum
  intro r hr
  calc
    _ ≤ primitiveCharacterMass T r *
        (totientReciprocalConstant * (1 + Real.log Q) / Nat.totient r) :=
      mul_le_mul_of_nonneg_left
        (sum_reciprocalTotient_multiples_le_log r Q (by have := (mem_Icc.mp hr).1; omega))
        (primitiveCharacterMass_nonneg T r)
    _ = _ := by ring

/-- A finite conductor reduction with a single logarithmic loss and an
explicit accumulated primitive-replacement error.-/
theorem sum_progressionMaxError_le_weighted_conductor_sum (T Q : ℕ) (hT : 1 ≤ T) :
    (∑ q ∈ Icc 1 Q, progressionMaxError T q) ≤
      totientReciprocalConstant * (1 + Real.log Q) *
        (∑ r ∈ Icc 1 Q, primitiveCharacterMass T r / Nat.totient r) +
          Q * (Real.log Q + 2 * Real.sqrt T * Real.log T) :=
  (sum_progressionMaxError_le_primitiveCharacter_sum T Q hT).trans
    (add_le_add (sum_primitiveCharacter_errors_le_weighted_conductor_sum T Q) le_rfl)

/-- The conductor reduction at the repository's exact BV endpoint and
modulus scale. The threshold and the logarithmic constant are uniform in Q.-/
theorem eventually_sum_progressionMaxError_le_weighted_conductor_sum
    (A : ℝ) (hA : 0 < A) :
    ∀ᶠ X : ℕ in atTop, ∀ Q : ℕ,
      (Q : ℝ) ≤ (X : ℝ) ^ (1 / 2 : ℝ) / (Real.log X) ^ (A + 2) →
      (∑ q ∈ Icc 1 Q, progressionMaxError (2 * X + 2) q) ≤
        totientReciprocalConstant * (1 + Real.log Q) *
          (∑ r ∈ Icc 1 Q, primitiveCharacterMass (2 * X + 2) r / Nat.totient r) +
            (X : ℝ) / (Real.log X) ^ A := by
  filter_upwards [eventually_sum_progressionMaxError_le_primitiveCharacter_sum A hA]
    with X hX Q hQ
  exact (hX Q hQ).trans
    (add_le_add (sum_primitiveCharacter_errors_le_weighted_conductor_sum (2 * X + 2) Q) le_rfl)

end TwinPrime.Analytic
