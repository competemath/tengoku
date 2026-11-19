import Tengoku.MagicSquaresFieldsLean.MagicSquares.Weil.LFunction.ReciprocalRoots
import Tengoku.Seed.RingTheory.PowerSeries.Derivative

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares.LN97

open scoped BigOperators

/-- The formal logarithmic derivative, used only when the constant
coefficient is nonzero. It involves no analytic convergence assumptions.-/
noncomputable def formalLogDerivative (P : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.derivative ℂ P * P⁻¹

@[simp]
theorem formalLogDerivative_one : formalLogDerivative 1 = 0 := by
  simp [formalLogDerivative, Derivation.map_one_eq_zero]

noncomputable def reciprocalFactor (a : ℂ) : PowerSeries ℂ :=
  1 - PowerSeries.C a * PowerSeries.X

theorem reciprocalFactor_constantCoeff (a : ℂ) :
    PowerSeries.constantCoeff (reciprocalFactor a) = 1 := by simp [reciprocalFactor]

variable {F : Type*} [Field F] [Fintype F]

/-- The logarithmic-derivative sequence of the actual split L-polynomial.-/
noncomputable def splitLTrace {r : ℕ} (roots : Fin r → F)
    (chars : Fin r → MulChar F ℂ) (s : ℕ) : ℂ :=
  PowerSeries.coeff (s - 1) (formalLogDerivative (splitLPolynomial roots chars : PowerSeries ℂ))

end MagicSquares.LN97
