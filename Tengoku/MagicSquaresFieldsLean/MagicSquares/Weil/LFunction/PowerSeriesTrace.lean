import Tengoku.MagicSquaresFieldsLean.MagicSquares.Weil.LFunction.ReciprocalRoots
import Tengoku.Seed.RingTheory.PowerSeries.Derivative

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares.LN97

open scoped BigOperators

/-- The formal logarithmic derivative, used only when the constant
coefficient is nonzero. It involves no analytic convergence assumptions.-/
noncomputable def formalLogDerivative (P : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.derivative ℂ P * P⁻¹

/--
@isnad1 id=eq.0h0v.s4.387f86534384 from=translated src=- shape=e467432f vocab=c38bc973
-/
@[simp]
theorem formalLogDerivative_one : formalLogDerivative 1 = 0 := by
  simp [formalLogDerivative, Derivation.map_one_eq_zero]

noncomputable def reciprocalFactor (a : ℂ) : PowerSeries ℂ :=
  1 - PowerSeries.C a * PowerSeries.X

/--
@isnad1 id=eq.0h1v.s5.75813a970ac4 from=translated src=- shape=c4f3e6af vocab=a9255025
-/
theorem reciprocalFactor_constantCoeff (a : ℂ) :
    PowerSeries.constantCoeff (reciprocalFactor a) = 1 := by simp [reciprocalFactor]

variable {F : Type*} [Field F] [Fintype F]

/-- The logarithmic-derivative sequence of the actual split L-polynomial.-/
noncomputable def splitLTrace {r : ℕ} (roots : Fin r → F)
    (chars : Fin r → MulChar F ℂ) (s : ℕ) : ℂ :=
  PowerSeries.coeff (s - 1) (formalLogDerivative (splitLPolynomial roots chars : PowerSeries ℂ))

end MagicSquares.LN97
