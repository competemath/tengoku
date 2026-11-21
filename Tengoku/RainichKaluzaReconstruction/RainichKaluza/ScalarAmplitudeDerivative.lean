import Tengoku.RainichKaluzaReconstruction.RainichKaluza.LorentzianScalarBlock
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.Module
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Differential reconstruction of scalar amplitudes

On the generic complementary spectral plane, the squared scalar components
are fixed by the curvature-derived diagonal functions.  This file computes
their directional derivatives from derivatives of the spectral roots and of
`q²`.  As in `SpectralProjectorDerivative`, derivative symbols are evaluated
algebraic data; manifold and covariant-derivative instantiation remains a
separate geometric step.
-/

namespace RainichKaluza

/-- Directional derivative of `q²=-e₃/e₁` on the nonzero-trace branch.-/
noncomputable def reconstructedQSqDerivative
    (e1 e3 de1 de3 : ℝ) : ℝ :=
  -((de3 * e1 - e3 * de1) / e1 ^ 2)

/-- The reconstructed derivative is exactly the differentiated form of
`e₁q²=-e₃`.-/
theorem reconstructedQSqDerivative_relation
    (e1 e3 de1 de3 : ℝ) (he1 : e1 ≠ 0) :
    de1 * (-e3 / e1) + e1 * reconstructedQSqDerivative e1 e3 de1 de3 =
      -de3 := by
  unfold reconstructedQSqDerivative
  field_simp [he1]
  ring

/-- Directional derivative of the forced `a`-eigendirection diagonal.-/
noncomputable def reconstructedDiagonalADerivative
    (a b qSq da db dqSq : ℝ) : ℝ :=
  ((2 * a * da - dqSq) * (a - b) -
    (a ^ 2 - qSq) * (da - db)) / (a - b) ^ 2

/-- Directional derivative of the forced `b`-eigendirection diagonal.-/
noncomputable def reconstructedDiagonalBDerivative
    (a b qSq da db dqSq : ℝ) : ℝ :=
  ((2 * b * db - dqSq) * (b - a) -
    (b ^ 2 - qSq) * (db - da)) / (b - a) ^ 2

/-- The `a` formula satisfies the differentiated Sylvester diagonal
identity.-/
theorem reconstructedDiagonalADerivative_relation
    (a b qSq da db dqSq : ℝ) (hab : a ≠ b) :
    (da - db) * reconstructedDiagonalA a b qSq +
      (a - b) * reconstructedDiagonalADerivative a b qSq da db dqSq =
        2 * a * da - dqSq := by
  unfold reconstructedDiagonalA reconstructedDiagonalADerivative
  field_simp [sub_ne_zero.mpr hab]
  ring

/-- The `b` formula satisfies the differentiated Sylvester diagonal
identity.-/
theorem reconstructedDiagonalBDerivative_relation
    (a b qSq da db dqSq : ℝ) (hab : a ≠ b) :
    (db - da) * reconstructedDiagonalB a b qSq +
      (b - a) * reconstructedDiagonalBDerivative a b qSq da db dqSq =
        2 * b * db - dqSq := by
  unfold reconstructedDiagonalB reconstructedDiagonalBDerivative
  field_simp [sub_ne_zero.mpr hab, sub_ne_zero.mpr hab.symm]
  ring

/-- Directional derivative of a nonzero scalar component reconstructed from
`u=εx²/2`, using `ε⁻¹=ε` for a signature sign.-/
noncomputable def scalarAmplitudeDerivative
    (epsilon x du : ℝ) : ℝ :=
  epsilon * du / x

/-- The amplitude formula solves the differentiated diagonal relation
`du=εx dx`.-/
theorem scalarAmplitudeDerivative_relation
    (epsilon x du : ℝ) (hepsilon : epsilon ^ 2 = 1) (hx : x ≠ 0) :
    epsilon * x * scalarAmplitudeDerivative epsilon x du = du := by
  unfold scalarAmplitudeDerivative
  calc
    epsilon * x * (epsilon * du / x) = epsilon ^ 2 * du := by
      field_simp [hx]
    _ = du := by rw [hepsilon]; simp

/-- The complete curvature-root formula for the derivative of the first
nonzero scalar amplitude.-/
noncomputable def reconstructedAmplitudeADerivative
    (epsilonA x a b qSq da db dqSq : ℝ) : ℝ :=
  scalarAmplitudeDerivative epsilonA x
    (reconstructedDiagonalADerivative a b qSq da db dqSq)

/-- The complete curvature-root formula for the derivative of the second
nonzero scalar amplitude.-/
noncomputable def reconstructedAmplitudeBDerivative
    (epsilonB y a b qSq da db dqSq : ℝ) : ℝ :=
  scalarAmplitudeDerivative epsilonB y
    (reconstructedDiagonalBDerivative a b qSq da db dqSq)

/-- The reconstructed first-amplitude derivative differentiates its forced
diagonal value.-/
theorem reconstructedAmplitudeADerivative_relation
    (epsilonA x a b qSq da db dqSq : ℝ)
    (hepsilonA : epsilonA ^ 2 = 1) (hx : x ≠ 0) :
    epsilonA * x *
      reconstructedAmplitudeADerivative epsilonA x a b qSq da db dqSq =
        reconstructedDiagonalADerivative a b qSq da db dqSq := by
  exact scalarAmplitudeDerivative_relation epsilonA x
    (reconstructedDiagonalADerivative a b qSq da db dqSq) hepsilonA hx

/-- The reconstructed second-amplitude derivative differentiates its forced
diagonal value.-/
theorem reconstructedAmplitudeBDerivative_relation
    (epsilonB y a b qSq da db dqSq : ℝ)
    (hepsilonB : epsilonB ^ 2 = 1) (hy : y ≠ 0) :
    epsilonB * y *
      reconstructedAmplitudeBDerivative epsilonB y a b qSq da db dqSq =
        reconstructedDiagonalBDerivative a b qSq da db dqSq := by
  exact scalarAmplitudeDerivative_relation epsilonB y
    (reconstructedDiagonalBDerivative a b qSq da db dqSq) hepsilonB hy

end RainichKaluza
