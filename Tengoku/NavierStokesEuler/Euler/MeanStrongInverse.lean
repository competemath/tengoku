import Tengoku.NavierStokesEuler.Euler.MeanStrongEquation

/-!
# Strong regularity of the genuinely constructed mean inverse

The result applies the strong-coordinate theorem to the actual coercive solve.
The input boundary inequality still has to be supplied by the concrete cutoff
operator and harmonic localization. No solution, momentum equation, acceleration,
or initial velocity condition is included in the hypotheses.
-/

noncomputable section

namespace EulerMeanVariationalInverse

open Set InnerProductSpace EulerTimeLp EulerTerminalTimePrimitive EulerMeanSolenoidal
  EulerVolterraConvolution

end EulerMeanVariationalInverse
