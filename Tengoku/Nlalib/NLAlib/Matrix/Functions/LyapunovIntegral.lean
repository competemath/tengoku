import Tengoku.Nlalib.NLAlib.Matrix.Functions.LyapunovDecay
import Tengoku.Seed.MeasureTheory.Integral.IntegralEqImproper
import Tengoku.Seed.Analysis.SpecialFunctions.ImproperIntegrals
import Tengoku.Seed.Analysis.Calculus.Deriv.Star

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The actual improper continuous Lyapunov Gramian

The Cayley construction supplies a solution, the strict Lyapunov certificate
supplies exponential decay, and improper FTC identifies that solution with
the actual semigroup integral. No decay or integral identity is assumed.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator Topology
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The semigroup Gramian integrand, using the adjoint of the actual exponential.-/
def lyapunovIntegrand (A Q : Matrix n n ℂ) (t : ℝ) : Matrix n n ℂ :=
  matrixExp (t • A) * Q * (matrixExp (t • A))ᴴ

/-- The actual improper Bochner integral over positive time. Changing `Ioi 0`
to `Ici 0` has no effect for Lebesgue measure.-/
def lyapunovGramian (A Q : Matrix n n ℂ) : Matrix n n ℂ :=
  ∫ t in Ioi (0 : ℝ), lyapunovIntegrand A Q t

end NLAlib
