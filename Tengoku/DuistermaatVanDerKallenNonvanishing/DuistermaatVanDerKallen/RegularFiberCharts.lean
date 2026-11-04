import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.LaurentGeometry
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.FiberTransport
import Tengoku.Seed.Analysis.Calculus.ImplicitContDiff
import Tengoku.Seed.Topology.Algebra.Module.FiniteDimension
import Tengoku.Seed.LinearAlgebra.Complex.FiniteDimensional

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Analytic local product coordinates at regular Laurent points. The first
coordinate is the original Laurent evaluation; the second lies in the kernel
of its actual real differential. -/

open Set
open scoped Topology

namespace DuistermaatVanDerKallen

noncomputable section

/-- The actual real differential in the original torus coordinates.-/
def laurentRealDifferential {d : ℕ} (f : MultiLaurent d) (z : Fin d → ℂ) :
    (Fin d → ℂ) →L[ℝ] ℂ :=
  (coordinateDifferential (polynomialTorusGradient (laurentRepresentative f) z)).restrictScalars ℝ

/-- One fixed Euclidean model for every regular fiber in rank `d`.-/
abbrev LaurentFiberModel (d : ℕ) := Fin (2 * d - 2) → ℝ

end

end DuistermaatVanDerKallen
