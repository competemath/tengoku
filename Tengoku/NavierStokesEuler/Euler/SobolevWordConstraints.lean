import Tengoku.NavierStokesEuler.Euler.SobolevWordBlocks
import Tengoku.NavierStokesEuler.Euler.DivergenceFreeHeat

/-! The actual lifted gradient and divergence constraints persist under every available strong derivative word. -/

noncomputable section

namespace EulerSobolevWordConstraints

open EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevWordBlocks EulerDivergenceFreeHeat

variable (period : ℝ) [Fact (0 < period)]

/-- The genuine orthogonal lifted gradient projection acting on the complete Sobolev scale. -/
def sobolevGradientProjection (q : ℕ) (κ : ℝ) (m : Vector3) :
    SobolevSpace period q →L[ℝ] SobolevSpace period q :=
  liftOperator period q (gradientProjection period κ m)
    (fun a f => (gradientProjection_translation period κ m a f).symm)

end EulerSobolevWordConstraints
