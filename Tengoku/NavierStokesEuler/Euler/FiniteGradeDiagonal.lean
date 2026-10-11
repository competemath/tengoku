import Tengoku.NavierStokesEuler.Euler.FiniteGradeAlgebra
import Tengoku

/-! The finite residual convolution is exactly the source's sum over i+j=n. -/

noncomputable section

namespace EulerFiniteGrades

open Finset Finset.HasAntidiagonal

variable {V W Q : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W] [AddCommGroup Q] [Module ℝ Q]

end EulerFiniteGrades
