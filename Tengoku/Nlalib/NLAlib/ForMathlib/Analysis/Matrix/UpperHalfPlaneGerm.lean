import Tengoku.Seed.Analysis.CStarAlgebra.Matrix
import Tengoku.Seed.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Tengoku.Seed.Analysis.Calculus.FDeriv.Analytic
import Tengoku.Seed.Analysis.Matrix.Order
import Tengoku.Seed.Tactic.Module
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Positive matrix imaginary parts near a real analytic germ

A positive derivative of an analytic matrix function that is Hermitian
on a real neighborhood makes it preserve the upper half-plane locally.
The same strict derivative estimate bounds its imaginary part by height.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology
namespace Matrix
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ

end Matrix
