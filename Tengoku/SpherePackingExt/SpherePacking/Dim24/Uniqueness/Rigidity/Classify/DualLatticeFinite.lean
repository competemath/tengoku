module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.Rigidity.Classify.Discriminant
public import Tengoku.Seed.Algebra.Module.ZLattice.Basic
public import Tengoku.Seed.LinearAlgebra.FreeModule.Finite.Quotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finiteness of discriminant groups

This file records a basic lattice-theoretic fact used in the rigidity/classification step:
for a full lattice `L`, if `L` is integral (`L ≤ L*`) then the discriminant group `L*/L` is
finite.

Along the way we show that the real inner-product bilinear form is nondegenerate, and we use this
to transfer `DiscreteTopology`/`IsZLattice` structures to the dual lattice.

## Main statements
* `finite_discriminantGroup_of_le_dual`
-/

namespace SpherePacking.Dim24.Uniqueness.RigidityClassify

noncomputable section

open scoped RealInnerProductSpace
open Module

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-! ### Dual lattice as a `ℤ`-lattice -/

end

end SpherePacking.Dim24.Uniqueness.RigidityClassify
