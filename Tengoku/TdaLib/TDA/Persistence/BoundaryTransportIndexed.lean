import Tengoku.TdaLib.TDA.Persistence.FiniteWeightedCoalescing
import Tengoku.TdaLib.TDA.Persistence.BoundaryTransportAtomic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Boundary transport of indexed atomic inputs

The native atomic measure coalesces repeated coordinates. Every indexed finite
matrix and every native finite matrix transfer with the same full powered cost.
The all-Borel value then follows from the native atomic theorem.
-/

set_option autoImplicit false
noncomputable section
namespace TDA.Persistence.BoundaryTransport
open scoped Classical NNReal ENNReal

universe u v
variable {I : Type u} {J : Type v} [Fintype I] [Fintype J]

end TDA.Persistence.BoundaryTransport
