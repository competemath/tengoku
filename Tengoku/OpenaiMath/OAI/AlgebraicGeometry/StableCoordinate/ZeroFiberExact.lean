import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.StableCoordinate.ZeroFiberTransport
import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.StableCoordinate.Presentation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace OAI

/-!
# The exact polynomial has affine-three-space zero fiber

The proved matrix presentation sends its distinguished parameter to the exact
polynomial `f`.  Transporting the explicit zero-fiber coordinate algebra
isomorphism therefore completes the zero case of Proposition 2.3 without
adding any assumptions to its headline statement.
-/

noncomputable section
namespace StableCoordinate

/-- The fiber at zero of the exact degree-five polynomial is affine
three-space, expressed as an isomorphism of complex coordinate algebras. -/
def zeroFiberEquiv : FiberRing 0 ≃ₐ[ℂ] R 3 :=
  ZeroFiber.zeroFiberEquivOfPresentation
    Presentation.originalPresentation Presentation.originalPresentation_p

theorem zeroFiber_isAffineThreeSpace : IsAffineThreeSpaceFiber 0 :=
  ⟨zeroFiberEquiv⟩

end StableCoordinate

end

end OAI
