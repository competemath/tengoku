/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.LinearAlgebra.BilinearForm.HodgeIndex
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.LinearAlgebra.QuadraticForm.OrthogonalityFiniteness
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.CentralCharge.Mukai.Chart

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Spherical-wall finiteness for exponential planes

The Hodge-index certificate, its signature calculation, and nondegeneracy now
live in the neutral linear-algebra module
`LinearAlgebra/BilinearForm/HodgeIndex.lean`.  This downstream wall module uses
that input to form the exponential positive plane and count lattice classes
whose spherical orthogonality walls pass through it.

No geometric surface or ample cone is constructed here.  `D` is an arbitrary
finite-dimensional real space and the lattice is the integer span of a supplied
real basis.
-/

open QuadraticMap Mukai

universe w

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial

noncomputable section

namespace DivisorSpace

variable {D : Type w} [NormedAddCommGroup D] [NormedSpace ℝ D]
variable {S : DivisorSpace D} {H : D}

/-- The positive plane of `exp(B + iω)`, spanned by its real and imaginary
parts.-/
def expPlane (S : DivisorSpace D) (B omega : D) : Submodule ℝ (Mukai.RealExtension D) :=
  PeriodDomain.pairSpan (Mukai.expRe S.intersection B omega)
    (Mukai.expIm S.intersection B omega)

/-- The exponential plane is positive as soon as `ω² > 0`; the `B`-field is
unconstrained.
@isnad1 id=ispositi.1h4v.s7.402ba96506c6 from=translated src=- shape=2a4dac0b vocab=439c526b
-/
theorem isPositivePlane_expPlane (S : DivisorSpace D) (B omega : D)
    (homega : 0 < S.pair omega omega) :
    PeriodDomain.IsPositivePlane (Mukai.realForm S.intersection) (expPlane S B omega) :=
  Mukai.isPositiveFrame_exp S.intersection B omega (fun x y => S.pair_comm x y) homega

variable [FiniteDimensional ℝ D]

/-- For a lattice in the real Mukai extension, only finitely many spherical
classes have a wall through the exponential plane.
@isnad1 id=finite.2h7v.s9.47c604eb1bd5 from=translated src=- shape=7c124eba vocab=5e3c7d2b
-/
theorem finite_walls_through_expPlane (h : S.HodgeDefinite H) (B omega : D)
    (homega : 0 < S.pair omega omega)
    {ι : Type*} [Finite ι] (b : Module.Basis ι ℝ (Mukai.RealExtension D)) :
    {δ : Mukai.RealExtension D |
        PeriodDomain.IsSphericalClass (Mukai.realForm S.intersection) δ ∧
        expPlane S B omega ∈ PeriodDomain.orthogonalityLocus (Mukai.realForm S.intersection) δ ∧
        δ ∈ (Submodule.span ℤ (Set.range b) : Set (Mukai.RealExtension D))}.Finite :=
  PeriodDomain.finite_orthogonalityLoci_through (hasSignatureTwo_of_hodgeDefinite h)
    (isPositivePlane_expPlane S B omega homega) b

/-- The same finiteness, stated as a bounded set of spherical classes
orthogonal to the plane.
@isnad1 id=finite.2h7v.s9.cb2f66b8bf05 from=translated src=- shape=9befa86a vocab=82d028ee
-/
theorem finite_sphericalOrthogonal_expPlane (h : S.HodgeDefinite H) (B omega : D)
    (homega : 0 < S.pair omega omega)
    {ι : Type*} [Finite ι] (b : Module.Basis ι ℝ (Mukai.RealExtension D)) :
    (PeriodDomain.sphericalOrthogonal (Mukai.realForm S.intersection) (expPlane S B omega)
      ∩ (Submodule.span ℤ (Set.range b) : Set (Mukai.RealExtension D))).Finite :=
  PeriodDomain.finite_sphericalOrthogonal_inter (hasSignatureTwo_of_hodgeDefinite h)
    (isPositivePlane_expPlane S B omega homega) b

end DivisorSpace

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial
