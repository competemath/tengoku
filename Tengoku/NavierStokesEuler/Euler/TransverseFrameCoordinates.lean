import Tengoku.NavierStokesEuler.Euler.TransverseVariationalOperator

/-!
# Recovering the source's transverse coordinates

The moving plane with normal `(F⁻¹)* m₀` is exactly the image under `F` of
the fixed plane `m₀⊥`.  Orthogonal projection gives a bounded coordinate map,
and on the moving plane its reconstruction is the identity.  These are
coefficient identities, not assumptions about a differential inverse.
-/

noncomputable section

namespace EulerTransverseFrameCoordinates

open InnerProductSpace ContinuousLinearMap

variable {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- The fixed reference transverse plane. -/
abbrev referencePlane (m₀ : E) : Submodule ℝ E := (ℝ ∙ m₀)ᗮ

/-- The actual pulled-back normal used by the packet construction. -/
def movingNormal (F : E ≃L[ℝ] E) (m₀ : E) : E := F.symm.toContinuousLinearMap.adjoint m₀

/-- Bounded recovery of fixed-plane coordinates from a physical displacement. -/
def coordinates (F : E ≃L[ℝ] E) (m₀ : E) : E →L[ℝ] referencePlane m₀ :=
  (referencePlane m₀).orthogonalProjectionOnto.comp F.symm.toContinuousLinearMap

/-- Any orthonormal identification with the fixed plane gives the source's `R⊥` coordinates. -/
def frameCoordinates (F : E ≃L[ℝ] E) (m₀ : E)
    (R : U ≃ₗᵢ[ℝ] referencePlane m₀) : E →L[ℝ] U :=
  R.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (coordinates F m₀)

section Paths

variable {X : Type*} [TopologicalSpace X]

/-- Applying a continuous inverse-frame path produces actual continuous
transverse coordinates, not separate incompatible pointwise choices. -/
def coordinatePath (m₀ : E) (R : U ≃ₗᵢ[ℝ] referencePlane m₀)
    (A : C(X, E →L[ℝ] E)) (η : C(X, E)) : C(X, U) :=
  ⟨fun t => R.symm ((referencePlane m₀).orthogonalProjectionOnto (A t (η t))),
    R.symm.continuous.comp ((referencePlane m₀).orthogonalProjectionOnto.continuous.comp
      (A.continuous.clm_apply η.continuous))⟩

end Paths

end EulerTransverseFrameCoordinates
