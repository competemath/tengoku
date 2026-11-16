import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_IsAffineOpen_ringKrullDim_stalk_le.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_IsAffineOpen_ringKrullDim_stalk_le

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

/--
@isnad1 id=le.2h3v.s9.6f64ac0d4b40 from=translated src=- shape=919c8513 vocab=4ce24e54
-/
theorem solution
    {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    ringKrullDim (X.presheaf.stalk x) ≤ ringKrullDim Γ(X, U) := by
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  haveI := hU.isLocalization_stalk ⟨x, hx⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf ⟨x, hx⟩).asIdeal (X.presheaf.stalk x)]
  exact Ideal.height_le_ringKrullDim_of_isPrime
