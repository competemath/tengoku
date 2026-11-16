import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_IsAffineOpen_isRegularLocalRing_stalk_of_isRegularRing.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_IsAffineOpen_isRegularLocalRing_stalk_of_isRegularRing

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

/--
@isnad1 id=isregula.3h3v.s8.bb67b81929fe from=translated src=- shape=16e731d8 vocab=13f0f401
-/
theorem solution
    {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (hreg : IsRegularRing Γ(X, U))
    (x : X) (hx : x ∈ U) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  haveI := hU.isLocalization_stalk ⟨x, hx⟩
  haveI := hreg
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
      (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal) (X.presheaf.stalk x)).toRingEquiv
