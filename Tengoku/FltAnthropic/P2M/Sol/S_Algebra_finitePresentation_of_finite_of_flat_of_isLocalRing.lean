import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_finitePresentation_of_finite_of_flat_of_isLocalRing.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Algebra_finitePresentation_of_finite_of_flat_of_isLocalRing

set_option autoImplicit false

universe u v

/--
@isnad1 id=finitepr.0h2v.s6.bdff0b6790ad from=translated src=- shape=3c006ed4 vocab=aac53082
-/
theorem solution
    {R : Type u} [CommRing R] [IsLocalRing R] (C : Type v) [CommRing C] [Algebra R C]
    [Module.Finite R C] [Module.Flat R C] :
    Algebra.FinitePresentation R C := by
  haveI : Module.Free R C := Module.free_of_flat_of_isLocalRing
  haveI : Module.FinitePresentation R C := Module.finitePresentation_of_projective R C
  exact Algebra.FinitePresentation.of_finitePresentation R C
