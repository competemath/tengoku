import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfAlgebra_bijective_of_faithfullyFlat_baseChange_bijective.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfAlgebra_bijective_of_faithfullyFlat_baseChange_bijective

set_option autoImplicit false

universe u v

/--
@isnad1 id=bijectiv.1h5v.s11.dd7e85a3ba91 from=translated src=- shape=5510b199 vocab=2879efff
-/
theorem solution
    {R : Type u} [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R'] [Module.FaithfullyFlat R R']
    {H : Type v} [CommRing H] [HopfAlgebra R H]
    {H' : Type v} [CommRing H'] [HopfAlgebra R H']
    (φ : H →ₐc[R] H') (hφ : Function.Bijective ((φ : H →ₐ[R] H').toLinearMap.baseChange R')) :
    Function.Bijective φ := by
  have h : Function.Bijective ((φ : H →ₐ[R] H').toLinearMap.lTensor R') := by
    rwa [← LinearMap.baseChange_eq_ltensor]
  exact (Module.FaithfullyFlat.lTensor_bijective_iff_bijective R R' _).mp h
