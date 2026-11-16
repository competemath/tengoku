import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_IsIntegral_injective_of_injective_algebraMap.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Algebra_IsIntegral_injective_of_injective_algebraMap

set_option autoImplicit false

theorem solution
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [IsDomain B] [IsDomain C]
    [Algebra A B] [Algebra A C] [Algebra.IsIntegral A B]
    (hinj : Function.Injective (algebraMap A C)) (φ : B →ₐ[A] C) :
    Function.Injective φ := by
  haveI : Nontrivial A := (algebraMap A C).domain_nontrivial
  rw [injective_iff_map_eq_zero]
  intro b hb
  have hker : RingHom.ker φ.toRingHom = ⊥ := by
    haveI : (RingHom.ker φ.toRingHom).IsPrime := RingHom.ker_isPrime _
    refine Ideal.eq_bot_of_comap_eq_bot (R := A) ?_
    refine (Submodule.eq_bot_iff _).mpr fun a ha => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker] at ha
    apply hinj
    rw [map_zero, ← ha]
    exact (φ.commutes a).symm
  have : b ∈ RingHom.ker φ.toRingHom := hb
  rw [hker] at this
  exact this
