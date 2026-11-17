import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDual
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDualMap
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDualInstances
import Tengoku.FltAnthropic.Theorems.Thm_Algebra_Etale_algHom_ext_of_forall_sub_mem_map_maximalIdeal_of_henselianLocalRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfAlgebra_apply_ofDual_eq_one_of_eq_comp_of_forall_sub_apply_one_mem_maximalIdeal_of_henselianLocalRing.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfAlgebra_apply_ofDual_eq_one_of_eq_comp_of_forall_sub_apply_one_mem_maximalIdeal_of_henselianLocalRing

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem solution
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (A : Type v) [CommRing A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A]
    [Module.Finite R A] [Module.Free R A]

    (M : Type v) [CommRing M] [HopfAlgebra R M] [Coalgebra.IsCocomm R M] [Module.Free R M] [Module.Finite R M]
    (π : A →ₐc[R] M) (hMet : Algebra.Etale R (CartierDual R M))

    (f : A →ₐ[R] R) (g : M →ₐ[R] R) (hf : f = g.comp (π : A →ₐ[R] M))
    (ψ : CartierDual R A →ₐ[R] R)
    (hψ : ∀ lam : CartierDual R A, ψ lam - lam 1 ∈ IsLocalRing.maximalIdeal R) :
    ψ ((CartierDual.ofDual R A) f.toLinearMap) = 1 := by

  set ghat : CartierDual R M := CartierDual.ofDual R M g.toLinearMap with hghat
  have hfhat : CartierDual.ofDual R A f.toLinearMap = CartierDual.map π ghat := by
    refine CartierDual.ext fun a => ?_
    rw [CartierDual.ofDual_apply, CartierDual.map_apply, hghat, CartierDual.ofDual_apply, hf]
    rfl

  set χ : CartierDual R M →ₐ[R] R := ψ.comp (CartierDual.map π : CartierDual R M →ₐ[R] CartierDual R A) with hχ
  haveI : Algebra.Etale R (CartierDual R M) := hMet
  have hχε : χ = Bialgebra.counitAlgHom R (CartierDual R M) := by
    refine Algebra.Etale.algHom_ext_of_forall_sub_mem_map_maximalIdeal_of_henselianLocalRing R
      (CartierDual R M) R χ (Bialgebra.counitAlgHom R (CartierDual R M)) fun μ => ?_
    rw [show Ideal.map (algebraMap R R) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R from
      Ideal.map_id _, hχ, AlgHom.comp_apply, Bialgebra.counitAlgHom_apply]
    erw [CartierDual.counit_apply]
    have h1 : (CartierDual.map π μ) 1 = μ 1 := by
      show μ (π 1) = μ 1
      rw [map_one]
    have h2 := hψ (CartierDual.map π μ)
    rw [h1] at h2
    change ψ (CartierDual.map π μ) - μ 1 ∈ IsLocalRing.maximalIdeal R
    exact h2

  have hχg : χ ghat = 1 := by
    rw [hχε, Bialgebra.counitAlgHom_apply]
    erw [CartierDual.counit_apply]
    rw [hghat, CartierDual.ofDual_apply]
    exact map_one g
  rw [hfhat]
  exact hχg
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
