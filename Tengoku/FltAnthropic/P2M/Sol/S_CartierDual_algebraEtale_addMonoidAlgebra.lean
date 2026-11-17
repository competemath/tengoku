import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDual
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDualInstances

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CartierDual_algebraEtale_addMonoidAlgebra.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CartierDual_algebraEtale_addMonoidAlgebra

set_option autoImplicit false

universe u v

open scoped TensorProduct

namespace MultEtale

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M]

noncomputable def ev : CartierDual R (AddMonoidAlgebra R M) →ₐ[R] (M → R) where
  toFun φ x := φ (AddMonoidAlgebra.single x 1)
  map_one' := by
    ext x
    simp [CartierDual.one_apply]
  map_mul' φ ψ := by
    ext x
    simp only [Pi.mul_apply]
    rw [CartierDual.mul_apply, AddMonoidAlgebra.comul_single]
    simp [TensorProduct.dualDistrib_apply]
  map_zero' := by ext; rfl
  map_add' _ _ := by ext; rfl
  commutes' r := by
    ext x
    simp [CartierDual.algebraMap_apply]

/--
@isnad1 id=eq.0h4v.s10.d5467304dd58 from=translated src=- shape=a5f58bf1 vocab=f104137f
-/
theorem ev_apply (φ : CartierDual R (AddMonoidAlgebra R M)) (x : M) :
    ev R M φ x = φ (AddMonoidAlgebra.single x 1) := rfl

/--
@isnad1 id=bijectiv.0h2v.s9.340524f59c07 from=translated src=- shape=a504c69c vocab=e5c63fff
-/
theorem ev_bijective : Function.Bijective (ev R M) := by
  constructor
  · intro φ ψ h
    have key : CartierDual.toDual R _ φ = CartierDual.toDual R _ ψ := by
      apply AddMonoidAlgebra.lhom_ext'
      intro x
      apply LinearMap.ext_ring
      have hx := congrFun h x
      simp only [ev_apply] at hx
      rw [LinearMap.comp_apply, LinearMap.comp_apply, AddMonoidAlgebra.lsingle_apply]
      exact hx
    exact (CartierDual.toDual R _).injective key
  · intro f
    refine ⟨CartierDual.ofDual R _
      ((Finsupp.linearCombination R f).comp (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap), ?_⟩
    ext x
    rw [ev_apply, CartierDual.ofDual_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      AddMonoidAlgebra.coeffLinearEquiv_apply, AddMonoidAlgebra.coeff_single,
      Finsupp.linearCombination_single, one_smul]

end MultEtale

/--
@isnad1 id=etale.0h2v.s7.96c32d931308 from=translated src=- shape=a920673e vocab=b12ac5eb
-/
theorem solution (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Finite M] :
    Algebra.Etale R (CartierDual R (AddMonoidAlgebra R M)) :=
  Algebra.Etale.of_equiv (AlgEquiv.ofBijective (MultEtale.ev R M) (MultEtale.ev_bijective R M)).symm

-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
