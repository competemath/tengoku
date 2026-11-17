import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDual

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CartierDual_exists_bialgEquiv_bidual.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CartierDual_exists_bialgEquiv_bidual

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 800000

open scoped TensorProduct

namespace P2mS17B

variable (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Bialgebra R A]
variable [Module.Finite R A] [Module.Free R A] [Coalgebra.IsCocomm R A]

noncomputable def ev : A →ₗ[R] CartierDual R (CartierDual R A) where
  toFun a := CartierDual.ofDual R (CartierDual R A)
    { toFun := fun φ => φ a
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_add' a b := by
    apply CartierDual.ext; intro φ
    show φ (a + b) = φ a + φ b
    exact map_add φ a b
  map_smul' r a := by
    apply CartierDual.ext; intro φ
    show φ (r • a) = r • φ a
    exact map_smul φ r a

/--
@isnad1 id=eq.0h4v.s9.3812f54f654d from=translated src=- shape=fb797a46 vocab=bd9dd5c7
-/
theorem ev_apply (a : A) (φ : CartierDual R A) : ev R A a φ = φ a := rfl

/--
@isnad1 id=bijectiv.0h2v.s9.f45e0d8769c2 from=translated src=- shape=5454286f vocab=811a5c21
-/
theorem ev_bijective : Function.Bijective (ev R A) :=
  (Module.evalEquiv R A).bijective

/--
@isnad1 id=eq.0h5v.s14.4e8de3ddc931 from=translated src=- shape=174b0e9f vocab=0cb1089c
-/
theorem flip₁ (a b : A) (w : CartierDual R A ⊗[R] CartierDual R A) :
    TensorProduct.dualDistrib R (CartierDual R A) (CartierDual R A)
        (CartierDual.toDual R _ (ev R A a) ⊗ₜ[R] CartierDual.toDual R _ (ev R A b)) w =
      TensorProduct.dualDistrib R A A
        (TensorProduct.map (CartierDual.toDual R A).toLinearMap (CartierDual.toDual R A).toLinearMap w) (a ⊗ₜ[R] b) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | tmul φ ψ =>
    rw [TensorProduct.dualDistrib_apply, TensorProduct.map_tmul, TensorProduct.dualDistrib_apply]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, LinearMap.add_apply, hx, hy]

/--
@isnad1 id=eq.0h5v.s14.cada9fa29112 from=translated src=- shape=6076da11 vocab=0cb1089c
-/
theorem flip₂ (φ ψ : CartierDual R A) (z : A ⊗[R] A) :
    TensorProduct.dualDistrib R (CartierDual R A) (CartierDual R A)
        (TensorProduct.map (CartierDual.toDual R (CartierDual R A)).toLinearMap
          (CartierDual.toDual R (CartierDual R A)).toLinearMap (TensorProduct.map (ev R A) (ev R A) z)) (φ ⊗ₜ[R] ψ) =
      TensorProduct.dualDistrib R A A (CartierDual.toDual R A φ ⊗ₜ[R] CartierDual.toDual R A ψ) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

/--
@isnad1 id=eq.0h4v.s10.2469afb99292 from=translated src=- shape=ff71896b vocab=5ada734c
-/
theorem ev_mul (a b : A) : ev R A (a * b) = ev R A a * ev R A b := by
  apply CartierDual.ext; intro φ
  rw [CartierDual.mul_apply, flip₁, CartierDual.comul_pairing]
  rfl

/--
@isnad1 id=eq.0h2v.s9.6550d754de84 from=translated src=- shape=eb25311f vocab=bd9dd5c7
-/
theorem ev_one : ev R A 1 = 1 := by
  apply CartierDual.ext; intro φ
  rw [CartierDual.one_apply, CartierDual.counit_apply]
  rfl

noncomputable def evAlgEquiv : A ≃ₐ[R] CartierDual R (CartierDual R A) :=
  AlgEquiv.ofBijective (AlgHom.ofLinearMap (ev R A) (ev_one R A) (ev_mul R A)) (ev_bijective R A)

/--
@isnad1 id=eq.0h3v.s9.0c342e63e2b7 from=translated src=- shape=43934c42 vocab=7011c5c6
-/
theorem evAlgEquiv_apply (a : A) : evAlgEquiv R A a = ev R A a := rfl

/--
@isnad1 id=eq.0h2v.s9.b38ad20135c1 from=translated src=- shape=50c24ce5 vocab=76b97f4e
-/
theorem counit_comp :
    (Bialgebra.counitAlgHom R (CartierDual R (CartierDual R A))).comp (evAlgEquiv R A : A →ₐ[R] _) =
      Bialgebra.counitAlgHom R A := by
  apply AlgHom.ext; intro a
  rw [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply, AlgEquiv.coe_toAlgHom,
    evAlgEquiv_apply]
  exact (CartierDual.counit_apply (R := R) (A := CartierDual R A) (ev R A a)).trans (CartierDual.one_apply a)

/--
@isnad1 id=eq.0h2v.s12.baecf10d072b from=translated src=- shape=f89e9412 vocab=8d230e19
-/
theorem map_comp_comul :
    (Algebra.TensorProduct.map (evAlgEquiv R A : A →ₐ[R] CartierDual R (CartierDual R A))
        (evAlgEquiv R A : A →ₐ[R] CartierDual R (CartierDual R A))).comp (Bialgebra.comulAlgHom R A) =
      (Bialgebra.comulAlgHom R (CartierDual R (CartierDual R A))).comp (evAlgEquiv R A : A →ₐ[R] _) := by
  apply AlgHom.ext; intro a
  rw [AlgHom.comp_apply, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, Bialgebra.comulAlgHom_apply,
    AlgEquiv.coe_toAlgHom, evAlgEquiv_apply]
  have hmap : ∀ w : A ⊗[R] A,
      (Algebra.TensorProduct.map (evAlgEquiv R A : A →ₐ[R] CartierDual R (CartierDual R A))
        (evAlgEquiv R A : A →ₐ[R] CartierDual R (CartierDual R A))) w =
      TensorProduct.map (ev R A) (ev R A) w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a b => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [hmap]
  apply CartierDual.tmul_eq_of_pairing_eq
  intro φ ψ
  rw [flip₂ R A φ ψ]
  erw [CartierDual.comul_pairing (R := R) (A := CartierDual R A) (ev R A a) φ ψ]
  rw [ev_apply, CartierDual.mul_apply]

end P2mS17B

open P2mS17B in
/--
@isnad1 id=ex.0h2v.s11.76847449545e from=translated src=- shape=1ebbe970 vocab=49a863f3
-/
theorem solution
    (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Bialgebra R A]
    [Module.Finite R A] [Module.Free R A] [Coalgebra.IsCocomm R A] :
    ∃ e : A ≃ₐc[R] CartierDual R (CartierDual R A), ∀ (a : A) (φ : CartierDual R A), e a φ = φ a :=
  ⟨BialgEquiv.ofAlgEquiv (evAlgEquiv R A) (counit_comp R A) (map_comp_comul R A), fun _ _ => rfl⟩
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
