import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDual
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDualMap
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CharacterClosure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CartierDual_dualBaseChangeLin_lTensor_map_eq_map_baseChange_dualBaseChangeLin.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CartierDual_dualBaseChangeLin_lTensor_map_eq_map_baseChange_dualBaseChangeLin

set_option autoImplicit false

open scoped TensorProduct

/--
@isnad1 id=eq.0h5v.s13.1ada21e57aca from=translated src=- shape=7b0b64fa vocab=db8b04d0
-/
theorem solution
    (O : Type) [CommRing O] (F : Type) [CommRing F] [Algebra O F]
    (A : Type) [CommRing A] [Bialgebra O A] [Module.Finite O A] [Module.Free O A]
    (f : A →ₐc[O] A) (w : F ⊗[O] CartierDual O A) :
    CartierDual.dualBaseChangeLin O F A
        (LinearMap.lTensor F ((CartierDual.map f : CartierDual O A →ₐc[O] CartierDual O A) :
          CartierDual O A →ₗ[O] CartierDual O A) w) =
      CartierDual.map (Bialgebra.TensorProduct.map (BialgHom.id F F) f)
        (CartierDual.dualBaseChangeLin O F A w) := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul c φ =>
      rw [LinearMap.lTensor_tmul]
      refine CartierDual.ext fun x => ?_
      rw [CartierDual.map_apply]
      induction x using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero, map_zero]
      | tmul c' a =>
          rw [Bialgebra.TensorProduct.map_tmul, BialgHom.id_apply,
            CartierDual.dualBaseChangeLin_tmul_tmul, CartierDual.dualBaseChangeLin_tmul_tmul]
          rfl
      | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | add x y hx hy => rw [map_add, map_add, hx, hy, ← map_add, ← map_add]
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
