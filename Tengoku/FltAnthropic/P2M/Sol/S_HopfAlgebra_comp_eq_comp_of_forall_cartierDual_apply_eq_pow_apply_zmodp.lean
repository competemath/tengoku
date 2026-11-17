import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDual
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDualMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfAlgebra_comp_eq_comp_of_forall_cartierDual_apply_eq_pow_apply_zmodp.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfAlgebra_comp_eq_comp_of_forall_cartierDual_apply_eq_pow_apply_zmodp

set_option autoImplicit false

namespace Ws23
namespace VComm

theorem eq_zero_of_forall_cartierDual_apply_eq_zero (p : ℕ) [Fact p.Prime]
    {C : Type} [CommRing C] [HopfAlgebra (ZMod p) C]
    (c : C) (h : ∀ φ : CartierDual (ZMod p) C, φ c = 0) : c = 0 := by
  exact (Module.forall_dual_apply_eq_zero_iff (ZMod p) c).1 fun f => h (CartierDual.ofDual (ZMod p) C f)

/--
@isnad1 id=eq.2h6v.s12.1f528a743a20 from=translated src=- shape=a41ebbbc vocab=47d52835
-/
theorem main (p : ℕ) [Fact p.Prime]
    {B : Type} [CommRing B] [HopfAlgebra (ZMod p) B] [Coalgebra.IsCocomm (ZMod p) B] [Module.Finite (ZMod p) B]
    {C : Type} [CommRing C] [HopfAlgebra (ZMod p) C] [Coalgebra.IsCocomm (ZMod p) C] [Module.Finite (ZMod p) C]
    (q : B →ₐc[ZMod p] C)
    (VB : B →ₐc[ZMod p] B) (hVB : ∀ (φ : CartierDual (ZMod p) B) (b : B), φ (VB b) = (φ ^ p) b)
    (VC : C →ₐc[ZMod p] C) (hVC : ∀ (φ : CartierDual (ZMod p) C) (c : C), φ (VC c) = (φ ^ p) c) :
    q.comp VB = VC.comp q := by
  apply BialgHom.ext
  intro b
  rw [BialgHom.comp_apply, BialgHom.comp_apply]
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_cartierDual_apply_eq_zero p
  intro φ
  rw [map_sub, sub_eq_zero]
  calc φ (q (VB b)) = CartierDual.map q φ (VB b) := (CartierDual.map_apply q φ (VB b)).symm
    _ = ((CartierDual.map q φ) ^ p) b := hVB _ b
    _ = (CartierDual.map q (φ ^ p)) b := by rw [map_pow]
    _ = (φ ^ p) (q b) := CartierDual.map_apply q (φ ^ p) b
    _ = φ (VC (q b)) := (hVC φ (q b)).symm

end Ws23.VComm

/--
@isnad1 id=eq.2h6v.s12.1f528a743a20 from=translated src=- shape=a41ebbbc vocab=47d52835
-/
theorem solution
    (p : ℕ) [Fact p.Prime]
    {B : Type} [CommRing B] [HopfAlgebra (ZMod p) B] [Coalgebra.IsCocomm (ZMod p) B] [Module.Finite (ZMod p) B]
    {C : Type} [CommRing C] [HopfAlgebra (ZMod p) C] [Coalgebra.IsCocomm (ZMod p) C] [Module.Finite (ZMod p) C]
    (q : B →ₐc[ZMod p] C)
    (VB : B →ₐc[ZMod p] B) (hVB : ∀ (φ : CartierDual (ZMod p) B) (b : B), φ (VB b) = (φ ^ p) b)
    (VC : C →ₐc[ZMod p] C) (hVC : ∀ (φ : CartierDual (ZMod p) C) (c : C), φ (VC c) = (φ ^ p) c) :
    q.comp VB = VC.comp q :=
  Ws23.VComm.main p q VB hVB VC hVC
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
