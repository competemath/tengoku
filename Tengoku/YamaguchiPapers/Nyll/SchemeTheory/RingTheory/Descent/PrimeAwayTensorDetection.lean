/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.SchemeTheory.RingTheory.Descent.PrimeAwayPairGluing
import Tengoku.Seed.Algebra.Module.LocalizedModule.Basic
import Tengoku.Seed.Algebra.Module.Torsion.Free
import Tengoku.Seed.RingTheory.Localization.BaseChange
import Tengoku.Seed.RingTheory.Flat.Localization
import Tengoku.Seed.RingTheory.Flat.TorsionFree
import Tengoku.Seed.RingTheory.Localization.Away.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Detecting an isomorphism on two principal opens

A map from a flat module is an isomorphism if it becomes an isomorphism
at two prime-away localizations and the first parameter acts injectively
on the target. The source's flat Hartogs equalizer constructs preimages.
-/

noncomputable section

namespace SchemeTheory

open scoped TensorProduct nonZeroDivisors

universe u v w w'

/-- Localization of a torsion-free module embeds the module into its tensor
extension, with the localization factor written on the right.
@isnad1 id=injectiv.1h4v.s7.76a954fb3f55 from=translated src=- shape=33e5b031 vocab=b10fc6a9
-/
theorem tmul_one_injective_of_isTorsionFree
    {R : Type u} [CommRing R] [IsDomain R]
    (A : Type v) [CommRing A] [Algebra R A]
    (T : Submonoid R) [IsLocalization T A] (hT : T ≤ nonZeroDivisors R)
    (M : Type w) [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M] :
    Function.Injective (fun m : M => m ⊗ₜ[R] (1 : A)) := by
  have hleft : Function.Injective (TensorProduct.mk R A M 1) := by
    apply (IsLocalizedModule.injective_iff_isRegular T _).mpr
    intro t
    exact IsSMulRegular.of_ne_zero (mem_nonZeroDivisors_iff_ne_zero.mp (hT t.2))
  intro m n hmn
  apply hleft
  change (1 : A) ⊗ₜ[R] m = (1 : A) ⊗ₜ[R] n
  have h := congrArg (TensorProduct.comm R M A) hmn
  simpa only [TensorProduct.comm_tmul] using h

section Pair

variable {R : Type u} [CommRing R] [IsDomain R]
variable (F : Type v) [Field F] [Algebra R F] [IsFractionRing R F]
variable {x y : R} (hx : Prime x) (hy : y ≠ 0) (hxy : ¬ x ∣ y)

local notation "Aₓ" => Localization.subalgebra.ofField F (Submonoid.powers x)
  (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hx.ne_zero))
local notation "Aᵧ" => Localization.subalgebra.ofField F (Submonoid.powers y)
  (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hy))

include hxy in
/-- Two principal-localization isomorphisms detect an isomorphism from a
flat source when the first parameter acts regularly on the target.
@isnad1 id=bijectiv.6h7v.s12.a440d53da7ce from=translated src=- shape=ca25170d vocab=dff52a25
-/
theorem linearMap_bijective_of_tensor_primeAwayPair
    {M : Type w} [AddCommGroup M] [Module R M] [Module.Flat R M]
    {N : Type w'} [AddCommGroup N] [Module R N] (hxN : IsSMulRegular N x)
    (f : M →ₗ[R] N)
    (hfx : Function.Bijective (f.rTensor Aₓ))
    (hfy : Function.Bijective (f.rTensor Aᵧ)) : Function.Bijective f := by
  have hiM : Function.Injective (fun m : M => m ⊗ₜ[R] (1 : Aₓ)) :=
    tmul_one_injective_of_isTorsionFree (Aₓ) (Submonoid.powers x)
      (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hx.ne_zero)) M
  have hiN : Function.Injective (fun n : N => n ⊗ₜ[R] (1 : Aₓ)) := by
    have hleft : Function.Injective (TensorProduct.mk R (Aₓ) N 1) := by
      apply (IsLocalizedModule.injective_iff_isRegular (Submonoid.powers x) _).mpr
      rintro ⟨_, n, rfl⟩
      exact IsSMulRegular.pow n hxN
    intro m n hmn
    apply hleft
    change (1 : Aₓ) ⊗ₜ[R] m = (1 : Aₓ) ⊗ₜ[R] n
    have h := congrArg (TensorProduct.comm R N (Aₓ)) hmn
    simpa only [TensorProduct.comm_tmul] using h
  have hfi : Function.Injective f := by
    intro m n hmn
    apply hiM
    apply hfx.1
    simpa only [LinearMap.rTensor_tmul] using congrArg (fun z : N => z ⊗ₜ[R] (1 : Aₓ)) hmn
  refine ⟨hfi, ?_⟩
  intro n
  obtain ⟨a, ha⟩ := hfx.2 (n ⊗ₜ[R] (1 : Aₓ))
  obtain ⟨b, hb⟩ := hfy.2 (n ⊗ₜ[R] (1 : Aᵧ))
  let : Module.Flat R F := IsLocalization.flat F (nonZeroDivisors R)
  have hcomm {T : Type v} [AddCommGroup T] [Module R T]
      (g : T →ₗ[R] F) (z : M ⊗[R] T) :
      (f.rTensor F) ((g.lTensor M) z) = (g.lTensor N) ((f.rTensor T) z) := by
    exact (LinearMap.congr_fun (LinearMap.rTensor_comp_lTensor (M := M) f g) z).trans
      (LinearMap.congr_fun (LinearMap.lTensor_comp_rTensor (M := M) f g) z).symm
  have hab : ((Aₓ).val.toLinearMap.lTensor M) a =
      ((Aᵧ).val.toLinearMap.lTensor M) b := by
    apply Module.Flat.rTensor_preserves_injective_linearMap f hfi
    rw [hcomm, hcomm, ha, hb]
    simp only [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, map_one]
  obtain ⟨m, hm, _⟩ := existsUnique_tensor_primeAwayPair F hx hy hxy M a b hab
  refine ⟨m, hiN ?_⟩
  calc
    f m ⊗ₜ[R] (1 : Aₓ) = (f.rTensor Aₓ) (m ⊗ₜ[R] 1) :=
      (LinearMap.rTensor_tmul (M := Aₓ) f (1 : Aₓ) m).symm
    _ = (f.rTensor Aₓ) a := congrArg (f.rTensor Aₓ) hm.1
    _ = n ⊗ₜ[R] 1 := ha

end Pair

end SchemeTheory
