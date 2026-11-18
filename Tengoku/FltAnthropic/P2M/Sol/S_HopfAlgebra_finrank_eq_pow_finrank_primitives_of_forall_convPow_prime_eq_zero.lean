import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDual
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDualInstances
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_DatumAndHonda
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_ModpRealization
import Tengoku.FltAnthropic.Theorems.Thm_HopfAlgebra_finrank_eq_pow_finrank_cotangent_of_forall_pow_prime_eq_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfAlgebra_finrank_eq_pow_finrank_primitives_of_forall_convPow_prime_eq_zero.lean`: wrote out 5 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 1 `p2m_open`, 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfAlgebra_finrank_eq_pow_finrank_primitives_of_forall_convPow_prime_eq_zero

set_option autoImplicit false

open scoped TensorProduct

noncomputable section

universe u v

namespace HopfAlgebra
export _root_.HopfAlgebra (mk finrank_eq_pow_finrank_cotangent_of_forall_pow_prime_eq_zero)
namespace PrimitivesDual
open _root_.HopfAlgebra

variable {k : Type u} [Field k] {A : Type v} [CommRing A] [Bialgebra k A]
variable [Module.Finite k A] [Coalgebra.IsCocomm k A]

local notation "D" => CartierDual k A

abbrev augIdeal (k : Type u) [Field k] (A : Type v) [CommRing A] [Bialgebra k A]
    [Module.Finite k A] [Coalgebra.IsCocomm k A] : Ideal (CartierDual k A) :=
  RingHom.ker (Bialgebra.counitAlgHom k (CartierDual k A))

local notation "J" => augIdeal k A

/--
@isnad1 id=iff.0h3v.s8.3bbd6371b7b4 from=translated src=- shape=c7ce4690 vocab=d7d052bd
-/
theorem mem_augIdeal_iff (φ : D) : φ ∈ J ↔ φ 1 = 0 := by
  rw [RingHom.mem_ker, Bialgebra.counitAlgHom_apply]
  show CartierDual.dualCounit k A (CartierDual.toDual k A φ) = 0 ↔ _
  rw [CartierDual.dualCounit_apply]
  rfl

def IsPrim (k : Type u) [Field k] {A : Type v} [CommRing A] [Bialgebra k A] (x : A) : Prop :=
  Coalgebra.comul (R := k) x = x ⊗ₜ[k] 1 + 1 ⊗ₜ[k] x

def prim (k : Type u) [Field k] (A : Type v) [CommRing A] [Bialgebra k A] : Submodule k A :=
  LinearMap.ker (Coalgebra.comul (R := k) (A := A)
    - (TensorProduct.mk k A A).flip 1 - TensorProduct.mk k A A 1)

omit [Module.Finite k A] [Coalgebra.IsCocomm k A] in
/--
@isnad1 id=iff.0h3v.s7.371dc08f4285 from=translated src=- shape=c70f9343 vocab=15dd305c
-/
theorem mem_prim_iff (x : A) : x ∈ prim k A ↔ IsPrim k x := by
  unfold prim IsPrim
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.sub_apply, sub_sub, sub_eq_zero]
  rfl

omit [Module.Finite k A] in

/--
@isnad1 id=eq.1h5v.s8.f16dab0bcb61 from=translated src=- shape=dd781e3a vocab=ee6e13be
-/
theorem mul_apply_of_isPrim {x : A} (hx : IsPrim k x) (φ ψ : D) :
    (φ * ψ) x = φ x * ψ 1 + φ 1 * ψ x := by
  rw [CartierDual.mul_apply, hx, map_add, TensorProduct.dualDistrib_apply,
    TensorProduct.dualDistrib_apply]
  rfl

omit [Module.Finite k A] in
/--
@isnad1 id=eq.0h4v.s8.fd32703f33a7 from=translated src=- shape=949096ce vocab=92dd2362
-/
theorem mul_apply_one (φ ψ : D) : (φ * ψ) 1 = φ 1 * ψ 1 := by
  rw [CartierDual.mul_apply, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
    TensorProduct.dualDistrib_apply]
  rfl

omit [Module.Finite k A] [Coalgebra.IsCocomm k A] in

/--
@isnad1 id=eq.1h3v.s8.989560e2f7b7 from=translated src=- shape=c0efe4b1 vocab=7a573668
-/
theorem counit_eq_zero_of_isPrim {x : A} (hx : IsPrim k x) : Coalgebra.counit (R := k) x = 0 := by
  have h := Coalgebra.rTensor_counit_comul (R := k) x
  rw [hx, map_add, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, Bialgebra.counit_one,
    add_eq_right] at h
  have h2 := congrArg (fun z => Coalgebra.counit (R := k) (TensorProduct.lid k A z)) h
  simp only [TensorProduct.lid_tmul, map_zero, map_smul, Bialgebra.counit_one, smul_eq_mul,
    mul_one] at h2
  exact h2

omit [Module.Finite k A] [Coalgebra.IsCocomm k A] in

/--
@isnad1 id=eq.1h4v.s8.d339e74a6c5e from=translated src=- shape=d65d4b89 vocab=12e6eb0a
-/
theorem apply_eq_sub_apply_of_isPrim {x : A} (hx : IsPrim k x) (φ : D) :
    φ x = (φ - φ 1 • (1 : D)) x := by
  show φ x = φ x - φ 1 • (1 : D) x
  rw [CartierDual.one_apply, counit_eq_zero_of_isPrim hx, smul_zero, sub_zero]

omit [Module.Finite k A] [Coalgebra.IsCocomm k A] in
/--
@isnad1 id=eq.0h3v.s8.a0d5f869556f from=translated src=- shape=10e246b0 vocab=30fb9591
-/
theorem sub_smul_one_apply_one (φ : D) : (φ - φ 1 • (1 : D)) 1 = 0 := by
  show φ 1 - φ 1 • (1 : D) 1 = 0
  rw [CartierDual.one_apply, Bialgebra.counit_one, smul_eq_mul, mul_one, sub_self]

def evJ (x : A) : ↥J →ₗ[k] k where
  toFun φ := (φ : D) x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
@isnad1 id=eq.0h4v.s11.16f80fe34d67 from=translated src=- shape=286cd06f vocab=4d6e6c76
-/
@[scoped simp] theorem evJ_apply (x : A) (φ : ↥J) : evJ x φ = (φ : D) x := rfl

/--
@isnad1 id=eq.1h5v.s12.fd1477ee7266 from=translated src=- shape=c5f1a235 vocab=c2a72524
-/
theorem evJ_mul {x : A} (hx : IsPrim k x) (φ ψ : ↥J) : evJ x (φ * ψ) = 0 := by
  rw [evJ_apply, MulMemClass.coe_mul, mul_apply_of_isPrim hx,
    (mem_augIdeal_iff _).1 φ.2, (mem_augIdeal_iff _).1 ψ.2, mul_zero, zero_mul, add_zero]

noncomputable def θ₀ {x : A} (hx : IsPrim k x) : (augIdeal k A).Cotangent →ₗ[k] k :=
  Ideal.Cotangent.lift (evJ x) (evJ_mul hx)

noncomputable def θ : ↥(prim k A) →ₗ[k] Module.Dual k (augIdeal k A).Cotangent where
  toFun x := θ₀ ((mem_prim_iff _).1 x.2)
  map_add' x y := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨φ, rfl⟩ := (augIdeal k A).toCotangent_surjective v
    show (φ : D) ((x : A) + y) = (φ : D) (x : A) + (φ : D) (y : A)
    exact map_add _ _ _
  map_smul' c x := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨φ, rfl⟩ := (augIdeal k A).toCotangent_surjective v
    show (φ : D) (c • (x : A)) = c • (φ : D) (x : A)
    exact map_smul _ _ _

/--
@isnad1 id=eq.0h4v.s12.5ee3dd020e3c from=translated src=- shape=a7d077de vocab=c50b7729
-/
theorem θ_apply_toCotangent (x : ↥(prim k A)) (φ : ↥J) :
    θ x ((augIdeal k A).toCotangent φ) = (φ : D) (x : A) := rfl

/--
@isnad1 id=injectiv.0h2v.s11.efe1f9cc1103 from=translated src=- shape=bcafd8fc vocab=a7b4843d
-/
theorem θ_injective : Function.Injective (θ (k := k) (A := A)) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  have hprim : IsPrim k (x : A) := (mem_prim_iff _).1 x.2
  refine Subtype.ext ((Module.forall_dual_apply_eq_zero_iff k (x : A)).1 fun f => ?_)

  let φ : D := CartierDual.ofDual k A f
  have hφ' : φ - φ 1 • (1 : D) ∈ J := (mem_augIdeal_iff _).2 (sub_smul_one_apply_one φ)
  have h := θ_apply_toCotangent x ⟨_, hφ'⟩
  rw [hx, LinearMap.zero_apply] at h
  show φ (x : A) = 0
  rw [apply_eq_sub_apply_of_isPrim hprim]
  exact h.symm

noncomputable def projJ : D →ₗ[k] ↥J where
  toFun φ := ⟨φ - φ 1 • (1 : D), (mem_augIdeal_iff _).2 (sub_smul_one_apply_one φ)⟩
  map_add' φ ψ := by
    refine Subtype.ext ?_
    show φ + ψ - (φ 1 + ψ 1) • (1 : D) = (φ - φ 1 • (1 : D)) + (ψ - ψ 1 • (1 : D))
    rw [add_smul]; abel
  map_smul' c φ := by
    refine Subtype.ext ?_
    show c • φ - (c * φ 1) • (1 : D) = c • (φ - φ 1 • (1 : D))
    rw [smul_sub, mul_smul]

/--
@isnad1 id=eq.0h3v.s11.74a34f00f7e3 from=translated src=- shape=ef0054e9 vocab=96010b03
-/
theorem coe_projJ (φ : D) : (projJ φ : D) = φ - φ 1 • (1 : D) := rfl

/--
@isnad1 id=eq.1h3v.s11.e9b767c61a57 from=translated src=- shape=98c2670b vocab=1b74f845
-/
theorem projJ_of_mem {φ : D} (hφ : φ ∈ J) : projJ φ = ⟨φ, hφ⟩ := by
  refine Subtype.ext ?_
  rw [coe_projJ, (mem_augIdeal_iff φ).1 hφ, zero_smul, sub_zero]

/--
@isnad1 id=eq.0h4v.s13.582efb9ac712 from=translated src=- shape=dbcd566b vocab=66e2cdfa
-/
theorem projJ_mul (φ ψ : D) :
    projJ (φ * ψ) = φ 1 • projJ ψ + ψ 1 • projJ φ + projJ φ * projJ ψ := by
  refine Subtype.ext ?_
  simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, MulMemClass.coe_mul, coe_projJ,
    mul_apply_one]
  simp only [Algebra.smul_def, mul_one, map_mul]
  ring

noncomputable def der (t : Module.Dual k (augIdeal k A).Cotangent) : D →ₗ[k] k :=
  t ∘ₗ ((augIdeal k A).toCotangent.restrictScalars k) ∘ₗ projJ

/--
@isnad1 id=eq.0h4v.s12.541d043cf3d4 from=translated src=- shape=45311731 vocab=72c79b6e
-/
theorem der_apply (t : Module.Dual k (augIdeal k A).Cotangent) (φ : D) :
    der t φ = t ((augIdeal k A).toCotangent (projJ φ)) := rfl

/--
@isnad1 id=eq.0h5v.s10.50bee44f6bad from=translated src=- shape=271b8f1e vocab=5de2ea71
-/
theorem der_mul (t : Module.Dual k (augIdeal k A).Cotangent) (φ ψ : D) :
    der t (φ * ψ) = φ 1 * der t ψ + ψ 1 * der t φ := by
  have h0 : (augIdeal k A).toCotangent (projJ φ * projJ ψ) = 0 := by
    rw [Ideal.toCotangent_eq_zero, MulMemClass.coe_mul, pow_two]
    exact Ideal.mul_mem_mul (projJ φ).2 (projJ ψ).2
  rw [der_apply, der_apply, der_apply, projJ_mul]
  simp only [map_add, LinearMap.map_smul_of_tower, h0, add_zero, map_smul, smul_eq_mul]

private noncomputable def _root_.HopfAlgebra.PrimitivesDual.lift (t : Module.Dual k (augIdeal k A).Cotangent) : A :=
  (Module.evalEquiv k A).symm (der t ∘ₗ (CartierDual.ofDual k A).toLinearMap)

export _root_.HopfAlgebra.PrimitivesDual (lift)
/--
@isnad1 id=eq.0h4v.s9.4a6a1e79053c from=translated src=- shape=e0f905cf vocab=ebd6d956
-/
theorem apply_lift (t : Module.Dual k (augIdeal k A).Cotangent) (φ : D) :
    φ (lift t) = der t φ := by
  show (CartierDual.toDual k A φ) ((Module.evalEquiv k A).symm _) = _
  rw [Module.apply_evalEquiv_symm_apply]
  rfl

omit [Coalgebra.IsCocomm k A] in

/--
@isnad1 id=eq.1h4v.s13.c1b5965db097 from=translated src=- shape=2c974200 vocab=041bd34f
-/
theorem tmul_ext {z z' : A ⊗[k] A}
    (h : ∀ f g : Module.Dual k A,
      TensorProduct.dualDistrib k A A (f ⊗ₜ[k] g) z = TensorProduct.dualDistrib k A A (f ⊗ₜ[k] g) z') :
    z = z' := by
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff k (z - z')).1 fun F => ?_
  obtain ⟨w, rfl⟩ := (TensorProduct.dualDistribEquiv k A A).surjective F
  rw [CartierDual.dualDistribEquiv_apply_eq, map_sub, sub_eq_zero]
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | tmul f g => exact h f g
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

/--
@isnad1 id=isprim.0h3v.s8.631541131eec from=translated src=- shape=87e86aa1 vocab=03663d9b
-/
theorem isPrim_lift (t : Module.Dual k (augIdeal k A).Cotangent) : IsPrim k (lift t) := by
  unfold IsPrim
  refine tmul_ext fun f g => ?_

  have hL : TensorProduct.dualDistrib k A A (f ⊗ₜ[k] g) (Coalgebra.comul (R := k) (lift t)) =
      (CartierDual.ofDual k A f * CartierDual.ofDual k A g) (lift t) :=
    (CartierDual.mul_apply _ _ _).symm
  rw [hL, apply_lift, der_mul, ← apply_lift, ← apply_lift, map_add,
    TensorProduct.dualDistrib_apply, TensorProduct.dualDistrib_apply]
  show f 1 * g (lift t) + g 1 * f (lift t) = f (lift t) * g 1 + f 1 * g (lift t)
  ring

/--
@isnad1 id=surjecti.0h2v.s11.88897c0e7d0a from=translated src=- shape=bcafd8fc vocab=c43b7197
-/
theorem θ_surjective : Function.Surjective (θ (k := k) (A := A)) := by
  intro t
  refine ⟨⟨lift t, (mem_prim_iff _).2 (isPrim_lift t)⟩, LinearMap.ext fun v => ?_⟩
  obtain ⟨φ, rfl⟩ := (augIdeal k A).toCotangent_surjective v
  rw [θ_apply_toCotangent]
  show (φ : D) (lift t) = _
  rw [apply_lift, der_apply, projJ_of_mem φ.2]

noncomputable def θEquiv : ↥(prim k A) ≃ₗ[k] Module.Dual k (augIdeal k A).Cotangent :=
  LinearEquiv.ofBijective θ ⟨θ_injective, θ_surjective⟩

scoped instance : Module.Finite k ↥J :=
  Module.IsNoetherian.finite k ↥((augIdeal k A).restrictScalars k)

scoped instance : Module.Finite k (augIdeal k A).Cotangent :=
  Module.Finite.of_surjective ((augIdeal k A).toCotangent.restrictScalars k)
    (augIdeal k A).toCotangent_surjective

/--
@isnad1 id=eq.0h2v.s9.ea8485910a21 from=translated src=- shape=f05cf14c vocab=6f8d5a0d
-/
theorem finrank_prim_eq :
    Module.finrank k ↥(prim k A) = Module.finrank k (augIdeal k A).Cotangent := by
  rw [θEquiv.finrank_eq, Subspace.dual_finrank_eq]

omit [Module.Finite k A] in
/--
@isnad1 id=eq.0h4v.s11.a9ea7f93cf7c from=translated src=- shape=249b58a6 vocab=851f8b44
-/
theorem toDual_pow (φ : D) (n : ℕ) :
    CartierDual.toDual k A (φ ^ n) = (WithConv.toConv (CartierDual.toDual k A φ) ^ n).ofConv := by
  induction n with
  | zero =>
    refine LinearMap.ext fun a => ?_
    rw [pow_zero, pow_zero, LinearMap.convOne_apply, Algebra.algebraMap_self_apply]
    exact CartierDual.one_apply a
  | succ n ih =>
    rw [pow_succ, CartierDual.toDual_mul, ih, WithConv.toConv_ofConv, ← pow_succ]

/--
@isnad1 id=eq.2h4v.s11.004bf2e58706 from=translated src=- shape=db6b7530 vocab=d3e1bbed
-/
theorem pow_eq_zero_of_counit_eq_zero {p : ℕ}
    (hV : ∀ β : WithConv (A →ₗ[k] k), β.ofConv 1 = 0 → β ^ p = 0)
    (φ : D) (hφ : Coalgebra.counit (R := k) φ = 0) : φ ^ p = 0 := by
  rw [CartierDual.counit_apply] at hφ
  have h := hV (WithConv.toConv (CartierDual.toDual k A φ)) hφ
  have h2 : CartierDual.toDual k A (φ ^ p) = 0 := by
    rw [toDual_pow, h, WithConv.ofConv_zero]
  exact CartierDual.ext fun a => congrArg (fun ψ : Module.Dual k A => ψ a) h2

/--
@isnad1 id=eq.1h3v.s10.df60622756d0 from=translated src=- shape=8876e9b8 vocab=f07f1ee9
-/
theorem finrank_eq_pow_finrank_prim (p : ℕ) [Fact p.Prime] [CharP k p]
    (hV : ∀ β : WithConv (A →ₗ[k] k), β.ofConv 1 = 0 → β ^ p = 0) :
    Module.finrank k A = p ^ Module.finrank k ↥(prim k A) := by
  rw [finrank_prim_eq, ← CartierDual.finrank_eq k A]
  exact HopfAlgebra.finrank_eq_pow_finrank_cotangent_of_forall_pow_prime_eq_zero k p (CartierDual k A)
    (pow_eq_zero_of_counit_eq_zero hV)

end HopfAlgebra.PrimitivesDual
open scoped _root_.P2MW.S_HopfAlgebra_finrank_eq_pow_finrank_primitives_of_forall_convPow_prime_eq_zero.HopfAlgebra _root_.P2MW.S_HopfAlgebra_finrank_eq_pow_finrank_primitives_of_forall_convPow_prime_eq_zero.HopfAlgebra.PrimitivesDual
open scoped _root_.P2MW.S_HopfAlgebra_finrank_eq_pow_finrank_primitives_of_forall_convPow_prime_eq_zero.HopfAlgebra

/--
@isnad1 id=eq.1h3v.s11.2ba324b9ac63 from=translated src=- shape=d72f91c2 vocab=b677b795
-/
theorem solution
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type v) [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]
    (hV : ∀ β : WithConv (A →ₗ[k] k), β.ofConv 1 = 0 → β ^ p = 0) :
    Module.finrank k A = p ^ Module.finrank k ↥(primitives k A) :=
  HopfAlgebra.PrimitivesDual.finrank_eq_pow_finrank_prim p hV
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
