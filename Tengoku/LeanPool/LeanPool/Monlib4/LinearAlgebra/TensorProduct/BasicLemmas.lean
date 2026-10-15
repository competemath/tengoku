/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Tengoku

/-!
# Some lemmas about `tensor_product`
-/

@[expose] public section

open scoped TensorProduct BigOperators

namespace TensorProduct

variable {R M N P Q : Type _} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
  [AddCommMonoid P] [AddCommMonoid Q] [Module R M] [Module R N] [Module R P]
  [Module R Q]

/-- Linear maps out of a tensor product are equal iff they agree on pure tensors.
@isnad1 id=iff.0h6v.s8.f1786296536f from=translated src=- shape=6517aad3 vocab=c676f709
-/
protected theorem ext_iff' {g h : M ⊗[R] N →ₗ[R] P} :
    g = h ↔ ∀ x y, g (x ⊗ₜ[R] y) = h (x ⊗ₜ[R] y) :=
  ⟨fun hxy x y => by rw [hxy], fun hxy => TensorProduct.ext' hxy⟩

/--
@isnad1 id=iff.0h7v.s10.30ed1f4bbaec from=translated src=- shape=aac45652 vocab=c676f709
-/
theorem ext'_iff {g h : (M ⊗[R] N) ⊗[R] Q →ₗ[R] P} :
    (∀ x : (M ⊗[R] N) ⊗[R] Q, g x = h x) ↔
      ∀ (x : M) (y : N) (z : Q),
        g ((x ⊗ₜ[R] y) ⊗ₜ[R] z) = h ((x ⊗ₜ[R] y) ⊗ₜ[R] z) := by
  refine ⟨fun hxy x y z => by rw [hxy], ?_⟩
  rw [← LinearMap.ext_iff]
  exact TensorProduct.ext_threefold

/--
@isnad1 id=eq.0h9v.s8.0ba1af0a9caf from=translated src=- shape=2f337257 vocab=638ac4b8
-/
@[simp]
theorem map_apply (f : M →ₗ[R] P) (t : N →ₗ[R] Q) (x : M) (y : N) :
    TensorProduct.map f t (x ⊗ₜ[R] y) = f x ⊗ₜ[R] t y :=
  rfl

/--
@isnad1 id=eq.0h7v.s10.0a453243a387 from=translated src=- shape=3a75c2e5 vocab=e8282841
-/
@[simp]
theorem comm_commutes {g : M ⊗[R] N →ₗ[R] P} {h : M ⊗[R] N →ₗ[R] Q} :
    (TensorProduct.comm R P Q).toLinearMap ∘ₗ TensorProduct.map g h =
      TensorProduct.map h g ∘ₗ
        (TensorProduct.comm R (M ⊗[R] N) (M ⊗[R] N)).toLinearMap := by
  simp_rw [TensorProduct.ext_iff', LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.comm_tmul, TensorProduct.map_apply, TensorProduct.comm_tmul, forall₂_true_iff]

/--
@isnad1 id=eq.0h4v.s9.3f1c793c1a37 from=translated src=- shape=e9b5fa44 vocab=e8282841
-/
theorem comm_commutes' {g : M →ₗ[R] M} {h : M →ₗ[R] R} :
    (TensorProduct.comm R M R).toLinearMap ∘ₗ TensorProduct.map g h =
      TensorProduct.map h g ∘ₗ (TensorProduct.comm R M M).toLinearMap := by
  simp_rw [TensorProduct.ext_iff', LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.comm_tmul, TensorProduct.map_apply, TensorProduct.comm_tmul,
    forall₂_true_iff]

/--
@isnad1 id=eq.0h10v.s10.2841dea96702 from=translated src=- shape=9ebbede9 vocab=cc5850d1
-/
theorem assoc_comp_map {R : Type _} [CommSemiring R] {M N M₂ N₂ P Q : Type _}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid M₂] [AddCommMonoid N₂]
    [AddCommMonoid P] [AddCommMonoid Q] [Module R M] [Module R N] [Module R M₂]
    [Module R N₂] [Module R P] [Module R Q] (f : M →ₗ[R] P) (t : N →ₗ[R] Q)
    (s : M₂ →ₗ[R] N₂) :
    (TensorProduct.assoc R P Q N₂).toLinearMap ∘ₗ TensorProduct.map (TensorProduct.map f t) s =
      TensorProduct.map f (TensorProduct.map t s) ∘ₗ
        (TensorProduct.assoc R M N M₂).toLinearMap := by
  apply TensorProduct.ext_threefold
  simp_all

/--
@isnad1 id=eq.0h10v.s11.94a94d5abea4 from=translated src=- shape=762bafd9 vocab=2eeef76b
-/
theorem assoc_symm_comp_map {R : Type _} [CommSemiring R] {M N M₂ N₂ P Q : Type _}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid M₂] [AddCommMonoid N₂]
    [AddCommMonoid P] [AddCommMonoid Q] [Module R M] [Module R N] [Module R M₂]
    [Module R N₂] [Module R P] [Module R Q] (f : M →ₗ[R] P) (t : N →ₗ[R] Q)
    (s : M₂ →ₗ[R] N₂) :
    (TensorProduct.assoc R P Q N₂).symm.toLinearMap ∘ₗ
        TensorProduct.map f (TensorProduct.map t s) =
      TensorProduct.map (TensorProduct.map f t) s ∘ₗ
        (TensorProduct.assoc R M N M₂).symm.toLinearMap := by
  apply TensorProduct.ext_threefold'
  simp_all

/--
@isnad1 id=eq.0h7v.s9.50706ac7932c from=translated src=- shape=7d9f79d6 vocab=e8282841
-/
theorem comm_map {R : Type _} [CommSemiring R] {M N P Q : Type _} [AddCommMonoid M]
    [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q] [Module R M] [Module R N]
    [Module R P] [Module R Q] (f : M →ₗ[R] P) (t : N →ₗ[R] Q) :
    (TensorProduct.comm R P Q).toLinearMap ∘ₗ TensorProduct.map f t =
      TensorProduct.map t f ∘ₗ (TensorProduct.comm R M N).toLinearMap := by
  simp_rw [TensorProduct.ext_iff', LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.map_apply, TensorProduct.comm_tmul, TensorProduct.map_apply, forall₂_true_iff]

/--
@isnad1 id=eq.0h7v.s9.ea616d16e01c from=translated src=- shape=ffcf0c24 vocab=98c1c876
-/
theorem comm_symm_map {R : Type _} [CommSemiring R] {M N P Q : Type _}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]
    [Module R M] [Module R N] [Module R P] [Module R Q] (f : M →ₗ[R] P)
    (t : N →ₗ[R] Q) :
    (TensorProduct.comm R P Q).symm.toLinearMap ∘ₗ TensorProduct.map t f =
      TensorProduct.map f t ∘ₗ (TensorProduct.comm R M N).symm.toLinearMap := by
  simp_rw [TensorProduct.ext_iff', LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.map_apply, TensorProduct.comm_symm_tmul, TensorProduct.map_apply,
    forall₂_true_iff]

/--
@isnad1 id=eq.0h9v.s8.4bf706446ec1 from=translated src=- shape=466f68d3 vocab=5b30ce43
-/
protected theorem map_sum {R : Type _} [CommSemiring R] {M₁ M₂ N₁ N₂ : Type _}
    [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid N₁] [AddCommMonoid N₂]
    [Module R M₁] [Module R M₂] [Module R N₁] [Module R N₂] (x : M₁ →ₗ[R] M₂)
    {α : Type _} (s : Finset α) (n : α → N₁ →ₗ[R] N₂) :
    map x (∑ a ∈ s, n a) = ∑ a ∈ s, map x (n a) := by
  simp_rw [TensorProduct.ext_iff', LinearMap.sum_apply, map_apply, LinearMap.coe_sum,
    Finset.sum_apply, tmul_sum, forall₂_true_iff]

/--
@isnad1 id=eq.0h9v.s8.4cc3f467bcfe from=translated src=- shape=4d156f26 vocab=5b30ce43
-/
theorem sum_map {R : Type _} [CommSemiring R] {M₁ M₂ N₁ N₂ : Type _}
    [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid N₁] [AddCommMonoid N₂]
    [Module R M₁] [Module R M₂] [Module R N₁] [Module R N₂] {α : Type _}
    (s : Finset α) (n : α → N₁ →ₗ[R] N₂) (x : M₁ →ₗ[R] M₂) :
    map (∑ a ∈ s, n a) x = ∑ a ∈ s, map (n a) x := by
  simp_rw [TensorProduct.ext_iff', LinearMap.sum_apply, map_apply, LinearMap.coe_sum,
    Finset.sum_apply, sum_tmul, forall₂_true_iff]

/--
@isnad1 id=eq.0h8v.s9.b05befb7a9ee from=translated src=- shape=6b1dba3f vocab=659bf1a2
-/
protected theorem map_smul {R : Type _} [CommSemiring R] {M₁ M₂ N₁ N₂ : Type _}
    [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid N₁] [AddCommMonoid N₂]
    [Module R M₁] [Module R M₂] [Module R N₁] [Module R N₂] (x : M₁ →ₗ[R] M₂)
    (y : N₁ →ₗ[R] N₂) (a : R) :
    map x (a • y) = a • map x y := by
  simp_rw [TensorProduct.ext_iff', LinearMap.smul_apply, map_apply, LinearMap.smul_apply,
    tmul_smul, forall₂_true_iff]

/--
@isnad1 id=eq.0h8v.s9.5f82b3f90a3d from=translated src=- shape=23c259b9 vocab=659bf1a2
-/
theorem smul_map {R : Type _} [CommSemiring R] {M₁ M₂ N₁ N₂ : Type _}
    [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid N₁] [AddCommMonoid N₂]
    [Module R M₁] [Module R M₂] [Module R N₁] [Module R N₂] (x : M₁ →ₗ[R] M₂)
    (y : N₁ →ₗ[R] N₂) (a : R) :
    map (a • x) y = a • map x y := by
  simp_rw [TensorProduct.ext_iff', LinearMap.smul_apply, map_apply, LinearMap.smul_apply,
    smul_tmul', forall₂_true_iff]

/--
@isnad1 id=eq.0h8v.s9.5c1762f50280 from=translated src=- shape=f05111ba vocab=e362bb74
-/
theorem add_map {R : Type _} [CommSemiring R] {M₁ M₂ N₁ N₂ : Type _}
    [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid N₁] [AddCommMonoid N₂]
    [Module R M₁] [Module R M₂] [Module R N₁] [Module R N₂] (x y : M₁ →ₗ[R] M₂)
    (z : N₁ →ₗ[R] N₂) :
    TensorProduct.map (x + y) z = TensorProduct.map x z + TensorProduct.map y z := by
  simp only [TensorProduct.ext_iff', TensorProduct.map_apply, LinearMap.add_apply, add_tmul,
    forall₂_true_iff]

/--
@isnad1 id=eq.0h6v.s8.70ddda842550 from=translated src=- shape=e7d702b0 vocab=33502b15
-/
protected theorem map_zero {R : Type _} [CommSemiring R] {M₁ N₁ M₂ N₂ : Type _}
    [AddCommMonoid M₁] [AddCommMonoid N₁] [AddCommMonoid M₂] [AddCommMonoid N₂]
    [Module R M₁] [Module R N₁] [Module R M₂] [Module R N₂] (x : M₁ →ₗ[R] N₁) :
    TensorProduct.map x (0 : M₂ →ₗ[R] N₂) = 0 := by
  simp_all

/--
@isnad1 id=eq.0h6v.s8.abfe7c690f6c from=translated src=- shape=6636c87b vocab=33502b15
-/
protected theorem zero_map {R : Type _} [CommSemiring R] {M₁ N₁ M₂ N₂ : Type _}
    [AddCommMonoid M₁] [AddCommMonoid N₁] [AddCommMonoid M₂] [AddCommMonoid N₂]
    [Module R M₁] [Module R N₁] [Module R M₂] [Module R N₂] (x : M₁ →ₗ[R] N₁) :
    TensorProduct.map (0 : M₂ →ₗ[R] N₂) x = 0 := by
  simp_all

/--
@isnad1 id=iff.0h5v.s7.80abd1e18c51 from=translated src=- shape=816a8105 vocab=53c931bf
-/
theorem tmul_eq_zero {R : Type _} [Field R] {M N : Type _} [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N] {x : M} {y : N} :
    x ⊗ₜ[R] y = 0 ↔ x = 0 ∨ y = 0 := by
  let b₁ := Module.Basis.ofVectorSpace R M
  let b₂ := Module.Basis.ofVectorSpace R N
  constructor
  · intro h
    apply_fun (b₁.tensorProduct b₂).repr at h
    simp only [Module.Basis.tensorProduct_repr_tmul_apply, DFunLike.ext_iff, Prod.forall,
      map_zero, Finsupp.zero_apply, smul_eq_zero] at h
    simp only [Module.Basis.ext_elem_iff b₁, Module.Basis.ext_elem_iff b₂, map_zero,
      Finsupp.zero_apply, ← forall_or_left, ← forall_or_right]
    exact fun _ _ => or_comm.mp (h _ _)
  · rintro (rfl | rfl)
    · exact TensorProduct.zero_tmul _ _
    · exact TensorProduct.tmul_zero _ _

/--
@isnad1 id=eq.0h3v.s7.5cabca2533b5 from=translated src=- shape=80fda3ad vocab=c8232a28
-/
theorem zero_tmul_zero {R : Type _} [CommSemiring R] {M N : Type _} [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N] : (0 : M ⊗[R] N) = 0 ⊗ₜ 0 := by
  rw [TensorProduct.zero_tmul]

/--
@isnad1 id=iff.0h4v.s9.122f8f51235d from=translated src=- shape=5311c032 vocab=73bcf98a
-/
theorem mapMul'_commute_iff {R M N : Type _} [CommSemiring R]
    [NonUnitalNonAssocSemiring M] [NonUnitalNonAssocSemiring N] [Module R M]
    [Module R N] [SMulCommClass R M M] [SMulCommClass R N N] [IsScalarTower R M M]
    [IsScalarTower R N N] {f : M →ₗ[R] N} :
    (LinearMap.mul' R N).comp (TensorProduct.map f f) = f.comp (LinearMap.mul' R M) ↔
      ∀ x y, f (x * y) = f x * f y := by
  simp only [TensorProduct.ext_iff', LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearMap.mul'_apply, eq_comm]

end TensorProduct

/--
@isnad1 id=eq.0h7v.s8.6bcbdaf12826 from=translated src=- shape=35472702 vocab=73017959
-/
theorem Algebra.TensorProduct.map_toLinearMap {R M N P Q : Type _} [CommSemiring R]
    [Semiring M] [Semiring N] [Semiring P] [Semiring Q] [Algebra R M] [Algebra R N]
    [Algebra R P] [Algebra R Q] (f : M →ₐ[R] N) (g : P →ₐ[R] Q) :
    AlgHom.toLinearMap (Algebra.TensorProduct.map f g) =
      _root_.TensorProduct.map (AlgHom.toLinearMap f) (AlgHom.toLinearMap g) :=
  rfl

/--
@isnad1 id=eq.0h4v.s9.519d89b2d421 from=translated src=- shape=e8bc9a15 vocab=1d0c78ee
-/
theorem AlgHom.commute_mapMul' {R M N : Type _} [CommSemiring R] [Semiring M]
    [Semiring N] [Algebra R M] [Algebra R N] (f : M →ₐ[R] N) :
    (LinearMap.mul' R N).comp (Algebra.TensorProduct.map f f).toLinearMap =
      f.toLinearMap.comp (LinearMap.mul' R M) := by
  simp only [TensorProduct.ext_iff', LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    LinearMap.mul'_apply, Algebra.TensorProduct.map_tmul, _root_.map_mul, forall₂_true_iff]

/--
@isnad1 id=eq.0h5v.s10.e1feac29d678 from=translated src=- shape=84b666d7 vocab=e02deee5
-/
theorem AlgHom.commute_mapMul'_apply {R M N : Type _} [CommSemiring R] [Semiring M]
    [Semiring N] [Algebra R M] [Algebra R N] (f : M →ₐ[R] N) (x : M ⊗[R] M) :
    (LinearMap.mul' R N) ((Algebra.TensorProduct.map f f) x) =
      f ((LinearMap.mul' R M) x) := by
  simp only [← LinearMap.comp_apply, ← AlgHom.toLinearMap_apply]
  revert x
  rw [← LinearMap.ext_iff]
  exact AlgHom.commute_mapMul' _

open TensorProduct

/--
@isnad1 id=eq.0h8v.s9.ab260f55e00c from=translated src=- shape=9fb347aa vocab=e362bb74
-/
theorem TensorProduct.map_add {R : Type _} [CommSemiring R] {M₁ M₂ N₁ N₂ : Type _}
    [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid N₁] [AddCommMonoid N₂]
    [Module R M₁] [Module R M₂] [Module R N₁] [Module R N₂] (x y : M₁ →ₗ[R] M₂)
    (z : N₁ →ₗ[R] N₂) :
    TensorProduct.map z (x + y) = map z x + map z y := by
  simp only [TensorProduct.ext_iff', TensorProduct.map_tmul, tmul_add, LinearMap.add_apply,
    forall₂_true_iff]
