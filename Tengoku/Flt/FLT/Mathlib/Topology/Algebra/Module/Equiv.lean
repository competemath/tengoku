/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Salvatore Mercuri, Pietro Monticone
-/
module

public import Tengoku
public import Tengoku.Flt.FLT.Mathlib.LinearAlgebra.Pi

/-!
# Equiv

Material destined for Mathlib.
-/

@[expose] public section

/-- Let `f : α → β` be a function on index types. A family of `R b`-linear homeomorphisms, indexed
by `b : β`, between the product over the fiber of `b` under `f` given as
`∀ (σ : { a : α // f a = b }) → γ₁ σ.1) ≃ₗ[R b] γ₂ b` lifts to an equivalence over the products
`∀ a, γ₁ a ≃ₗ[∀ b, R b] ∀ b, γ₂ b` with product scalars `∀ b, R b`, provided that `∀ b, R b` acts on
`∀ a, γ₁ a` fiberwise. This is `Equiv.piCongrFiberwise` as a `ContinuousLinearEquiv` with product
scalars. -/
def ContinuousLinearEquiv.piScalarPiCongrFiberwise {α : Type*} {β : Type*} {R : β → Type*}
    {γ₁ : α → Type*} {γ₂ : β → Type*} {f : α → β} [(a : α) → TopologicalSpace (γ₁ a)]
    [(b : β) → TopologicalSpace (γ₂ b)] [(b : β) → Semiring (R b)] [(a : α) → AddCommMonoid (γ₁ a)]
    [(b : β) → AddCommMonoid (γ₂ b)] [(b : β) → (a : { a : α // f a = b }) → Module (R b) (γ₁ a)]
    [(b : β) → Module (R b) (γ₂ b)] [Module ((b : β) → R b) ((a : α) → γ₁ a)]
    [Pi.FiberwiseSMul f R γ₁]
    (e : (b : β) → ((σ : { a : α // f a = b }) → γ₁ σ.1) ≃L[R b] γ₂ b) :
    ((a : α) → γ₁ a) ≃L[∀ b, R b] ((b : β) → γ₂ b) where
  __ := LinearEquiv.piScalarPiCongrFiberwise fun b => (e b).toLinearEquiv
  continuous_invFun := by
    change Continuous (fun (g : (b : β) → γ₂ b) a ↦ (e (f a)).symm (g (f a)) ⟨a, rfl⟩)
    fun_prop
  continuous_toFun := by
    change Continuous (fun (x : (a : α) → γ₁ a) ↦
      Pi.map (fun a ↦ ⇑(e a)) fun _ y ↦ (fun _ ↦ x _) _)
    fun_prop

/-- Given `φ : α → β → Type*` and `R : α → Type*` such that `φ a b` is an `R a` module for all
`a b`, this is the continuous linear equivalence between `∀ a b, φ a b` and `∀ b a, φ a b` with
product scalars. This is `Equiv.piComm` as a product-scalar `ContinuousLinearEquiv`. -/
def ContinuousLinearEquiv.piScalarPiComm {α β : Type*} (R : α → Type*) (φ : α → β → Type*)
    [(a : α) → Semiring (R a)] [(a : α) → (b : β) → AddCommMonoid (φ a b)]
    [(a : α) → (b : β) → Module (R a) (φ a b)] [(a : α) → (b : β) → TopologicalSpace (φ a b)] :
    ((a : α) → (b : β) → φ a b) ≃L[∀ a, R a] ((b : β) → (a : α) → φ a b) where
  __ := LinearEquiv.piScalarPiComm R φ
  continuous_toFun := by
    change Continuous (fun (x : (a : α) → (b : β) → φ a b) ↦ Function.swap x)
    fun_prop
  continuous_invFun := by
    change Continuous (fun x ↦ Function.swap x)
    fun_prop

/--
@isnad1 id=eq.0h4v.s7.92524b8baf57 from=translated src=- shape=e2519a0c vocab=134f3e03
-/
lemma ContinuousLinearEquiv.toContinuousAddEquiv_trans
    {R : Type*} {E : Type*} [Semiring R] [AddCommMonoid E] [Module R E]
    [TopologicalSpace E] {e f : E ≃L[R] E} :
    (e.trans f).toContinuousAddEquiv =
      e.toContinuousAddEquiv.trans f.toContinuousAddEquiv := rfl

/--
@isnad1 id=isunit.0h5v.s9.7ebe733b5cc7 from=translated src=- shape=8d417948 vocab=cf20e0c0
-/
lemma ContinuousLinearEquiv.toMatrix_isUnit_det
    {F : Type*} [CommRing F] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : Type*} [AddCommGroup V] [Module F V] [TopologicalSpace V]
    (b : Module.Basis ι F V) (ρ : V ≃L[F] V) :
    IsUnit ((ρ.toLinearMap.toMatrix b b).det) := LinearEquiv.isUnit_det ρ.toLinearEquiv b b

/--
@isnad1 id=isunit.0h5v.s9.9bc10583cb66 from=translated src=- shape=a4be9c62 vocab=ee3e428f
-/
lemma ContinuousLinearEquiv.toMatrix_isUnit
    {F : Type*} [CommRing F] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : Type*} [AddCommGroup V] [Module F V] [TopologicalSpace V]
    (b : Module.Basis ι F V) (ρ : V ≃L[F] V) :
    IsUnit (ρ.toLinearMap.toMatrix b b) :=
  (Matrix.isUnit_iff_isUnit_det (ρ.toLinearMap.toMatrix b b)).mpr
    (toMatrix_isUnit_det b ρ)

/--
@isnad1 id=ne.0h5v.s9.043525f284e0 from=translated src=- shape=400606fa vocab=be2fafa4
-/
lemma ContinuousLinearEquiv.toMatrix_det_ne_zero
    {F : Type*} [CommRing F] [Nontrivial F] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : Type*} [AddCommGroup V] [Module F V] [TopologicalSpace V]
    (b : Module.Basis ι F V) (ρ : V ≃L[F] V) :
    (ρ.toLinearMap.toMatrix b b).det ≠ 0 :=
  IsUnit.ne_zero (ContinuousLinearEquiv.toMatrix_isUnit_det b ρ)

section toContinuousLinearEquiv

variable {F : Type*} [CommRing F] [TopologicalSpace F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [AddCommGroup V] [Module F V] [TopologicalSpace V]
variable [IsModuleTopology F V] [ContinuousAdd V]

namespace Matrix

/-- Given `M : Matrix ι ι F`, `b : Module.Basis ι F V` and `h : M.det ≠ 0`,
  this is the continuous linear equivalence arising from
  `Matrix.toLinearEquiv b M (Ne.isUnit h)` -/
noncomputable def toContinuousLinearEquiv
    (M : Matrix ι ι F) (b : Module.Basis ι F V) (h : IsUnit M.det) : V ≃L[F] V :=
  let e := Matrix.toLinearEquiv b M h
  have ce : Continuous e :=
    IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have ce_inv : Continuous e.symm :=
    IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  ⟨e, ce, ce_inv⟩

/--
@isnad1 id=eq.1h6v.s9.2bed5aa706c5 from=translated src=- shape=da2e06db vocab=72f23890
-/
@[simp]
lemma toContinousLinearEquiv_apply
    (M : Matrix ι ι F) (b : Module.Basis ι F V) (h : IsUnit M.det) (x : V) :
    (M.toContinuousLinearEquiv b h) x = toLin b b M x := rfl

/--
@isnad1 id=eq.1h5v.s9.2b0d6a938c6d from=translated src=- shape=bb8be4a2 vocab=72f23890
-/
@[simp]
lemma toContinuousLinearEquiv_toLin_coe
    (M : Matrix ι ι F) (b : Module.Basis ι F V) (h : IsUnit M.det) :
    ⇑(M.toContinuousLinearEquiv b h) = ⇑(toLin b b M) := rfl

/--
@isnad1 id=eq.1h5v.s8.5611c1f3062c from=translated src=- shape=b7f949a0 vocab=13247242
-/
@[simp]
lemma toContinuousLinearEquiv_toLinearEquiv
    (b : Module.Basis ι F V) (M : Matrix ι ι F) (h : IsUnit M.det) :
    (M.toContinuousLinearEquiv b h).toLinearEquiv = Matrix.toLinearEquiv b M h := rfl

/--
@isnad1 id=eq.1h5v.s9.12e4ad9c2087 from=translated src=- shape=4b1c2941 vocab=5fdd31b5
-/
lemma toContinousLinearEquiv_toMatrix
    (b : Module.Basis ι F V) (M : Matrix ι ι F) (h : IsUnit M.det) :
    (M.toContinuousLinearEquiv b h ).toLinearMap.toMatrix b b = M :=
  (LinearEquiv.eq_symm_apply (LinearMap.toMatrix b b)).mp rfl

/--
@isnad1 id=other.2h6v.s8.9d53f33a51d8 from=translated src=- shape=23441286 vocab=8f6d18cb
-/
lemma toContinousLinearEquiv_mul
    (b : Module.Basis ι F V)
    (A : Matrix ι ι F) (hA : IsUnit A.det) (B : Matrix ι ι F) (hB : IsUnit B.det) :
    have hAB : IsUnit (A * B).det := by rw[Matrix.det_mul]; exact IsUnit.mul hA hB
    (A * B).toContinuousLinearEquiv b hAB =
    (B.toContinuousLinearEquiv b hB).trans (A.toContinuousLinearEquiv b hA) := by
  ext x
  simp [ContinuousLinearEquiv.trans_apply, Matrix.toLin_mul b b]

end Matrix

/--
@isnad1 id=eq.0h5v.s9.3ff7d5415af2 from=translated src=- shape=2fa9dcf9 vocab=0fd037a5
-/
lemma ContinuousLinearEquiv.toMatrix_toContinousLinearEquiv
    (b : Module.Basis ι F V) (ρ : V ≃L[F] V) :
    (ρ.toLinearEquiv.toMatrix b b).toContinuousLinearEquiv b
    (ContinuousLinearEquiv.toMatrix_isUnit_det b ρ ) = ρ := by
  ext
  simp

/--
@isnad1 id=eq.0h5v.s7.7b33c2a7fe88 from=translated src=- shape=7d2c30a2 vocab=1c1ccd57
-/
theorem ContinuousLinearEquiv.toContinuousAddEquiv_apply {R : Type*} {M N : Type*}
    [Semiring R] [TopologicalSpace M] [TopologicalSpace N] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N]
    (f : M ≃L[R] N) (m : M) : f.toContinuousAddEquiv m = f m := rfl

end toContinuousLinearEquiv
