/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.Frobenius.Constructions
public import Tengoku.Seed.RingTheory.Coalgebra.Basic
public import Tengoku.Seed.RingTheory.TensorProduct.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The coalgebra carried by a commutative Frobenius algebra

For a finite-free commutative Frobenius algebra, the inverse metric tensor
`C = F.casimir` defines a comultiplication by

`Δ(a) = (a ⊗ 1) C`.

This file proves that multiplication and comultiplication satisfy the
Frobenius relation and that `Δ`, together with the original Frobenius
functional, gives a cocommutative coalgebra.  The construction is explicit in
the Frobenius object `F`; it is deliberately not installed as a global
typeclass instance, because the same algebra may carry several Frobenius
functionals.

## Reading the Lean notation

* Multiplication on `A ⊗[R] A` is componentwise:
  `(a ⊗ b) * (c ⊗ d) = ac ⊗ bd`.
* `LinearMap.mulRight R C` is the linear map `t ↦ t * C`.
* `f.comp g` means first apply `g`, then apply `f`.
* The tensor associator appears explicitly in mathlib's coassociativity law.
-/

@[expose] public section

namespace AxiomaticGW

open TensorProduct

namespace CommFrobeniusAlgebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [Module.Free R A] [Module.Finite R A]

/-- Multiplying the first tensor leg by `a` moves the input of the associated
endomorphism from `x` to `a * x`.-/
theorem tensorEndEquiv_includeLeft_mul (F : CommFrobeniusAlgebra R A)
    (a : A) (t : A ⊗[R] A) (x : A) :
    F.pairing.tensorEndEquiv ((a ⊗ₜ[R] 1) * t) x =
      F.pairing.tensorEndEquiv t (a * x) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [mul_zero, map_zero, LinearMap.zero_apply]
  | tmul u v => simp only [Algebra.TensorProduct.tmul_mul_tmul,
      mul_comm a u, one_mul, SymmetricPerfectPairing.tensorEndEquiv_tmul,
      pairing_apply, mul_assoc]
  | add t₁ t₂ h₁ h₂ => simp only [mul_add, map_add, LinearMap.add_apply, h₁, h₂]

/-- Multiplying the second tensor leg by `a` multiplies the output of the
associated endomorphism by `a`.-/
theorem tensorEndEquiv_includeRight_mul (F : CommFrobeniusAlgebra R A)
    (a : A) (t : A ⊗[R] A) (x : A) :
    F.pairing.tensorEndEquiv ((1 ⊗ₜ[R] a) * t) x =
      a * F.pairing.tensorEndEquiv t x := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [mul_zero, map_zero, LinearMap.zero_apply]
  | tmul u v => simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      mul_comm a, SymmetricPerfectPairing.tensorEndEquiv_tmul, pairing_apply,
      Algebra.smul_mul_assoc]
  | add t₁ t₂ h₁ h₂ =>
      simp only [mul_add, map_add, LinearMap.add_apply, h₁, h₂, mul_add]

/-- The Casimir tensor is balanced over the algebra:
`(a ⊗ 1) * C = (1 ⊗ a) * C`.

This tensor identity is the main computational form of invariance of the
Frobenius pairing.-/
theorem includeLeft_mul_casimir_eq_includeRight_mul_casimir
    (F : CommFrobeniusAlgebra R A) (a : A) :
    (a ⊗ₜ[R] 1) * F.casimir = (1 ⊗ₜ[R] a) * F.casimir := by
  apply F.pairing.tensorEndEquiv.injective
  apply LinearMap.ext
  intro x
  rw [F.tensorEndEquiv_includeLeft_mul, F.tensorEndEquiv_includeRight_mul]
  simp only [tensorEndEquiv_casimir, LinearMap.id_coe, id_eq]

/-- The canonical Frobenius comultiplication `Δ(a) = (a ⊗ 1) * C`.-/
noncomputable def comul (F : CommFrobeniusAlgebra R A) :
    A →ₗ[R] A ⊗[R] A :=
  (LinearMap.mulRight R F.casimir).comp
    (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toLinearMap

/-- Evaluation formula using the first leg of the Casimir tensor.-/
theorem comul_apply (F : CommFrobeniusAlgebra R A) (a : A) :
    F.comul a = (a ⊗ₜ[R] 1) * F.casimir := rfl

/-- Equivalent evaluation formula using the second leg.-/
theorem comul_apply_right (F : CommFrobeniusAlgebra R A) (a : A) :
    F.comul a = (1 ⊗ₜ[R] a) * F.casimir :=
  F.includeLeft_mul_casimir_eq_includeRight_mul_casimir a

/-- The Casimir tensor is the comultiplication of the algebra unit.-/
@[simp]
theorem comul_one (F : CommFrobeniusAlgebra R A) : F.comul 1 = F.casimir := by
  rw [comul_apply, ← Algebra.TensorProduct.one_def, one_mul]

/-- Contracting `Δ(a)` with the metric gives multiplication by `a`.-/
@[simp]
theorem tensorEndEquiv_comul (F : CommFrobeniusAlgebra R A) (a x : A) :
    F.pairing.tensorEndEquiv (F.comul a) x = a * x := by
  rw [comul_apply, F.tensorEndEquiv_includeLeft_mul]
  simp only [tensorEndEquiv_casimir, LinearMap.id_coe, id_eq]

/-- Left-linearity of comultiplication, one half of the Frobenius relation.-/
theorem comul_mul (F : CommFrobeniusAlgebra R A) (a b : A) :
    F.comul (a * b) = (a ⊗ₜ[R] 1) * F.comul b := by
  simp only [comul_apply]
  rw [← mul_assoc]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

/-- Right-linearity of comultiplication, the other half of the Frobenius
relation.-/
theorem comul_mul_right (F : CommFrobeniusAlgebra R A) (a b : A) :
    F.comul (a * b) = (1 ⊗ₜ[R] b) * F.comul a := by
  rw [comul_apply_right, comul_apply_right, ← mul_assoc]
  simp only [mul_comm, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

omit [Module.Free R A] [Module.Finite R A] in
/-- Swapping the tensor factors in a product swaps each factor.-/
theorem comm_mul_tmul_left (a : A) (t : A ⊗[R] A) :
    TensorProduct.comm R A A ((a ⊗ₜ[R] 1) * t) =
      (1 ⊗ₜ[R] a) * TensorProduct.comm R A A t := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [mul_zero, map_zero]
  | tmul u v => simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      comm_tmul]
  | add t₁ t₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂]

/-- The canonical Frobenius comultiplication is cocommutative.-/
@[simp]
theorem comm_comul (F : CommFrobeniusAlgebra R A) (a : A) :
    TensorProduct.comm R A A (F.comul a) = F.comul a := by
  rw [comul_apply, comm_mul_tmul_left]
  rw [show TensorProduct.comm R A A F.casimir = F.casimir by
    simpa only [casimir] using F.pairing.copairing_comm]
  exact (F.includeLeft_mul_casimir_eq_includeRight_mul_casimir a).symm

/-- Applying the left tensor unitor after contracting the first leg with the
counit is the same as contracting the tensor against `1` via the metric.-/
theorem lid_counit_rTensor (F : CommFrobeniusAlgebra R A) (t : A ⊗[R] A) :
    TensorProduct.lid R A (F.counit.rTensor A t) =
      F.pairing.tensorEndEquiv t 1 := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | tmul u v => simp only [LinearMap.rTensor_tmul, lid_tmul,
      SymmetricPerfectPairing.tensorEndEquiv_tmul, pairing_apply, mul_one]
  | add t₁ t₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]

/-- The first counit law, written in mathlib's explicit-unitor convention.-/
@[simp]
theorem rTensor_counit_comul (F : CommFrobeniusAlgebra R A) (a : A) :
    F.counit.rTensor A (F.comul a) = 1 ⊗ₜ[R] a := by
  apply (TensorProduct.lid R A).injective
  rw [F.lid_counit_rTensor]
  rw [F.tensorEndEquiv_comul]
  simp only [mul_one, lid_tmul, one_smul]

/-- Applying the right tensor unitor after contracting the second leg with the
counit can be computed by first swapping the tensor.-/
theorem rid_counit_lTensor (F : CommFrobeniusAlgebra R A) (t : A ⊗[R] A) :
    TensorProduct.rid R A (F.counit.lTensor A t) =
      F.pairing.tensorEndEquiv (TensorProduct.comm R A A t) 1 := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | tmul u v => simp only [LinearMap.lTensor_tmul, rid_tmul, comm_tmul,
      SymmetricPerfectPairing.tensorEndEquiv_tmul, pairing_apply, mul_one]
  | add t₁ t₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]

/-- The second counit law.-/
@[simp]
theorem lTensor_counit_comul (F : CommFrobeniusAlgebra R A) (a : A) :
    F.counit.lTensor A (F.comul a) = a ⊗ₜ[R] 1 := by
  apply (TensorProduct.rid R A).injective
  rw [F.rid_counit_lTensor, F.comm_comul]
  rw [F.tensorEndEquiv_comul]
  simp only [mul_one, rid_tmul, one_smul]

omit [Module.Free R A] [Module.Finite R A] in
/-- Multiplying a fixed element into the first tensor leg commutes with
multiplying the two tensor legs together.-/
theorem mul'_includeLeft_mul (a : A) (t : A ⊗[R] A) :
    LinearMap.mul' R A ((a ⊗ₜ[R] 1) * t) =
      a * LinearMap.mul' R A t := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [mul_zero, map_zero]
  | tmul u v => simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_comm,
      mul_one, LinearMap.mul'_apply, mul_left_comm]
  | add t₁ t₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂]

/-- Multiplication after comultiplication is multiplication by the handle
element: `μ(Δ(a)) = a * E`.-/
@[simp]
theorem mul'_comul (F : CommFrobeniusAlgebra R A) (a : A) :
    LinearMap.mul' R A (F.comul a) = a * F.handleElement := by
  rw [comul_apply, mul'_includeLeft_mul]
  rfl

/-! ## Coassociativity

To compare tensors with three factors, we use the same perfect pairing to
turn the first tensor factor into the input of a linear map.  This avoids a
basis calculation: the resulting map is an equivalence, so equality after
contraction proves equality of the original tensors.
-/

/-- Contract the first factor of `A ⊗ W`, for an arbitrary target module `W`.
The earlier `tensorEndEquiv` is the special case `W = A`.-/
noncomputable def tensorModuleHomEquiv (F : CommFrobeniusAlgebra R A)
    (W : Type*) [AddCommGroup W] [Module R W] :
    A ⊗[R] W ≃ₗ[R] A →ₗ[R] W :=
  (TensorProduct.congr F.pairing.toDual (LinearEquiv.refl R W)).trans
    (dualTensorHomEquiv R A W)

/-- Evaluation of `tensorModuleHomEquiv` on a pure tensor.-/
@[simp]
theorem tensorModuleHomEquiv_tmul (F : CommFrobeniusAlgebra R A)
    {W : Type*} [AddCommGroup W] [Module R W] (a x : A) (w : W) :
    F.tensorModuleHomEquiv W (a ⊗ₜ[R] w) x = F.pairing.form a x • w := by
  first
    | (all_goals grind; done)
    | (all_goals simp_all; done)
    | (all_goals aesop; done)
    | (all_goals omega; done)
    | (all_goals norm_num; done)
    | (all_goals positivity; done)
    | (all_goals linarith; done)
    | (all_goals decide; done)
    | (all_goals tauto; done)

/-- Contracting the first leg after reassociating `(A ⊗ A) ⊗ A` contracts the
first leg of the inner two-tensor.-/
theorem tensorModuleHomEquiv_assoc_tmul (F : CommFrobeniusAlgebra R A)
    (s : A ⊗[R] A) (q x : A) :
    F.tensorModuleHomEquiv (A ⊗[R] A)
        (TensorProduct.assoc R A A A (s ⊗ₜ[R] q)) x =
      F.pairing.tensorEndEquiv s x ⊗ₜ[R] q := by
  induction s using TensorProduct.induction_on with
  | zero => simp only [zero_tmul, map_zero, LinearMap.zero_apply]
  | tmul u v => simp only [assoc_tmul, tensorModuleHomEquiv_tmul,
      pairing_apply, smul_tmul', SymmetricPerfectPairing.tensorEndEquiv_tmul]
  | add s₁ s₂ h₁ h₂ =>
      simp only [add_tmul, map_add, LinearMap.add_apply, h₁, h₂]

/-- After applying `Δ` to the first tensor factor, contraction turns it into
multiplication by the contracted vector.-/
theorem tensorModuleHomEquiv_assoc_comul_rTensor
    (F : CommFrobeniusAlgebra R A) (t : A ⊗[R] A) (x : A) :
    F.tensorModuleHomEquiv (A ⊗[R] A)
        (TensorProduct.assoc R A A A (F.comul.rTensor A t)) x =
      (x ⊗ₜ[R] 1) * t := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply, mul_zero]
  | tmul p q =>
      rw [LinearMap.rTensor_tmul, F.tensorModuleHomEquiv_assoc_tmul]
      rw [F.tensorEndEquiv_comul]
      simp only [mul_comm, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | add t₁ t₂ h₁ h₂ =>
      simp only [map_add, LinearMap.add_apply, mul_add, h₁, h₂]

/-- After applying `Δ` to the second tensor factor, contraction may be moved
through `Δ` by linearity.-/
theorem tensorModuleHomEquiv_comul_lTensor
    (F : CommFrobeniusAlgebra R A) (t : A ⊗[R] A) (x : A) :
    F.tensorModuleHomEquiv (A ⊗[R] A) (F.comul.lTensor A t) x =
      F.comul (F.pairing.tensorEndEquiv t x) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | tmul p q => simp only [LinearMap.lTensor_tmul,
      tensorModuleHomEquiv_tmul, pairing_apply,
      SymmetricPerfectPairing.tensorEndEquiv_tmul, map_smul]
  | add t₁ t₂ h₁ h₂ =>
      simp only [map_add, LinearMap.add_apply, h₁, h₂]

/-- Pointwise coassociativity of the canonical comultiplication.-/
theorem coassoc_apply (F : CommFrobeniusAlgebra R A) (a : A) :
    TensorProduct.assoc R A A A (F.comul.rTensor A (F.comul a)) =
      F.comul.lTensor A (F.comul a) := by
  apply (F.tensorModuleHomEquiv (A ⊗[R] A)).injective
  apply LinearMap.ext
  intro x
  rw [F.tensorModuleHomEquiv_assoc_comul_rTensor,
    F.tensorModuleHomEquiv_comul_lTensor, F.tensorEndEquiv_comul]
  simpa only [mul_comm x a] using (F.comul_mul x a).symm

/-- Coassociativity as an equality of linear maps, in exactly the form required
by mathlib's `Coalgebra` structure.-/
theorem coassoc (F : CommFrobeniusAlgebra R A) :
    TensorProduct.assoc R A A A ∘ₗ F.comul.rTensor A ∘ₗ F.comul =
      F.comul.lTensor A ∘ₗ F.comul := by
  ext a
  exact F.coassoc_apply a

/-! ## Interoperability with mathlib's coalgebra API -/

/-- The comultiplication and original Frobenius functional, bundled as
mathlib's preliminary `CoalgebraStruct`.-/
@[reducible]
noncomputable def toCoalgebraStruct (F : CommFrobeniusAlgebra R A) :
    CoalgebraStruct R A where
  comul := F.comul
  counit := F.counit

/-- A finite-free commutative Frobenius algebra canonically determines a
coalgebra.

This is an explicit definition rather than a global instance.  To use
mathlib's coalgebra notation and lemmas locally, write

```lean
letI : Coalgebra R A := F.toCoalgebra
```-/
@[reducible]
noncomputable def toCoalgebra (F : CommFrobeniusAlgebra R A) :
    Coalgebra R A where
  comul := F.comul
  counit := F.counit
  coassoc := F.coassoc
  rTensor_counit_comp_comul := by
    ext a
    exact F.rTensor_counit_comul a
  lTensor_counit_comp_comul := by
    ext a
    exact F.lTensor_counit_comul a

/-- The coalgebra obtained from a commutative Frobenius algebra is
cocommutative.

This declaration is designed for local use immediately after installing
`F.toCoalgebra`.-/
theorem toIsCocomm (F : CommFrobeniusAlgebra R A) :
    letI : Coalgebra R A := F.toCoalgebra
    Coalgebra.IsCocomm R A := by
  letI : Coalgebra R A := F.toCoalgebra
  constructor
  change (TensorProduct.comm R A A).comp F.comul = F.comul
  ext a
  exact F.comm_comul a

end CommFrobeniusAlgebra

end AxiomaticGW
