/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.Seed.FieldTheory.AlgebraicClosure
import Tengoku.Seed.FieldTheory.IsAlgClosed.Basic
import Tengoku.Seed.FieldTheory.IsAlgClosed.AlgebraicClosure
import Tengoku.Seed.FieldTheory.IntermediateField.Adjoin.Basic
import Tengoku.Seed.RingTheory.Flat.Domain
import Tengoku.Seed.RingTheory.TensorProduct.Finite
import Tengoku.Seed.LinearAlgebra.Dimension.Constructions
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Affine.Point

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The constant field of an elliptic curve function field

The keystone bridge (issue #434):  if the base change of a field extension `E / F` to the
algebraic closure `AlgebraicClosure F` is a domain, then `F` is relatively algebraically closed in
`E`, i.e. `algebraicClosure F E = ⊥`.

## Main results

* `algebraicClosure_eq_bot_of_isDomain_tensor` — the field-theoretic keystone: geometric
  integrality (`IsDomain (AlgebraicClosure F ⊗[F] E)`) forces `algebraicClosure F E = ⊥`.
* `WeierstrassCurve.Affine.algebraicClosure_functionField_eq_bot_of_isDomain_tensor` — the keystone
  specialised to the function field `F(W)` of a Weierstrass curve, delivering the exact `halg`
  hypothesis (`algebraicClosure F W.FunctionField = ⊥`) carried by `WeilPairingConstant.lean`
  (PR #162), conditional on the geometric-integrality datum
  `IsDomain (AlgebraicClosure F ⊗[F] W.FunctionField)`.

## The geometric-integrality hypothesis is discharged elsewhere — it is not open

⚠️ This section used to be headed *"Remaining for #434"* and to call the discharge of
`IsDomain (AlgebraicClosure F ⊗[F] W.FunctionField)` *"the remaining, heavier follow-on"*.  **It is
merged**, by exactly the route named here: `WeierstrassCurve.Affine.isDomain_tensor_functionField`
(`EllipticCurves/FunctionField/ConstantFieldDomain.lean`) obtains it from
`WeierstrassCurve.Affine.irreducible_polynomial` over the algebraically closed base — the
Weierstrass polynomial stays irreducible, so `F̄ ⊗ F[W]` is a domain and `F̄ ⊗ F(W)` is a
localisation of it — and it is registered as an **instance**, so the two results this file states
are available unconditionally there, as
`WeierstrassCurve.Affine.algebraicClosure_functionField_eq_bot`.  The
`halg`-consuming lemmas of `WeilPairingConstant.lean` were made unconditional at the same time and
carry no residual constant-field hypothesis.

The conditional forms are kept here deliberately: they are the general field-theoretic statement
(`algebraicClosure_eq_bot_of_isDomain_tensor` is about an arbitrary extension `E / F`) and this file
must stay upstream of the tensor/localisation machinery that discharges the datum.
-/

open scoped TensorProduct IntermediateField

/-- **The keystone bridge.**  If the base change of `E / F` to `AlgebraicClosure F` is a domain,
then `F` is relatively algebraically closed in `E`: `algebraicClosure F E = ⊥`.

The proof takes an algebraic `z ∈ E`, forms the finite subextension `L := F⟮z⟯`, and base changes
to `F̄ := AlgebraicClosure F`.  The inclusion `L ↪ E` tensors (over the flat/free `F̄`) to an
injection `F̄ ⊗ L ↪ F̄ ⊗ E`, so `F̄ ⊗ L` is a domain.  Being finite over the algebraically closed
`F̄`, it is integral, hence `algebraMap F̄ (F̄ ⊗ L)` is bijective and `finrank F̄ (F̄ ⊗ L) = 1`.
Base change preserves finrank, so `finrank F L = 1`, forcing `L = ⊥` and `z ∈ F`. -/
theorem algebraicClosure_eq_bot_of_isDomain_tensor
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (hdom : IsDomain (AlgebraicClosure F ⊗[F] E)) :
    algebraicClosure F E = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [mem_algebraicClosure_iff] at hx
  have hint : IsIntegral F x := hx.isIntegral
  set L := F⟮x⟯ with hL
  haveI : FiniteDimensional F L := IntermediateField.adjoin.finiteDimensional hint
  -- the inclusion `L ↪ E` and its base change to `F̄ = AlgebraicClosure F`
  let φ : L →ₐ[F] E := L.val
  have hφinj : Function.Injective φ := L.val.injective
  let Φ : (AlgebraicClosure F ⊗[F] L) →ₐ[AlgebraicClosure F] (AlgebraicClosure F ⊗[F] E) :=
    Algebra.TensorProduct.map (AlgHom.id (AlgebraicClosure F) (AlgebraicClosure F)) φ
  have hΦinj : Function.Injective Φ :=
    Module.Flat.lTensor_preserves_injective_linearMap φ.toLinearMap hφinj
  haveI : IsDomain (AlgebraicClosure F ⊗[F] L) := Function.Injective.isDomain Φ.toRingHom hΦinj
  -- `F̄ ⊗ L` is finite over the algebraically closed `F̄`, hence integral, hence `finrank = 1`
  have hbij : Function.Bijective
      (algebraMap (AlgebraicClosure F) (AlgebraicClosure F ⊗[F] L)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  have hrank1 : Module.finrank (AlgebraicClosure F) (AlgebraicClosure F ⊗[F] L) = 1 := by
    rw [← (AlgEquiv.ofBijective (Algebra.ofId (AlgebraicClosure F) (AlgebraicClosure F ⊗[F] L))
      hbij).toLinearEquiv.finrank_eq, Module.finrank_self]
  have hfin : Module.finrank F L = 1 := by
    rw [← Module.finrank_baseChange (R := AlgebraicClosure F) (S := F) (M' := L)]
    exact hrank1
  have hLbot : L = ⊥ := IntermediateField.finrank_eq_one_iff.mp hfin
  rw [hL] at hLbot
  exact IntermediateField.adjoin_simple_eq_bot_iff.mp hLbot

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F}

/-- **The constant field of a Weierstrass function field (conditional form).**  Specialises the
keystone bridge `algebraicClosure_eq_bot_of_isDomain_tensor` to `E = W.FunctionField`: given the
geometric-integrality datum `IsDomain (AlgebraicClosure F ⊗[F] W.FunctionField)`, the base field `F`
is relatively algebraically closed in `F(W)`.  This is exactly the `halg` hypothesis carried by
`WeilPairingConstant.lean` (PR #162); supplying it makes the Weil-pairing element's constancy and
translation-slot bilinearity unconditional. -/
theorem algebraicClosure_functionField_eq_bot_of_isDomain_tensor
    (hdom : IsDomain (AlgebraicClosure F ⊗[F] W.FunctionField)) :
    algebraicClosure F W.FunctionField = ⊥ :=
  algebraicClosure_eq_bot_of_isDomain_tensor hdom

end WeierstrassCurve.Affine
