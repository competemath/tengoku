/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Equivalences for modules associated to representations

This module gives direct-sum, equivariant-map, and tensor-product equivalences for modules
associated to representations.
-/

open scoped TensorProduct DirectSum

namespace RepresentationTheory.AsModuleEquivalences

section DirectSumAsModule

variable {k G : Type*} [CommSemiring k] [Monoid G]
variable {ι : Type*} {V : ι → Type*}
variable [(i : ι) → AddCommMonoid (V i)] [(i : ι) → Module k (V i)]

end DirectSumAsModule

section Intertwiner

variable {k G : Type*} [CommSemiring k] [Monoid G]
variable {V W : Type*} [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]

end Intertwiner

section TrivialTprodSplit

open scoped TensorProduct
open TensorProduct

variable {k G S W : Type*} [CommRing k] [Monoid G]
variable [AddCommGroup S] [Module k S] [AddCommGroup W] [Module k W]
variable {β : Type*} [Fintype β] [DecidableEq β]

/-- Provides the basis-indexed linear equivalence from a tensor product to a direct sum.-/
noncomputable def tensorProductToDirectSum (b : Module.Basis β k S) :
    S ⊗[k] W ≃ₗ[k] DirectSum β (fun _ => W) :=
  TensorProduct.congr b.repr (LinearEquiv.refl k W) ≪≫ₗ
    TensorProduct.finsuppScalarLeft k W β ≪≫ₗ
      Finsupp.linearEquivFunOnFinite k W β ≪≫ₗ
        (DirectSum.linearEquivFunOnFintype k β (fun _ => W)).symm

/-- Describes the direct-sum coordinates of a pure tensor using the chosen basis coefficients.
@isnad1 id=eq.0h7v.s10.7ccabb0f4ed2 from=translated src=- shape=6896b607 vocab=f8b4ad92
-/
theorem tensorProductToDirectSum_tmul (b : Module.Basis β k S) (s : S) (w : W) :
    (DirectSum.linearEquivFunOnFintype k β (fun _ => W))
        (tensorProductToDirectSum (W := W) b (s ⊗ₜ[k] w)) =
      fun i => b.repr s i • w := by
  simp only [tensorProductToDirectSum, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply]
  funext i
  simp [Finsupp.linearEquivFunOnFinite_apply, TensorProduct.finsuppScalarLeft_apply_tmul_apply]

/-- Evaluating the image of a pure tensor at an index gives the corresponding basis coefficient times its second factor.
@isnad1 id=eq.0h8v.s9.afd97d455717 from=translated src=- shape=fd881906 vocab=ec6ca7ba
-/
@[simp] theorem tensorProductToDirectSum_tmul_apply
    (b : Module.Basis β k S) (s : S) (w : W) (i : β) :
    tensorProductToDirectSum (W := W) b (s ⊗ₜ[k] w) i = b.repr s i • w := by
  have := congrFun (tensorProductToDirectSum_tmul b s w) i
  simpa using this

end TrivialTprodSplit

end RepresentationTheory.AsModuleEquivalences
