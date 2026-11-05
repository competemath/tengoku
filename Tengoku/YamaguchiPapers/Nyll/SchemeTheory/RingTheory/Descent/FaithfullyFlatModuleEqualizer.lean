/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Tengoku.Seed.RingTheory.TensorProduct.IncludeLeftSubRight

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The module equalizer for faithfully flat base change

This file develops the degree-zero part of faithfully flat descent for
modules.  The first step is the split case: if an algebra admits an algebra
section, then the usual Amitsur pair remains exact after tensoring with an
arbitrary module.
-/

@[expose] public noncomputable section

namespace EtaleFundamentalGroups

open scoped TensorProduct

universe u v w

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]

/-- The contraction of `S ⊗[R] M` induced by an algebra section `S →ₐ[R] R`.-/
private def tensorProductCounitOfSection (g : S →ₐ[R] R) :
    S ⊗[R] M →ₗ[R] M :=
  (TensorProduct.lid R M).toLinearMap ∘ₗ
    TensorProduct.map g.toLinearMap (LinearMap.id : M →ₗ[R] M)

@[simp]
private theorem tensorProductCounitOfSection_tmul
    (g : S →ₐ[R] R) (s : S) (m : M) :
    tensorProductCounitOfSection g (s ⊗ₜ[R] m) = g s • m := by
  simp [tensorProductCounitOfSection]

/-- Apply an algebra section to the first algebra factor of
`(S ⊗[R] S) ⊗[R] M`.-/
private def tensorProductFirstCounitOfSection (g : S →ₐ[R] R) :
    (S ⊗[R] S) ⊗[R] M →ₗ[R] S ⊗[R] M :=
  ((TensorProduct.lid R S).toLinearMap ∘ₗ
      TensorProduct.map g.toLinearMap (LinearMap.id : S →ₗ[R] S)).rTensor M

@[simp]
private theorem tensorProductFirstCounitOfSection_tmul
    (g : S →ₐ[R] R) (s t : S) (m : M) :
    tensorProductFirstCounitOfSection g ((s ⊗ₜ[R] t) ⊗ₜ[R] m) =
      (g s • t) ⊗ₜ[R] m := by
  simp [tensorProductFirstCounitOfSection]

/-- Multiplication of the two algebra factors after base change.-/
private def tensorProductBaseChangeCounit :
    S ⊗[R] (S ⊗[R] M) →ₗ[R] S ⊗[R] M :=
  ((Algebra.TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S).toLinearMap.rTensor M) ∘ₗ
    (TensorProduct.assoc R S S M).symm.toLinearMap

@[simp]
private theorem tensorProductBaseChangeCounit_tmul
    (a s : S) (m : M) :
    tensorProductBaseChangeCounit (a ⊗ₜ[R] (s ⊗ₜ[R] m)) =
      (a * s) ⊗ₜ[R] m := by
  simp [tensorProductBaseChangeCounit]

/-- Multiply the first two algebra factors in
`S ⊗ ((S ⊗ S) ⊗ M)`, leaving the third algebra factor untouched.-/
private def tensorProductBaseChangeFirstMultiplication :
    S ⊗[R] ((S ⊗[R] S) ⊗[R] M) →ₗ[R] S ⊗[R] (S ⊗[R] M) :=
  (TensorProduct.assoc R S S M).toLinearMap ∘ₗ
    ((((Algebra.TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S).toLinearMap.rTensor S) ∘ₗ
      (TensorProduct.assoc R S S S).symm.toLinearMap).rTensor M) ∘ₗ
    (TensorProduct.assoc R S (S ⊗[R] S) M).symm.toLinearMap

@[simp]
private theorem tensorProductBaseChangeFirstMultiplication_tmul
    (a s t : S) (m : M) :
    tensorProductBaseChangeFirstMultiplication
        (a ⊗ₜ[R] ((s ⊗ₜ[R] t) ⊗ₜ[R] m)) =
      (a * s) ⊗ₜ[R] (t ⊗ₜ[R] m) := by
  simp [tensorProductBaseChangeFirstMultiplication]

/-- Pull an extended module back along the left projection
`S ⇉ S ⊗[R] S`.-/
def tensorProductDescentLeft :
    S ⊗[R] M →ₗ[R] (S ⊗[R] S) ⊗[R] M :=
  (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S).toLinearMap.rTensor M

/-- Pull an extended module back along the right projection
`S ⇉ S ⊗[R] S`.-/
def tensorProductDescentRight :
    S ⊗[R] M →ₗ[R] (S ⊗[R] S) ⊗[R] M :=
  (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S).toLinearMap.rTensor M

@[simp]
theorem tensorProductDescentLeft_tmul (s : S) (m : M) :
    tensorProductDescentLeft (s ⊗ₜ[R] m) =
      (s ⊗ₜ[R] 1) ⊗ₜ[R] m :=
  rfl

@[simp]
theorem tensorProductDescentRight_tmul (s : S) (m : M) :
    tensorProductDescentRight (s ⊗ₜ[R] m) =
      (1 ⊗ₜ[R] s) ⊗ₜ[R] m :=
  rfl

/-- The canonical map from an `R`-module to the equalizer of its two
pullbacks from `S` to `S ⊗[R] S`.-/
def tensorProductEqualizerMap :
    M →ₗ[R] LinearMap.eqLocus
      (tensorProductDescentLeft (R := R) (S := S) (M := M))
      (tensorProductDescentRight (R := R) (S := S) (M := M)) :=
  LinearMap.codRestrict _ (TensorProduct.mk R S M 1) (by
    intro m
    simp [tensorProductDescentLeft, tensorProductDescentRight])

@[simp]
theorem tensorProductEqualizerMap_coe (m : M) :
    (tensorProductEqualizerMap (R := R) (S := S) (M := M) m : S ⊗[R] M) =
      1 ⊗ₜ[R] m :=
  rfl

end EtaleFundamentalGroups

end
