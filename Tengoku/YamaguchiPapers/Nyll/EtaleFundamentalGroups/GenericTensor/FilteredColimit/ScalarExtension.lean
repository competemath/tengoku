/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.Algebra.Algebra.Equiv
import Tengoku.Seed.RingTheory.TensorProduct.Basic
import Tengoku.Seed.RingTheory.TensorProduct.Maps

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Scalar extension of tensor equivalences with literal compatibility

The tensor universal property extends a map along an actual coefficient
algebra homomorphism. The same construction on its inverse produces the
extended equivalence. Both compatibility squares with a later coefficient
algebra are retained. No additional algebra structure between the two
coefficient rings is installed.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe u

private theorem tensorAlgHom_tmul
    {K E B X : Type u} [CommRing K] [CommRing E] [CommRing B] [CommRing X]
    [Algebra K E] [Algebra K B] [Algebra E X]
    (f : (E ⊗[K] B) →ₐ[E] X) (e : E) (b : B) :
    f (e ⊗ₜ[K] b) = e • f ((1 : E) ⊗ₜ[K] b) := by
  calc
    f (e ⊗ₜ[K] b) = f (e • ((1 : E) ⊗ₜ[K] b)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    _ = e • f ((1 : E) ⊗ₜ[K] b) := f.toLinearMap.map_smul e _

private theorem tensorMap_smul
    {K E T B : Type u} [CommRing K] [CommRing E] [CommRing T] [CommRing B]
    [Algebra K E] [Algebra K T] [Algebra K B]
    (η : E →ₐ[K] T) (e : E) (x : E ⊗[K] B) :
    Algebra.TensorProduct.map η (AlgHom.id K B) (e • x) =
      η e • Algebra.TensorProduct.map η (AlgHom.id K B) x := by
  rw [Algebra.smul_def, map_mul, Algebra.smul_def]
  change Algebra.TensorProduct.map η (AlgHom.id K B) (e ⊗ₜ[K] (1 : B)) *
      Algebra.TensorProduct.map η (AlgHom.id K B) x =
    (η e ⊗ₜ[K] (1 : B)) * Algebra.TensorProduct.map η (AlgHom.id K B) x
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

variable {K E T B D : Type u}
  [CommRing K] [CommRing E] [CommRing T] [CommRing B] [CommRing D]
  [Algebra K E] [Algebra K T] [Algebra K B] [Algebra K D]

/-- Extend a tensor-algebra morphism along the specified coefficient map,
using the actual tensor universal property.-/
def tensorScalarExtendAlgHom (η : E →ₐ[K] T)
    (f : (E ⊗[K] B) →ₐ[E] (E ⊗[K] D)) :
    (T ⊗[K] B) →ₐ[T] (T ⊗[K] D) :=
  AlgHom.liftEquiv K T B (T ⊗[K] D)
    ((Algebra.TensorProduct.map η (AlgHom.id K D)).comp
      ((f.restrictScalars K).comp Algebra.TensorProduct.includeRight))

/-- The extended map has its specified value on every pure tensor.-/
theorem tensorScalarExtendAlgHom_tmul (η : E →ₐ[K] T)
    (f : (E ⊗[K] B) →ₐ[E] (E ⊗[K] D)) (t : T) (b : B) :
    tensorScalarExtendAlgHom η f (t ⊗ₜ[K] b) =
      t • Algebra.TensorProduct.map η (AlgHom.id K D) (f ((1 : E) ⊗ₜ[K] b)) := by
  exact AlgHom.liftEquiv_tmul _ t b

/-- A literal forward compatibility square survives extension of scalars.-/
theorem tensorScalarExtendAlgHom_square
    {F : Type u} [CommRing F] [Algebra K F]
    (η : E →ₐ[K] T) (σ : T →ₐ[K] F)
    (f : (E ⊗[K] B) →ₐ[E] (E ⊗[K] D))
    (g : (F ⊗[K] B) →ₐ[F] (F ⊗[K] D))
    (h : (Algebra.TensorProduct.map (σ.comp η) (AlgHom.id K D)).comp
        (f.restrictScalars K) = (g.restrictScalars K).comp
          (Algebra.TensorProduct.map (σ.comp η) (AlgHom.id K B))) :
    (Algebra.TensorProduct.map σ (AlgHom.id K D)).comp
        ((tensorScalarExtendAlgHom η f).restrictScalars K) =
      (g.restrictScalars K).comp (Algebra.TensorProduct.map σ (AlgHom.id K B)) := by
  apply Algebra.TensorProduct.ext'
  intro t b
  have h₁ := AlgHom.congr_fun h ((1 : E) ⊗ₜ[K] b)
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply] at h₁
  change Algebra.TensorProduct.map σ (AlgHom.id K D)
    (tensorScalarExtendAlgHom η f (t ⊗ₜ[K] b)) =
      g (Algebra.TensorProduct.map σ (AlgHom.id K B) (t ⊗ₜ[K] b))
  rw [tensorScalarExtendAlgHom_tmul, tensorMap_smul,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, tensorAlgHom_tmul g]
  apply congrArg (fun x => σ t • x)
  calc
    Algebra.TensorProduct.map σ (AlgHom.id K D)
        (Algebra.TensorProduct.map η (AlgHom.id K D) (f ((1 : E) ⊗ₜ[K] b))) =
      Algebra.TensorProduct.map (σ.comp η) (AlgHom.id K D)
        (f ((1 : E) ⊗ₜ[K] b)) := by
          rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.id_comp]
    _ = g ((1 : F) ⊗ₜ[K] b) := h₁

end EtaleFundamentalGroups
