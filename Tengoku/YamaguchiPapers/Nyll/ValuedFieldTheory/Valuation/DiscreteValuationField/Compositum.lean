/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.Algebra.Algebra.Subalgebra.Lattice
import Tengoku.Seed.FieldTheory.IntermediateField.Adjoin.Basic
import Tengoku.Seed.FieldTheory.Relrank
import Tengoku.Seed.FieldTheory.LinearDisjoint
import Tengoku.Seed.FieldTheory.SeparableClosure
import Tengoku.Seed.RingTheory.Ideal.Quotient.Operations
import Tengoku.Seed.RingTheory.Unramified.Field
import Tengoku.Seed.RingTheory.TensorProduct.Finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Field-theoretic composita for finite valued extensions

The actual common-top part of Abhyankar's lemma needs valuation data on the
compositum `L ⊔ K'` inside a common ambient field.  This file records the
purely field-theoretic source facts before any valuation extension is added:
finite-dimensionality over either branch, degree bounds and equalities, the
intersection degree square, and separability of the common top.
-/

noncomputable section

universe u v

namespace DiscreteValuationField
namespace FieldCompositum

open scoped TensorProduct

variable {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]

instance supRightAlgebra (L K' : IntermediateField K Ω) :
    Algebra K' (L ⊔ K' : IntermediateField K Ω) :=
  (IntermediateField.inclusion (show K' ≤ L ⊔ K' from le_sup_right)).toAlgebra

instance supLeftAlgebra (L K' : IntermediateField K Ω) :
    Algebra L (L ⊔ K' : IntermediateField K Ω) :=
  (IntermediateField.inclusion (show L ≤ L ⊔ K' from le_sup_left)).toAlgebra

/-- The field-level product map `K' ⊗_K L -> Ω` has image exactly the
compositum subalgebra `L ⊔ K'`.  This is the order matching the later
valuation-ring tensor product `O_K' ⊗_{O_K} O_L`.-/
theorem sup_flip_productMap_range
    (L K' : IntermediateField K Ω) [FiniteDimensional K L] :
    (Algebra.TensorProduct.productMap K'.val L.val).range =
      (L ⊔ K').toSubalgebra := by
  rw [Algebra.TensorProduct.productMap_range, K'.range_val, L.range_val,
    ← IntermediateField.sup_toSubalgebra_of_right (E1 := K') (E2 := L),
    sup_comm]

/-- Every element of the compositum is represented by a tensor under the
field-level product map `K' ⊗_K L -> Ω`, in the order matching the valuation
ring tensor product.-/
theorem exists_flip_tensor_productMap_eq_of_mem_sup
    (L K' : IntermediateField K Ω) [FiniteDimensional K L]
    {x : Ω} (hx : x ∈ (L ⊔ K' : IntermediateField K Ω)) :
    ∃ z : K' ⊗[K] L, Algebra.TensorProduct.productMap K'.val L.val z = x := by
  have hmem :
      x ∈ (Algebra.TensorProduct.productMap K'.val L.val).range := by
    rw [sup_flip_productMap_range (K := K) (Ω := Ω) L K']
    exact hx
  rcases hmem with ⟨z, hz⟩
  exact ⟨z, hz⟩

/-- The product map `K' ⊗_K L -> L ⊔ K'` agrees with the ambient product map
after coercing the target back to `Ω`.-/
theorem sup_flip_productMap_val_comp
    (L K' : IntermediateField K Ω) :
    (L ⊔ K').val.comp
        (Algebra.TensorProduct.productMap
          (IntermediateField.inclusion (show K' ≤ L ⊔ K' from le_sup_right))
          (IntermediateField.inclusion (show L ≤ L ⊔ K' from le_sup_left))) =
        Algebra.TensorProduct.productMap K'.val L.val := by
    apply Algebra.TensorProduct.ext
    · ext a
      rfl
    · ext b
      rfl

/-- Every element of the compositum subtype is represented by a tensor under
the intrinsic product map `K' ⊗_K L -> L ⊔ K'`.-/
theorem exists_sup_flip_tensor_productMap_eq
    (L K' : IntermediateField K Ω) [FiniteDimensional K L]
    (x : (L ⊔ K' : IntermediateField K Ω)) :
    ∃ z : K' ⊗[K] L,
      Algebra.TensorProduct.productMap
          (IntermediateField.inclusion (show K' ≤ L ⊔ K' from le_sup_right))
          (IntermediateField.inclusion (show L ≤ L ⊔ K' from le_sup_left)) z =
        x := by
  rcases exists_flip_tensor_productMap_eq_of_mem_sup
      (K := K) (Ω := Ω) L K' x.2 with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  apply Subtype.ext
  rw [← hz]
  exact congrArg (fun f => f z)
    (sup_flip_productMap_val_comp (K := K) (Ω := Ω) L K')

/-- The intrinsic field-level product map `K' ⊗_K L -> L ⊔ K'` is
surjective.  This is the source form aligned with the valuation-ring tensor
map used in the unramified base-change construction.-/
theorem sup_flip_productMap_surjective
    (L K' : IntermediateField K Ω) [FiniteDimensional K L] :
    Function.Surjective
      (Algebra.TensorProduct.productMap
        (IntermediateField.inclusion (show K' ≤ L ⊔ K' from le_sup_right))
        (IntermediateField.inclusion (show L ≤ L ⊔ K' from le_sup_left))) := by
  intro x
  exact exists_sup_flip_tensor_productMap_eq (K := K) (Ω := Ω) L K' x

/-- The intrinsic product map `K' ⊗_K L -> L ⊔ K'`, regarded as a
`K'`-algebra hom.  This is the field-level base-change map used in the
the unramified base-change theorem; no separability of `K'/K` is involved.-/
noncomputable def supFlipProductMapRightAlgHom
    (L K' : IntermediateField K Ω) :
    K' ⊗[K] L →ₐ[K'] (L ⊔ K' : IntermediateField K Ω) :=
  AlgHom.mk'
    (Algebra.TensorProduct.productMap
      (IntermediateField.inclusion (show K' ≤ L ⊔ K' from le_sup_right))
      (IntermediateField.inclusion (show L ≤ L ⊔ K' from le_sup_left))).toRingHom
    (by
      intro c x
      simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra])

/-- The `K'`-algebra product map `K' ⊗_K L -> L ⊔ K'` is surjective.-/
theorem supFlipProductMapRightAlgHom_surjective
    (L K' : IntermediateField K Ω) [FiniteDimensional K L] :
    Function.Surjective
      (supFlipProductMapRightAlgHom (K := K) (Ω := Ω) L K') := by
  simpa [supFlipProductMapRightAlgHom] using
    sup_flip_productMap_surjective (K := K) (Ω := Ω) L K'

/-- The actual compositum `L ⊔ K'` is finite over the right factor whenever
the left factor is finite over the base.

This is the finite-dimensional source needed for unramified base change:
base change by an arbitrary algebraic extension is reduced elementwise to a
finite right subextension, but the finiteness of the right branch itself comes
from the finite left factor.-/
theorem finiteDimensional_sup_over_right_of_left
    (L K' : IntermediateField K Ω) [FiniteDimensional K L] :
    FiniteDimensional K' (L ⊔ K' : IntermediateField K Ω) := by
  exact
    FiniteDimensional.of_surjective
      (supFlipProductMapRightAlgHom (K := K) (Ω := Ω) L K').toLinearMap
      (supFlipProductMapRightAlgHom_surjective (K := K) (Ω := Ω) L K')

/-- The algebraic first-isomorphism theorem with the source ring structure
fixed by its commutative-ring parent.-/
local instance tensorProductIdealHasQuotient
    (L K' : IntermediateField K Ω) :
    HasQuotient (K' ⊗[K] L) (Ideal (K' ⊗[K] L)) :=
  @Ideal.instHasQuotient (K' ⊗[K] L)
    (inferInstance : CommRing (K' ⊗[K] L)).toRing

private noncomputable def quotientKerAlgEquivOfSurjectiveCommRing
    {R A B : Type*}
    [ringR : CommSemiring R] [ringA : CommRing A]
    [algebraRA : Algebra R A]
    [ringB : Semiring B] [algebraRB : Algebra R B]
    {f : A →ₐ[R] B} (hf : Function.Surjective f) :
    (@HasQuotient.Quotient A (Ideal A)
      (@Ideal.instHasQuotient A ringA.toRing)
      (RingHom.ker f.toRingHom)) ≃ₐ[R] B :=
  Ideal.quotientKerAlgEquivOfSurjective hf

/-- The field factor selected by the product map `K' ⊗_K L -> L ⊔ K'` is
the actual compositum field: quotienting by the kernel of the surjective
`K'`-algebra map gives `L ⊔ K'`.-/
noncomputable def supFlipProductMapRightAlgHomQuotientKerAlgEquiv
    (L K' : IntermediateField K Ω) [FiniteDimensional K L] :
    ((K' ⊗[K] L) ⧸
        (RingHom.ker
          (supFlipProductMapRightAlgHom (K := K) (Ω := Ω) L K').toRingHom))
      ≃ₐ[K'] (L ⊔ K' : IntermediateField K Ω) :=
  let f : K' ⊗[K] L →ₐ[K'] (L ⊔ K' : IntermediateField K Ω) :=
    supFlipProductMapRightAlgHom (K := K) (Ω := Ω) L K'
  have hf : Function.Surjective f :=
    supFlipProductMapRightAlgHom_surjective (K := K) (Ω := Ω) L K'
  quotientKerAlgEquivOfSurjectiveCommRing
    (R := K') (A := K' ⊗[K] L)
    (B := (L ⊔ K' : IntermediateField K Ω))
    (ringR := (inferInstance : CommSemiring K'))
    (ringA := (inferInstance : CommRing (K' ⊗[K] L)))
    (algebraRA := (inferInstance : Algebra K' (K' ⊗[K] L)))
    (ringB := (inferInstance : Semiring (L ⊔ K' : IntermediateField K Ω)))
    (algebraRB := (inferInstance : Algebra K' (L ⊔ K' : IntermediateField K Ω)))
    (f := f) hf

end FieldCompositum
end DiscreteValuationField

end
