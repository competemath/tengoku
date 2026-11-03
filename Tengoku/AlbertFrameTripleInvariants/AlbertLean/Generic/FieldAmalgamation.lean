import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FieldPointNilpotence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms exists_common_field` (it only prints; the queue checks the axioms of every declaration). -/

/-! Embed two extensions of a common field into a further common field.
The construction is used to compare a normalized Albert chart at two field
points; it does not specialize arbitrary rational functions. -/

noncomputable section
open scoped TensorProduct

namespace AlbertLean.Generic.FieldAmalgamation

universe u

/-- Two field extensions of a common field embed in another common field.
No algebraicity, algebraic closure, or tensor-domain hypothesis is required.
The tensor product need only be nontrivial; its maximal quotient is a field.
@isnad1 id=ex.0h5v.s8.defdf73fff53 from=translated src=- shape=b6b436cb vocab=cd79d1fa
-/
theorem exists_common_field
    {F L N : Type u} [Field F] [Field L] [Field N]
    (leftBase : F →+* L) (rightBase : F →+* N) :
    ∃ (E : Type u) (_ : Field E) (left : L →+* E) (right : N →+* E),
      Function.Injective left ∧ Function.Injective right ∧
        left.comp leftBase = right.comp rightBase := by
  letI : Algebra F L := leftBase.toAlgebra
  letI : Algebra F N := rightBase.toAlgebra
  let T := L ⊗[F] N
  let c : T →ₗ[F] L :=
    (TensorProduct.rid F L).toLinearMap.comp
      (TensorProduct.map LinearMap.id
        (TensorDifferenceAlgebraicity.scalarRetraction F N))
  have hc : c 1 = 1 := by
    change (TensorProduct.rid F L)
      ((TensorProduct.map (LinearMap.id : L →ₗ[F] L)
        (TensorDifferenceAlgebraicity.scalarRetraction F N))
          ((1 : L) ⊗ₜ[F] (1 : N))) = 1
    rw [TensorProduct.map_tmul]
    simp only [LinearMap.id_apply,
      TensorDifferenceAlgebraicity.scalarRetraction_one,
      TensorProduct.rid_tmul, one_smul]
  letI : Nontrivial T := ⟨⟨1, 0, by
    intro h
    have hz := congrArg c h
    rw [hc, map_zero] at hz
    exact one_ne_zero hz⟩⟩
  obtain ⟨m, hm⟩ := Ideal.exists_maximal T
  letI : m.IsMaximal := hm
  let E := T ⧸ m
  letI : Field E := Ideal.Quotient.field m
  let q : T →+* E := Ideal.Quotient.mk m
  let il : L →ₐ[F] T := Algebra.TensorProduct.includeLeft (S := F)
  let ir : N →ₐ[F] T := Algebra.TensorProduct.includeRight
  let left : L →+* E := q.comp il.toRingHom
  let right : N →+* E := q.comp ir.toRingHom
  refine ⟨E, inferInstance, left, right, left.injective, right.injective, ?_⟩
  ext x
  change q (il (algebraMap F L x)) = q (ir (algebraMap F N x))
  rw [il.commutes, ir.commutes]

end AlbertLean.Generic.FieldAmalgamation
