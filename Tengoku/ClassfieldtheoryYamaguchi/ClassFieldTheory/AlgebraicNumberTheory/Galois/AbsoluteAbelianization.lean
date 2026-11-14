/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.FieldTheory.Galois.Abelian
import Tengoku.Seed.FieldTheory.Galois.Profinite
import Tengoku.Seed.FieldTheory.IsSepClosed
import Tengoku.Seed.Topology.Algebra.Group.TopologicalAbelianization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.ClassfieldtheoryYamaguchi end Tengoku.ClassfieldtheoryYamaguchi open Tengoku.ClassfieldtheoryYamaguchi
set_option autoImplicit false

/-!
# Absolute abelianization inside the separable closure

For an arbitrary field, this module identifies the topological abelianization
of the Galois group of its separable closure with the Galois group of the
maximal abelian subextension.  Working inside the separable closure makes the
construction uniform in every characteristic.
-/

noncomputable section

open scoped IsMulCommutative

variable (K : Type) [Field K]

/-- The closure of the commutator subgroup of the separable absolute Galois
group, packaged as a closed subgroup.-/
def _root_.Tengoku.ClassfieldtheoryYamaguchi.absoluteCommutatorClosure :
    ClosedSubgroup Gal(SeparableClosure K / K) where
  toSubgroup :=
    (commutator Gal(SeparableClosure K / K)).topologicalClosure
  isClosed' := Subgroup.isClosed_topologicalClosure _

/-- The topological closure of the absolute commutator subgroup is normal.
@isnad1 id=normal.0h1v.s10.97bf806210c9 from=translated src=- shape=faacd8f5 vocab=5a801647
-/
instance _root_.Tengoku.ClassfieldtheoryYamaguchi.absoluteCommutatorClosure_normal :
    (absoluteCommutatorClosure K).Normal := by
  change
    ((commutator Gal(SeparableClosure K / K)).topologicalClosure).Normal
  infer_instance

/-- The maximal abelian subextension of the separable closure.-/
def _root_.Tengoku.ClassfieldtheoryYamaguchi.maximalAbelianExtension :
    IntermediateField K (SeparableClosure K) :=
  IntermediateField.fixedField (absoluteCommutatorClosure K).toSubgroup

/-- The maximal abelian subextension is Galois over the base field.
@isnad1 id=isgalois.0h1v.s9.2b4b6b6aff15 from=translated src=- shape=37b33571 vocab=c80ca2f2
-/
instance _root_.Tengoku.ClassfieldtheoryYamaguchi.maximalAbelianExtension_isGalois :
    IsGalois K (maximalAbelianExtension K) := by
  apply (InfiniteGalois.normal_iff_isGalois
    (maximalAbelianExtension K)).1
  change
    (IntermediateField.fixedField
      (absoluteCommutatorClosure K).toSubgroup).fixingSubgroup.Normal
  rw [InfiniteGalois.fixingSubgroup_fixedField
    (absoluteCommutatorClosure K)]
  infer_instance

/-- The algebraic quotient equivalence from the absolute topological
abelianization to the Galois group of the maximal abelian extension.-/
noncomputable def _root_.Tengoku.ClassfieldtheoryYamaguchi.absoluteAbelianizationMulEquivMaximalAbelianGalois :
    TopologicalAbelianization Gal(SeparableClosure K / K) ≃*
      Gal(maximalAbelianExtension K / K) :=
  InfiniteGalois.normalAutEquivQuotient (absoluteCommutatorClosure K)

/-- The algebraic equivalence sends a quotient class to restriction to the
maximal abelian extension.
@isnad1 id=eq.0h2v.s17.baa19a9258db from=translated src=- shape=b586675f vocab=d065ebe2
-/
@[simp]
theorem _root_.Tengoku.ClassfieldtheoryYamaguchi.absoluteAbelianizationMulEquivMaximalAbelianGalois_mk
    (sigma : Gal(SeparableClosure K / K)) :
    absoluteAbelianizationMulEquivMaximalAbelianGalois K
        (QuotientGroup.mk sigma) =
      AlgEquiv.restrictNormalHom (maximalAbelianExtension K) sigma :=
  rfl

/-- The algebraic equivalence from the absolute abelianization is continuous.
@isnad1 id=continuo.0h1v.s16.48d0f18d68a6 from=translated src=- shape=e7c4bf00 vocab=375b2937
-/
theorem _root_.Tengoku.ClassfieldtheoryYamaguchi.absoluteAbelianizationMulEquivMaximalAbelianGalois_continuous :
    Continuous (absoluteAbelianizationMulEquivMaximalAbelianGalois K) := by
  apply (QuotientGroup.isQuotientMap_mk
    (absoluteCommutatorClosure K).toSubgroup).continuous_iff.2
  refine (InfiniteGalois.restrictNormalHom_continuous
    (maximalAbelianExtension K)).congr ?_
  intro sigma
  exact
    (absoluteAbelianizationMulEquivMaximalAbelianGalois_mk K sigma).symm

/-- The canonical topological identification of the absolute separable
Galois group's abelianization with the maximal abelian Galois group.-/
noncomputable def _root_.Tengoku.ClassfieldtheoryYamaguchi.absoluteTopologicalAbelianizationEquivMaximalAbelianGalois :
    TopologicalAbelianization Gal(SeparableClosure K / K) ≃ₜ*
      Gal(maximalAbelianExtension K / K) := by
  letI : T2Space Gal(maximalAbelianExtension K / K) :=
    krullTopology_t2
  let h :
      TopologicalAbelianization Gal(SeparableClosure K / K) ≃ₜ
        Gal(maximalAbelianExtension K / K) :=
    Continuous.homeoOfEquivCompactToT2
      (f := (absoluteAbelianizationMulEquivMaximalAbelianGalois K).toEquiv)
      (absoluteAbelianizationMulEquivMaximalAbelianGalois_continuous K)
  exact
    { h with
      map_mul' :=
        (absoluteAbelianizationMulEquivMaximalAbelianGalois K).map_mul }

/-- The absolute topological abelianization is totally disconnected.
@isnad1 id=totallyd.0h1v.s11.36255af5bf52 from=translated src=- shape=7c5d9ad3 vocab=62f5cb76
-/
instance _root_.Tengoku.ClassfieldtheoryYamaguchi.absoluteTopologicalAbelianization_totallyDisconnectedSpace :
    TotallyDisconnectedSpace
      (TopologicalAbelianization Gal(SeparableClosure K / K)) :=
  Homeomorph.totallyDisconnectedSpace
    (absoluteTopologicalAbelianizationEquivMaximalAbelianGalois K).symm.toHomeomorph

/-- Every finite abelian intermediate field of the separable closure is
contained in the maximal abelian extension.
@isnad1 id=le.0h2v.s11.1196561f7176 from=translated src=- shape=025fb784 vocab=8f6a4fd4
-/
theorem _root_.Tengoku.ClassfieldtheoryYamaguchi.finiteAbelianIntermediateField_le_maximalAbelianExtension
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] :
    E ≤ maximalAbelianExtension K := by
  rw [maximalAbelianExtension, IntermediateField.le_iff_le]
  change
    (commutator Gal(SeparableClosure K / K)).topologicalClosure ≤
      E.fixingSubgroup
  apply Subgroup.topologicalClosure_minimal
  · rw [← E.restrictNormalHom_ker]
    exact
      Abelianization.commutator_subset_ker
        (AlgEquiv.restrictNormalHom
          (F := K) (K₁ := SeparableClosure K) E)
  · exact E.fixingSubgroup_isClosed

/-- A selected embedding of a finite abelian extension into the maximal
abelian extension.  Naming this embedding keeps downstream finite-coordinate
arguments independent of the implementation of the separable closure.-/
noncomputable def _root_.Tengoku.ClassfieldtheoryYamaguchi.finiteAbelianExtensionEmbeddingIntoMaximalAbelianExtension
    (L : Type*) [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    L →ₐ[K] maximalAbelianExtension K := by
  let i : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let e : L ≃ₐ[K] i.fieldRange := i.equivFieldRange
  letI : FiniteDimensional K i.fieldRange :=
    e.toLinearEquiv.finiteDimensional
  letI : IsAbelianGalois K i.fieldRange :=
    IsAbelianGalois.of_algHom e.symm.toAlgHom
  have hle : i.fieldRange ≤ maximalAbelianExtension K :=
    finiteAbelianIntermediateField_le_maximalAbelianExtension K i.fieldRange
  exact
    i.codRestrict (maximalAbelianExtension K).toSubalgebra
      (fun x => hle (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩))

/-- The finite Galois intermediate field of the maximal abelian extension
selected by a finite abelian extension.-/
noncomputable def _root_.Tengoku.ClassfieldtheoryYamaguchi.finiteAbelianExtensionInMaximalAbelianExtension
    (L : Type*) [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    FiniteGaloisIntermediateField K (maximalAbelianExtension K) :=
  let j := finiteAbelianExtensionEmbeddingIntoMaximalAbelianExtension K L
  { toIntermediateField := j.fieldRange
    finiteDimensional := j.equivFieldRange.toLinearEquiv.finiteDimensional
    isGalois := IsGalois.of_algEquiv j.equivFieldRange }

/-- The selected finite layer is canonically equivalent to the original
finite abelian extension.-/
noncomputable def _root_.Tengoku.ClassfieldtheoryYamaguchi.finiteAbelianExtensionEquivInMaximalAbelianExtension
    (L : Type*) [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    L ≃ₐ[K] finiteAbelianExtensionInMaximalAbelianExtension K L :=
  (finiteAbelianExtensionEmbeddingIntoMaximalAbelianExtension K L).equivFieldRange
-- Tengoku: root names of this library moved to Tengoku.ClassfieldtheoryYamaguchi so they do not collide with other libraries (generated)
