/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.ClassfieldtheoryYamaguchi.ClassFieldTheory.AlgebraicNumberTheory.NormalClosure
import Tengoku.ClassfieldtheoryYamaguchi.GaloisCohomology.GroupTheory.Quotient
import Tengoku.Seed.FieldTheory.Galois.Abelian

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Maximal abelian subextensions inside finite normal closures

For a finite extension `L / K`, its chosen finite normal closure contains a
distinguished copy of `L`.  The subgroup fixing that copy, together with the
commutator subgroup of the full Galois group, cuts out the largest abelian
Galois intermediate field contained in the distinguished copy.
-/

noncomputable section

open scoped IsMulCommutative

universe u v

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- The subgroup of the finite-normal-closure Galois group fixing the
distinguished copy of the original extension.-/
noncomputable def finiteNormalClosureOriginalFixingSubgroup :
    Subgroup Gal(finiteNormalClosure K L / K) :=
  (finiteNormalClosureOriginalField K L).fixingSubgroup

/-- The relative Galois group over the distinguished original field is the
corresponding fixing subgroup of the full normal-closure Galois group.-/
noncomputable def finiteNormalClosureOriginalFixingSubgroupEquiv :
    Gal(finiteNormalClosure K L /
        finiteNormalClosureOriginalField K L) ≃*
      finiteNormalClosureOriginalFixingSubgroup K L := by
  change
    Gal(finiteNormalClosure K L /
        finiteNormalClosureOriginalField K L) ≃*
      (finiteNormalClosureOriginalField K L).fixingSubgroup
  exact
    (IntermediateField.fixingSubgroupEquiv
      (finiteNormalClosureOriginalField K L)).symm

/-- The largest abelian Galois intermediate field of the finite normal
closure that is contained in the distinguished copy of the original field.-/
noncomputable def finiteNormalClosureMaximalAbelianSubfield :
    IntermediateField K (finiteNormalClosure K L) :=
  IntermediateField.fixedField
    (finiteNormalClosureOriginalFixingSubgroup K L ⊔
      _root_.commutator Gal(finiteNormalClosure K L / K))

/-- The maximal abelian subfield is contained in the distinguished copy of
the original extension.
@isnad1 id=le.0h2v.s9.d944100fd170 from=translated src=- shape=2e09bba1 vocab=270252c9
-/
theorem finiteNormalClosureMaximalAbelianSubfield_le_originalField :
    finiteNormalClosureMaximalAbelianSubfield K L ≤
      finiteNormalClosureOriginalField K L := by
  let N := finiteNormalClosure K L
  let E : IntermediateField K N :=
    finiteNormalClosureOriginalField K L
  let G := Gal(N/K)
  let H : Subgroup G :=
    finiteNormalClosureOriginalFixingSubgroup K L
  change
    IntermediateField.fixedField
        (H ⊔ _root_.commutator G) ≤ E
  calc
    IntermediateField.fixedField
        (H ⊔ _root_.commutator G) ≤
        IntermediateField.fixedField H :=
      IntermediateField.fixedField_le le_sup_left
    _ = E := by
      change IntermediateField.fixedField E.fixingSubgroup = E
      exact IsGalois.fixedField_fixingSubgroup E

/-- Every abelian Galois intermediate field contained in the distinguished
original field is contained in the maximal abelian subfield.
@isnad1 id=le.1h3v.s11.d9c4e009e097 from=translated src=- shape=77fb5499 vocab=4e673007
-/
theorem finiteNormalClosureMaximalAbelianSubfield_greatest
    (F : IntermediateField K (finiteNormalClosure K L))
    [IsAbelianGalois K F]
    (hF : F ≤ finiteNormalClosureOriginalField K L) :
    F ≤ finiteNormalClosureMaximalAbelianSubfield K L := by
  let N := finiteNormalClosure K L
  let E : IntermediateField K N :=
    finiteNormalClosureOriginalField K L
  let G := Gal(N/K)
  let H : Subgroup G :=
    finiteNormalClosureOriginalFixingSubgroup K L
  change
    F ≤ IntermediateField.fixedField
      (H ⊔ _root_.commutator G)
  apply
    (IntermediateField.le_iff_le
      (H ⊔ _root_.commutator G) F).2
  apply sup_le
  · change E.fixingSubgroup ≤ F.fixingSubgroup
    exact IntermediateField.fixingSubgroup_le hF
  · rw [← F.restrictNormalHom_ker]
    exact Abelianization.commutator_subset_ker
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := N) F)
