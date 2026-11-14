/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.FieldTheory.Galois.Basic
import Tengoku.Seed.FieldTheory.Normal.Closure
import Tengoku.Seed.NumberTheory.NumberField.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.ClassfieldtheoryYamaguchi end Tengoku.ClassfieldtheoryYamaguchi open Tengoku.ClassfieldtheoryYamaguchi
set_option autoImplicit false

/-!
# A finite normal closure of a number-field extension

This file places the normal-closure construction used throughout the
global theory below the adelic and splitting developments that consume
it.  The closure is formed inside mathlib's fixed algebraic closure, and
the original field is embedded by the canonical chosen lift.
-/

noncomputable section

universe u v

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- The normal closure of `L / K`, constructed inside a fixed
algebraic closure of `K`.-/
abbrev _root_.Tengoku.ClassfieldtheoryYamaguchi.finiteNormalClosure :=
  IntermediateField.normalClosure K L (AlgebraicClosure K)

/--
@isnad1 id=numberfi.0h2v.s7.cbe8620a8f4b from=translated src=- shape=30bdd4e5 vocab=96b33b28
-/
noncomputable instance _root_.Tengoku.ClassfieldtheoryYamaguchi.finiteNormalClosure_numberField :
    NumberField (finiteNormalClosure K L) :=
  NumberField.of_module_finite K (finiteNormalClosure K L)

/--
@isnad1 id=isgalois.0h2v.s7.a13373d312e5 from=translated src=- shape=1c7b8051 vocab=d5d48be3
-/
noncomputable instance _root_.Tengoku.ClassfieldtheoryYamaguchi.finiteNormalClosure_isGalois :
    IsGalois K (finiteNormalClosure K L) := by
  let f : L →ₐ[K] AlgebraicClosure K :=
    IsAlgClosed.lift
  let : Algebra L (AlgebraicClosure K) :=
    f.toRingHom.toAlgebra
  let : IsScalarTower K L (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq'
      f.comp_algebraMap.symm
  infer_instance

/-- A fixed embedding of `L` into its normal closure.-/
noncomputable def _root_.Tengoku.ClassfieldtheoryYamaguchi.finiteNormalClosureEmbedding :
    L →ₐ[K] finiteNormalClosure K L :=
  let f : L →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  f.codRestrict
    (IntermediateField.normalClosure K L
      (AlgebraicClosure K)).toSubalgebra
    (fun x =>
      f.fieldRange_le_normalClosure
        (show f x ∈ f.fieldRange from ⟨x, rfl⟩))

/-- The distinguished copy of `L` in its finite normal closure.-/
noncomputable def _root_.Tengoku.ClassfieldtheoryYamaguchi.finiteNormalClosureOriginalField :
    IntermediateField K (finiteNormalClosure K L) :=
  (finiteNormalClosureEmbedding K L).fieldRange

/-- The original extension is canonically equivalent to its
distinguished copy in the finite normal closure.-/
noncomputable def _root_.Tengoku.ClassfieldtheoryYamaguchi.finiteNormalClosureOriginalFieldEquiv :
    L ≃ₐ[K] finiteNormalClosureOriginalField K L :=
  (finiteNormalClosureEmbedding K L).equivFieldRange

omit [NumberField K] [NumberField L] in
/-- Normal closure is invariant under replacing its source by an
isomorphic field.
@isnad1 id=eq.1h5v.s8.4519b2a67957 from=translated src=- shape=df6bd335 vocab=a9e3310b
-/
theorem _root_.Tengoku.ClassfieldtheoryYamaguchi.normalClosure_eq_top_of_source_algEquiv
    {M E : Type*}
    [Field M] [Algebra K M]
    [Field E] [Algebra K E]
    (e : L ≃ₐ[K] E)
    (hclosure :
      IntermediateField.normalClosure K L M = ⊤) :
    IntermediateField.normalClosure K E M = ⊤ := by
  apply top_unique
  rw [← hclosure]
  apply
    (normalClosure_le_iff
      (K := L)).2
  intro f
  let g : E →ₐ[K] M :=
    f.comp e.symm.toAlgHom
  have hRange :
      f.fieldRange = g.fieldRange := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨e y, by simp [g]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨e.symm y, by simp [g]⟩
  rw [hRange]
  exact g.fieldRange_le_normalClosure

/-- The distinguished copy of `L` generates its finite normal closure
under its `K`-conjugates.
@isnad1 id=eq.0h2v.s12.33d81ba34aa2 from=translated src=- shape=9845bba4 vocab=7f449fef
-/
theorem _root_.Tengoku.ClassfieldtheoryYamaguchi.finiteNormalClosureOriginalField_normalClosure_eq_top :
    IntermediateField.normalClosure K
        (finiteNormalClosureOriginalField K L)
        (finiteNormalClosure K L) =
      ⊤ := by
  let : Nonempty (L →ₐ[K] AlgebraicClosure K) :=
    ⟨IsAlgClosed.lift⟩
  have hAbstract :
      IntermediateField.normalClosure K L
          (finiteNormalClosure K L) =
        ⊤ :=
    (Algebra.IsAlgebraic.isNormalClosure_iff.mp
      (show IsNormalClosure K L
          (finiteNormalClosure K L) from inferInstance)).2
  exact
    normalClosure_eq_top_of_source_algEquiv
      (K := K) (L := L)
      (finiteNormalClosureOriginalFieldEquiv K L)
      hAbstract

/-- The degree of the original extension is bounded by the degree of
its finite normal closure.
@isnad1 id=le.0h2v.s9.c8201dbcf7bc from=translated src=- shape=4c7b863f vocab=6c1f92fe
-/
theorem _root_.Tengoku.ClassfieldtheoryYamaguchi.finrank_le_finiteNormalClosure :
    Module.finrank K L ≤
      Module.finrank K (finiteNormalClosure K L) := by
  exact
    (finiteNormalClosureEmbedding K L).toLinearMap
      |>.finrank_le_finrank_of_injective
        (finiteNormalClosureEmbedding K L).injective

/-- A degree-one finite field extension is the base field as an
algebra.-/
noncomputable def _root_.Tengoku.ClassfieldtheoryYamaguchi.algEquivBaseOfFinrankEqOne
    (hdegree : Module.finrank K L = 1) :
    L ≃ₐ[K] K :=
  (AlgEquiv.ofBijective
    (Algebra.ofId K L)
    ((Algebra.finrank_eq_one_iff_bijective_algebraMap).mp
      hdegree)).symm
-- Tengoku: root names of this library moved to Tengoku.ClassfieldtheoryYamaguchi so they do not collide with other libraries (generated)
